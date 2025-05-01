import pandas as pd
import numpy as np
from scipy.stats import entropy
import joblib

# ====================== 加载模型和编码器 ======================
model = joblib.load('models/old/xgboost_traffic_model.pkl')
label_encoder = joblib.load('models/old/label_encoder.pkl')

# ====================== 特征计算工具函数（与训练代码一致）======================
def calculate_entropy(hex_str):
    """计算Hex字符串的字节熵值"""
    hex_str = hex_str.replace(" ", "")
    byte_values = [int(hex_str[i:i + 2], 16) for i in range(0, len(hex_str), 2) if i + 2 <= len(hex_str)]
    if not byte_values:
        return 0.0
    freq = np.bincount(byte_values, minlength=256)
    prob = freq / freq.sum()
    return entropy(prob, base=2)

def parse_hex_features(hex_str):
    """解析Hex字段的统计特征"""
    hex_str = hex_str.replace(" ", "")
    bytes_list = [int(hex_str[i:i + 2], 16) for i in range(0, len(hex_str), 2) if i + 2 <= len(hex_str)]
    if not bytes_list:
        return {}
    return {
        "hex_mean": np.mean(bytes_list),
        "hex_std": np.std(bytes_list),
        "hex_entropy": calculate_entropy(hex_str),
        "hex_length": len(bytes_list)
    }

def extract_tls_features(tls_records):
    """从TLS记录中提取特征"""
    if not tls_records:
        return {}
    content_types = [r.get('content_type', -1) for r in tls_records]
    tls_versions = [r.get('tls_version', '0000') for r in tls_records]
    encrypted_lengths = [r.get('length', 0) for r in tls_records]
    return {
        "tls_version_main": int(tls_versions[0][:2], 16) if tls_versions else 0,
        "tls_content_type_mode": max(set(content_types), key=content_types.count) if content_types else -1,
        "tls_encrypted_mean": np.mean(encrypted_lengths) if encrypted_lengths else 0,
        "tls_record_count": len(tls_records)
    }

def extract_all_features(row):
    """特征提取函数（与训练代码一致）"""
    features = {}
    try:
        # ----------- 基础字段特征 -----------
        features['proto'] = row['Protocol']
        features['length'] = row['Length']

        # ----------- 解析Parsed_Hex字段 -----------
        parsed = eval(row['Parsed_Hex'])

        # 1. 网络层(IP)特征
        ip = parsed.get('ip', {})
        features.update({
            'ip_ttl': ip.get('ttl', 0),
            'ip_df_flag': 1 if ip.get('flags', {}).get('DF', False) else 0,
            'ip_len': ip.get('len', 0)
        })

        # 2. 传输层(TCP/UDP)特征
        tcp = parsed.get('tcp', {})
        features.update({
            'tcp_dport': tcp.get('dport', 0),
            'tcp_window': tcp.get('window', 0),
            'tcp_ack_flag': 1 if tcp.get('flags', {}).get('ACK', False) else 0
        })

        # 3. TLS特征（如果存在）
        tls_features = extract_tls_features(parsed.get('tls_records', []))
        features.update({f"tls_{k}": v for k, v in tls_features.items()})

        # 4. Hex字段特征
        hex_str = row['Hex'].replace(' ', '')
        hex_features = parse_hex_features(hex_str)
        features.update(hex_features)

        # ----------- 派生特征 -----------
        features['is_dynamic_port'] = 1 if features.get('tcp_dport', 0) > 1024 else 0
        features['is_modern_tls'] = 1 if features.get('tls_version_main', 0) >= 0x03 else 0

    except Exception as e:
        print(f"Error processing row: {e}")
        return None

    return features

# ====================== 主流程 ======================
if __name__ == "__main__":
    # 加载测试数据
    test_df = pd.read_excel('test.xlsx')
    
    # 提取特征
    feature_list = []
    for idx, row in test_df.iterrows():
        features = extract_all_features(row)
        if features is not None:
            feature_list.append(features)
    feature_df = pd.DataFrame(feature_list)
    
    # 处理类别特征（与训练一致）
    feature_df = pd.get_dummies(feature_df, columns=['proto'], dummy_na=True)
    
    # 对齐特征列（关键步骤）
    # 获取模型训练时的特征顺序
    try:
        required_columns = model.feature_names_in_
    except AttributeError:
        raise RuntimeError("模型不支持特征名称推断，请确保使用XGBoost 1.3+版本")
    
    # 创建全零DataFrame并填充现有特征
    aligned_df = pd.DataFrame(columns=required_columns)
    aligned_df = aligned_df.fillna(0)
    for col in feature_df.columns:
        if col in aligned_df.columns:
            aligned_df[col] = feature_df[col]
    
    # 填充缺失值（与训练逻辑一致）
    aligned_df.fillna({
        'tls_encrypted_mean': 0,
        'hex_entropy': aligned_df['hex_entropy'].median(),
        'hex_mean': 0,
        'hex_std': 0
    }, inplace=True)
    
    # 最终填充所有剩余NaN为0
    aligned_df.fillna(0, inplace=True)
    
    # 预测
    y_pred_encoded = model.predict(aligned_df)
    y_pred = label_encoder.inverse_transform(y_pred_encoded)
    
    # 添加预测结果到原始数据
    test_df['predicted_label'] = y_pred
    
    output_path = 'Outputs/test_original_predictions.xlsx'
    test_df.to_excel(output_path, index=False)
    print(f"预测结果已保存到 {output_path}")