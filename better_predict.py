import pandas as pd
import joblib
from sklearn.preprocessing import LabelEncoder
from sklearn.impute import SimpleImputer
import numpy as np
import os
from scipy.stats import entropy


# ====================== 特征提取函数 ======================
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
    """从单行数据中提取所有特征"""
    features = {}
    try:
        # ----------- 基础字段特征 ----------- 
        features['proto'] = row['Protocol']
        features['length'] = row['Length']

        # ----------- 解析Parsed_Hex字段 ----------- 
        parsed = eval(row['Parsed_Hex'])  # 确保数据是合法Python字典

        # 1. 网络层(IP)特征
        ip = parsed.get('ip', {})
        features.update({
            'ip_ttl': ip.get('ttl', 0),
            'ip_df_flag': 1 if ip.get('flags', {}).get('DF', False) else 0,
            'ip_len': ip.get('len', 0)
        })

        # 2. 传输层(TCP)特征
        tcp = parsed.get('tcp', {})
        features.update({
            'tcp_dport': tcp.get('dport', 0),
            'tcp_window': tcp.get('window', 0),
            'tcp_ack_flag': 1 if tcp.get('flags', {}).get('ACK', False) else 0
        })

        # 3. TLS特征
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
        return None  # 跳过错误行

    return features

# ====================== 数据加载与特征生成 ======================
def load_and_process_test_data(file_path):
    """加载测试数据并提取特征"""
    test_data = pd.read_excel(file_path)

    # 提取特征并过滤错误行
    feature_list = []
    for idx, row in test_data.iterrows():
        features = extract_all_features(row)
        if features is not None:
            feature_list.append(features)

    return pd.DataFrame(feature_list)

# ====================== 预测流程 ====================== 
if __name__ == "__main__":
    # 加载并处理测试数据
    test_file_path = './test.xlsx'  # 测试数据文件路径
    output_df = pd.read_excel(test_file_path)
    test_df = load_and_process_test_data(test_file_path)
    

    # 加载所有预处理对象
    model = joblib.load('./models/better/xgboost_traffic_model.pkl')
    label_encoder = joblib.load('./models/better/label_encoder.pkl')
    proto_encoder = joblib.load('./models/better/proto_encoder.pkl')
    imputer = joblib.load('./models/better/imputer.pkl')
    train_columns = joblib.load('./models/better/train_columns.pkl')  # 加载训练时的列顺序

    # ==== 关键修改1：强制列对齐 ====
    # 处理proto编码
    if 'proto' in test_df.columns:
        proto_encoded = proto_encoder.transform(test_df[['proto']])
        proto_encoded_df = pd.DataFrame(proto_encoded, columns=proto_encoder.get_feature_names_out(['proto']))
        test_df = pd.concat([test_df.drop('proto', axis=1), proto_encoded_df], axis=1)
    else:
        proto_encoded_df = pd.DataFrame(columns=proto_encoder.get_feature_names_out(['proto']))
        test_df = pd.concat([test_df, proto_encoded_df], axis=1)

    # 填充缺失列（确保特征数量一致）
    missing_cols = set(train_columns) - set(test_df.columns)
    for col in missing_cols:
        test_df[col] = 0  # 缺失列填充0

    # 按训练时的列顺序排序（必须严格一致）
    test_df = test_df[train_columns]

    # ==== 关键修改2：正确的缺失值填充 ====
    # 注意：这里不需要单独选择数值列，imputer已保存完整的填充策略
    X_test_imputed = imputer.transform(test_df)  # 直接使用全部列

    # 进行预测
    y_pred = model.predict(X_test_imputed)

    # 将预测结果添加为新列
    output_df['predicted_label'] = label_encoder.inverse_transform(y_pred)

    # 保存结果
    output_path = './Outputs/test_better_predictions.xlsx'
    output_df.to_excel(output_path, index=False)
    print(f"预测结果已保存至 {output_path}")