import os
import pandas as pd
import numpy as np
from scipy.stats import entropy
from sklearn.preprocessing import LabelEncoder
from sklearn.model_selection import train_test_split
from sklearn.utils.class_weight import compute_sample_weight
from xgboost import XGBClassifier
from sklearn.metrics import classification_report
import joblib
from imblearn.over_sampling import SMOTE
from sklearn.impute import SimpleImputer
from sklearn.preprocessing import OneHotEncoder

# ====================== 特征计算工具函数 ======================
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


# ====================== 主特征提取函数 ======================
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

        # 标签处理
        features['label'] = row['app_aux']  # 确保列名正确

    except Exception as e:
        print(f"Error processing row: {e}")
        return None  # 跳过错误行

    return features


# ====================== 数据加载与特征生成 ======================
def load_and_process_data(folder_path):
    """加载并合并所有xlsx文件数据"""
    all_data = []
    xlsx_files = [f for f in os.listdir(folder_path) if f.endswith('.xlsx')]

    for file in xlsx_files:
        file_path = os.path.join(folder_path, file)
        try:
            raw_data = pd.read_excel(file_path)
            # 检查必要列是否存在
            required_columns = ['Protocol', 'Hex', 'Parsed_Hex', 'app_aux']
            if not all(col in raw_data.columns for col in required_columns):
                print(f"文件 {file} 缺少必要列，已跳过")
                continue
            all_data.append(raw_data)
        except Exception as e:
            print(f"读取文件 {file} 失败: {e}")
            continue

    if not all_data:
        raise ValueError("未找到有效数据文件")

    # 合并所有数据
    combined_data = pd.concat(all_data, ignore_index=True)

    # 提取特征并过滤错误行
    feature_list = []
    for idx, row in combined_data.iterrows():
        features = extract_all_features(row)
        if features is not None:
            feature_list.append(features)

    return pd.DataFrame(feature_list)


# ====================== 主流程 ======================
if __name__ == "__main__":
    # 数据加载
    folder_path = './xlsx'  # xlsx文件夹路径
    feature_df = load_and_process_data(folder_path)

    # 检查标签是否存在且为字符串
    if 'label' not in feature_df.columns:
        raise KeyError("标签列 'label' 不存在，请检查数据！")
    feature_df['label'] = feature_df['label'].astype(str)

    # ====================== 特征工程 ======================
    proto_encoder = OneHotEncoder(handle_unknown='ignore', sparse_output=False)

    proto_encoded = proto_encoder.fit_transform(feature_df[['proto']])
    proto_encoded_df = pd.DataFrame(proto_encoded, columns=proto_encoder.get_feature_names_out(['proto']))

    # 合并编码后的特征
    feature_df = pd.concat([feature_df.drop('proto', axis=1), proto_encoded_df], axis=1)

    # 保存编码器
    joblib.dump(proto_encoder, './models/better/proto_encoder.pkl')




    # 填充缺失值
    feature_df.fillna({
        'tls_encrypted_mean': 0,
        'hex_entropy': feature_df['hex_entropy'].median(),
        'hex_mean': 0,
        'hex_std': 0
    }, inplace=True)

    # 标签编码
    label_encoder = LabelEncoder()
    feature_df['label_encoded'] = label_encoder.fit_transform(feature_df['label'])

    # ====================== 模型训练 ======================
    # 分离特征和标签
    X = feature_df.drop(['label', 'label_encoded'], axis=1)
    y = feature_df['label_encoded']

    # 检查类别数量
    num_classes = len(np.unique(y))
    print(f"检测到类别数量: {num_classes}")

    # 划分训练测试集（分层抽样）
    X_train, X_test, y_train, y_test = train_test_split(
        X, y,
        test_size=0.2,
        stratify=y,  # 保持类别分布
        random_state=42
    )

    # ====================== 缺失值处理 ======================
    # 训练阶段保存 imputer
    imputer = SimpleImputer(strategy='mean')
    X_train_imputed = imputer.fit_transform(X_train)
    joblib.dump(imputer, './models/better/imputer.pkl')  # 保存填充器
    
    X_test_imputed = imputer.transform(X_test)

    # ====================== SMOTE 过采样 ======================
    smote = SMOTE(sampling_strategy='auto', random_state=42)
    X_train_resampled, y_train_resampled = smote.fit_resample(X_train_imputed, y_train)

    # ====================== 样本加权 ======================
    sample_weights = compute_sample_weight(class_weight='balanced', y=y_train_resampled)

    # ====================== 训练模型 ======================
    model = XGBClassifier(
        objective='multi:softprob',
        num_class=num_classes,  # 动态设置类别数
        n_estimators=300,
        max_depth=6,
        learning_rate=0.05,
        use_label_encoder=False,
        eval_metric='mlogloss'
    )
    model.fit(X_train_resampled, y_train_resampled, sample_weight=sample_weights)

    # 预测与评估
    y_pred = model.predict(X_test_imputed)
    print("\n分类报告：")
    print(classification_report(y_test, y_pred, target_names=label_encoder.classes_, zero_division=0))

    # 特征重要性分析
    importance_df = pd.DataFrame({
        'feature': X.columns,
        'importance': model.feature_importances_
    }).sort_values('importance', ascending=False)
    print("\n特征重要性Top10：")
    print(importance_df.head(10))

    # 保存模型和编码器
    joblib.dump(model, './models/better/xgboost_traffic_model.pkl')
    joblib.dump(label_encoder, './models/better/label_encoder.pkl')
    # 训练代码末尾添加：
    joblib.dump(X_train.columns.tolist(), './models/better/train_columns.pkl')
    print("模型和编码器已保存！")
