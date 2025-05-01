import pandas as pd
import numpy as np
import seaborn as sns
import matplotlib.pyplot as plt
import os
from scipy.stats import entropy

# 计算Hex字符串的熵值
def calculate_entropy(hex_str):
    hex_str = hex_str.replace(" ", "")
    byte_values = [int(hex_str[i:i + 2], 16) for i in range(0, len(hex_str), 2) if i + 2 <= len(hex_str)]
    if not byte_values:
        return 0.0
    freq = np.bincount(byte_values, minlength=256)
    prob = freq / freq.sum()
    return entropy(prob, base=2)

# 解析Hex字符串的特征
def parse_hex_features(hex_str):
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

# 提取TLS特征
def extract_tls_features(tls_records):
    tls_features = {}
    if tls_records:
        content_types = [r.get('content_type', -1) for r in tls_records]
        tls_versions = [r.get('tls_version', '0000') for r in tls_records]
        encrypted_lengths = [r.get('length', 0) for r in tls_records]
        tls_features.update({
            "tls_version_main": int(tls_versions[0][:2], 16) if tls_versions else 0,
            "tls_content_type_mode": max(set(content_types), key=content_types.count) if content_types else -1,
            "tls_encrypted_mean": np.mean(encrypted_lengths) if encrypted_lengths else 0,
            "tls_record_count": len(tls_records)
        })
    return tls_features

# 提取所有特征
def extract_all_features(row):
    features = {}
    try:
        features['proto'] = row['Protocol']
        features['length'] = row['Length']

        parsed = eval(row['Parsed_Hex'])

        # IP层特征
        ip = parsed.get('ip', {})
        features.update({
            'ip_ttl': ip.get('ttl', 0),
            'ip_df_flag': 1 if ip.get('flags', {}).get('DF', False) else 0,
            'ip_len': ip.get('len', 0)
        })

        # TCP层特征
        tcp = parsed.get('tcp', {})
        features.update({
            'tcp_dport': tcp.get('dport', 0),
            'tcp_window': tcp.get('window', 0),
            'tcp_ack_flag': 1 if tcp.get('flags', {}).get('ACK', False) else 0
        })

        # TLS特征
        tls_features = extract_tls_features(parsed.get('tls_records', []))
        features.update({f"tls_{k}": v for k, v in tls_features.items()})

        # Hex字段特征
        hex_str = row['Hex'].replace(' ', '')
        hex_features = parse_hex_features(hex_str)
        features.update(hex_features)

        # 派生特征
        features['is_dynamic_port'] = 1 if features.get('tcp_dport', 0) > 1024 else 0
        features['is_modern_tls'] = 1 if features.get('tls_version_main', 0) >= 0x03 else 0
        features['label'] = row['app_aux']

    except Exception as e:
        print(f"Error processing row: {e}")
        return None  

    return features  

# 绘制所有特征的图
def plot_features_by_label(features_df, output_dir):
    # 获取唯一标签
    labels = features_df['label'].unique()
    
    # 创建目录保存图像
    os.makedirs(output_dir, exist_ok=True)

    # 绘制每个标签的特征图
    for label in labels:
        label_data = features_df[features_df['label'] == label]
        
        # 创建2行3列的子图布局
        num_features = len(features_df.columns) - 1  # 排除'label'列
        num_cols = 3
        num_rows = (num_features // num_cols) + (num_features % num_cols > 0)
        fig, axes = plt.subplots(num_rows, num_cols, figsize=(15, num_rows * 5))

        # 将axes展平，方便迭代
        axes = axes.flatten()

        # 按照特征的层次绘制每个特征
        feature_columns = [col for col in features_df.columns if col != 'label']
        for i, feature in enumerate(feature_columns):
            ax = axes[i]
            sns.histplot(label_data[feature], kde=True, bins=30, color='skyblue', ax=ax)
            ax.set_title(f'{feature}')  # 设置子图标题

        # 隐藏多余的空白子图
        for j in range(i + 1, len(axes)):
            axes[j].axis('off')

        # 调整布局
        plt.tight_layout(rect=[0, 0.03, 1, 0.95])

        # 保存图像
        file_name = f"{label}_all_features_combined.png"
        file_path = os.path.join(output_dir, file_name)
        plt.savefig(file_path)  # 保存为PNG文件
        plt.close()  # 关闭图像以释放内存

        print(f"图像已保存至: {file_path}")


xlsx_files = []

def recursive_listdir(path):

    files = os.listdir(path)
    for file in files:
        file_path = os.path.join(path, file)

        if os.path.isfile(file_path):
            xlsx_files.append(file_path)

        elif os.path.isdir(file_path):
          recursive_listdir(file_path)


# 主要流程
if __name__ == "__main__":
    # 假设数据已加载为DataFrame df，您可以根据您的数据调整这部分
    # df = pd.read_excel("data.xlsx")
    recursive_listdir(r'./xlsx')

    for file in xlsx_files:
        df = pd.read_excel(file)
        features_list = []
        for _, row in df.iterrows():
            features = extract_all_features(row)
            if features:
                features_list.append(features)

        features_df = pd.DataFrame(features_list)

        # 设置输出目录
        output_dir = './output_plots'
        
        # 绘制特征图
        plot_features_by_label(features_df, output_dir)
