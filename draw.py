import pandas as pd
import numpy as np
import seaborn as sns
import matplotlib.pyplot as plt
from scipy.stats import entropy
import os

# 初始化存储xlsx文件的列表
xlsx_files = []

def recursive_listdir(path):
    """递归列出指定目录下的所有文件"""
    files = os.listdir(path)
    for file in files:
        file_path = os.path.join(path, file)
        if os.path.isfile(file_path):
            xlsx_files.append(file_path)  # 如果是文件，添加到列表
        elif os.path.isdir(file_path):
            recursive_listdir(file_path)  # 如果是文件夹，递归调用

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
    """解析Hex字符串的统计特征"""
    hex_str = hex_str.replace(" ", "")
    bytes_list = [int(hex_str[i:i + 2], 16) for i in range(0, len(hex_str), 2) if i + 2 <= len(hex_str)]
    if not bytes_list:
        return {}
    return {
        "hex_mean": np.mean(bytes_list),  # 字节平均值
        "hex_std": np.std(bytes_list),    # 字节标准差
        "hex_entropy": calculate_entropy(hex_str),  # 字节熵值
        "hex_length": len(bytes_list)    # 字节长度
    }

def extract_features(row):
    """从单行数据中提取特征"""
    features = {}
    try:
        # 解析Parsed_Hex字段
        parsed = eval(row['Parsed_Hex'])  # 确保数据是合法的Python字典

        # 提取Hex特征
        hex_str = row['Hex'].replace(' ', '')
        hex_features = parse_hex_features(hex_str)
        features.update(hex_features)

        # 提取TLS特征
        tls_records = parsed.get('tls_records', [])
        if tls_records:
            content_types = [r.get('content_type', -1) for r in tls_records]
            tls_versions = [r.get('tls_version', '0000') for r in tls_records]
            encrypted_lengths = [r.get('length', 0) for r in tls_records]
            features.update({
                "tls_version_main": int(tls_versions[0][:2], 16) if tls_versions else 0,  # TLS版本
                "tls_content_type_mode": max(set(content_types), key=content_types.count) if content_types else -1,  # TLS内容类型
                "tls_encrypted_mean": np.mean(encrypted_lengths) if encrypted_lengths else 0,  # TLS加密长度均值
                "tls_record_count": len(tls_records)  # TLS记录数量
            })

        # 派生特征
        features['is_dynamic_port'] = 1 if row.get('tcp_dport', 0) > 1024 else 0  # 判断是否为动态端口
        features['is_modern_tls'] = 1 if features.get('tls_version_main', 0) >= 0x03 else 0  # 判断是否为现代TLS

    except Exception as e:
        print(f"Error processing row: {e}")
        return None  # 跳过有错误的行

    return features

if __name__ == "__main__":
    recursive_listdir(r'./xlsx')  # 列出所有xlsx文件

    for file in xlsx_files:
        # 加载数据
        df = pd.read_excel(file)

        # 提取特征
        features_list = []
        for _, row in df.iterrows():
            features = extract_features(row)
            if features:
                features['label'] = row['app_aux']  # 添加标签
                features_list.append(features)

        # 转换为DataFrame
        features_df = pd.DataFrame(features_list)

        # 设置绘图风格
        sns.set(style="whitegrid")

        # 获取唯一标签
        labels = features_df['label'].unique()

        # 创建保存图像的目录
        output_dir = './output_plots'
        os.makedirs(output_dir, exist_ok=True)

        # 为每个标签绘制并保存合并的图像
        for label in labels:
            label_data = features_df[features_df['label'] == label]
            
            # 创建一个包含四个子图的图像
            fig, axes = plt.subplots(2, 2, figsize=(15, 10))  # 2行2列的子图
            fig.suptitle(f'{label} - 特征分布', fontsize=16)  # 设置大标题

            # 绘制每个特征的分布图
            for i, feature in enumerate(['hex_mean', 'hex_std', 'hex_entropy', 'hex_length']):
                ax = axes[i // 2, i % 2]  # 获取当前子图的位置
                sns.histplot(label_data[feature], kde=True, bins=30, color='skyblue', ax=ax)
                ax.set_title(f'{feature}')  # 设置子图标题

            # 调整布局，使标题和子图不会重叠
            plt.tight_layout(rect=[0, 0.03, 1, 0.95])

            # 保存图像
            file_name = f"{label}_features_combined.png"  # 文件名由标签组成
            file_path = os.path.join(output_dir, file_name)
            plt.savefig(file_path)  # 保存为PNG文件
            plt.close()  # 关闭图像以释放内存

            print(f"图像已保存至: {file_path}")