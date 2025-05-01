import pandas as pd
import binascii
from scapy.all import IP, TCP, raw
from scapy.layers.tls.record import TLS
import re
import os

xlsx_files = []

def recursive_listdir(path):

    files = os.listdir(path)
    for file in files:
        file_path = os.path.join(path, file)

        if os.path.isfile(file_path):
            xlsx_files.append(file_path)

        elif os.path.isdir(file_path):
          recursive_listdir(file_path)


def parse_hex(hex_string):
    """
    解析Hex字符串，返回IPv4、TCP、TLS分层结构
    输入示例： "45 00 00 a2 50 95 40 00 6b 06 d1 ef cd bc 0c 5b 0a 08 08 b2 01 bb ..."
    输出：包含IPv4头、TCP头、TLS记录层的字典
    """
    try:
        # 清理Hex字符串并转换为二进制数据
        hex_clean = re.sub(r'\s+', '', hex_string.strip())
        bytes_data = bytes.fromhex(hex_clean)
        
        # 初始化结果字典
        parsed = {"ip": {}, "tcp": {}, "tls_records": []}
        
        ####################################
        # Step 1: 解析IPv4头（20字节）
        ####################################
        ip_pkt = IP(bytes_data)
        parsed["ip"] = {
            "version": ip_pkt.version,
            "ihl": ip_pkt.ihl,  # 头长度（单位：4字节）
            "tos": ip_pkt.tos,
            "len": ip_pkt.len,   # 总长度（单位：字节）
            "id": ip_pkt.id,
            "flags": {           # 解析标志位
                "DF": ip_pkt.flags.DF,
                "MF": ip_pkt.flags.MF
            },
            "frag": ip_pkt.frag, # 片偏移
            "ttl": ip_pkt.ttl,
            "proto": ip_pkt.proto,
            "chksum": ip_pkt.chksum,
            "src": ip_pkt.src,
            "dst": ip_pkt.dst
        }
        
        ####################################
        # Step 2: 解析TCP头（20字节）
        ####################################
        if TCP in ip_pkt:
            tcp_pkt = ip_pkt[TCP]
            parsed["tcp"] = {
                "sport": tcp_pkt.sport,
                "dport": tcp_pkt.dport,
                "seq": tcp_pkt.seq,
                "ack": tcp_pkt.ack,
                "dataofs": tcp_pkt.dataofs,  # TCP头长度（单位：4字节）
                "flags": {                  # 标志位解析
                    "ACK": tcp_pkt.flags.ACK,
                    "SYN": tcp_pkt.flags.SYN,
                    "FIN": tcp_pkt.flags.FIN,
                    "PSH": tcp_pkt.flags.PSH
                },
                "window": tcp_pkt.window,
                "chksum": tcp_pkt.chksum,
                "urgptr": tcp_pkt.urgptr
            }
            
            ####################################
            # Step 3: 解析TLS记录层（从TCP载荷开始）
            ####################################
            tcp_payload = raw(tcp_pkt.payload)
            offset = 0
            
            # 循环解析多个TLS记录
            while offset < len(tcp_payload):
                if offset + 5 > len(tcp_payload):
                    break  # 剩余数据不足TLS头长度
                
                # 解析TLS记录头（5字节）
                content_type = tcp_payload[offset]
                tls_version = tcp_payload[offset+1:offset+3].hex()
                length = int.from_bytes(tcp_payload[offset+3:offset+5], byteorder='big')
                
                # 提取加密数据块
                end = offset + 5 + length
                if end > len(tcp_payload):
                    break  # 数据不完整
                encrypted_data = tcp_payload[offset+5:end].hex()
                
                # 记录TLS信息
                parsed["tls_records"].append({
                    "content_type": content_type,
                    "tls_version": tls_version,
                    "length": length,
                    "encrypted_data": encrypted_data
                })
                
                offset = end  # 移动到下一个记录
        
        return parsed
    
    except Exception as e:
        return {"error": str(e)}


def save_to_json(file, df):
    # 确保输出目录存在
    output_dir = './hex_jsons/'
    os.makedirs(output_dir, exist_ok=True)

    # 修复文件名提取逻辑（避免路径层级问题）
    filename = os.path.basename(file).replace('.xlsx', '.json')
    json_filename = os.path.join(output_dir, filename)

    # 提取前几行数据（保持为 DataFrame）
    parsed_hex_data = df[['Parsed_Hex']].head()  # 确保是 DataFrame，不是 Series

    # 保存为格式化 JSON（indent=4 表示缩进层级）
    parsed_hex_data.to_json(
        json_filename,
        orient='records',  # 按行保存为数组格式
        force_ascii=False,
        indent=4          # 关键参数：添加缩进和换行
    )

    print(f"JSON 文件已保存至: {json_filename}")


if __name__ == "__main__":
    recursive_listdir(r'./xlsx')

    for file in xlsx_files:
        # 读取 Excel 文件
        df = pd.read_excel(file)
        # 应用标准化
        save_to_json(file, df)
        
        # # 显示读取的数据
        # print(df.head())  # 输出前几行数据进行查看

        # # 对 Hex 列进行解析
        # df['Parsed_Hex'] = df['Hex'].apply(parse_hex)

        # # 显示解析后的数据
        # print(df['Parsed_Hex'].head())  # 输出前几行解析后的数据进行查看
        # # 将解析后的数据保存到新的 Excel 文件
        # df.to_excel(file, index=False)  # 保存到原文件，覆盖原数据
        # print(f"解析后的数据已保存到 {file}")

