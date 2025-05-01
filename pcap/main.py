import pandas as pd
import binascii

# 读取 Excel 文件
df = pd.read_excel('your_file.xlsx')

# 显示读取的数据
print(df.head())  # 输出前几行数据进行查看

# 提取 Hex 列并解析
def parse_hex(hex_string):
    try:
        # 将 Hex 字符串转换为字节数据
        byte_data = bytes.fromhex(hex_string)
        # 返回解析后的字节数据，或者可以进一步解析成可读的格式
        return binascii.hexlify(byte_data).decode('utf-8')
    except Exception as e:
        return str(e)

# 对 Hex 列进行解析
df['Parsed_Hex'] = df['Hex'].apply(parse_hex)

# 输出解析后的结果
print(df[['No.', 'Time', 'Source', 'Destination', 'Protocol', 'Length', 'Hex', 'Parsed_Hex']].head())

# 保存修改后的数据到新的 Excel 文件（如果需要）
df.to_excel('parsed_file.xlsx', index=False)
