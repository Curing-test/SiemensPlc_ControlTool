# -*- coding: utf-8 -*-
"""
PLC 可视化查询工具 V2.6.1 (代码格式化 & 日志编码修正)

改进：
- 使用 black 风格格式化代码。
- 在 logging.basicConfig 中也明确指定 UTF-8 编码，增强日志编码一致性。
- 增加了关于日志文件编码的注释。
- 包含 V2.6 的地址格式解耦、String 调试等功能。
"""

# --- 标准库导入 ---
import ipaddress
import json
import logging
import math
import os
import sqlite3
import sys
import threading
import time
import webbrowser
from datetime import datetime, timedelta
from datetime import time as dt_time
from logging.handlers import RotatingFileHandler, TimedRotatingFileHandler

# --- 第三方库导入 ---
try:
    import snap7
    from snap7.exceptions import Snap7Exception
    from snap7.util import (
        get_bool,
        get_byte,
        get_dword,
        get_dint,
        get_int,
        get_real,
        get_word,
    )
except ImportError:
    print("错误: 未找到 snap7 库。请先安装: pip install python-snap7")
    sys.exit(1)

try:
    from tkcalendar import DateEntry
except ImportError:
    print("错误: 未找到 tkcalendar 库。请先安装: pip install tkcalendar")
    sys.exit(1)

# --- Tkinter 导入 ---
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

# --- 常量定义 ---
MAX_RESULT_UI_CACHE = 5000
MAX_ALARM_UI_CACHE = 10000
HISTORY_PAGE_SIZE = 50
CONFIG_FILE = "configs.json"
ADDRESS_MAPPING_FILE = "address_mapping.json"
ALARM_HISTORY_FILE = "alarm_history.jsonl"
LOG_FILE = "plc_query.log"
DB_FILE = "plc_query_data.db"
DATA_RETENTION_DAYS = 7

# --- 日志配置 ---
# 确保日志目录存在
log_dir = os.path.dirname(LOG_FILE)
if log_dir and not os.path.exists(log_dir):
    try:
        os.makedirs(log_dir)
    except OSError as e:
        print(f"创建日志目录 {log_dir} 失败: {e}")

# 配置日志格式
log_formatter = logging.Formatter(
    "%(asctime)s.%(msecs)03d - %(levelname)s [%(threadName)s] - %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)

# 配置按时间滚动的处理器，显式使用 UTF-8
log_time_handler = TimedRotatingFileHandler(
    LOG_FILE,
    when="D",
    interval=1,
    backupCount=DATA_RETENTION_DAYS,
    encoding="utf-8",  # 确保写入时使用 UTF-8
)
log_time_handler.setFormatter(log_formatter)

# 配置按大小滚动的处理器，显式使用 UTF-8
log_size_handler = RotatingFileHandler(
    LOG_FILE,
    maxBytes=20 * 1024 * 1024,
    backupCount=5,
    encoding="utf-8",  # 确保写入时使用 UTF-8
)
log_size_handler.setFormatter(log_formatter)

# 获取根日志记录器并清除现有处理器（防止重复日志）
root_logger = logging.getLogger()
if root_logger.hasHandlers():
    root_logger.handlers.clear()

# 配置基础日志设置，也指定 handlers 和 encoding
# 注意：日志文件本身是 UTF-8 编码。如果查看时出现乱码，
# 请确保使用的文本编辑器或查看工具是以 UTF-8 编码打开该文件的。
logging.basicConfig(
    level=logging.DEBUG,
    handlers=[log_time_handler, log_size_handler],
    encoding="utf-8",  # 明确指定基础配置编码（通常由handlers覆盖，但加上无害）
)

# 降低 snap7 库的日志级别，避免过多信息
logging.getLogger("snap7").setLevel(logging.WARNING)

logging.info("--- PLC 可视化查询工具 启动 (V3.0) ---")


# --- 辅助函数 ---
def convert_to_string(data: bytearray) -> str:
    """将 Siemens S7 String 的 bytearray 解码为 Python 字符串。"""
    if not isinstance(data, bytearray):
        logging.warning(f"[convert_to_string] 无效的数据类型: {type(data)}")
        return ""
    logging.debug(
        f"[convert_to_string] 接收到的原始 bytearray (len={len(data)}): {data.hex()}"
    )
    try:
        if len(data) >= 2:
            max_len_byte = data[0]
            actual_len = data[1]
            logging.debug(
                f"[convert_to_string] MaxLenByte: {max_len_byte}, ActualLen: {actual_len}"
            )
            if actual_len > max_len_byte:
                logging.warning(
                    f"[convert_to_string] 警告: ActualLen ({actual_len}) > MaxLenByte ({max_len_byte}). 可能数据损坏。"
                )
            if 2 + actual_len > len(data):
                logging.warning(
                    f"[convert_to_string] 警告: ActualLen ({actual_len}) 超出接收到的数据长度 ({len(data)}). 可能读取不完整。"
                )
                actual_len = len(data) - 2

            start_index = 2
            end_index = start_index + actual_len
            logging.debug(
                f"[convert_to_string] 尝试解码字节范围: {start_index} 到 {end_index}"
            )
            decoded_string = data[start_index:end_index].decode(
                "utf-8", errors="replace"
            )
            return decoded_string.rstrip("\x00")
        else:
            logging.warning(
                f"[convert_to_string] 接收到过短的 bytearray (len={len(data)}): {data.hex()}"
            )
            return ""
    except UnicodeDecodeError as ude:
        logging.warning(
            f"[convert_to_string] 字符串数据 UTF-8 解码失败: {ude}. 返回原始数据的十六进制表示。"
        )
        return data.hex()
    except IndexError:
        logging.warning(
            f"[convert_to_string] 字符串转换期间发生 IndexError (数据格式可能错误): {data.hex()}"
        )
        return data.hex()
    except Exception as e:
        logging.error(f"[convert_to_string] 转换时发生意外错误: {e}", exc_info=True)
        return data.hex()


def bytearray_to_string(ba: bytearray, encoding: str = 'utf-8') -> str:
    """
    将 bytearray 转换为字符串

    参数:
        ba (bytearray): 输入的 bytearray 对象
        encoding (str): 解码使用的编码方式（默认 'utf-8'）

    返回:
        str: 转换后的字符串

    异常:
        UnicodeDecodeError: 如果编码不匹配且未处理错误
    """
    try:
        return ba.decode(encoding)
    except UnicodeDecodeError:
        return f"编码错误：请检查编码方式（当前使用 {encoding}）"

def validate_config(config: dict, config_name: str = "Unknown") -> bool:
    """
    验证单个 PLC 配置字典，包括 address_format_prefix，但不强制其与 data_type 关联。
    """
    required_keys = [
        "plc_address",
        "db_block",
        "start_position",
        "data_type",
        "address_format_prefix",
    ]
    supported_types = [
        "bool",
        "byte",
        "word",
        "dword",
        "int",
        "dint",
        "real",
        "string",
    ]
    supported_format_prefixes = ["DBX", "DBB", "DBW", "DBD"]

    if not isinstance(config, dict):
        logging.warning("配置验证失败：输入不是字典。")
        return False

    try:
        for key in required_keys:
            if key not in config:
                if key == "address_format_prefix":
                    data_type_temp = config.get("data_type")
                    if data_type_temp == "bool":
                        config[key] = "DBX"
                    elif data_type_temp in ["word", "int"]:
                        config[key] = "DBW"
                    elif data_type_temp in ["dword", "dint", "real"]:
                        config[key] = "DBD"
                    else:
                        config[key] = "DBB"
                    logging.warning(
                        f"配置 '{config_name}' 缺少 '{key}'，已根据数据类型推断为 '{config[key]}'"
                    )
                else:
                    raise KeyError(f"缺少必需的键: '{key}'")

        ipaddress.ip_address(config["plc_address"])
        db = int(config["db_block"])
        if db < 0:
            raise ValueError("DB 块号不能为负数。")
        data_type = config["data_type"]
        if data_type not in supported_types:
            raise ValueError(
                f"不支持的数据类型: '{data_type}'。支持: {supported_types}"
            )

        address_format = config["address_format_prefix"].upper()
        if address_format not in supported_format_prefixes:
            raise ValueError(
                f"无效的地址格式前缀: '{address_format}'。必须是 {supported_format_prefixes} 之一。"
            )
        config["address_format_prefix"] = address_format

        start_pos_str = str(config["start_position"])
        if "." in start_pos_str:
            if data_type == "bool":
                parts = start_pos_str.split(".")
                if len(parts) != 2 or not all(p.isdigit() for p in parts):
                    raise ValueError("Bool 地址必须是 '<byte>.<bit>' 格式。")
                byte, bit = int(parts[0]), int(parts[1])
                if not (0 <= bit <= 7):
                    raise ValueError("Bool 位号必须在 0-7 之间。")
                if address_format != "DBX":
                    logging.warning(
                        f"配置 '{config_name}': Bool 类型数据将强制使用 DBX 地址格式，忽略配置的 '{address_format}'。"
                    )
                    config["address_format_prefix"] = "DBX"
            else:
                val = float(start_pos_str)
                if not val.is_integer() or val < 0:
                    raise ValueError(
                        f"类型 '{data_type}' 的起始地址 '{start_pos_str}' 格式无效。"
                    )
                int(val)
        else:
            # if data_type == "bool":
            #     raise ValueError("Bool 地址格式必须是 '<byte>.<bit>'。")
            # else:
                val = int(start_pos_str)
                if val < 0:
                    raise ValueError("起始地址不能为负数。")

        str_len = int(config.get("string_length", 30))
        if data_type == "string" and str_len <= 0:
            raise ValueError("字符串长度必须为正数。")
        scan_count = int(config.get("scan_count", 1))
        if scan_count <= 0:
            raise ValueError("扫描数量必须为正数。")
        interval_val = float(config.get("interval", 1.0))
        if interval_val <= 0:
            raise ValueError("查询间隔必须为正数。")
        interval_len_val = int(config.get("interval_length", 0))
        if interval_len_val < 0:
            raise ValueError("地址间隔不能为负数。")

        logging.debug(
            f"配置 '{config_name}' 验证通过 (地址格式前缀: {address_format})。"
        )
        return True

    except (ValueError, TypeError, KeyError, ipaddress.AddressValueError, Exception) as e:
        logging.warning(f"配置 '{config_name}' 验证失败: {e} | 配置内容: {config}")
        return False


# --- 默认配置结构 ---
DEFAULT_CONFIG = {
    "plc_address": "192.168.0.1",
    "db_block": "1",
    "start_position": "0",
    "data_type": "real",
    "address_format_prefix": "DBD",
    "string_length": "30",
    "scan_count": "1",
    "interval": "1.0",
    "interval_length": "0",
    "continuous": False,
}


# --- 主应用程序类 ---
class PLCVisualizationTool:
    """PLC 可视化查询工具的主应用程序类。"""

    def __init__(self, root_window):
        """初始化应用程序。"""
        self.root = root_window
        self.root.title("PLC 可视化查询工具 V3.0")
        self.root.geometry("1350x850")
        self.root.option_add("*Font", "TkDefaultFont 9")

        self.style = ttk.Style()
        self._apply_theme()

        self.db_conn = None
        self.db_cursor = None
        self._init_db()

        self.top_frame = ttk.Frame(self.root, padding="10 5 10 0")
        self.top_frame.pack(fill=tk.X)
        self.time_label = ttk.Label(
            self.top_frame, text="", font=("Segoe UI", 14, "bold")
        )
        self.time_label.pack(side=tk.RIGHT)
        self.update_time()

        self.configs = self.load_configs()
        self.address_map = self.load_address_mapping()
        self.query_threads = []
        self.querying = False
        self.prev_values = {}
        self.error_count = {}

        self.query_all = tk.BooleanVar(value=False)
        self.show_history_ui = tk.BooleanVar(value=True)
        self.continuous = tk.BooleanVar(value=False)

        self.original_data = []
        self.alarm_original_data = []
        self.history_search_results = []

        self.current_page = 1
        self.current_alarm_page = 1
        self.current_history_page = 1
        self.page_size = 50
        self.total_pages = 1
        self.total_alarm_pages = 1
        self.total_history_pages = 1

        self.create_menu()
        self.create_operation_area()
        self.create_notebook_tabs()

        self.status_label = ttk.Label(
            root_window, text="就绪", anchor=tk.W, padding="10 2 10 2"
        )
        self.status_label.pack(side=tk.BOTTOM, fill=tk.X)

        self.delete_old_db_records()
        self.load_alarm_history()
        self.update_alarm_display()
        self.update_result_display()
        self.update_history_display()

        self.client_for_validation = snap7.client.Client()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    def _apply_theme(self):
        """尝试应用一个现代的 ttk 主题。"""
        available = self.style.theme_names()
        logging.debug(f"可用的 ttk 主题: {available}")
        preferred = ["vista", "xpnative", "clam", "alt", "default"]
        for theme in preferred:
            if theme in available:
                try:
                    self.style.theme_use(theme)
                    logging.info(f"使用主题: {theme}")
                    bg_color = self.style.lookup("TFrame", "background")
                    self.root.configure(bg=bg_color)
                    return
                except tk.TclError:
                    logging.warning(f"应用主题 '{theme}' 失败。")
        logging.warning("未找到或应用首选主题，使用系统默认。")
        self.root.configure(bg="#f0f0f0")

    # --- 数据库方法 ---
    def _init_db(self):
        """初始化 SQLite 数据库连接、游标，并创建必要的表和索引。"""
        try:
            self.db_conn = sqlite3.connect(DB_FILE, check_same_thread=False)
            self.db_cursor = self.db_conn.cursor()
            logging.info(f"成功连接到数据库: {DB_FILE}")
            self.db_cursor.execute(
                """
                CREATE TABLE IF NOT EXISTS query_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT, timestamp TEXT NOT NULL,
                    config_name TEXT NOT NULL, address TEXT NOT NULL,
                    address_name TEXT, data_type TEXT, value TEXT )
            """
            )
            self.db_cursor.execute(
                "CREATE INDEX IF NOT EXISTS idx_timestamp ON query_log (timestamp)"
            )
            self.db_cursor.execute(
                "CREATE INDEX IF NOT EXISTS idx_address ON query_log (address)"
            )
            self.db_cursor.execute(
                "CREATE INDEX IF NOT EXISTS idx_address_name ON query_log (address_name)"
            )
            self.db_conn.commit()
            logging.info("数据库表 'query_log' 和相关索引已初始化。")
        except sqlite3.Error as e:
            logging.error(f"数据库初始化错误: {e}", exc_info=True)
            messagebox.showerror(
                "数据库错误", f"无法初始化或连接数据库 '{DB_FILE}':\n{e}", parent=self.root
            )
            self.db_conn = None
            self.db_cursor = None

    def _close_db(self):
        """安全地关闭 SQLite 数据库连接。"""
        if self.db_conn:
            try:
                self.db_conn.commit()
                self.db_conn.close()
                logging.info("数据库连接已关闭。")
            except sqlite3.Error as e:
                logging.error(f"关闭数据库连接时出错: {e}", exc_info=True)
        self.db_conn = None
        self.db_cursor = None

    def delete_old_db_records(self):
        """从 query_log 表中删除早于 DATA_RETENTION_DAYS 的记录。"""
        if not self.db_conn or not self.db_cursor:
            logging.warning("数据库未连接。跳过删除旧记录。")
            return
        try:
            cutoff_date = datetime.now() - timedelta(days=DATA_RETENTION_DAYS)
            cutoff_str = cutoff_date.strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
            logging.info(f"正在删除早于 {cutoff_str} 的数据库记录...")
            self.db_cursor.execute(
                "DELETE FROM query_log WHERE timestamp < ?", (cutoff_str,)
            )
            deleted_count = self.db_cursor.rowcount
            self.db_conn.commit()
            if deleted_count > 0:
                logging.info(f"成功删除 {deleted_count} 条旧的数据库记录。")
            else:
                logging.info("未找到符合删除条件的旧数据库记录。")
        except sqlite3.Error as e:
            logging.error(f"删除旧数据库记录时出错: {e}", exc_info=True)

    def save_results_to_db(self, results_batch: list):
        """将一批查询结果保存到 SQLite 数据库。"""
        if not self.db_conn or not self.db_cursor:
            logging.error("数据库未连接。无法保存结果。")
            return False
        if not results_batch:
            logging.debug("没有结果需要保存到数据库。")
            return True
        sql = """INSERT INTO query_log (timestamp, config_name, address, address_name, data_type, value) VALUES (?, ?, ?, ?, ?, ?)"""
        try:
            self.db_cursor.executemany(sql, results_batch)
            self.db_conn.commit()
            logging.debug(f"成功将 {len(results_batch)} 条结果保存到数据库。")
            return True
        except sqlite3.Error as e:
            logging.error(f"将结果批处理保存到数据库时出错: {e}", exc_info=True)
            try:
                self.db_conn.rollback()
                logging.warning("由于插入错误，数据库事务已回滚。")
            except sqlite3.Error as rb_e:
                logging.error(f"回滚数据库事务失败: {rb_e}")
            messagebox.showwarning(
                "数据库写入失败",
                f"无法将部分或全部查询结果保存到数据库:\n{e}",
                parent=self.root,
            )
            return False

    # --- 配置和映射文件处理 ---
    def load_configs(self) -> dict:
        """从 CONFIG_FILE 加载并验证配置。"""
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                configs_from_file = json.load(f)
            if not isinstance(configs_from_file, dict):
                raise TypeError("配置文件根必须是字典。")
            valid_configs = {}
            for name, config_data in configs_from_file.items():
                if isinstance(config_data, dict):
                    full_config = DEFAULT_CONFIG.copy()
                    full_config.update(config_data)
                    if validate_config(full_config, config_name=name):
                        valid_configs[name] = full_config
                else:
                    logging.warning(
                        f"跳过 {CONFIG_FILE} 中的无效条目 '{name}' (不是字典)。"
                    )
            if not valid_configs:
                logging.warning(
                    f"'{CONFIG_FILE}' 不包含有效配置或是空的。使用默认示例。"
                )
                if os.path.exists(CONFIG_FILE) and os.path.getsize(CONFIG_FILE) > 2:
                    messagebox.showwarning(
                        "配置加载警告",
                        f"配置文件 '{CONFIG_FILE}' 中未找到有效配置。\n请检查文件格式或添加配置。",
                        parent=self.root,
                    )
                return {"默认配置 (示例)": DEFAULT_CONFIG.copy()}
            else:
                logging.info(f"已加载 {len(valid_configs)} 个有效配置。")
                return valid_configs
        except FileNotFoundError:
            logging.info(f"未找到 '{CONFIG_FILE}'。使用默认示例。")
            return {"默认配置 (示例)": DEFAULT_CONFIG.copy()}
        except (json.JSONDecodeError, TypeError) as e:
            logging.error(f"解码来自 '{CONFIG_FILE}' 的 JSON/格式错误: {e}")
            messagebox.showerror(
                "配置错误",
                f"配置文件 '{CONFIG_FILE}' 格式错误。\n错误: {e}\n\n将使用默认配置。",
                parent=self.root,
            )
            return {"默认配置 (示例)": DEFAULT_CONFIG.copy()}
        except Exception as e:
            logging.error(f"从 '{CONFIG_FILE}' 加载配置失败: {e}", exc_info=True)
            messagebox.showerror("错误", f"加载配置文件失败: {e}", parent=self.root)
            return {"默认配置 (示例)": DEFAULT_CONFIG.copy()}

    def save_configs(self):
        """将当前配置 (self.configs) 保存到 CONFIG_FILE。"""
        try:
            example_key = "默认配置 (示例)"
            configs_to_save = {
                k: v
                for k, v in self.configs.items()
                if k != example_key or v != DEFAULT_CONFIG
            }
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(configs_to_save, f, indent=4, ensure_ascii=False)
            logging.info(f"配置已成功保存到 {CONFIG_FILE}。")
        except Exception as e:
            logging.error(f"保存配置失败: {e}", exc_info=True)
            messagebox.showerror("错误", f"保存配置失败: {e}", parent=self.root)

    def load_address_mapping(self) -> dict:
        """从 ADDRESS_MAPPING_FILE 加载地址到名称的映射。"""
        mapping = {}
        if not os.path.exists(ADDRESS_MAPPING_FILE):
            logging.warning(f"未找到 '{ADDRESS_MAPPING_FILE}'。不使用名称。")
            return mapping
        try:
            with open(ADDRESS_MAPPING_FILE, "r", encoding="utf-8") as f:
                mapping_from_file = json.load(f)
            if isinstance(mapping_from_file, dict):
                mapping = mapping_from_file
                logging.info(
                    f"已从 {ADDRESS_MAPPING_FILE} 加载 {len(mapping)} 个地址映射。"
                )
            else:
                logging.error(f"{ADDRESS_MAPPING_FILE} 中的格式无效：根不是字典。")
                messagebox.showerror(
                    "地址映射错误",
                    f"地址映射文件 '{ADDRESS_MAPPING_FILE}' 格式无效。",
                    parent=self.root,
                )
        except json.JSONDecodeError as e:
            logging.error(f"从 {ADDRESS_MAPPING_FILE} 解码 JSON 错误: {e}")
            messagebox.showerror(
                "地址映射错误",
                f"解析地址映射文件 '{ADDRESS_MAPPING_FILE}' 失败: {e}",
                parent=self.root,
            )
        except Exception as e:
            logging.error(f"加载 {ADDRESS_MAPPING_FILE} 失败: {e}", exc_info=True)
            messagebox.showerror("地址映射错误", f"加载地址映射出错: {e}", parent=self.root)
        return mapping

    def reload_address_mapping(self):
        """重新加载地址映射文件。"""
        logging.info("正在重新加载地址映射...")
        self.address_map = self.load_address_mapping()
        messagebox.showinfo(
            "地址映射", f"已重新加载地址映射 ({len(self.address_map)} 条).", parent=self.root
        )
        self.update_status("地址映射已重新加载")

    # --- GUI 创建方法 ---
    def create_menu(self):
        """创建主应用程序菜单栏。"""
        menubar = tk.Menu(self.root)
        config_menu = tk.Menu(menubar, tearoff=0)
        config_menu.add_command(label="新增配置", command=self.add_config)
        config_menu.add_command(label="修改配置", command=self.edit_config)
        config_menu.add_command(label="删除配置", command=self.delete_config)
        config_menu.add_separator()
        config_menu.add_command(label="导入配置", command=self.import_configs)
        config_menu.add_command(label="导出配置", command=self.export_configs)
        config_menu.add_separator()
        config_menu.add_command(
            label="重新加载地址映射", command=self.reload_address_mapping
        )
        menubar.add_cascade(label="配置管理", menu=config_menu)
        view_menu = tk.Menu(menubar, tearoff=0)
        view_menu.add_command(label="查看日志文件", command=self.open_log_file)
        view_menu.add_command(label="打开数据文件位置", command=self.open_db_folder)
        menubar.add_cascade(label="查看", menu=view_menu)
        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="使用说明", command=self.show_help)
        menubar.add_cascade(label="帮助", menu=help_menu)
        self.root.config(menu=menubar)

    def create_operation_area(self):
        """创建顶部区域，包含实时查询控件。"""
        self.operation_frame = ttk.Frame(self.root, padding="10 5")
        self.operation_frame.pack(fill=tk.X)
        config_frame = ttk.Frame(self.operation_frame)
        config_frame.pack(side=tk.LEFT, padx=(0, 15))
        ttk.Label(config_frame, text="选择配置:").grid(
            row=0, column=0, padx=(0, 5), sticky="w"
        )
        self.config_combobox = ttk.Combobox(
            config_frame, values=list(self.configs.keys()), state="readonly", width=25
        )
        if self.configs:
            self.config_combobox.set(list(self.configs.keys())[0])
        else:
            self.config_combobox.set("请先添加配置")
            self.config_combobox.config(state=tk.DISABLED)
        self.config_combobox.grid(row=0, column=1)
        control_frame = ttk.Frame(self.operation_frame)
        control_frame.pack(side=tk.LEFT, padx=15)
        self.query_all_checkbox = ttk.Checkbutton(
            control_frame, text="查询所有", variable=self.query_all
        )
        self.query_all_checkbox.grid(row=0, column=0, padx=5, sticky="w")
        self.continuous_checkbox = ttk.Checkbutton(
            control_frame, text="持续查询", variable=self.continuous
        )
        self.continuous_checkbox.grid(row=0, column=1, padx=5, sticky="w")
        self.show_history_ui_checkbox = ttk.Checkbutton(
            control_frame, text="追加历史(界面)", variable=self.show_history_ui
        )
        self.show_history_ui_checkbox.grid(row=0, column=2, padx=5, sticky="w")
        button_frame = ttk.Frame(self.operation_frame)
        button_frame.pack(side=tk.LEFT, padx=(15, 0))
        self.query_button = ttk.Button(
            button_frame, text="查 询", command=self.start_query, width=8
        )
        self.query_button.pack(side=tk.LEFT, padx=3)
        self.stop_button = ttk.Button(
            button_frame, text="停 止", command=self.stop_query, state=tk.DISABLED, width=8
        )
        self.stop_button.pack(side=tk.LEFT, padx=3)
        self.clear_button = ttk.Button(
            button_frame, text="清空活动列表", command=self.clear_ui_results, width=11
        )
        self.clear_button.pack(side=tk.LEFT, padx=3)
        is_example_only = len(self.configs) == 1 and "默认配置 (示例)" in self.configs
        if not self.configs or is_example_only:
            self.query_button.config(state=tk.DISABLED)

    def create_notebook_tabs(self):
        """创建包含结果、报警和历史查询选项卡的 Notebook 控件。"""
        self.notebook = ttk.Notebook(self.root, padding="5 5 5 5")
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 5))
        self.result_tab = ttk.Frame(self.notebook, padding="5")
        self.alarm_tab = ttk.Frame(self.notebook, padding="5")
        self.history_tab = ttk.Frame(self.notebook, padding="5")
        self.notebook.add(self.result_tab, text=" 查询结果 ", sticky="nsew")
        self.notebook.add(self.alarm_tab, text=" 报警监控 ", sticky="nsew")
        self.notebook.add(self.history_tab, text=" 历史查询 ", sticky="nsew")
        self.init_result_tab(self.result_tab)
        self.init_alarm_tab(self.alarm_tab)
        self.init_history_tab(self.history_tab)
        self.root.grid_rowconfigure(2, weight=1)
        self.root.grid_columnconfigure(0, weight=1)

    def _init_treeview_tab(
        self,
        parent_frame,
        tree_columns,
        tree_col_widths,
        tree_widget_attr,
        page_label_attr,
        first_cmd,
        prev_cmd,
        next_cmd,
        last_cmd,
        page_size,
    ):
        """初始化包含 Treeview 和分页控件的选项卡的通用辅助函数。"""
        tree_frame = ttk.Frame(parent_frame)
        tree_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 5))
        treeview = ttk.Treeview(
            tree_frame, columns=tree_columns, show="headings", height=15
        )
        setattr(self, tree_widget_attr, treeview)
        for col in tree_columns:
            width = tree_col_widths.get(col, 100)
            minwidth = 40 if col == "序号" else 60
            stretch = tk.YES if col in ["值", "地址名称", "旧值", "新值"] else tk.NO
            treeview.heading(col, text=col, anchor=tk.CENTER)
            treeview.column(
                col, width=width, minwidth=minwidth, anchor=tk.CENTER, stretch=stretch
            )
        vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=treeview.yview)
        hsb = ttk.Scrollbar(tree_frame, orient="horizontal", command=treeview.xview)
        treeview.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        tree_frame.grid_rowconfigure(0, weight=1)
        tree_frame.grid_columnconfigure(0, weight=1)
        treeview.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        pagination_frame = ttk.Frame(parent_frame)
        pagination_frame.pack(fill=tk.X, pady=(5, 0))
        spacer = ttk.Frame(pagination_frame)
        spacer.pack(side=tk.LEFT, expand=True)
        ttk.Button(pagination_frame, text="首页", command=first_cmd, width=6).pack(
            side=tk.LEFT, padx=2
        )
        ttk.Button(pagination_frame, text="上一页", command=prev_cmd, width=7).pack(
            side=tk.LEFT, padx=2
        )
        page_label = ttk.Label(
            pagination_frame, text="第 1 / 1 页", width=15, anchor=tk.CENTER
        )
        page_label.pack(side=tk.LEFT, padx=5, ipady=2)
        setattr(self, page_label_attr, page_label)
        ttk.Button(pagination_frame, text="下一页", command=next_cmd, width=7).pack(
            side=tk.LEFT, padx=2
        )
        ttk.Button(pagination_frame, text="末页", command=last_cmd, width=6).pack(
            side=tk.LEFT, padx=2
        )
        spacer = ttk.Frame(pagination_frame)
        spacer.pack(side=tk.RIGHT, expand=True)

    def init_result_tab(self, parent_frame):
        """初始化“查询结果”选项卡（实时数据）。"""
        columns = ("序号", "配置名称", "时间", "地址", "地址名称", "类型", "值")
        col_widths = {
            "序号": 50,
            "配置名称": 150,
            "时间": 160,
            "地址": 180,
            "地址名称": 200,
            "类型": 80,
            "值": 300,
        }
        self._init_treeview_tab(
            parent_frame,
            columns,
            col_widths,
            tree_widget_attr="result_tree",
            page_label_attr="page_label",
            first_cmd=self.go_to_first_page,
            prev_cmd=self.go_to_previous_page,
            next_cmd=self.go_to_next_page,
            last_cmd=self.go_to_last_page,
            page_size=self.page_size,
        )

    def init_alarm_tab(self, parent_frame):
        """初始化“报警监控”选项卡。"""
        columns = ("时间", "配置名称", "地址", "地址名称", "旧值", "新值")
        col_widths = {
            "时间": 160,
            "配置名称": 150,
            "地址": 180,
            "地址名称": 200,
            "旧值": 150,
            "新值": 150,
        }
        self._init_treeview_tab(
            parent_frame,
            columns,
            col_widths,
            tree_widget_attr="alarm_tree",
            page_label_attr="alarm_page_label",
            first_cmd=self.go_to_first_page_alarm,
            prev_cmd=self.go_to_previous_page_alarm,
            next_cmd=self.go_to_next_page_alarm,
            last_cmd=self.go_to_last_page_alarm,
            page_size=self.page_size,
        )

    def init_history_tab(self, parent_frame):
        """初始化“历史查询”选项卡。"""
        search_frame = ttk.Frame(parent_frame, padding="10 10 10 5")
        search_frame.pack(fill=tk.X)
        search_frame.columnconfigure(7, weight=1)
        row_idx = 0
        ttk.Label(search_frame, text="开始时间:").grid(
            row=row_idx, column=0, padx=(0, 2), pady=5, sticky="w"
        )
        self.start_date_entry = DateEntry(
            search_frame,
            width=12,
            background="darkblue",
            foreground="white",
            borderwidth=2,
            date_pattern="y-mm-dd",
            locale="zh_CN",
        )
        self.start_date_entry.grid(
            row=row_idx, column=1, padx=(0, 5), pady=5, sticky="w"
        )
        self.start_time_entry = ttk.Entry(search_frame, width=10)
        self.start_time_entry.grid(
            row=row_idx, column=2, padx=(0, 15), pady=5, sticky="w"
        )
        self.start_time_entry.insert(0, "00:00:00")
        ttk.Label(search_frame, text="结束时间:").grid(
            row=row_idx, column=3, padx=(10, 2), pady=5, sticky="w"
        )
        self.end_date_entry = DateEntry(
            search_frame,
            width=12,
            background="darkblue",
            foreground="white",
            borderwidth=2,
            date_pattern="y-mm-dd",
            locale="zh_CN",
        )
        self.end_date_entry.grid(
            row=row_idx, column=4, padx=(0, 5), pady=5, sticky="w"
        )
        self.end_time_entry = ttk.Entry(search_frame, width=10)
        self.end_time_entry.grid(
            row=row_idx, column=5, padx=(0, 15), pady=5, sticky="w"
        )
        self.end_time_entry.insert(0, "23:59:59")
        ttk.Label(search_frame, text="地址/名称过滤:").grid(
            row=row_idx, column=6, padx=(10, 2), pady=5, sticky="w"
        )
        self.address_filter_entry = ttk.Entry(search_frame)
        self.address_filter_entry.grid(
            row=row_idx, column=7, padx=(0, 10), pady=5, sticky="ew"
        )
        button_frame = ttk.Frame(search_frame)
        button_frame.grid(row=row_idx, column=8, padx=(5, 0), pady=5, sticky="e")
        search_button = ttk.Button(
            button_frame, text="查询历史", command=self.search_history, width=10
        )
        search_button.pack(side=tk.LEFT, padx=(0, 5))
        clear_hist_button = ttk.Button(
            button_frame, text="清空列表", command=self.clear_history_results, width=10
        )
        clear_hist_button.pack(side=tk.LEFT)
        columns = ("序号", "配置名称", "时间", "地址", "地址名称", "类型", "值")
        col_widths = {
            "序号": 50,
            "配置名称": 150,
            "时间": 160,
            "地址": 180,
            "地址名称": 200,
            "类型": 80,
            "值": 300,
        }
        self._init_treeview_tab(
            parent_frame,
            columns,
            col_widths,
            tree_widget_attr="history_tree",
            page_label_attr="history_page_label",
            first_cmd=self.go_to_first_page_history,
            prev_cmd=self.go_to_previous_page_history,
            next_cmd=self.go_to_next_page_history,
            last_cmd=self.go_to_last_page_history,
            page_size=HISTORY_PAGE_SIZE,
        )

    # --- 配置 CRUD 方法 ---
    def create_config_entries(self, parent_window, current_config: dict) -> dict:
        """创建并填充新增/编辑配置对话框的条目小部件，包括地址格式前缀。"""
        entries = {}
        row_index = 1
        labels = {
            "plc_address": "PLC 地址:",
            "db_block": "DB 块 (DB号):",
            "start_position": "起始地址 (字节或X.Y):",
            "data_type": "数据类型:",
            "address_format_prefix": "地址格式前缀:",
            "string_length": "字符串长度 (仅String):",
            "scan_count": "扫描数量 (点数):",
            "interval": "查询间隔 (秒):",
            "interval_length": "地址间隔 (字节):",
        }
        data_types = [
            "bool",
            "byte",
            "word",
            "dword",
            "int",
            "dint",
            "real",
            "string",
        ]
        format_prefixes = ["DBX", "DBB", "DBW", "DBD"]

        parent_window.columnconfigure(1, weight=1)
        for key, label_text in labels.items():
            lbl = ttk.Label(parent_window, text=label_text)
            lbl.grid(row=row_index, column=0, padx=(10, 5), pady=5, sticky="w")
            if key == "data_type":
                widget = ttk.Combobox(
                    parent_window, values=data_types, state="readonly", width=33
                )
                widget.set(current_config.get(key, DEFAULT_CONFIG.get(key)))
            elif key == "address_format_prefix":
                widget = ttk.Combobox(
                    parent_window, values=format_prefixes, state="readonly", width=33
                )
                widget.set(current_config.get(key, DEFAULT_CONFIG.get(key)))
            else:
                widget = ttk.Entry(parent_window, width=35)
                default_val = DEFAULT_CONFIG.get(key, "")
                widget.insert(0, str(current_config.get(key, default_val)))
            widget.grid(row=row_index, column=1, padx=(0, 10), pady=5, sticky="ew")
            entries[key] = widget
            row_index += 1
        return entries

    def _show_config_dialog(
        self, title, save_command, initial_config, old_name=None
    ):
        """创建新增/编辑配置对话框窗口的辅助函数。"""
        config_window = tk.Toplevel(self.root)
        config_window.title(title)
        config_window.geometry("450x460")  # 可能需要调整高度以适应新字段
        config_window.resizable(False, False)
        config_window.grab_set()
        config_window.transient(self.root)
        form_frame = ttk.Frame(config_window, padding="10")
        form_frame.pack(fill=tk.BOTH, expand=True)
        form_frame.columnconfigure(1, weight=1)
        ttk.Label(form_frame, text="配置名称:").grid(
            row=0, column=0, padx=(0, 5), pady=10, sticky="w"
        )
        config_name_entry = ttk.Entry(form_frame)
        if old_name:
            config_name_entry.insert(0, old_name)
        config_name_entry.grid(row=0, column=1, padx=(0, 10), pady=10, sticky="ew")
        entries = self.create_config_entries(form_frame, initial_config)
        button_frame = ttk.Frame(config_window, padding="10")
        button_frame.pack(fill=tk.X)
        save_args = (config_window, entries, config_name_entry)
        if old_name:
            save_args += (old_name,)
        ttk.Button(
            button_frame, text="保存", command=lambda args=save_args: save_command(*args)
        ).pack(side=tk.RIGHT, padx=5)
        ttk.Button(button_frame, text="取消", command=config_window.destroy).pack(
            side=tk.RIGHT
        )
        config_name_entry.focus_set()

    def add_config(self):
        """打开对话框以添加新的 PLC 配置。"""
        self._show_config_dialog(
            title="新增配置", save_command=self.save_new_config, initial_config=DEFAULT_CONFIG
        )

    def edit_config(self):
        """打开对话框以编辑选定的 PLC 配置。"""
        selected_name = self.config_combobox.get()
        example_key = "默认配置 (示例)"
        no_config_msg = "请先添加配置"
        if not selected_name or selected_name in [example_key, no_config_msg]:
            messagebox.showwarning("操作无效", "请选择一个有效的配置进行修改。", parent=self.root)
            return
        if selected_name not in self.configs:
            messagebox.showerror("错误", f"未找到配置 '{selected_name}'。", parent=self.root)
            return
        current_config = self.configs[selected_name]
        self._show_config_dialog(
            title=f"修改配置 - {selected_name}",
            save_command=self.save_edited_config,
            initial_config=current_config,
            old_name=selected_name,
        )

    def _validate_and_save_config(
        self, window, entries, name_entry, old_name=None
    ):
        """验证和保存新增或编辑配置的通用逻辑。"""
        config_name = name_entry.get().strip()
        example_key = "默认配置 (示例)"
        if not config_name:
            messagebox.showerror("错误", "配置名称不能为空。", parent=window)
            return None
        is_new_name = old_name is None or config_name != old_name
        if config_name == example_key and (
            old_name is None or old_name != example_key
        ):
            messagebox.showerror(
                "错误", f"不能使用保留名称 '{example_key}'.", parent=window
            )
            return None
        if is_new_name and config_name in self.configs:
            messagebox.showerror(
                "错误", f"配置名称 '{config_name}' 已被其他配置使用。", parent=window
            )
            return None
        new_config_data = {}
        for key, widget in entries.items():
            try:
                value = (
                    widget.get().strip() if isinstance(widget, tk.Entry) else widget.get()
                )
                new_config_data[key] = value
            except AttributeError:
                logging.error(f"获取键 '{key}' 的控件值时出错")
                new_config_data[key] = None
        if not validate_config(new_config_data, config_name=config_name):
            messagebox.showerror(
                "错误",
                "配置参数无效或不完整。\n请检查地址格式前缀、Bool地址格式等，并查看日志获取详情。",
                parent=window,
            )
            return None
        # 保存配置
        if old_name and is_new_name and old_name in self.configs:
            del self.configs[old_name]
        if example_key in self.configs and (
            old_name is None or config_name != example_key
        ):
            if len(self.configs) > 1 or old_name is None:
                del self.configs[example_key]
        self.configs[config_name] = new_config_data
        self.save_configs()
        return config_name

    def save_new_config(self, window, entries, name_entry):
        """保存新添加的配置。"""
        saved_name = self._validate_and_save_config(window, entries, name_entry)
        if saved_name:
            config_keys = list(self.configs.keys())
            self.config_combobox["values"] = config_keys
            self.config_combobox.set(saved_name)
            self.config_combobox.config(state="readonly")
            self.update_ui_state(querying=False)
            logging.info(f"新配置 '{saved_name}' 已添加并保存。")
            self.update_status(f"配置 '{saved_name}' 已添加")
            window.destroy()

    def save_edited_config(self, window, entries, name_entry, old_config_name):
        """保存编辑后的配置。"""
        saved_name = self._validate_and_save_config(
            window, entries, name_entry, old_name=old_config_name
        )
        if saved_name:
            config_keys = list(self.configs.keys())
            self.config_combobox["values"] = config_keys
            self.config_combobox.set(saved_name)
            self.update_ui_state(querying=False)
            log_msg = f"配置 '{old_config_name}' 已修改"
            if saved_name != old_config_name:
                log_msg += f" (重命名为 '{saved_name}')"
            logging.info(log_msg + " 并保存。")
            self.update_status(f"配置 '{saved_name}' 已修改")
            window.destroy()

    def delete_config(self):
        """删除当前选定的配置。"""
        selected_name = self.config_combobox.get()
        example_key = "默认配置 (示例)"
        no_config_msg = "请先添加配置"
        if not selected_name or selected_name in [example_key, no_config_msg]:
            messagebox.showwarning("操作无效", "请选择一个有效的配置进行删除。", parent=self.root)
            return
        if selected_name not in self.configs:
            messagebox.showerror("错误", f"未找到配置 '{selected_name}'。", parent=self.root)
            return
        if messagebox.askyesno(
            "确认删除",
            f"确定要永久删除配置 '{selected_name}' 吗？",
            icon="warning",
            parent=self.root,
        ):
            try:
                del self.configs[selected_name]
            except Exception as e:
                logging.error(f"删除配置 '{selected_name}' 时出错: {e}", exc_info=True)
                messagebox.showerror("删除错误", f"删除配置失败: {e}", parent=self.root)
                return
            if not self.configs:
                self.configs[example_key] = DEFAULT_CONFIG.copy()
            self.save_configs()
            config_keys = list(self.configs.keys())
            self.config_combobox["values"] = config_keys
            self.config_combobox.set(config_keys[0])
            self.config_combobox.config(
                state="readonly" if config_keys[0] != example_key else tk.DISABLED
            )
            self.update_ui_state(querying=False)
            logging.info(f"配置 '{selected_name}' 已删除。")
            self.update_status(f"配置 '{selected_name}' 已删除")

    # --- 报警历史处理 ---
    def save_alarm_history(
        self, config_name, address, address_name, old_value, new_value
    ):
        """将单个报警记录追加到持久化的 JSON Lines 文件中。"""
        entry = {
            "时间": datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "配置名称": config_name,
            "地址": address,
            "地址名称": address_name or "",
            "旧值": str(old_value),
            "新值": str(new_value),
        }
        try:
            with open(ALARM_HISTORY_FILE, "a", encoding="utf-8") as f:
                f.write(json.dumps(entry, ensure_ascii=False) + "\n")
        except Exception as e:
            logging.error(f"无法将报警记录保存到 {ALARM_HISTORY_FILE}: {e}")

    def load_alarm_history(self):
        """从 JSON Lines 文件加载报警历史到 UI 内存缓存中。"""
        self.alarm_original_data = []
        if not os.path.exists(ALARM_HISTORY_FILE):
            logging.info(
                f"未找到报警历史文件 '{ALARM_HISTORY_FILE}'。将在第一次报警时创建。"
            )
            return
        temp_list = []
        try:
            with open(ALARM_HISTORY_FILE, "r", encoding="utf-8") as f:
                for line_num, line in enumerate(f, 1):
                    line_content = line.strip()
                    if not line_content:
                        continue
                    try:
                        entry = json.loads(line_content)
                        temp_list.append(
                            (
                                entry.get("时间", "N/A"),
                                entry.get("配置名称", "N/A"),
                                entry.get("地址", "N/A"),
                                entry.get("地址名称", ""),
                                entry.get("旧值", "N/A"),
                                entry.get("新值", "N/A"),
                            )
                        )
                    except json.JSONDecodeError:
                        logging.warning(
                            f"跳过 {ALARM_HISTORY_FILE} 中无效的 JSON 行 {line_num}: {line_content[:100]}..."
                        )
                    except Exception as parse_e:
                        logging.error(
                            f"处理来自 {ALARM_HISTORY_FILE} 的行 {line_num} 时出错: {parse_e} - 行内容: {line_content[:100]}..."
                        )
            if len(temp_list) > MAX_ALARM_UI_CACHE:
                logging.warning(
                    f"加载的报警历史 ({len(temp_list)}) 超过 UI 缓存限制 ({MAX_ALARM_UI_CACHE})。将截断最旧的报警。"
                )
                self.alarm_original_data = temp_list[-MAX_ALARM_UI_CACHE:]
            else:
                self.alarm_original_data = temp_list
            self.alarm_original_data.reverse()
            logging.info(
                f"已从 {ALARM_HISTORY_FILE} 加载 {len(self.alarm_original_data)} 条报警记录到 UI 缓存。"
            )
        except Exception as e:
            logging.error(f"加载 {ALARM_HISTORY_FILE} 失败: {e}", exc_info=True)
            messagebox.showerror("错误", f"加载报警记录文件失败: {e}", parent=self.root)

    # --- 查询执行和数据处理 ---
    def start_query(self):
        """根据用户选择启动 PLC 查询过程。"""
        if self.querying:
            logging.warning("请求启动查询，但查询已在运行中。")
            return
        selected_config = self.config_combobox.get()
        is_example = selected_config == "默认配置 (示例)"
        is_no_cfg_msg = selected_config == "请先添加配置"
        has_valid_configs = any(
            name != "默认配置 (示例)" for name in self.configs
        )
        query_all_checked = self.query_all.get()
        if not query_all_checked and (is_no_cfg_msg or is_example):
            messagebox.showwarning(
                "启动查询失败",
                "请选择一个有效的配置或勾选 '查询所有'。\n(无法直接查询示例配置)",
                parent=self.root,
            )
            return
        if query_all_checked and not has_valid_configs:
            messagebox.showwarning(
                "查询所有失败", "没有有效的非示例配置可供查询。", parent=self.root
            )
            return
        if not self.configs:
            messagebox.showwarning("启动查询失败", "没有配置可查询。", parent=self.root)
            return
        try:
            self.querying = True
            self.update_ui_state(querying=True)
            self.query_threads = []
            self.error_count.clear()
            if not self.show_history_ui.get():
                logging.info("清除 UI 实时结果缓存（追加关闭）。")
                self.original_data.clear()
                self.current_page = 1
                self.update_result_display()
            self.update_status("正在启动查询...")
            configs_to_query = []
            if query_all_checked:
                configs_to_query = [
                    (name, cfg)
                    for name, cfg in self.configs.items()
                    if name != "默认配置 (示例)"
                ]
                log_msg = f"开始查询所有 {len(configs_to_query)} 个有效配置..."
            else:
                configs_to_query = [(selected_config, self.configs[selected_config])]
                log_msg = f"开始查询选定配置: '{selected_config}'..."
            logging.info(log_msg)
            for config_name, config_data in configs_to_query:
                thread_config = config_data.copy()
                thread_config["continuous"] = self.continuous.get()
                thread_config["_config_name"] = config_name
                thread = threading.Thread(
                    target=self.run_query_thread,
                    args=(thread_config,),
                    daemon=True,
                    name=f"Query-{config_name}",
                )
                self.query_threads.append(thread)
                thread.start()
            self.update_status("查询进行中...")
        except Exception as e:
            logging.error(f"启动查询过程时出错: {e}", exc_info=True)
            messagebox.showerror("启动错误", f"启动查询时发生错误: {e}", parent=self.root)
            self.stop_query()

    def run_query_thread(self, thread_config: dict):
        """每个查询线程执行的主要函数。"""
        config_name = thread_config.get("_config_name", "Unknown")
        plc_address = thread_config.get("plc_address", "N/A")
        is_continuous = thread_config.get("continuous", False)
        try:
            interval = max(0.1, float(thread_config.get("interval", 1.0)))
        except ValueError:
            interval = 1.0
        self.error_count[config_name] = 0
        max_consecutive_errors = 5
        client = snap7.client.Client()
        is_connected = False
        consecutive_read_errors = 0
        try:
            while self.querying:
                if not is_connected:
                    if not self.querying:
                        break
                    try:
                        status_msg = f"({config_name}) 连接中..."
                        self.root.after(0, self.update_status, status_msg)
                        logging.debug(f"({config_name}) 尝试连接: {plc_address}")
                        client.connect(plc_address, 0, 1)
                        is_connected = client.get_connected()
                    except (Snap7Exception, OSError, Exception) as conn_e:
                        is_connected = False
                        self.error_count[config_name] += 1
                        err_msg = f"({config_name}) 连接失败 ({self.error_count[config_name]}/{max_consecutive_errors}): {conn_e}"
                        logging.error(err_msg)
                        self.root.after(
                            0, self.update_status, f"({config_name}) 连接失败..."
                        )
                    if is_connected:
                        logging.info(f"({config_name}) 已连接到 {plc_address}")
                        self.error_count[config_name] = 0
                        consecutive_read_errors = 0
                        self.root.after(0, self.update_status, f"({config_name}) 已连接")
                    elif self.error_count[config_name] >= max_consecutive_errors:
                        final_err = f"配置 '{config_name}' ({plc_address}) 连续连接失败 {max_consecutive_errors} 次，已停止查询此配置。"
                        logging.error(final_err)
                        self.root.after(
                            0,
                            lambda m=final_err: messagebox.showerror(
                                "连接错误", m, parent=self.root
                            ),
                        )
                        break
                    elif self.querying:
                        time.sleep(max(interval, 2.0))
                        continue
                results_data = None
                if is_connected:
                    if not self.querying:
                        break
                    try:
                        self.root.after(
                            0, self.update_status, f"({config_name}) 读取数据..."
                        )
                        results_data = self.read_data(client, thread_config)
                        consecutive_read_errors = 0
                        logging.debug(
                            f"({config_name}) 读取成功: {len(results_data)} 项。"
                        )
                        self.root.after(
                            0, self.update_status, f"({config_name}) 读取完成"
                        )
                    except (Snap7Exception, ValueError, Exception) as read_e:
                        results_data = None
                        consecutive_read_errors += 1
                        read_err_msg = f"({config_name}) 读取错误 ({consecutive_read_errors}/{max_consecutive_errors}): {read_e}"
                        logging.error(read_err_msg, exc_info=True)
                        self.root.after(
                            0, self.update_status, f"({config_name}) 读取错误!"
                        )
                    if results_data is None:  # 如果读取失败
                        if isinstance(read_e, ValueError):
                            final_read_err = f"配置 '{config_name}' 读取失败 (参数错误):\n{read_e}\n请检查配置并重新查询。"
                            logging.error(final_read_err)
                            self.root.after(
                                0,
                                lambda m=final_read_err: messagebox.showerror(
                                    "配置读取错误", m, parent=self.root
                                ),
                            )
                            break
                        else:
                            is_connected = False
                            try: client.disconnect();
                            except Exception: pass
                            logging.warning(f"({config_name}) 读取错误，断开连接。")
                        if consecutive_read_errors >= max_consecutive_errors:
                            final_read_err = f"配置 '{config_name}' 连续读取错误 {max_consecutive_errors} 次，已停止查询此配置。"
                            logging.error(final_read_err)
                            self.root.after(
                                0,
                                lambda m=final_read_err: messagebox.showerror(
                                    "通信/读取错误", m, parent=self.root
                                ),
                            )
                            break
                        elif self.querying:
                            time.sleep(max(interval, 1.0))
                            continue
                if results_data is not None:
                    self.root.after(
                        0, self.update_results_and_alarms, results_data, thread_config
                    )
                if not is_continuous:
                    logging.info(f"({config_name}) 单次查询完成。")
                    break
                if self.querying:
                    status_msg = f"({config_name}) 等待 {interval:.1f}s..."
                    self.root.after(0, self.update_status, status_msg)
                    time.sleep(interval)
        except Exception as thread_e:
            logging.error(
                f"!!! 查询线程 ({config_name}) 中未处理的错误: {thread_e}", exc_info=True
            )
            self.root.after(0, self.update_status, f"({config_name}) 线程错误!")
        finally:
            logging.info(f"查询线程 ({config_name}) 正在清理并退出。")
            if client.get_connected():
                try:
                    client.disconnect()
                    logging.debug(f"({config_name}) 已从 PLC 断开连接。")
                except Exception as disc_e:
                    logging.error(
                        f"({config_name}) 清理期间断开客户端连接时出错: {disc_e}"
                    )


    def read_data(self, client: snap7.client.Client, config: dict) -> list:
        """
        根据提供的配置从连接的 PLC 读取数据。
        使用配置的 address_format_prefix 构建地址字符串。
        实际读取字节数和解析由 data_type 决定。

        ! S7-1200/1500 注意: 仍然要求目标 DB 块 **禁用** "优化块访问"。
        """
        results = []
        try:
            db_block = int(config["db_block"])
            start_pos_str = config["start_position"]
            scan_count = int(config.get("scan_count", 1))
            interval_len = int(config.get("interval_length", 0))
            data_type = config["data_type"]
            # ---> 确保 str_len 在循环外获取一次 <---
            str_len = int(config.get("string_length", 10))
            if data_type == "string" and str_len <= 0:
                 raise ValueError("字符串长度必须为正数。") # Add validation here too

            address_format = config.get("address_format_prefix", "DBB").upper()
            config_name = config.get("_config_name", "Unknown")

            if "." in start_pos_str and data_type == "bool":
                byte_part, bit_part = map(int, start_pos_str.split("."))
                current_byte, current_bit = byte_part, bit_part
                address_format = "DBX"
            else:
                # 确保非 bool 类型不包含小数点
                if '.' in start_pos_str:
                    val = float(start_pos_str)
                    if not val.is_integer() or val < 0: raise ValueError(f"类型 '{data_type}' 的起始地址 '{start_pos_str}' 格式无效。")
                    current_byte = int(val)
                else:
                     current_byte = int(start_pos_str)
                     if current_byte < 0: raise ValueError("起始地址不能为负数。")
                current_bit = 0 # Not used for non-bool, but set for clarity
        except (ValueError, TypeError) as e:
            raise ValueError(
                f"读取解析期间配置无效 (类型: {config.get('data_type','N/A')}, 起始: '{config.get('start_position','N/A')}', 长度: '{config.get('string_length','N/A')}'): {e}"
            ) from e

        max_plc_byte = 65535

        for i in range(scan_count):
            if not self.querying:
                break

            addr_str = ""
            read_value = None
            read_value_str = ""
            bytes_to_read = 0
            byte_offset_for_next = 0
            next_bit_for_next = 0

            # --- 确定读取字节数 (基于 data_type) ---
            if data_type == "bool":
                bytes_to_read = 1
            elif data_type == "byte":
                bytes_to_read = 1
            elif data_type in ["word", "int"]:
                bytes_to_read = 2
            elif data_type in ["dword", "dint", "real"]:
                bytes_to_read = 4
            elif data_type == "string":
                # 再次确认 str_len 是从配置正确读取的
                # str_len = int(config.get("string_length", 10)) # 不应在循环内重复获取
                bytes_to_read = str_len # 应该是 2 + 20 = 22
                logging.debug(f"({config_name}) String read size calculated:  {str_len} = {bytes_to_read}")
            else:
                raise ValueError(f"未知数据类型 '{data_type}' 无法确定读取字节数。")

            # --- 构建地址字符串 (基于 address_format) ---
            if address_format == "DBX":  # Bool 类型
                addr_str = f"DB{db_block}.DBX{current_byte}.{current_bit}"
                next_bit = current_bit
                byte_rollover = 0
                if next_bit > 7:
                    next_bit = 0
                    byte_rollover = 1
                byte_offset_for_next = byte_rollover + interval_len
                next_bit_for_next = next_bit
            else:  # 非 Bool 类型
                addr_str = f"DB{db_block}.{address_format}{current_byte}"
                if data_type == "string":
                    addr_str += f" (S{str_len})" # 使用循环外获取的 str_len
                # 偏移量计算基于本次读取的字节数
                byte_offset_for_next = bytes_to_read + interval_len

            # --- 检查地址边界 ---
            read_end_byte = current_byte + bytes_to_read # 计算读取的最后一个字节的位置+1
            if current_byte < 0 or read_end_byte > (max_plc_byte + 1):
                 logging.warning(
                    f"({config_name}) 计算的读取范围 {addr_str} (起始: {current_byte}, 结束字节: {read_end_byte-1}) 可能超出DB块限制 ({max_plc_byte})."
                 )
                 # Allow read attempt, snap7 handles errors if address is invalid

            # --- 执行读取 ---
            # --->>> 添加修正逻辑 <<<---
            actual_size_to_read = bytes_to_read
            if data_type == "string":
                correct_string_size = 2 + str_len
                if bytes_to_read != correct_string_size:
                    logging.warning(
                        f"({config_name}) [CORRECTION] Mismatch detected for string read size. Expected {correct_string_size}, but calculated {bytes_to_read}. Forcing correct size."
                    )
                    actual_size_to_read = correct_string_size # 强制使用正确的大小

            logging.debug(
                # 使用 actual_size_to_read 记录将要读取的大小
                f"({config_name}) 读取: {addr_str} ({actual_size_to_read} 字节 @ DB{db_block}:{current_byte})"
            )
            try:
                data: bytearray = client.db_read(
                    db_number=db_block, start=current_byte, size=actual_size_to_read # 使用修正后的大小
                )
                if data_type == "string":
                    # 检查返回的数据长度是否符合预期
                    if len(data) != actual_size_to_read:
                         logging.warning(f"({config_name}) String read for {addr_str}: Requested {actual_size_to_read} bytes, but received {len(data)}. Data: {data.hex()}")
                    else:
                         logging.info(
                            f"({config_name}) String read successful for {addr_str}. Raw bytearray (len={len(data)}): {data.hex()}"
                         )
            except Snap7Exception as snap_ex:
                logging.error(
                    f"({config_name}) Snap7 读取错误 for {addr_str}: {snap_ex}",
                    exc_info=True,
                )
                # 让外层循环处理错误和重试
                raise snap_ex
            except Exception as read_ex:
                logging.error(
                    f"({config_name}) 读取时发生未知错误 for {addr_str}: {read_ex}",
                    exc_info=True,
                )
                raise read_ex

            # --- 解析数据 (基于 data_type) ---
            try:
                # ... (解析逻辑保持不变) ...
                if data_type == "bool": read_value = get_bool(data, byte_index=0, bool_index=current_bit); read_value_str = str(read_value)
                elif data_type == "byte": read_value = get_byte(data, 0); read_value_str = str(read_value)
                elif data_type == "word": read_value = get_word(data, 0); read_value_str = str(read_value)
                elif data_type == "dword": read_value = get_dword(data, 0); read_value_str = str(read_value)
                elif data_type == "int": read_value = get_int(data, 0); read_value_str = str(read_value)
                elif data_type == "dint": read_value = get_dint(data, 0); read_value_str = str(read_value)
                elif data_type == "real": read_value = get_real(data, 0); read_value_str = f"{read_value:.4f}"
                elif data_type == "string":
                    # read_value = convert_to_string(data) # convert_to_string 会处理收到的数据
                    read_value = bytearray_to_string(data)  # convert_to_string 会处理收到的数据
                    bytearray_to_string
                    read_value_str = read_value
                    # 移动日志到解析后
                    logging.info(
                        f"({config_name}) String conversion result for {addr_str}: '{read_value_str}'"
                    )

            except Exception as parse_ex:
                logging.error(
                    f"({config_name}) 解析数据错误 for {addr_str} (Type: {data_type}): {parse_ex}",
                    exc_info=True,
                )
                read_value = None
                read_value_str = f"Error: {parse_ex}"

            # --- 存储结果 ---
            results.append((addr_str, data_type, read_value_str, read_value))
            logging.debug(f"({config_name}) 解析值: '{read_value_str}'") # 增加引号便于看清空字符串

            # --- 前进到下一个地址 ---
            current_byte += byte_offset_for_next # 使用之前计算的偏移量
            if data_type == "bool":
                current_bit = next_bit_for_next

        return results

    def update_results_and_alarms(self, results_data: list, config: dict):
        """处理来自读取周期的结果：更新 UI 缓存、保存到数据库、检查报警。"""
        try:
            current_time_iso = datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
            config_name = config.get("_config_name", "Unknown")
            new_ui_entries = []
            results_for_db = []
            raw_results_for_alarm = []
            for address, dtype, value_str, raw_value in results_data:
                address_name = self.address_map.get(address, "")
                ui_tuple = (
                    config_name,
                    current_time_iso,
                    address,
                    address_name,
                    dtype,
                    value_str,
                )
                new_ui_entries.append(ui_tuple)
                db_tuple = (
                    current_time_iso,
                    config_name,
                    address,
                    address_name,
                    dtype,
                    value_str,
                )
                results_for_db.append(db_tuple)
                raw_results_for_alarm.append((address, dtype, raw_value))
            save_success = self.save_results_to_db(results_for_db)
            if not save_success:
                logging.warning(
                    f"({config_name}) 未能将部分/全部结果保存到数据库。UI 可能仍会更新。"
                )
            if self.show_history_ui.get():
                start_index = len(self.original_data)
                indexed_new = [
                    (i + start_index + 1, *entry)
                    for i, entry in enumerate(reversed(new_ui_entries))
                ]
                self.original_data = indexed_new + self.original_data
                if len(self.original_data) > MAX_RESULT_UI_CACHE:
                    logging.debug(
                        f"UI 结果缓存大小 ({len(self.original_data)}) 超过限制 ({MAX_RESULT_UI_CACHE})。正在从缓存中修剪最旧的条目。"
                    )
                    self.original_data = self.original_data[:MAX_RESULT_UI_CACHE]
            self.update_result_display()
            self.check_alarms(raw_results_for_alarm, config_name)
        except Exception as e:
            logging.error(f"在主线程中处理结果更新时出错: {e}", exc_info=True)

    def check_alarms(self, raw_results: list, config_name: str):
        """比较当前原始值与先前存储的值以检测更改（报警）。"""
        current_time_iso = datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
        alarm_detected_in_batch = False
        for address, dtype, current_raw_value in raw_results:
            cache_key = (config_name, address)
            previous_raw_value = self.prev_values.get(cache_key)
            if current_raw_value is not None and not isinstance(
                current_raw_value, Exception
            ):
                self.prev_values[cache_key] = current_raw_value
                if (
                    previous_raw_value is not None
                    and previous_raw_value != current_raw_value
                ):
                    alarm_detected_in_batch = True
                    address_name = self.address_map.get(address, "")
                    logging.info(
                        f"检测到报警! 配置: '{config_name}', 地址: {address} ('{address_name}'), 变化: '{previous_raw_value}' -> '{current_raw_value}'"
                    )
                    old_val_str = (
                        f"{previous_raw_value:.4f}"
                        if isinstance(previous_raw_value, float)
                        else str(previous_raw_value)
                    )
                    new_val_str = (
                        f"{current_raw_value:.4f}"
                        if isinstance(current_raw_value, float)
                        else str(current_raw_value)
                    )
                    alarm_entry = (
                        current_time_iso,
                        config_name,
                        address,
                        address_name,
                        old_val_str,
                        new_val_str,
                    )
                    self.alarm_original_data.insert(0, alarm_entry)
                    if len(self.alarm_original_data) > MAX_ALARM_UI_CACHE:
                        self.alarm_original_data.pop()
                    self.save_alarm_history(
                        config_name, address, address_name, old_val_str, new_val_str
                    )
            else:
                if cache_key in self.prev_values:
                    del self.prev_values[cache_key]
        if alarm_detected_in_batch:
            if self.current_alarm_page != 1:
                self.current_alarm_page = 1
            self.update_alarm_display()

    # --- UI 控制方法 ---
    def stop_query(self):
        """优雅地停止所有活动的查询线程。"""
        if not self.querying:
            logging.debug("请求停止查询，但当前没有查询在运行。")
            return
        logging.info("请求停止查询。正在向线程发送信号...")
        self.querying = False
        join_timeout = 2.0
        threads_to_join = [t for t in self.query_threads if t.is_alive()]
        logging.debug(f"尝试加入 {len(threads_to_join)} 个活动查询线程...")
        start_time = time.time()
        for thread in threads_to_join:
            try:
                thread.join(join_timeout)
            except Exception as e:
                logging.error(f"加入线程 '{thread.name}' 时出错: {e}")
        elapsed_time = time.time() - start_time
        remaining_threads = [t.name for t in self.query_threads if t.is_alive()]
        if remaining_threads:
            logging.warning(
                f"等待线程停止超时 ({join_timeout:.1f}s)。剩余: {remaining_threads}"
            )
        else:
            logging.info(f"所有活动查询线程已成功停止 ({elapsed_time:.2f}s)。")
        self.query_threads.clear()
        self.update_ui_state(querying=False)
        self.update_status("查询已停止")

    def update_ui_state(self, querying: bool):
        """根据查询是否活动来启用或禁用 UI 元素。"""
        menu_state = tk.DISABLED if querying else tk.NORMAL
        is_example = self.config_combobox.get() == "默认配置 (示例)"
        is_no_cfg = self.config_combobox.get() == "请先添加配置"
        can_query_single = self.configs and not is_no_cfg and not is_example
        can_query_all_valid = any(
            name != "默认配置 (示例)" for name in self.configs
        )
        if querying:
            self.query_button.config(state=tk.DISABLED)
            self.stop_button.config(state=tk.NORMAL)
            self.config_combobox.config(state=tk.DISABLED)
            self.query_all_checkbox.config(state=tk.DISABLED)
            self.continuous_checkbox.config(state=tk.DISABLED)
            self.clear_button.config(state=tk.DISABLED)
        else:
            can_start_query = can_query_single or can_query_all_valid
            self.query_button.config(
                state=tk.NORMAL if can_start_query else tk.DISABLED
            )
            self.stop_button.config(state=tk.DISABLED)
            self.config_combobox.config(
                state="readonly" if self.configs else tk.DISABLED
            )
            self.query_all_checkbox.config(
                state=tk.NORMAL if can_query_all_valid else tk.DISABLED
            )
            self.continuous_checkbox.config(state=tk.NORMAL)
            self.clear_button.config(state=tk.NORMAL)
        try:
            menubar = self.root.nametowidget(self.root.cget("menu"))
            menubar.entryconfig(0, state=menu_state)
        except (tk.TclError, AttributeError, IndexError):
            logging.warning("无法根据查询状态更新菜单状态。")

    def update_status(self, message: str):
        """从任何线程安全地更新状态栏标签。"""
        try:
            if self.status_label and self.status_label.winfo_exists():
                self.status_label.config(text=message)
        except tk.TclError:
            pass  # Widget might be destroyed during shutdown
        except Exception as e:
            logging.error(f"更新状态栏时发生意外错误: {e}")

    def clear_ui_results(self):
        """仅清除实时结果和报警的 UI 缓存和显示。"""
        msg = "确定要清空 [查询结果] 和 [报警监控] 标签页的显示列表吗？\n(数据库和历史查询结果不会被删除)"
        if messagebox.askyesno("确认清空活动列表", msg, parent=self.root):
            self.original_data.clear()
            for item in self.result_tree.get_children():
                self.result_tree.delete(item)
            self.current_page = 1
            self.update_result_display()
            self.alarm_original_data.clear()
            for item in self.alarm_tree.get_children():
                self.alarm_tree.delete(item)
            self.current_alarm_page = 1
            self.update_alarm_display()
            self.update_status("界面活动结果已清空")
            logging.info("UI 实时结果和报警显示缓存已清除。")

    def clear_history_results(self):
        """清除历史搜索结果缓存和显示。"""
        if not self.history_search_results:
            return
        msg = "确定要清空当前 [历史查询] 标签页的显示列表吗？"
        if messagebox.askyesno("确认清空历史列表", msg, parent=self.root):
            self.history_search_results.clear()
            for item in self.history_tree.get_children():
                self.history_tree.delete(item)
            self.current_history_page = 1
            self.update_history_display()
            self.update_status("历史查询结果已清空")
            logging.info("UI 历史搜索结果缓存已清除。")

    # --- 分页更新显示辅助方法 ---
    def _update_treeview_display(
        self,
        treeview,
        data_list,
        current_page_attr,
        total_pages_attr,
        page_label,
        page_size,
        data_mapper_func=None,
    ):
        """使用分页数据更新 treeview 的辅助函数。"""
        for item in treeview.get_children():
            treeview.delete(item)
        total_items = len(data_list)
        total_pages = max(1, math.ceil(total_items / page_size))
        setattr(self, total_pages_attr, total_pages)
        current_page = getattr(self, current_page_attr)
        current_page = max(1, min(current_page, total_pages))
        setattr(self, current_page_attr, current_page)
        start_idx = (current_page - 1) * page_size
        end_idx = min(start_idx + page_size, total_items)
        for data_tuple in data_list[start_idx:end_idx]:
            try:
                display_values = (
                    data_mapper_func(data_tuple) if data_mapper_func else data_tuple
                )
                treeview.insert("", tk.END, values=display_values)
            except Exception as e:
                logging.error(f"将数据插入 Treeview 时出错: {e} | 数据: {data_tuple}")
        page_label.config(
            text=f"第 {current_page} / {total_pages} 页 ({total_items} 条)"
        )

    # --- 实时结果分页 ---
    def update_result_display(self):
        """更新实时结果 Treeview。"""
        self._update_treeview_display(
            self.result_tree,
            self.original_data,
            "current_page",
            "total_pages",
            self.page_label,
            self.page_size,
        )

    def go_to_first_page(self):
        """导航到实时结果的第一页。"""
        if self.current_page != 1:
            self.current_page = 1
            self.update_result_display()

    def go_to_previous_page(self):
        """导航到实时结果的上一页。"""
        if self.current_page > 1:
            self.current_page -= 1
            self.update_result_display()

    def go_to_next_page(self):
        """导航到实时结果的下一页。"""
        if self.current_page < self.total_pages:
            self.current_page += 1
            self.update_result_display()

    def go_to_last_page(self):
        """导航到实时结果的最后一页。"""
        if self.current_page != self.total_pages:
            self.current_page = self.total_pages
            self.update_result_display()

    # --- 报警分页 ---
    def update_alarm_display(self):
        """更新报警 Treeview。"""
        self._update_treeview_display(
            self.alarm_tree,
            self.alarm_original_data,
            "current_alarm_page",
            "total_alarm_pages",
            self.alarm_page_label,
            self.page_size,
        )

    def go_to_first_page_alarm(self):
        """导航到报警的第一页。"""
        if self.current_alarm_page != 1:
            self.current_alarm_page = 1
            self.update_alarm_display()

    def go_to_previous_page_alarm(self):
        """导航到报警的上一页。"""
        if self.current_alarm_page > 1:
            self.current_alarm_page -= 1
            self.update_alarm_display()

    def go_to_next_page_alarm(self):
        """导航到报警的下一页。"""
        if self.current_alarm_page < self.total_alarm_pages:
            self.current_alarm_page += 1
            self.update_alarm_display()

    def go_to_last_page_alarm(self):
        """导航到报警的最后一页。"""
        if self.current_alarm_page != self.total_alarm_pages:
            self.current_alarm_page = self.total_alarm_pages
            self.update_alarm_display()

    # --- 历史查询逻辑 ---
    def search_history(self):
        """根据历史查询选项卡中的条件从数据库查询记录。"""
        try:
            start_date = self.start_date_entry.get_date()
            start_time_str = self.start_time_entry.get().strip()
            end_date = self.end_date_entry.get_date()
            end_time_str = self.end_time_entry.get().strip()
            try:
                start_t = (
                    dt_time.min
                    if not start_time_str or start_time_str == "00:00:00"
                    else datetime.strptime(start_time_str, "%H:%M:%S").time()
                )
                end_t = (
                    dt_time.max.replace(microsecond=0)
                    if not end_time_str or end_time_str == "23:59:59"
                    else datetime.strptime(end_time_str, "%H:%M:%S").time()
                )
            except ValueError:
                messagebox.showerror(
                    "时间格式错误", "时间格式无效，请输入 HH:MM:SS 格式。", parent=self.root
                )
                return
            start_dt = datetime.combine(start_date, start_t)
            end_dt = datetime.combine(end_date, end_t)
            if start_dt > end_dt:
                messagebox.showerror("日期错误", "开始时间不能晚于结束时间。", parent=self.root)
                return
            start_ts_str = start_dt.strftime("%Y-%m-%d %H:%M:%S") + ".000"
            end_ts_str = end_dt.strftime("%Y-%m-%d %H:%M:%S") + ".999"
        except ValueError as date_err:
            messagebox.showerror(
                "日期格式错误", f"日期选择无效或格式错误:\n{date_err}", parent=self.root
            )
            return
        except Exception as dt_err:
            logging.error(f"解析日期时间时出错: {dt_err}", exc_info=True)
            messagebox.showerror(
                "错误", f"处理日期时间时发生错误:\n{dt_err}", parent=self.root
            )
            return

        address_filter = self.address_filter_entry.get().strip()
        filter_pattern = f"%{address_filter}%" if address_filter else "%"

        if not self.db_conn or not self.db_cursor:
            messagebox.showerror(
                "数据库错误", "数据库未连接，无法查询历史记录。", parent=self.root
            )
            return

        sql = """ SELECT timestamp, config_name, address, address_name, data_type, value FROM query_log WHERE timestamp BETWEEN ? AND ? AND (address LIKE ? OR address_name LIKE ?) ORDER BY timestamp DESC """
        try:
            self.update_status("正在查询历史记录...")
            self.root.update_idletasks()
            logging.info(
                f"执行历史查询: 时间范围 ['{start_ts_str}' - '{end_ts_str}'], 地址/名称 LIKE '{filter_pattern}'"
            )
            self.db_cursor.execute(
                sql, (start_ts_str, end_ts_str, filter_pattern, filter_pattern)
            )
            fetched_rows = self.db_cursor.fetchall()
            self.history_search_results = [
                (i + 1, *row) for i, row in enumerate(fetched_rows)
            ]
            count = len(self.history_search_results)
            logging.info(f"历史查询返回 {count} 条记录。")
            self.update_status(f"历史查询完成 ({count} 条)")
            self.current_history_page = 1
            self.update_history_display()
        except sqlite3.Error as e:
            logging.error(f"历史记录搜索期间发生数据库错误: {e}", exc_info=True)
            messagebox.showerror(
                "查询错误", f"查询历史记录时发生数据库错误:\n{e}", parent=self.root
            )
            self.update_status("历史查询失败")
        except Exception as e:
            logging.error(f"历史记录搜索期间发生意外错误: {e}", exc_info=True)
            messagebox.showerror(
                "查询错误", f"查询历史记录时发生未知错误:\n{e}", parent=self.root
            )
            self.update_status("历史查询失败")

    # --- 历史记录分页方法 ---
    def _map_history_data_for_display(self, data_tuple):
        """将数据库缓存元组映射到 Treeview 列的顺序。"""
        # 缓存: (序号, 时间戳, 配置名, 地址, 地址名, 类型, 值)
        # 显示: (序号, 配置名称, 时间, 地址, 地址名称, 类型, 值)
        return (
            data_tuple[0],  # 序号
            data_tuple[2],  # 配置名称
            data_tuple[1],  # 时间
            data_tuple[3],  # 地址
            data_tuple[4],  # 地址名称
            data_tuple[5],  # 类型
            data_tuple[6],  # 值
        )

    def update_history_display(self):
        """使用当前历史缓存和页码更新历史 Treeview。"""
        self._update_treeview_display(
            self.history_tree,
            self.history_search_results,
            "current_history_page",
            "total_history_pages",
            self.history_page_label,
            HISTORY_PAGE_SIZE,
            self._map_history_data_for_display,
        )

    def go_to_first_page_history(self):
        """导航到历史结果的第一页。"""
        if self.current_history_page != 1:
            self.current_history_page = 1
            self.update_history_display()

    def go_to_previous_page_history(self):
        """导航到历史结果的上一页。"""
        if self.current_history_page > 1:
            self.current_history_page -= 1
            self.update_history_display()

    def go_to_next_page_history(self):
        """导航到历史结果的下一页。"""
        if self.current_history_page < self.total_history_pages:
            self.current_history_page += 1
            self.update_history_display()

    def go_to_last_page_history(self):
        """导航到历史结果的最后一页。"""
        if self.current_history_page != self.total_history_pages:
            self.current_history_page = self.total_history_pages
            self.update_history_display()

    # --- 实用工具方法 ---
    def update_time(self):
        """每秒更新右上角的时间显示标签。"""
        try:
            time_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        except Exception as e:
            logging.error(f"更新时间显示时出错: {e}")
            return  # Exit if time formatting fails
        # Check if widgets exist before configuring (robust against closing window)
        if self.root and self.root.winfo_exists() and self.time_label and self.time_label.winfo_exists():
            try:
                self.time_label.config(text=time_str)
                # Schedule next update only if successful
                self.root.after(1000, self.update_time)
            except tk.TclError:
                 # Handle rare case where widget might be destroyed between check and config
                 logging.warning("TclError occurred updating time label, likely during shutdown.")
            except Exception as e:
                 logging.error(f"更新时间标签时发生意外错误: {e}")
        else:
            logging.debug("Time label update skipped, widget destroyed.")


    def show_help(self):
        """显示帮助/关于信息，包含 address_format_prefix 和 String 说明。"""
        help_text = f"""PLC地址值监控工具 v3.0

##  V3.0 目前支持功能:
- 支持多PLC监控配置高并发查询
- 支持查询数据持久化，目前支持日志和SQLite数据库存储
- 支持历史数据查询，支持按照时间、地址名称、地址位置进行筛选
- 支持批量地址位置和地址名称映射配置，可以在文件夹中的address_mapping.json进行修改
- 支持毫秒级地址位值变化监控报警
- 支持地址位持续查询，目前设置为查询最新的5000条数据监控,历史数据不设限制
- 支持查询列表，监控列表，历史查询界面分页功能
- 右上角当前时间加粗展示
- 支持页面持续查询，追加历史查询
- 监控日志记录内容优化

*********使用过程中如有任何问题，请钉钉与袁锦浩联系，并附上截图和情况说明***********

配置说明:
- **数据类型 (data_type):** 定义如何 *解释* PLC 内存中的数据，并决定读取多少字节。
    支持: bool, byte, word, dword, int, dint, real, string。
- **地址格式前缀 (address_format_prefix):** 定义地址在界面上如何 *显示*。
    选项: DBX, DBB, DBW, DBD。
    (注意: Bool 类型将始终显示为 DBX)
- **起始地址 (start_position):**
    - bool: `<byte>.<bit>` (例如 `0.1`)
    - 其他类型: 字节偏移量 (例如 `10`)
- **字符串长度 (string_length):** *仅* 当数据类型为 string 时有效。
    应设置为 PLC 中定义的 String 的 *数据区* 长度 (例如 `STRING[20]` -> 长度填 `20`)。
    
**String 类型读取要点:**
1.  确保 PLC 中的 DB 块**未**勾选 "优化块访问"。
2.  **数据类型** 设置为 `string`。
3.  **地址格式前缀** 通常设置为 `DBB`。
4.  **起始地址** 设置为 S7 String 结构开始的字节偏移量（即 `max_len` 字节所在的地址）。
5.  **字符串长度** 设置为 PLC 中定义的 String 的 *数据区* 长度。
6.  如果读取失败，请检查日志文件 (`{LOG_FILE}`) 中的详细错误和原始数据。

使用提示:
- 历史查询页使用日历选日期，时间格式 HH:MM:SS。地址/名称过滤支持部分匹配。
- 清空按钮仅影响界面列表，不删除数据库或文件。
- 日志文件 ({LOG_FILE}) 是 UTF-8 编码，请使用支持此编码的工具查看。
"""
        messagebox.showinfo("帮助 / 说明", help_text, parent=self.root)

    def open_log_file(self):
        """使用默认系统查看器打开应用程序日志文件。"""
        try:
            log_path = os.path.abspath(LOG_FILE)
        except Exception as e:
            logging.error(f"获取日志文件路径失败: {e}")
            messagebox.showerror("错误", f"无法获取日志文件路径:\n{e}", parent=self.root)
            return

        if os.path.exists(log_path):
            try:
                webbrowser.open(f"file:///{log_path}")
                logging.info(f"正在打开日志文件: {log_path}")
            except Exception as e:
                logging.error(f"打开日志文件 {LOG_FILE} 失败: {e}")
                messagebox.showerror("错误", f"无法打开日志文件: {e}", parent=self.root)
        else:
            messagebox.showinfo("信息", f"日志文件 '{LOG_FILE}' 未创建。", parent=self.root)

    def open_db_folder(self):
        """打开包含 SQLite 数据库文件的文件夹。"""
        try:
            db_dir = os.path.dirname(os.path.abspath(DB_FILE))
        except Exception as e:
            logging.error(f"获取数据库文件夹路径失败: {e}")
            messagebox.showerror("错误", f"无法获取数据文件位置:\n{e}", parent=self.root)
            return

        if os.path.exists(db_dir):
            try:
                webbrowser.open(f"file:///{db_dir}")
                logging.info(f"已打开数据库文件夹: {db_dir}")
            except Exception as e:
                logging.error(f"打开数据库文件夹失败: {e}", exc_info=True)
                messagebox.showerror(
                    "错误", f"无法打开数据文件位置:\n{e}", parent=self.root
                )
        else:
            messagebox.showwarning("打开失败", f"文件夹不存在: {db_dir}", parent=self.root)

    def import_configs(self):
        """处理从 JSON 文件导入 PLC 配置。"""
        filepath = filedialog.askopenfilename(
            title="选择要导入的配置文件",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            parent=self.root,
        )
        if not filepath:
            return
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                imported_configs_raw = json.load(f)
            if not isinstance(imported_configs_raw, dict):
                raise ValueError("导入的文件根元素必须是 JSON 对象 (字典)。")
            imported_count, skipped_count, invalid_count = 0, 0, 0
            overwrite_all = None
            for name, config_data in imported_configs_raw.items():
                if not isinstance(config_data, dict):
                    logging.warning(f"导入跳过: '{name}' 不是字典。")
                    invalid_count += 1
                    continue
                full_config = DEFAULT_CONFIG.copy()
                full_config.update(config_data)
                if not validate_config(full_config, config_name=f"{name} (导入)"):
                    logging.warning(f"导入跳过: '{name}' 无效。请查看日志。")
                    invalid_count += 1
                    continue
                example_key = "默认配置 (示例)"
                if name in self.configs and name != example_key:
                    if overwrite_all is None:
                        choice = messagebox.askyesnocancel(
                            "导入冲突",
                            f"配置 '{name}' 已存在。\n\n是: 覆盖\n否: 跳过\n取消: 中止",
                            parent=self.root,
                        )
                        if choice is None:
                            messagebox.showinfo("导入中止", "导入操作已取消。", parent=self.root)
                            return
                        overwrite_all = bool(choice)
                    if overwrite_all:
                        self.configs[name] = full_config
                        imported_count += 1
                        logging.info(f"已导入 (覆盖): '{name}'")
                    else:
                        skipped_count += 1
                        logging.info(f"导入跳过 (已存在): '{name}'")
                else:
                    if name == example_key and example_key in self.configs:
                        del self.configs[example_key]
                    self.configs[name] = full_config
                    imported_count += 1
                    logging.info(f"已导入 (新增/示例): '{name}'")
            if imported_count > 0:
                self.save_configs()
                config_keys = list(self.configs.keys())
                self.config_combobox["values"] = config_keys
                if config_keys:
                    self.config_combobox.set(config_keys[0])
                self.update_ui_state(querying=False)
            msg = f"导入完成。\n\n成功导入/覆盖: {imported_count}\n跳过已存在: {skipped_count}\n跳过无效格式: {invalid_count}"
            messagebox.showinfo("导入结果", msg, parent=self.root)
            self.update_status("配置导入完成")
        except FileNotFoundError:
            messagebox.showerror("导入错误", f"文件未找到: {filepath}", parent=self.root)
        except (json.JSONDecodeError, ValueError) as e:
            messagebox.showerror(
                "导入错误",
                f"文件 '{os.path.basename(filepath)}' 格式错误:\n{e}",
                parent=self.root,
            )
        except Exception as e:
            logging.error(f"从 {filepath} 导入时出错: {e}", exc_info=True)
            messagebox.showerror("导入错误", f"导入时发生未知错误: {e}", parent=self.root)

    def export_configs(self):
        """处理将当前 PLC 配置导出到 JSON 文件。"""
        example_key = "默认配置 (示例)"
        configs_to_export = {
            k: v for k, v in self.configs.items() if k != example_key
        }
        if not configs_to_export:
            messagebox.showinfo("导出配置", "没有有效的配置可供导出。", parent=self.root)
            return
        filepath = filedialog.asksaveasfilename(
            title="选择导出配置文件的位置",
            defaultextension=".json",
            initialfile="plc_configs_export.json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            parent=self.root,
        )
        if not filepath:
            return
        try:
            with open(filepath, "w", encoding="utf-8") as f:
                json.dump(configs_to_export, f, indent=4, ensure_ascii=False)
            logging.info(f"配置已成功导出到 {filepath}")
            messagebox.showinfo("导出成功", f"配置已成功导出到:\n{filepath}", parent=self.root)
            self.update_status("配置导出完成")
        except Exception as e:
            logging.error(f"导出配置失败: {e}", exc_info=True)
            messagebox.showerror("导出错误", f"导出配置失败: {e}", parent=self.root)

    # --- 应用程序退出处理 ---
    def on_close(self):
        """处理窗口关闭事件。"""
        if self.querying:
            if messagebox.askyesno(
                "退出确认", "查询仍在进行中，确定要停止查询并退出吗？", parent=self.root
            ):
                self.stop_query()
                self.root.after(100, self._close_and_destroy)
            else:
                return
        else:
            self._close_and_destroy()

    def _close_and_destroy(self):
        """关闭数据库并销毁主窗口的内部辅助方法。"""
        logging.info("退出前关闭数据库连接...")
        self._close_db()
        logging.info("--- PLC 可视化查询工具 已关闭 ---")
        if self.root:
            try:
                self.root.destroy()
            except tk.TclError:
                logging.warning("销毁 root 时发生 TclError，可能已在关闭。")


# --- 主执行块 ---
if __name__ == "__main__":
    # --- 确保必要的配置文件存在 ---
    if not os.path.exists(ADDRESS_MAPPING_FILE):
        try:
            with open(ADDRESS_MAPPING_FILE, "w", encoding="utf-8") as f:
                example_map = {
                    "DB1.DBX0.0": "机器启动信号",
                    "DB1.DBD4": "反应釜A液位 (Real)",
                    "DB2.DBW10": "传送带速度设定 (Int)",
                    "DB3.DBB20 (S10)": "当前批次号 (String)",
                }
                json.dump(example_map, f, indent=4, ensure_ascii=False)
            logging.info(f"已创建示例映射文件: {ADDRESS_MAPPING_FILE}")
        except Exception as e:
            logging.error(f"无法创建示例映射文件: {e}")

    # --- 创建并运行应用程序 ---
    try:
        root = tk.Tk()
        app = PLCVisualizationTool(root)
        root.mainloop()
    except Exception as main_e:
        logging.critical(f"主执行中未处理的异常: {main_e}", exc_info=True)
        try:
            messagebox.showerror(
                "严重错误", f"应用程序遇到严重错误并需要关闭:\n{main_e}"
            )
        except:
            print(f"严重错误: {main_e}", file=sys.stderr)
        sys.exit(1)
