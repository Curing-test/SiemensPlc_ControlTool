from cx_Freeze import setup, Executable

build_exe_options = {
    "packages": ["os"],  # 在这里添加你的依赖模块
    "excludes": []       # 在这里添加不需要包含的模块
}
setup(
    name="PLCVisualizationTool",
    version="1.0",
    description="PLC 可视化查询工具",
    options = {"build_exe": build_exe_options},
    executables=[Executable("ReadCode.py", base="Win32GUI")]
)
#123123123