for %%i in (*.m) do java ExtractFunctionNames "%%i" > names(%%i).txt