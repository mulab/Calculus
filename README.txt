根目录下是整体控制程序
Rubi(Rule Based Integration)下是基于规则/积分表的积分
Albi(Algorithm Based Integration)下是基于算法的积分
Albi\Risch\下是Risch和Parallel Risch算法

内核会调用且仅调用一次init.m来将Albi、Rubi中的函数接口加载到内存中（在IntegrateU第一次运行到相关部分时），根目录下的init.m会调用子目录下的init.m

-----------------------------------------------------

该分支内对Rubi的Int函数添加了打印信息功能，当一个Int函数体被调用的时候，会自动打印该Int位置。