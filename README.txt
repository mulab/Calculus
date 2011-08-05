根目录下是整体控制程序
Rubi(Rule Based Integration)下是基于规则/积分表的积分
Albi(Algorithm Based Integration)下士基于算法的积分
Albi\SIN-like\下是仿SIN系统，以被积函数线索进行转换
Albi\Rational\下是有理函数积分
Albi\Risch\下是Risch和Parallel Risch算法
utility下是mU或者Mathematica没有提供的，可能被其它部分也使用的工具函数

这里认为内核会调用且仅调用一次init.m来将Albi, Rubi, utility中的函数接口加载到内存中，根目录下的init.m会调用三个子目录下的init.m