Integrate.u是最老的基本表，暂供老版本内核使用，不再进行维护。
InTable.m是SIN-like Integration System所使用的积分表，NoCloseTable.m类似，不过内容是无闭形式被积函数表；
InTable.u和NoCloseTable.u是对应的mU内核版本。

暂时Rubi3本身存在一些bug，等待其更新放出，我们对其的改动请见original下的README。Rubi2虽然已经被其他CAS如matheclipse使用（http://code.google.com/p/symja/wiki/RubiIntegration），但是网上暂时没找到Mathematica代码下载。所以现在还是保存了TableInt.m和NoCloseInt.m——改自InTable.m的和Rubi3兼容的积分表。

最后init.m初始化，载入InTable.m和original目录下的Rubi3包，运行init.m之后，就可以使用Int[f,x]来查询积分表了。

修改Rubi中的一些函数名:将sin更正为Sin,将Sim更正为Simplify。

在Rubi中增加了一条新的规则