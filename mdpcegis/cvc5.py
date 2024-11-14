import cvc5
from cvc5 import Kind, Plugin, Solver, TermManager

class PluginListen(Plugin):
    def __init__(self, tm):
        self.tm = tm
        super().__init__(tm)
    
    # called on decision
    def check(self):
        print("PluginListen: check")
        intSort = self.tm.getIntegerSort()
        x = self.tm.mkConst(intSort, "x")
        # print all assertions about x
        return []

    def notifySatClause(self, cl):
        super().notifySatClause(cl)
        print("PluginListen: learned SAT clause", cl)

    def notifyTheoryLemma(self, lem):
        super().notifyTheoryLemma(lem)
        print("PluginListen: learned theory lemma", lem)

    def getName(self):
        return "PluginListen"
    
if __name__ == "__main__":
        # NOTE: this shouldn't be necessary but ensures notifySatClause is called here.
    tm = TermManager()
    solver = Solver()
    solver.setOption("produce-models", "true");
    solver.setOption("produce-unsat-cores", "true");

    solver.setOption("plugin-notify-sat-clause-in-solve", "true")
    pl = PluginListen(tm)
    pl.solver = solver
    solver.addPlugin(pl)
    intSort = tm.mkBitVectorSort(2)
    
    # print(solver.getPropEngine())
    # prop_engine.getPropDecisions();

    x = tm.mkConst(intSort, "x")
    y = tm.mkConst(intSort, "y")
    # 0 < x < 5, 0 < y < 5
    c1 = tm.mkTerm(Kind.GT, x, tm.mkBitVector(2, 0))
    c2 = tm.mkTerm(Kind.GT, y, tm.mkBitVector(2))
    c3 = tm.mkTerm(Kind.LT, x, tm.mkInteger(5))
    c4 = tm.mkTerm(Kind.LT, y, tm.mkInteger(5))
    solver.assertFormula(c1)
    solver.assertFormula(c2)
    solver.assertFormula(c3)
    solver.assertFormula(c4)

    ctn1 = tm.mkTerm(Kind.GT, x, y)
    # ctn2 = tm.mkTerm(Kind.STRING_CONTAINS, y, x)
    # solver.assertFormula(tm.mkTerm(Kind.OR, ctn1))
    solver.assertFormula(ctn1)
    # lx = tm.mkTerm(Kind.STRING_LENGTH, x)
    # ly = tm.mkTerm(Kind.STRING_LENGTH, y)
    # lc = tm.mkTerm(Kind.GT, lx, ly)
    # solver.assertFormula(lc)
    result = solver.checkSat()
    print(result)
    assert result.isSat()
    print(solver.getValue(x))
    print(solver.getValue(y))
