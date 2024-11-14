import z3

class Plugin(z3.UserPropagateBase):
    def __init__(self, solver):
        super().__init__(solver, None)
        self.add_fixed(self._fixed)

    def register_variables(self, variables):
        for var in variables:
            self.add(var)

    def _fixed(self, ast, value):
        # add this equality as a conflict
        self.conflict(deps=[ast], eqs=[(ast, value)])

def main():
    s = z3.Solver()

    x = z3.BitVec("x", 32)

    s.add(x == 5)

    p = Plugin(s)
    p.register_variables([x])

    print(s.assertions())
    print(s.check())
    print(s.model())

if __name__ == "__main__":
    main()
