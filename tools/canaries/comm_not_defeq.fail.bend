import Base

# NEGATIVE canary: refl only discharges *definitional* equality. `add` is not
# definitionally commutative on abstract words (it needs `U32.add_comm`), so this
# must fail. If it starts checking, the checker is equating distinct stuck terms.
def canary(a: U32, b: U32) -> {U32.add(a, b) == U32.add(b, a) : U32}:
  {==}
