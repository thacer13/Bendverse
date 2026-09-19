import Base

# POSITIVE canary: `U32.is_eq` on literals must reduce to `True`. This is the
# reflection surface our material guards depend on (`Word.cmp` → `Cmp.is_eq`).
def canary() -> {U32.is_eq(3, 3) == True{} : Bool}:
  {==}
