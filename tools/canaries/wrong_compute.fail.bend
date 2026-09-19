import Base

# NEGATIVE canary: refl must NOT discharge a miscalculated equality. If this
# starts checking, the checker is accepting terms it should not.
def canary() -> {U32.add(2, 3) == 6 : U32}:
  {==}
