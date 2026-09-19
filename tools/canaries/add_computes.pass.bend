import Base

# POSITIVE canary: the checker must reduce a closed computation. If this stops
# checking, normalization is missing/stuck for `U32.add` — a red flag for every
# proof that relies on `{==}`.
def canary() -> {U32.add(2, 3) == 5 : U32}:
  {==}
