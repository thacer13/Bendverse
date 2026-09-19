import Base

# NEGATIVE canary: refl must NOT discharge a contradiction. If this ever starts
# checking, the checker is over-eager — a soundness alarm, not a slowdown.
def canary() -> {False{} == True{} : Bool}:
  {==}
