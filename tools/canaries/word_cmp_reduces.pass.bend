import Base

# POSITIVE canary: `Word.cmp` on concrete words must reduce through `Cmp` to
# `Cmp.is_eq`, so a `{==}` proof of `... == True` goes through. Guards the
# reflection lemmas in `src/word.bend`.
def canary() -> {Cmp.is_eq(Word.cmp(32n, Word.zero(32n), Word.zero(32n))) == True{} : Bool}:
  {==}
