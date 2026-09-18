import Base

type Cell is Data:
  Cell{material: U32, cohesion: U32, active: U32, support: U32, fall: U32}

def empty() -> U32:
  0

def bedrock() -> U32:
  1

def sand() -> U32:
  2

def rock() -> U32:
  3

def rubble() -> U32:
  4

def water() -> U32:
  5

def material(w: U32) -> U32:
  (w .&. 31 : U32)

def cohesion(w: U32) -> U32:
  ((w >> 5n) .&. 63 : U32)

def active(w: U32) -> U32:
  ((w >> 11n) .&. 1 : U32)

# The activity bit (bit 11) as a named mask and the two word-level operations on
# it. Naming them keeps the engine and the laws on the semantic operation rather
# than on a literal layout constant.
def active_mask() -> U32:
  2048

def activate(+w: U32) -> U32:
  U32.or(w, active_mask())

def deactivate(+w: U32) -> U32:
  U32.and(w, U32.not(active_mask()))

def support(w: U32) -> U32:
  ((w >> 12n) .&. 31 : U32)

def fall(w: U32) -> U32:
  ((w >> 17n) .&. 63 : U32)

def encode(mat: U32, coh: U32, act: U32, sup: U32, fl: U32) -> U32:
  (U32.and(mat, 31)
   .|. (U32.and(coh, 63) << 5n)
   .|. (U32.and(act, 1) << 11n)
   .|. (U32.and(sup, 31) << 12n)
   .|. (U32.and(fl, 63) << 17n) : U32)

def decode(+w: U32) -> Cell:
  Cell{material(w), cohesion(w), active(w), support(w), fall(w)}

def reencode(+w: U32) -> U32:
  encode(material(w), cohesion(w), active(w), support(w), fall(w))

def density(m: U32) -> U32:
  match m:
    case 0:
      0
    case 1:
      255
    case 2:
      100
    case 3:
      200
    case 4:
      150
    case 5:
      80
    case _:
      0

def static(m: U32) -> Bool:
  match m:
    case 1:
      True{}
    case _:
      False{}

def slides(m: U32) -> Bool:
  match m:
    case 2:
      True{}
    case 4:
      True{}
    case 5:
      True{}
    case _:
      False{}

def default_cohesion(m: U32) -> U32:
  match m:
    case 1:
      63
    case 3:
      48
    case _:
      0
