# `List` lemmas Base does not ship: append is associative and has `Nil` as a
# right unit, `List.reverse` meets `append`, and `List.length` is additive.
# All six are by induction on the list; none is reflexivity.
#
# Imported from BendHub 0x085d89db9ee8a21865e959816bb20e5b/list.bend (the
# `&2, Nat` shape is that package's; it checks verbatim in Bend 2.0.17). Kept
# here rather than re-derived because `bend_lemmas` indexes this directory:
# `src/settle.bend`'s `app` is `List.append(&2, Nat, ...)`, so every lemma
# below applies to `app` without a bridge.
#
# Rewrite orientation (the whole reason these are stated this way): `%lem(args)
# : P` rewrites with `lem : {a == b}` by eliminating `b` — the RIGHT side is
# the form your goal currently holds. So each lemma is written
# `{target == what-the-goal-holds-now}`, i.e. the left side is the shape the
# goal should end up in.

import Base

def append_nil2(xs: List<&2, Nat>) -> {xs == List.append(&2, Nat, xs, Nil{}) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %append_nil2(t) : {h <> t == h <> _ : List<&2, Nat>}
      {==}

def append_assoc2(xs: List<&2, Nat>, ys: List<&2, Nat>, zs: List<&2, Nat>)
  -> {List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) == List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %append_assoc2(t, ys, zs) : {h <> List.append(&2, Nat, t, List.append(&2, Nat, ys, zs)) == h <> _ : List<&2, Nat>}
      {==}

def reverse_go_spec(xs: List<&2, Nat>, +acc: List<&2, Nat>)
  -> {List.append(&2, Nat, List.reverse(&2, Nat, xs), acc) == List.reverse.go(&2, Nat, xs, acc) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %reverse_go_spec(t, h <> Nil{}) : {List.append(&2, Nat, _, acc) == List.reverse.go(&2, Nat, t, h <> acc) : List<&2, Nat>}
      %append_assoc2(List.reverse(&2, Nat, t), h <> Nil{}, acc) : {_ == List.reverse.go(&2, Nat, t, h <> acc) : List<&2, Nat>}
      %reverse_go_spec(t, h <> acc) : {List.append(&2, Nat, List.reverse(&2, Nat, t), h <> acc) == _ : List<&2, Nat>}
      {==}

def reverse_append2(xs: List<&2, Nat>, +ys: List<&2, Nat>)
  -> {List.append(&2, Nat, List.reverse(&2, Nat, ys), List.reverse(&2, Nat, xs)) == List.reverse(&2, Nat, List.append(&2, Nat, xs, ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      %append_nil2(List.reverse.go(&2, Nat, ys, [])) : {_ == List.reverse.go(&2, Nat, ys, []) : List<&2, Nat>}
      {==}
    case Con{+h, +t}:
      %reverse_go_spec(t, h <> Nil{}) : {List.append(&2, Nat, List.reverse.go(&2, Nat, ys, []), _) == List.reverse.go(&2, Nat, List.append(&2, Nat, t, ys), [h]) : List<&2, Nat>}
      %reverse_go_spec(List.append(&2, Nat, t, ys), h <> Nil{}) : {List.append(&2, Nat, List.reverse.go(&2, Nat, ys, []), List.append(&2, Nat, List.reverse(&2, Nat, t), h <> Nil{})) == _ : List<&2, Nat>}
      %reverse_append2(t, ys) : {List.append(&2, Nat, List.reverse.go(&2, Nat, ys, []), List.append(&2, Nat, List.reverse(&2, Nat, t), h <> Nil{})) == List.append(&2, Nat, _, h <> Nil{}) : List<&2, Nat>}
      %append_assoc2(List.reverse.go(&2, Nat, ys, []), List.reverse(&2, Nat, t), h <> Nil{}) : {List.append(&2, Nat, List.reverse.go(&2, Nat, ys, []), List.append(&2, Nat, List.reverse(&2, Nat, t), h <> Nil{})) == _ : List<&2, Nat>}
      {==}

def reverse_reverse(xs: List<&2, Nat>) -> {xs == List.reverse(&2, Nat, List.reverse(&2, Nat, xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %reverse_go_spec(t, h <> Nil{}) : {h <> t == List.reverse.go(&2, Nat, _, []) : List<&2, Nat>}
      %reverse_append2(List.reverse(&2, Nat, t), h <> Nil{}) : {h <> t == _ : List<&2, Nat>}
      %reverse_reverse(t) : {h <> t == List.append(&2, Nat, List.reverse(&2, Nat, h <> Nil{}), _) : List<&2, Nat>}
      {==}

def length_append(xs: List<&2, Nat>, ys: List<&2, Nat>)
  -> {Nat.add(List.length(&2, Nat, xs), List.length(&2, Nat, ys)) == List.length(&2, Nat, List.append(&2, Nat, xs, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %length_append(t, ys) : {1n+Nat.add(List.length(&2, Nat, t), List.length(&2, Nat, ys)) == 1n+_ : Nat}
      {==}
