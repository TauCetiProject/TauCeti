/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Fintype.EquivFin

/-!
# Powers of a closed path

A closed path `p : Quiver.Path a a` can be concatenated with itself, so it has powers
`TauCeti.Quiver.loopPow p n`, the path that runs around `p` exactly `n` times. Their lengths are
the multiples `n * p.length` of the length of `p`, so a *nontrivial* closed path has pairwise
distinct powers and the type of closed paths at `a` is infinite.

That last statement is the source of every "an oriented cycle makes something infinite" argument.
In `TauCeti.RepresentationTheory.Quiver.Acyclic.FinitePaths` it is what turns finiteness of the
path space into acyclicity, and through the path basis it is what makes the path algebra of a
quiver with an oriented cycle infinite-dimensional.

## Main definitions

* `TauCeti.Quiver.loopPow`: the `n`-th power of a closed path, `p` concatenated with itself `n`
  times; the empty concatenation is `Quiver.Path.nil`.

## Main results

* `TauCeti.Quiver.length_loopPow`: the `n`-th power of `p` has length `n * p.length`, and
  `TauCeti.Quiver.loopPow_add` adds exponents, which is what makes `loopPow` a power.
* `TauCeti.Quiver.loopPow_injective`: the powers of a closed path of positive length are pairwise
  distinct.
* `TauCeti.Quiver.infinite_path_self_of_ne_nil`: **a nontrivial closed path forces infinitely many
  closed paths**, and `TauCeti.Quiver.eq_nil_of_finite_path_self` is the contrapositive: at a
  vertex carrying finitely many closed paths, the trivial path is the only one.

## Implementation notes

The powers are stated for a closed path rather than for a general `p : Quiver.Path a b`, since
concatenating `p` with itself is what needs `a = b`. They are not packaged as a `Monoid` structure
on `Quiver.Path a a`: nothing here needs one, and it would put a multiplication on a type whose
elements already compose partially, as arbitrary paths.
-/

public section

namespace TauCeti

namespace Quiver

universe u v

variable {V : Type u} [_root_.Quiver.{v} V] {a : V}

/-- The `n`-th power of a closed path: `p` concatenated with itself `n` times, with the empty
concatenation the trivial path. -/
def loopPow (p : _root_.Quiver.Path a a) : ℕ → _root_.Quiver.Path a a
  | 0 => _root_.Quiver.Path.nil
  | n + 1 => (loopPow p n).comp p

@[simp]
theorem loopPow_zero (p : _root_.Quiver.Path a a) : loopPow p 0 = _root_.Quiver.Path.nil :=
  (rfl)

/-- The recursion `loopPow` is defined by: one more turn around `p` is one more concatenation. -/
theorem loopPow_succ (p : _root_.Quiver.Path a a) (n : ℕ) :
    loopPow p (n + 1) = (loopPow p n).comp p :=
  (rfl)

@[simp]
theorem loopPow_one (p : _root_.Quiver.Path a a) : loopPow p 1 = p := by
  rw [loopPow_succ, loopPow_zero, _root_.Quiver.Path.nil_comp]

@[simp]
theorem length_loopPow (p : _root_.Quiver.Path a a) (n : ℕ) :
    (loopPow p n).length = n * p.length := by
  induction n with
  | zero => rw [loopPow_zero, _root_.Quiver.Path.length_nil, Nat.zero_mul]
  | succ n ih =>
    rw [loopPow_succ, _root_.Quiver.Path.length_comp, ih, Nat.add_mul, Nat.one_mul]

/-- **The powers of a closed path add exponents.** With `TauCeti.Quiver.loopPow_zero` this says
that `n ↦ loopPow p n` is a monoid homomorphism from `(ℕ, +)` into the closed paths at `a` under
concatenation. -/
theorem loopPow_add (p : _root_.Quiver.Path a a) (m n : ℕ) :
    loopPow p (m + n) = (loopPow p m).comp (loopPow p n) := by
  induction n with
  | zero => rw [Nat.add_zero, loopPow_zero, _root_.Quiver.Path.comp_nil]
  | succ n ih =>
    rw [← Nat.add_assoc, loopPow_succ, ih, loopPow_succ, _root_.Quiver.Path.comp_assoc]

/-- **The powers of a closed path of positive length are pairwise distinct**, because their
lengths are the distinct multiples of `p.length`. -/
theorem loopPow_injective {p : _root_.Quiver.Path a a} (hp : 0 < p.length) :
    Function.Injective (loopPow p) := by
  intro m n hmn
  have hlen := congrArg _root_.Quiver.Path.length hmn
  rw [length_loopPow, length_loopPow] at hlen
  exact Nat.eq_of_mul_eq_mul_right hp hlen

/-- **A nontrivial closed path forces infinitely many closed paths**, namely its powers. -/
theorem infinite_path_self_of_ne_nil {p : _root_.Quiver.Path a a}
    (hp : p ≠ _root_.Quiver.Path.nil) : Infinite (_root_.Quiver.Path a a) :=
  Infinite.of_injective _ <| loopPow_injective <|
    Nat.pos_of_ne_zero fun h => hp (p.eq_nil_of_length_zero h)

/-- **Finitely many closed paths at a vertex leave only the trivial one**, the contrapositive of
`TauCeti.Quiver.infinite_path_self_of_ne_nil`. -/
theorem eq_nil_of_finite_path_self [Finite (_root_.Quiver.Path a a)]
    (p : _root_.Quiver.Path a a) : p = _root_.Quiver.Path.nil := by
  by_contra hp
  exact (infinite_path_self_of_ne_nil hp).false

end Quiver

end TauCeti
