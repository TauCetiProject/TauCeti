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
`p.loopPow n`, the path that runs around `p` exactly `n` times. Their lengths are the multiples
`n * p.length` of the length of `p`, so a *nontrivial* closed path has pairwise distinct powers
and the type of closed paths at `a` is infinite.

That last statement is the source of every "an oriented cycle makes something infinite" argument.
In `TauCeti.RepresentationTheory.Quiver.Acyclic.FinitePaths` it is what turns finiteness of the
path space into acyclicity, and through the path basis it is what makes the path algebra of a
quiver with an oriented cycle infinite-dimensional.

## Main definitions

* `Quiver.Path.loopPow`: the `n`-th power of a closed path, `p` concatenated with itself `n`
  times; the empty concatenation is `Quiver.Path.nil`.

## Main results

* `Quiver.Path.length_loopPow`: the `n`-th power of `p` has length `n * p.length`, and
  `Quiver.Path.loopPow_add` adds exponents, which is what makes `loopPow` a power.
* `Quiver.Path.loopPow_injective`: the powers of a closed path of positive length are pairwise
  distinct.
* `Quiver.Path.infinite_of_ne_nil`: **a nontrivial closed path forces infinitely many closed
  paths**, and `Quiver.Path.eq_nil_of_finite` is the contrapositive: at a vertex carrying finitely
  many closed paths, the trivial path is the only one.

## Implementation notes

The powers are stated for a closed path rather than for a general `p : Quiver.Path a b`, since
concatenating `p` with itself is what needs `a = b`. They are not packaged as a `Monoid` structure
on `Quiver.Path a a`: nothing here needs one, and it would put a multiplication on a type whose
elements already compose partially, as arbitrary paths.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} [Quiver.{v} V] {a : V}

/-- The `n`-th power of a closed path: `p` concatenated with itself `n` times, with the empty
concatenation the trivial path. -/
def _root_.Quiver.Path.loopPow (p : Quiver.Path a a) : ℕ → Quiver.Path a a
  | 0 => Quiver.Path.nil
  | n + 1 => (p.loopPow n).comp p

@[simp]
theorem _root_.Quiver.Path.loopPow_zero (p : Quiver.Path a a) : p.loopPow 0 = Quiver.Path.nil :=
  (rfl)

/-- **One more turn around `p` is one more concatenation**, the recursion `loopPow` is defined
by. -/
@[simp]
theorem _root_.Quiver.Path.loopPow_succ (p : Quiver.Path a a) (n : ℕ) :
    p.loopPow (n + 1) = (p.loopPow n).comp p :=
  (rfl)

/-- **Every power of the trivial path is trivial**: running around a path of no arrows changes
nothing. -/
@[simp]
theorem _root_.Quiver.Path.nil_loopPow (n : ℕ) :
    (Quiver.Path.nil : Quiver.Path a a).loopPow n = Quiver.Path.nil := by
  induction n with
  | zero => rw [Quiver.Path.loopPow_zero]
  | succ n ih => rw [Quiver.Path.loopPow_succ, ih, Quiver.Path.comp_nil]

/-- **The `n`-th power of a closed path has length `n * p.length`**: each of the `n` turns
contributes the arrows of `p` once. -/
@[simp]
theorem _root_.Quiver.Path.length_loopPow (p : Quiver.Path a a) (n : ℕ) :
    (p.loopPow n).length = n * p.length := by
  induction n with
  | zero => rw [Quiver.Path.loopPow_zero, Quiver.Path.length_nil, Nat.zero_mul]
  | succ n ih =>
    rw [Quiver.Path.loopPow_succ, Quiver.Path.length_comp, ih, Nat.add_mul, Nat.one_mul]

/-- **The powers of a closed path add exponents.** With `Quiver.Path.loopPow_zero` this says that
`n ↦ p.loopPow n` is a monoid homomorphism from `(ℕ, +)` into the closed paths at `a` under
concatenation. -/
theorem _root_.Quiver.Path.loopPow_add (p : Quiver.Path a a) (m n : ℕ) :
    p.loopPow (m + n) = (p.loopPow m).comp (p.loopPow n) := by
  induction n with
  | zero => rw [Nat.add_zero, Quiver.Path.loopPow_zero, Quiver.Path.comp_nil]
  | succ n ih =>
    rw [← Nat.add_assoc, Quiver.Path.loopPow_succ, ih, Quiver.Path.loopPow_succ,
      Quiver.Path.comp_assoc]

/-- **The powers of a closed path of positive length are pairwise distinct**, because their
lengths are the distinct multiples of `p.length`. -/
theorem _root_.Quiver.Path.loopPow_injective {p : Quiver.Path a a} (hp : 0 < p.length) :
    Function.Injective p.loopPow := by
  intro m n hmn
  have hlen := congrArg Quiver.Path.length hmn
  rw [Quiver.Path.length_loopPow, Quiver.Path.length_loopPow] at hlen
  exact Nat.eq_of_mul_eq_mul_right hp hlen

/-- **A nontrivial closed path forces infinitely many closed paths**, namely its powers. -/
theorem _root_.Quiver.Path.infinite_of_ne_nil {p : Quiver.Path a a} (hp : p ≠ Quiver.Path.nil) :
    Infinite (Quiver.Path a a) :=
  Infinite.of_injective _ <| Quiver.Path.loopPow_injective <|
    Nat.pos_of_ne_zero fun h => hp (p.eq_nil_of_length_zero h)

/-- **Finitely many closed paths at a vertex leave only the trivial one**, the contrapositive of
`Quiver.Path.infinite_of_ne_nil`. -/
theorem _root_.Quiver.Path.eq_nil_of_finite [Finite (Quiver.Path a a)] (p : Quiver.Path a a) :
    p = Quiver.Path.nil := by
  by_contra hp
  exact (Quiver.Path.infinite_of_ne_nil hp).false

end TauCeti
