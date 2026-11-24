/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import TauCeti.GroupTheory.ExponentialGroup.FreeCompletion
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Lyndon's completion

*Lyndon's completion* `G^{ℤ[t]}` of a group `G` is its tensor completion over the ring `ℤ[t]` of
integer polynomials: a group with exponents in `ℤ[t]`, with a homomorphism from `G` through which
every homomorphism from `G` to such a group factors uniquely by a homomorphism commuting with
exponentiation. For a free group `F` it is Lyndon's free `ℤ[t]`-group `F^{ℤ[t]}`.

## Main definitions

* `TauCeti.ExponentialGroup.LyndonCompletion G`: the tensor completion of `G` over `ℤ[t]`, with
  its exponentiation by `ℤ[t]` as a global instance.

## Implementation notes

`LyndonCompletion G` is an abbreviation of `TauCeti.ExponentialGroup.Completion ℤ[X] G`, so the
API of the tensor completion applies to it at `A = ℤ[t]`:
* the coefficient homomorphism `G →* G^{ℤ[t]}` is
  `TauCeti.ExponentialGroup.Completion.of (A := ℤ[X])`;
* the universal property is `TauCeti.ExponentialGroup.Completion.isCompletion_of`;
* every group embeds in its Lyndon completion:
  `TauCeti.ExponentialGroup.Completion.of_injective (Polynomial.evalRingHom 1)`; the evaluation
  `Polynomial.evalRingHom` needs `import Mathlib.Algebra.Polynomial.Eval.Defs`, which this file
  does not re-export;
* generation by the image of `G` under exponentiation is
  `TauCeti.ExponentialGroup.Completion.eq_top_of_range_le`;
* Lyndon's completion of the infinite cyclic group is the additive group of `ℤ[t]`, by the
  comparison isomorphism `isCompletion_of.mulEquiv (IsExponentialGroup.isCompletion_intCast ℤ[X])`
  onto `Multiplicative ℤ[X]`. Its statement uses the exponentiation of `Multiplicative ℤ[X]` by
  `ℤ[X]`, a scoped instance activated by
  `open scoped TauCeti.IsExponentialGroup.MultiplicativePow`.

The exponentiation of the tensor completion is a scoped instance, since for the exponents `ℕ` and
`ℤ` it would compete with the usual powers of a group; the exponents `ℤ[t]` compete with nothing,
so here it is a global instance.

## References

* A. G. Myasnikov, V. N. Remeslennikov, D. E. Serbin, *Regular free length functions on Lyndon's
  free `ℤ[t]`-group `F^{ℤ[t]}`*, §2.1.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I*, J. Algebra
  200 (1998), §1, Definitions 6–7.
* R. C. Lyndon, *Groups with parametric exponents*, Trans. Amer. Math. Soc. 96 (1960).
-/

public section

open Polynomial

universe u

namespace TauCeti.ExponentialGroup

/-- Lyndon's completion `G^{ℤ[t]}` of a group `G`: its tensor completion over the ring `ℤ[t]` of
integer polynomials. For a free group it is Lyndon's free `ℤ[t]`-group. -/
abbrev LyndonCompletion (G : Type u) [Group G] : Type u :=
  Completion ℤ[X] G

namespace LyndonCompletion

variable {G : Type u} [Group G]

/-- The exponentiation of Lyndon's completion by integer polynomials. -/
noncomputable instance : Pow (LyndonCompletion G) ℤ[X] :=
  Completion.instPow

/-- Lyndon's completion is a `ℤ[t]`-group. -/
instance : IsExponentialGroup ℤ[X] (LyndonCompletion G) :=
  Completion.instIsExponentialGroup

/-! ### Examples: the universal property, the laws of a `ℤ[t]`-group, the infinite cyclic group -/

open Completion

-- A homomorphism from `G` to a `ℤ[t]`-group extends uniquely to a homomorphism from the
-- completion commuting with exponentiation.
example {H : Type*} [Group H] [Pow H ℤ[X]] [IsExponentialGroup ℤ[X] H] (φ : G →* H) :
    ∃! ψ : ExponentialHom ℤ[X] (LyndonCompletion G) H, ψ.toMonoidHom.comp (of (A := ℤ[X])) = φ :=
  isCompletion_of.existsUnique H φ

-- The coefficient homomorphism keeps a generator `a` of the free group of rank two nontrivial.
example : (of (A := ℤ[X]) (FreeGroup.of 0) : LyndonCompletion (FreeGroup (Fin 2))) ≠ 1 :=
  (map_ne_one_iff _ (of_injective (evalRingHom 1))).2 (FreeGroup.of_ne_one 0)

-- `a ^ (t + 1) = a ^ t * a`
example (a : LyndonCompletion G) : a ^ (X + 1 : ℤ[X]) = a ^ (X : ℤ[X]) * a :=
  IsExponentialGroup.pow_add_one a X

-- `(a ^ t) ^ t = a ^ t²`
example (a : LyndonCompletion G) : (a ^ (X : ℤ[X])) ^ (X : ℤ[X]) = a ^ (X ^ 2 : ℤ[X]) :=
  (IsExponentialGroup.pow_sq a X).symm

open scoped IsExponentialGroup.MultiplicativePow

-- Lyndon's completion of the infinite cyclic group is the additive group of `ℤ[t]`: their
-- comparison isomorphism takes the coefficient `n` to the constant polynomial `n`.
example (n : ℤ) :
    isCompletion_of.mulEquiv (IsExponentialGroup.isCompletion_intCast ℤ[X])
      (of (A := ℤ[X]) (Multiplicative.ofAdd n)) = Multiplicative.ofAdd (n : ℤ[X]) := by
  simp

-- It takes `x ^ p` to `p` times the image of `x`, so it is an isomorphism of `ℤ[t]`-groups.
example (x : LyndonCompletion (Multiplicative ℤ)) (p : ℤ[X]) :
    (isCompletion_of.mulEquiv (IsExponentialGroup.isCompletion_intCast ℤ[X]) (x ^ p)).toAdd =
      p * (isCompletion_of.mulEquiv (IsExponentialGroup.isCompletion_intCast ℤ[X]) x).toAdd := by
  simp

end LyndonCompletion

end TauCeti.ExponentialGroup
