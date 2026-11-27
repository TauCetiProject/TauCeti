/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.JacobiSum.Basic
public import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Jacobsthal.Basic
public import TauCeti.NumberTheory.MulChar.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.JacobiSum.Basic
import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.NumberTheory.MulChar.Orthogonality

/-!
# The Jacobi-sum expansions of the Jacobsthal sums

Let `F` be a finite field with quadratic character `η`, and let `J(χ, η)` be Mathlib's Jacobi sum
of complex characters. Group the terms of the Jacobsthal sums `ψ_n(a) = ∑_x η(x^n + a)` and
`φ_n(a) = ∑_x η(x) η(x^n + a)` by `u = x^n`. For `ψ_n`, the number of `x` with `x^n = u` is
`1 + ∑_{χ^n = 1, χ ≠ 1} χ(u)` for `n ≠ 0` (`TauCeti.card_pow_eq_eq_one_add_sum_filter_mulChar`).
For `φ_n`, the sum of `η(x)` over `x^n = u` is `∑_{χ^n = η} χ(u)`
(`TauCeti.sum_filter_mulChar_pow_eq_apply_eq_sum_filter_pow_eq`). For `a ≠ 0` the substitution
`u = -a t` turns `∑_u χ(u) η(u + a)` into `η(a) χ(-a) J(χ, η)`.

## Main results

* `TauCeti.jacobsthalPsi_eq_sum_jacobiSum`: for `n ≠ 0` and `a ≠ 0` in odd characteristic,
  `ψ_n(a) = η(a) ∑_{χ^n = 1, χ ≠ 1} χ(-a) J(χ, η)`.
* `TauCeti.jacobsthalPhi_eq_sum_jacobiSum`: for `a ≠ 0`, `φ_n(a) = η(a) ∑_{χ^n = η} χ(-a) J(χ, η)`.
  The sum is empty, and `φ_n(a) = 0`, unless `η` is an `n`-th power.
-/

public section

open Finset

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `MulChar.sum_mul_apply_add_eq_mul_jacobiSum` for the complex quadratic character `η`:
`∑_u χ(u) η(u + a) = η(a) χ(-a) J(χ, η)` for `a ≠ 0`. -/
private lemma sum_mul_quadraticChar_add (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    ∑ u : F, χ u * (quadraticChar F (u + a) : ℂ) = quadraticChar F a *
      (χ (-a) * jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ))) := by
  have h := MulChar.sum_mul_apply_add_eq_mul_jacobiSum χ
    ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) (Units.mk0 a ha)
  simp only [Units.val_mk0, MulChar.ringHomComp_apply, eq_intCast] at h
  rw [h, mul_assoc]

/-- **The Jacobi-sum expansion of `ψ_n`**: for `n ≠ 0` and `a ≠ 0` in odd characteristic,
`ψ_n(a) = η(a) ∑_{χ^n = 1, χ ≠ 1} χ(-a) J(χ, η)`, the sum over the nontrivial complex characters
of order dividing `n`, with `η` the complex quadratic character. -/
theorem jacobsthalPsi_eq_sum_jacobiSum [DecidableEq (MulChar F ℂ)] (hF : ringChar F ≠ 2) {n : ℕ}
    (hn : n ≠ 0) {a : F} (ha : a ≠ 0) :
    (jacobsthalPsi n a : ℂ) = quadraticChar F a *
      ∑ χ : MulChar F ℂ with χ ^ n = 1 ∧ χ ≠ 1,
        χ (-a) * jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) := by
  have hcount : ∀ u : F, (#{x : F | x ^ n = u} : ℂ) =
      1 + ∑ χ : MulChar F ℂ with χ ^ n = 1 ∧ χ ≠ 1, χ u := fun u ↦ by
    have : NeZero (Monoid.exponent (Fˣ ⧸ (powMonoidHom n : Fˣ →* Fˣ).range)) :=
      ⟨Monoid.exponent_ne_zero_of_finite⟩
    rw [← card_pow_eq_eq_one_add_sum_filter_mulChar hn, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  have h0 : ∑ u : F, (quadraticChar F (u + a) : ℂ) = 0 := by
    exact_mod_cast sum_quadraticChar_add hF a
  calc (jacobsthalPsi n a : ℂ)
      = ∑ u : F, (#{x : F | x ^ n = u} : ℂ) * quadraticChar F (u + a) := by
        rw [jacobsthalPsi_def, Int.cast_sum, ← sum_fiberwise univ (fun x : F ↦ x ^ n)]
        refine sum_congr rfl fun u _ ↦ ?_
        rw [sum_congr rfl fun x hx ↦ by rw [(mem_filter.1 hx).2], sum_const, nsmul_eq_mul]
    _ = _ := by
        simp_rw [hcount, add_mul, one_mul, sum_add_distrib, h0, zero_add, sum_mul]
        rw [sum_comm, mul_sum]
        exact sum_congr rfl fun χ _ ↦ sum_mul_quadraticChar_add χ ha

/-- **The Jacobi-sum expansion of `φ_n`**: for `a ≠ 0`,
`φ_n(a) = η(a) ∑_{χ^n = η} χ(-a) J(χ, η)`, the sum over the complex characters whose `n`-th power
is the complex quadratic character `η`. -/
theorem jacobsthalPhi_eq_sum_jacobiSum [DecidableEq (MulChar F ℂ)] (n : ℕ) {a : F} (ha : a ≠ 0) :
    (jacobsthalPhi n a : ℂ) = quadraticChar F a *
      ∑ χ : MulChar F ℂ with χ ^ n = (quadraticChar F).ringHomComp (Int.castRingHom ℂ),
        χ (-a) * jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) := by
  have : NeZero (Monoid.exponent Fˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  calc (jacobsthalPhi n a : ℂ)
      = ∑ u : F, (∑ x : F with x ^ n = u,
          (quadraticChar F).ringHomComp (Int.castRingHom ℂ) x) * quadraticChar F (u + a) := by
        rw [jacobsthalPhi_def, Int.cast_sum, ← sum_fiberwise univ (fun x : F ↦ x ^ n)]
        refine sum_congr rfl fun u _ ↦ ?_
        rw [sum_mul]
        refine sum_congr rfl fun x hx ↦ ?_
        rw [(mem_filter.1 hx).2, Int.cast_mul, MulChar.ringHomComp_apply, eq_intCast]
    _ = ∑ u : F, (∑ χ : MulChar F ℂ with
          χ ^ n = (quadraticChar F).ringHomComp (Int.castRingHom ℂ), χ u) *
          quadraticChar F (u + a) := by
        simp_rw [sum_filter_mulChar_pow_eq_apply_eq_sum_filter_pow_eq]
    _ = _ := by
        simp_rw [sum_mul]
        rw [sum_comm, mul_sum]
        exact sum_congr rfl fun χ _ ↦ sum_mul_quadraticChar_add χ ha

end TauCeti
