/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Formal solutions at an irregular singularity of rank one

Consider `w'' + f(z) w' + g(z) w = 0` near `z = ∞`, where `f(z) ∼ ∑ fₛ z⁻ˢ` and
`g(z) ∼ ∑ gₛ z⁻ˢ`; the coefficient sequences are recorded as formal power series `F` and `G` in
the variable `X = z⁻¹`. When `f₀`, `g₀` and `g₁` are not all zero, infinity is an irregular
singularity of rank one, and the equation has formal solutions (DLMF 2.7.8)

`exp(κ z) z^μ ∑ aₛ z⁻ˢ`,

where `κ` is a root of the characteristic equation `κ² + f₀ κ + g₀ = 0` (2.7.9),
`μ = -(κ f₁ + g₁) / (f₀ + 2κ)` (2.7.10), and the coefficients are determined by `a₀ = 1` and the
recursion (2.7.11)

`(f₀ + 2κ) s aₛ = (s - μ) (s - 1 - μ) aₛ₋₁ + ∑_{k=1}^{s} (κ fₖ₊₁ + gₖ₊₁ - (s - k - μ) fₖ) aₛ₋ₖ`.

This requires the two characteristic roots to be distinct, `f₀ + 2κ ≠ 0`. This file proves that
these series are formal solutions, and that their truncations solve the equation up to a residual
of the next order. The actual solutions with these asymptotic expansions are obtained from the
truncations by solving a Volterra integral equation for the error, with this residual as the
forcing term (Olver, Chapter 7, §2).

Solutions are written in the logarithmic coordinate `z = exp ζ`. There `z^μ = exp(μ ζ)` needs no
choice of branch, the truncations are entire functions of `ζ`, and `w(e^ζ) = W(ζ)` turns the
equation into `W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0`. The limit `z → ∞` in a sector
becomes `Re ζ → +∞` with `Im ζ` in a bounded interval; the residual estimates below hold
uniformly in `Im ζ`.

## Main definitions

* `TauCeti.rankOneOperator F G κ μ A`: the formal operator
  `X² (θ - μ) (θ - μ + 1) A - X (2κ + F) (θ - μ) A + (κ² + κ F + G) A`, with `θ = X d/dX`,
  obtained by substituting `exp(κ z) z^μ A(z⁻¹)` into the equation.
* `TauCeti.rankOneCoeff F G κ μ`: the coefficients of DLMF 2.7.11, normalized by `a₀ = 1`.
* `TauCeti.rankOneFormalSolution κ μ a N`: the truncation `exp(κ e^ζ + μ ζ) ∑_{s<N} aₛ e^{-sζ}`.

## Main results

* `TauCeti.coeff_zero_rankOneOperator`, `TauCeti.coeff_one_rankOneOperator`,
  `TauCeti.coeff_add_two_rankOneOperator`: the coefficients of the formal operator, which give
  2.7.9, 2.7.10 and 2.7.11.
* `TauCeti.mul_rankOneCoeff`: the recursion 2.7.11.
* `TauCeti.rankOneOperator_mk_rankOneCoeff`: under 2.7.9 and 2.7.10 with distinct roots, the
  series with the coefficients of 2.7.11 is a formal solution.
* `TauCeti.eq_rankOneCoeff_of_rankOneOperator_eq_zero`: it is the only formal solution with
  `a₀ = 1`.
* `TauCeti.isBigO_rankOneFormalSolution_residual_sub`: for arbitrary coefficients, the residual of
  the truncation after `N` terms, up to `O(exp(κ e^ζ + (μ + 1 - N) ζ))`, is given by the first
  `N + 1` coefficients of the formal operator.
* `TauCeti.isBigO_rankOneFormalSolution_residual`,
  `TauCeti.isBigO_rankOneFormalSolution_rankOneCoeff_residual`: for a formal solution the residual
  of the truncation after `N` terms is `O(exp(κ e^ζ + (μ + 1 - N) ζ))` as `Re ζ → +∞`, that is
  `O(e^{κ z} z^{μ - N - 1})` in the original variable.

## Implementation notes

The truncation is `exp(κ e^ζ + μ ζ) p(e^{-ζ})` for the polynomial `p` of the first `N`
coefficients, and `d/dζ` acts on `p(e^{-ζ})` as `-θ`. Multiplied by `e^{-2ζ}`, the residual is
therefore `exp(κ e^ζ + μ ζ)` times the formal operator, applied to `p` and evaluated at `e^{-ζ}`,
up to the errors in the expansions of `f` and `g`.

## References

* NIST Digital Library of Mathematical Functions, §2.7(ii), equations (2.7.7)–(2.7.11),
  <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 7, §§1–2.
-/

public section

open Bornology Filter Finset Asymptotics PowerSeries
open scoped Topology Complex

namespace TauCeti

/-! ### The formal operator -/

/-- The operator obtained by substituting a formal solution `exp(κ z) z^μ ∑ aₛ z⁻ˢ` into
`w'' + f(z) w' + g(z) w = 0`, where `f(z) = ∑ fₛ z⁻ˢ` and `g(z) = ∑ gₛ z⁻ˢ` are the formal series
`F` and `G` in the variable `X = z⁻¹`. With `θ = X d/dX`, it is

`X² (θ - μ) (θ - μ + 1) A - X (2κ + F) (θ - μ) A + (κ² + κ F + G) A`,

which is `z^{-μ} exp(-κ z)` times the left-hand side of the equation evaluated at
`exp(κ z) z^μ A(z⁻¹)`. The formal series is a formal solution when this operator vanishes. -/
noncomputable def rankOneOperator (F G : ℂ⟦X⟧) (κ μ : ℂ) (A : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  X ^ 2 * (X * d⁄dX (X * d⁄dX A - C μ * A) - C (μ - 1) * (X * d⁄dX A - C μ * A)) -
    X * (C (2 * κ) + F) * (X * d⁄dX A - C μ * A) + (C (κ ^ 2) + C κ * F + G) * A

theorem rankOneOperator_def (F G : ℂ⟦X⟧) (κ μ : ℂ) (A : ℂ⟦X⟧) :
    rankOneOperator F G κ μ A =
      X ^ 2 * (X * d⁄dX (X * d⁄dX A - C μ * A) - C (μ - 1) * (X * d⁄dX A - C μ * A)) -
        X * (C (2 * κ) + F) * (X * d⁄dX A - C μ * A) + (C (κ ^ 2) + C κ * F + G) * A := by
  rw [rankOneOperator]

/-- The coefficients of `θ A - c A`, where `θ = X d/dX`, are `(n - c) aₙ`. -/
private lemma coeff_X_mul_derivative_sub (c : ℂ) (A : ℂ⟦X⟧) (n : ℕ) :
    coeff n (X * d⁄dX A - C c * A) = (n - c) * coeff n A := by
  rw [map_sub, coeff_X_mul_derivative, coeff_C_mul, sub_mul]

/-- `θ - c` preserves divisibility by `Xⁿ`. -/
private lemma X_pow_dvd_X_mul_derivative_sub_C_mul {n : ℕ} {A : ℂ⟦X⟧} (hA : X ^ n ∣ A) (c : ℂ) :
    X ^ n ∣ X * d⁄dX A - C c * A := by
  rw [X_pow_dvd_iff] at hA ⊢
  intro m hm
  rw [coeff_X_mul_derivative_sub, hA m hm, mul_zero]

/-- If `Xⁿ ∣ A`, the operator applied to `A` agrees with `(κ² + κ F + G) A` modulo `Xⁿ⁺¹`: the
coefficient of `Xᵐ` in the operator depends on `aₘ` only through `(κ² + κ f₀ + g₀) aₘ`. -/
private lemma X_pow_succ_dvd_rankOneOperator_sub (F G : ℂ⟦X⟧) (κ μ : ℂ) {n : ℕ} {A : ℂ⟦X⟧}
    (hA : X ^ n ∣ A) :
    X ^ (n + 1) ∣ rankOneOperator F G κ μ A - (C (κ ^ 2) + C κ * F + G) * A := by
  have h₁ := X_pow_dvd_X_mul_derivative_sub_C_mul hA μ
  have h₂ := X_pow_dvd_X_mul_derivative_sub_C_mul h₁ (μ - 1)
  rw [rankOneOperator, add_sub_cancel_right]
  refine dvd_sub ?_ ?_
  · have h : (X : ℂ⟦X⟧) ^ (n + 1) ∣ X ^ 2 * X ^ n := by
      rw [← pow_add]; exact pow_dvd_pow X (by omega)
    exact h.trans (mul_dvd_mul_left _ h₂)
  · rw [pow_succ', mul_assoc]
    exact mul_dvd_mul_left X (dvd_mul_of_dvd_right h₁ _)

/-- The constant coefficient of the operator is `(κ² + κ f₀ + g₀) a₀`: it vanishes for `a₀ ≠ 0`
exactly when `κ` is a root of the characteristic equation `κ² + f₀ κ + g₀ = 0` (DLMF 2.7.9). -/
theorem coeff_zero_rankOneOperator (F G : ℂ⟦X⟧) (κ μ : ℂ) (A : ℂ⟦X⟧) :
    coeff 0 (rankOneOperator F G κ μ A) =
      (κ ^ 2 + κ * coeff 0 F + coeff 0 G) * coeff 0 A := by
  simp [rankOneOperator, coeff_zero_eq_constantCoeff]

/-- The coefficient of `X` in the operator. When `κ² + κ f₀ + g₀ = 0` it is
`(μ (f₀ + 2κ) + κ f₁ + g₁) a₀`, so for `a₀ ≠ 0` and a simple root `κ`, `f₀ + 2κ ≠ 0`, it vanishes
exactly when `μ` is given by DLMF 2.7.10. -/
theorem coeff_one_rankOneOperator (F G : ℂ⟦X⟧) (κ μ : ℂ) (A : ℂ⟦X⟧) :
    coeff 1 (rankOneOperator F G κ μ A) =
      (μ * (coeff 0 F + 2 * κ) + κ * coeff 1 F + coeff 1 G) * coeff 0 A +
        (κ ^ 2 + κ * coeff 0 F + coeff 0 G) * coeff 1 A := by
  have h1 := coeff_X_mul_derivative_sub μ A 0
  rw [coeff_zero_eq_constantCoeff_apply] at h1
  simp only [rankOneOperator, map_add, map_sub, pow_two, mul_assoc, coeff_succ_X_mul,
    coeff_zero_eq_constantCoeff_apply, map_mul, coeff_C_mul, h1,
    coeff_mul (n := 1) _ A, Nat.antidiagonal_succ, Nat.antidiagonal_zero]
  simp [coeff_zero_eq_constantCoeff_apply]
  ring

/-- The coefficient of `Xˢ⁺²` in the operator. The terms in `aₛ₊₂` and `aₛ₊₁` are displayed
separately; when `κ² + κ f₀ + g₀ = 0` and `μ (f₀ + 2κ) + κ f₁ + g₁ = 0` they combine to
`-(s + 1) (f₀ + 2κ) aₛ₊₁`, which gives the recursion of DLMF 2.7.11. -/
theorem coeff_add_two_rankOneOperator (F G : ℂ⟦X⟧) (κ μ : ℂ) (A : ℂ⟦X⟧) (s : ℕ) :
    coeff (s + 2) (rankOneOperator F G κ μ A) =
      (κ ^ 2 + κ * coeff 0 F + coeff 0 G) * coeff (s + 2) A +
        ((κ * coeff 1 F + coeff 1 G) - (coeff 0 F + 2 * κ) * (s + 1 - μ)) * coeff (s + 1) A +
        (s + 1 - μ) * (s - μ) * coeff s A +
        ∑ j ∈ range (s + 1), (κ * coeff (s + 2 - j) F + coeff (s + 2 - j) G -
          (j - μ) * coeff (s + 1 - j) F) * coeff j A := by
  rw [rankOneOperator, map_add, map_sub, coeff_X_pow_mul, mul_assoc, coeff_succ_X_mul,
    coeff_X_mul_derivative_sub, coeff_X_mul_derivative_sub, mul_comm (C (2 * κ) + F),
    mul_comm (C (κ ^ 2) + C κ * F + G), coeff_mul, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, sum_range_succ (n := s + 2), sum_range_succ (n := s + 1)]
  simp only [coeff_X_mul_derivative_sub, map_add, coeff_C_mul, coeff_C]
  have h₁ : ∀ x ∈ range (s + 1), (x - μ) * coeff x A *
      ((if s + 1 - x = 0 then 2 * κ else 0) + coeff (s + 1 - x) F) =
        (x - μ) * coeff (s + 1 - x) F * coeff x A := fun x hx ↦ by
    have := mem_range.1 hx
    split_ifs with h
    · omega
    · ring
  have h₂ : ∀ x ∈ range (s + 1), coeff x A *
      ((if s + 2 - x = 0 then κ ^ 2 else 0) + κ * coeff (s + 2 - x) F + coeff (s + 2 - x) G) =
        (κ * coeff (s + 2 - x) F + coeff (s + 2 - x) G) * coeff x A := fun x hx ↦ by
    have := mem_range.1 hx
    split_ifs with h
    · omega
    · ring
  rw [sum_congr rfl h₁, sum_congr rfl h₂]
  simp only [sub_mul, sum_sub_distrib, Nat.sub_self, show s + 2 - (s + 1) = 1 by omega,
    ite_true, one_ne_zero, ite_false]
  push_cast
  ring

/-! ### The coefficients of the formal solutions -/

/-- The coefficients `aₛ` of the formal solution `exp(κ z) z^μ ∑ aₛ z⁻ˢ` of
`w'' + f(z) w' + g(z) w = 0`, where `f(z) = ∑ fₛ z⁻ˢ` and `g(z) = ∑ gₛ z⁻ˢ` are the formal series
`F` and `G`, normalized by `a₀ = 1` and defined by the recursion of DLMF 2.7.11,

`(f₀ + 2κ) s aₛ = (s - μ) (s - 1 - μ) aₛ₋₁ + ∑_{k=1}^{s} (κ fₖ₊₁ + gₖ₊₁ - (s - k - μ) fₖ) aₛ₋ₖ`.

When `f₀ + 2κ ≠ 0` they satisfy this recursion (`TauCeti.mul_rankOneCoeff`). For a root `κ` of
the characteristic equation `κ² + f₀ κ + g₀ = 0` this says that `κ` differs from the other root
`-f₀ - κ`. -/
noncomputable def rankOneCoeff (F G : ℂ⟦X⟧) (κ μ : ℂ) : ℕ → ℂ
  | 0 => 1
  | s + 1 => ((coeff 0 F + 2 * κ) * (s + 1))⁻¹ *
      ((s + 1 - μ) * (s - μ) * rankOneCoeff F G κ μ s +
        ∑ j : Fin (s + 1), (κ * coeff (s + 2 - j) F + coeff (s + 2 - j) G -
          (j - μ) * coeff (s + 1 - j) F) * rankOneCoeff F G κ μ j)

@[simp]
theorem rankOneCoeff_zero (F G : ℂ⟦X⟧) (κ μ : ℂ) : rankOneCoeff F G κ μ 0 = 1 := by
  rw [rankOneCoeff]

theorem rankOneCoeff_succ (F G : ℂ⟦X⟧) (κ μ : ℂ) (s : ℕ) :
    rankOneCoeff F G κ μ (s + 1) = ((coeff 0 F + 2 * κ) * (s + 1))⁻¹ *
      ((s + 1 - μ) * (s - μ) * rankOneCoeff F G κ μ s +
        ∑ j ∈ range (s + 1), (κ * coeff (s + 2 - j) F + coeff (s + 2 - j) G -
          (j - μ) * coeff (s + 1 - j) F) * rankOneCoeff F G κ μ j) := by
  rw [rankOneCoeff, Fin.sum_univ_eq_sum_range (fun j ↦ (κ * coeff (s + 2 - j) F +
    coeff (s + 2 - j) G - (j - μ) * coeff (s + 1 - j) F) * rankOneCoeff F G κ μ j)]

/-- The recursion of `TauCeti.rankOneCoeff` with the sum indexed by the earlier coefficient. -/
private lemma mul_rankOneCoeff_succ {F G : ℂ⟦X⟧} {κ : ℂ} (hne : coeff 0 F + 2 * κ ≠ 0) (μ : ℂ)
    (s : ℕ) : (coeff 0 F + 2 * κ) * (s + 1) * rankOneCoeff F G κ μ (s + 1) =
      (s + 1 - μ) * (s - μ) * rankOneCoeff F G κ μ s +
        ∑ j ∈ range (s + 1), (κ * coeff (s + 2 - j) F + coeff (s + 2 - j) G -
          (j - μ) * coeff (s + 1 - j) F) * rankOneCoeff F G κ μ j := by
  rw [rankOneCoeff_succ, ← mul_assoc,
    mul_inv_cancel₀ (mul_ne_zero hne (Nat.cast_add_one_ne_zero s)), one_mul]

/-- When `f₀ + 2κ ≠ 0`, the coefficients `TauCeti.rankOneCoeff` satisfy the recursion DLMF 2.7.11,
`(f₀ + 2κ) s aₛ = (s - μ) (s - 1 - μ) aₛ₋₁ + ∑_{k=1}^{s} (κ fₖ₊₁ + gₖ₊₁ - (s - k - μ) fₖ) aₛ₋ₖ`,
here at `s + 1` for `s ≥ 0`. -/
theorem mul_rankOneCoeff {F G : ℂ⟦X⟧} {κ : ℂ} (hne : coeff 0 F + 2 * κ ≠ 0) (μ : ℂ) (s : ℕ) :
    (coeff 0 F + 2 * κ) * (s + 1) * rankOneCoeff F G κ μ (s + 1) =
      (s + 1 - μ) * (s - μ) * rankOneCoeff F G κ μ s +
        ∑ k ∈ Icc 1 (s + 1), (κ * coeff (k + 1) F + coeff (k + 1) G -
          (s + 1 - k - μ) * coeff k F) * rankOneCoeff F G κ μ (s + 1 - k) := by
  rw [mul_rankOneCoeff_succ hne, ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
    ← sum_range_reflect]
  congr 1
  refine sum_congr (by simp) fun k hk ↦ ?_
  have hk := mem_range.1 hk
  rw [show s + 1 - 1 - k = s - k by omega, show s + 2 - (s - k) = 1 + k + 1 by omega,
    show s + 1 - (s - k) = 1 + k by omega, show s + 1 - (1 + k) = s - k by omega,
    Nat.cast_sub (by omega : k ≤ s)]
  push_cast
  ring

/-- **Formal solutions at an irregular singularity of rank one** (DLMF 2.7.8–2.7.11). If `κ` is a
root of the characteristic equation `κ² + f₀ κ + g₀ = 0` (2.7.9) different from the other root,
that is `f₀ + 2κ ≠ 0`, and `μ (f₀ + 2κ) = -(κ f₁ + g₁)` (2.7.10), then the series
`exp(κ z) z^μ ∑ aₛ z⁻ˢ` with the coefficients `TauCeti.rankOneCoeff` of 2.7.11 is a formal solution
of `w'' + f(z) w' + g(z) w = 0`. -/
theorem rankOneOperator_mk_rankOneCoeff {F G : ℂ⟦X⟧} {κ μ : ℂ}
    (hκ : κ ^ 2 + κ * coeff 0 F + coeff 0 G = 0) (hne : coeff 0 F + 2 * κ ≠ 0)
    (hμ : μ * (coeff 0 F + 2 * κ) + κ * coeff 1 F + coeff 1 G = 0) :
    rankOneOperator F G κ μ (mk (rankOneCoeff F G κ μ)) = 0 := by
  ext n
  rw [map_zero]
  rcases n with _ | _ | s
  · rw [coeff_zero_rankOneOperator, hκ, zero_mul]
  · rw [coeff_one_rankOneOperator, hκ, hμ, zero_mul, zero_mul, add_zero]
  · rw [coeff_add_two_rankOneOperator, hκ, zero_mul, zero_add]
    simp only [coeff_mk]
    linear_combination rankOneCoeff F G κ μ (s + 1) * hμ - mul_rankOneCoeff_succ (G := G) hne μ s

/-- The normalized formal solution is unique: if `exp(κ z) z^μ ∑ bₛ z⁻ˢ` is a formal solution with
`b₀ = 1` and `f₀ + 2κ ≠ 0`, then `bₛ` are the coefficients `TauCeti.rankOneCoeff` of DLMF 2.7.11.
The conditions 2.7.9 and 2.7.10 on `κ` and `μ` are then the constant and linear coefficients of
the equation `rankOneOperator F G κ μ (mk b) = 0`. -/
theorem eq_rankOneCoeff_of_rankOneOperator_eq_zero {F G : ℂ⟦X⟧} {κ μ : ℂ} {b : ℕ → ℂ}
    (hb : rankOneOperator F G κ μ (mk b) = 0) (hb₀ : b 0 = 1) (hne : coeff 0 F + 2 * κ ≠ 0) :
    b = rankOneCoeff F G κ μ := by
  have h₀ := coeff_zero_rankOneOperator F G κ μ (mk b)
  have h₁ := coeff_one_rankOneOperator F G κ μ (mk b)
  rw [hb, map_zero, coeff_mk, hb₀, mul_one] at h₀
  rw [hb, map_zero, coeff_mk, coeff_mk, hb₀, mul_one, ← h₀, zero_mul, add_zero] at h₁
  funext s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rcases s with _ | s
    · rw [hb₀, rankOneCoeff_zero]
    have h := coeff_add_two_rankOneOperator F G κ μ (mk b) s
    rw [hb, map_zero, ← h₀, zero_mul, zero_add] at h
    simp only [coeff_mk] at h
    rw [sum_congr rfl fun j hj ↦ by rw [ih j (by have := mem_range.1 hj; omega)],
      ih s (by omega)] at h
    refine mul_left_cancel₀ (mul_ne_zero hne (Nat.cast_add_one_ne_zero s)) ?_
    linear_combination h - mul_rankOneCoeff_succ (G := G) hne μ s - b (s + 1) * h₁

/-! ### Truncated formal solutions in logarithmic coordinates -/

/-- The truncation after `N` terms of the formal solution `exp(κ z) z^μ ∑ aₛ z⁻ˢ` of
`w'' + f(z) w' + g(z) w = 0` at an irregular singularity of rank one at infinity, written in the
logarithmic coordinate `z = exp ζ`: `exp(κ e^ζ + μ ζ) ∑_{s<N} aₛ e^{-sζ}`. In this coordinate the
power `z^μ = exp(μ ζ)` needs no choice of branch, and the function is entire. -/
noncomputable def rankOneFormalSolution (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) (ζ : ℂ) : ℂ :=
  cexp (κ * cexp ζ + μ * ζ) * ∑ s ∈ range N, a s * cexp (-(s * ζ))

theorem rankOneFormalSolution_def (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) (ζ : ℂ) :
    rankOneFormalSolution κ μ a N ζ =
      cexp (κ * cexp ζ + μ * ζ) * ∑ s ∈ range N, a s * cexp (-(s * ζ)) := by
  rw [rankOneFormalSolution]

section Analytic

/-- The Euler operator `θ = X d/dX` on polynomials. -/
private noncomputable def polyEuler (p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X * Polynomial.derivative p

private lemma coe_polyEuler (p : Polynomial ℂ) :
    ((polyEuler p : Polynomial ℂ) : ℂ⟦X⟧) = X * d⁄dX (p : ℂ⟦X⟧) := by
  rw [polyEuler, Polynomial.coe_mul, Polynomial.coe_X, derivative_coe]

/-- `ζ ↦ p(e^{-ζ})` has derivative `-(θ p)(e^{-ζ})`. -/
private lemma hasDerivAt_eval_exp_neg (p : Polynomial ℂ) (ζ : ℂ) :
    HasDerivAt (fun ζ ↦ p.eval (cexp (-ζ))) (-(polyEuler p).eval (cexp (-ζ))) ζ := by
  have h := (p.hasDerivAt (cexp (-ζ))).comp ζ ((hasDerivAt_neg ζ).cexp)
  refine h.congr_deriv ?_
  rw [polyEuler, Polynomial.eval_mul, Polynomial.eval_X]
  ring

/-- The function `exp(κ e^ζ + μ ζ) p(e^{-ζ})` for a polynomial `p`. -/
private noncomputable def expEval (κ μ : ℂ) (p : Polynomial ℂ) (ζ : ℂ) : ℂ :=
  cexp (κ * cexp ζ + μ * ζ) * p.eval (cexp (-ζ))

private lemma rankOneFormalSolution_eq_expEval (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) :
    rankOneFormalSolution κ μ a N = expEval κ μ (trunc N (mk a)) := by
  ext ζ
  rw [rankOneFormalSolution, expEval, eval_trunc]
  congr 1
  refine sum_congr rfl fun s _ ↦ ?_
  rw [coeff_mk, ← Complex.exp_natCast_mul, mul_neg]

private lemma hasDerivAt_cexp_mul_cexp_add (κ μ ζ : ℂ) :
    HasDerivAt (fun ζ ↦ cexp (κ * cexp ζ + μ * ζ))
      (cexp (κ * cexp ζ + μ * ζ) * (κ * cexp ζ + μ)) ζ := by
  have h := (((Complex.hasDerivAt_exp ζ).const_mul κ).add ((hasDerivAt_id ζ).const_mul μ)).cexp
  simpa using h

/-- The first derivative of `exp(κ e^ζ + μ ζ) p(e^{-ζ})`. -/
private lemma hasDerivAt_expEval (κ μ : ℂ) (p : Polynomial ℂ) (ζ : ℂ) :
    HasDerivAt (expEval κ μ p) (cexp (κ * cexp ζ + μ * ζ) *
      ((κ * cexp ζ + μ) * p.eval (cexp (-ζ)) - (polyEuler p).eval (cexp (-ζ)))) ζ :=
  ((hasDerivAt_cexp_mul_cexp_add κ μ ζ).mul (hasDerivAt_eval_exp_neg p ζ)).congr_deriv (by ring)

/-- The second derivative of `exp(κ e^ζ + μ ζ) p(e^{-ζ})`. -/
private lemma hasDerivAt_deriv_expEval (κ μ : ℂ) (p : Polynomial ℂ) (ζ : ℂ) :
    HasDerivAt (deriv (expEval κ μ p)) (cexp (κ * cexp ζ + μ * ζ) *
      (((κ * cexp ζ + μ) ^ 2 + κ * cexp ζ) * p.eval (cexp (-ζ)) -
        2 * (κ * cexp ζ + μ) * (polyEuler p).eval (cexp (-ζ)) +
        (polyEuler (polyEuler p)).eval (cexp (-ζ)))) ζ := by
  have hd : deriv (expEval κ μ p) = fun ζ ↦ cexp (κ * cexp ζ + μ * ζ) *
      ((κ * cexp ζ + μ) * p.eval (cexp (-ζ)) - (polyEuler p).eval (cexp (-ζ))) :=
    funext fun ζ ↦ (hasDerivAt_expEval κ μ p ζ).deriv
  rw [hd]
  exact ((hasDerivAt_cexp_mul_cexp_add κ μ ζ).mul
    (((((Complex.hasDerivAt_exp ζ).const_mul κ).add_const μ).mul
      (hasDerivAt_eval_exp_neg p ζ)).sub (hasDerivAt_eval_exp_neg (polyEuler p) ζ))).congr_deriv
    (by simp only [Pi.mul_apply, Pi.sub_apply]; ring)

/-- `(θ - μ) p`, for the Euler operator `θ = X d/dX`. -/
private noncomputable def polyEulerSub (μ : ℂ) (p : Polynomial ℂ) : Polynomial ℂ :=
  polyEuler p - Polynomial.C μ * p

/-- The operator `TauCeti.rankOneOperator` on polynomials `F`, `G`, `p`. -/
private noncomputable def residualPoly (κ μ : ℂ) (F G p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 2 * (polyEuler (polyEuler p) - Polynomial.C μ * polyEuler p -
      Polynomial.C (μ - 1) * polyEulerSub μ p) -
    Polynomial.X * (Polynomial.C (2 * κ) + F) * polyEulerSub μ p +
    (Polynomial.C (κ ^ 2) + Polynomial.C κ * F + G) * p

private lemma coe_residualPoly (κ μ : ℂ) (F G p : Polynomial ℂ) :
    ((residualPoly κ μ F G p : Polynomial ℂ) : ℂ⟦X⟧) =
      rankOneOperator (F : ℂ⟦X⟧) (G : ℂ⟦X⟧) κ μ (p : ℂ⟦X⟧) := by
  simp only [residualPoly, polyEulerSub, rankOneOperator, Polynomial.coe_add, Polynomial.coe_sub,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C, coe_polyEuler,
    map_sub, ← smul_eq_C_mul, Derivation.map_smul]
  simp only [smul_eq_C_mul]
  ring

/-- The residual of `exp(κ e^ζ + μ ζ) p(e^{-ζ})` in the equation
`W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0`, multiplied by `e^{-2ζ}`, is
`exp(κ e^ζ + μ ζ)` times the formal operator evaluated at `w = e^{-ζ}`. -/
private lemma residual_expEval (f g : ℂ → ℂ) (κ μ : ℂ) (p : Polynomial ℂ) (ζ : ℂ) :
    cexp (-ζ) ^ 2 * (deriv (deriv (expEval κ μ p)) ζ +
      (cexp ζ * f (cexp ζ) - 1) * deriv (expEval κ μ p) ζ +
        cexp ζ ^ 2 * g (cexp ζ) * expEval κ μ p ζ) =
      cexp (κ * cexp ζ + μ * ζ) * (cexp (-ζ) ^ 2 *
        (polyEuler (polyEuler p) - Polynomial.C μ * polyEuler p -
          Polynomial.C (μ - 1) * polyEulerSub μ p).eval (cexp (-ζ)) -
        cexp (-ζ) * (2 * κ + f (cexp ζ)) * (polyEulerSub μ p).eval (cexp (-ζ)) +
        (κ ^ 2 + κ * f (cexp ζ) + g (cexp ζ)) * p.eval (cexp (-ζ))) := by
  have hzw : cexp ζ * cexp (-ζ) = 1 := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [(hasDerivAt_deriv_expEval κ μ p ζ).deriv, (hasDerivAt_expEval κ μ p ζ).deriv, expEval]
  simp only [polyEulerSub, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  set z := cexp ζ
  set w := cexp (-ζ)
  set E := cexp (κ * z + μ * ζ)
  set P := p.eval w
  set DP := (polyEuler p).eval w
  linear_combination E * ((κ ^ 2 * (z * w + 1) + 2 * κ * μ * w + κ * f z * (z * w + 1) +
    μ * w * f z + g z * (z * w + 1)) * P + (-2 * κ * w - w * f z) * DP) * hzw

private lemma tendsto_cexp_neg_comap_re_atTop :
    Tendsto (fun ζ ↦ cexp (-ζ)) (comap Complex.re atTop) (𝓝 0) := by
  simpa only [Function.comp_def, Complex.exp_neg] using
    tendsto_inv₀_cobounded.comp Complex.tendsto_exp_comap_re_atTop

private lemma isBigO_eval_cexp_neg_one (q : Polynomial ℂ) :
    (fun ζ ↦ q.eval (cexp (-ζ))) =O[comap Complex.re atTop] fun _ ↦ (1 : ℂ) :=
  ((q.continuous.tendsto 0).comp tendsto_cexp_neg_comap_re_atTop).isBigO_one ℂ

private lemma isBigO_eval_cexp_neg_of_X_pow_dvd {n : ℕ} {q : Polynomial ℂ}
    (hq : Polynomial.X ^ n ∣ q) :
    (fun ζ ↦ q.eval (cexp (-ζ))) =O[comap Complex.re atTop] fun ζ ↦ cexp (-ζ) ^ n := by
  obtain ⟨r, rfl⟩ := hq
  simpa using (isBigO_refl (fun ζ ↦ cexp (-ζ) ^ n) _).mul (isBigO_eval_cexp_neg_one r)

/-- An expansion `f(z) = ∑_{k ≤ N} fₖ z⁻ᵏ + O(z^{-N-1})` as `z → ∞`, read along `z = e^ζ`. -/
private lemma isBigO_comp_cexp_sub_eval_trunc {f : ℂ → ℂ} {F : ℂ⟦X⟧} {N : ℕ}
    (hf : (fun z ↦ f z - ∑ k ∈ range (N + 1), coeff k F * z⁻¹ ^ k) =O[cobounded ℂ]
      fun z ↦ z⁻¹ ^ (N + 1)) :
    (fun ζ ↦ f (cexp ζ) - (trunc (N + 1) F).eval (cexp (-ζ))) =O[comap Complex.re atTop]
      fun ζ ↦ cexp (-ζ) ^ (N + 1) := by
  simpa only [Function.comp_def, eval_trunc, Complex.exp_neg] using
    hf.comp_tendsto Complex.tendsto_exp_comap_re_atTop

private lemma X_pow_dvd_sub_coe_trunc (n : ℕ) (F : ℂ⟦X⟧) : X ^ n ∣ F - (trunc n F : ℂ⟦X⟧) :=
  ⟨_, sub_eq_iff_eq_add.2 (eq_X_pow_mul_shift_add_trunc n F)⟩

/-- Replacing `F` and `G` by series congruent to them modulo `Xⁿ` changes the operator only
modulo `Xⁿ`. -/
private lemma X_pow_dvd_rankOneOperator_sub_rankOneOperator {n : ℕ} {F G F' G' : ℂ⟦X⟧}
    (hF : X ^ n ∣ F - F') (hG : X ^ n ∣ G - G') (κ μ : ℂ) (A : ℂ⟦X⟧) :
    X ^ n ∣ rankOneOperator F G κ μ A - rankOneOperator F' G' κ μ A := by
  have h : rankOneOperator F G κ μ A - rankOneOperator F' G' κ μ A =
      (F - F') * (-(X * (X * d⁄dX A - C μ * A)) + C κ * A) + (G - G') * A := by
    simp only [rankOneOperator]; ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left hF _) (dvd_mul_of_dvd_left hG _)

/-- The residual of `exp(κ e^ζ + μ ζ) p(e^{-ζ})` in
`W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0`, written through the polynomial operator with
`f`, `g` replaced by polynomials `Fp`, `Gp` and the corresponding errors. -/
private lemma residual_expEval_eq (f g : ℂ → ℂ) (κ μ : ℂ) (p Fp Gp : Polynomial ℂ) (ζ : ℂ) :
    deriv (deriv (expEval κ μ p)) ζ + (cexp ζ * f (cexp ζ) - 1) * deriv (expEval κ μ p) ζ +
        cexp (2 * ζ) * g (cexp ζ) * expEval κ μ p ζ =
      cexp (κ * cexp ζ + (μ + 2) * ζ) * ((residualPoly κ μ Fp Gp p).eval (cexp (-ζ)) -
        (Polynomial.X.eval (cexp (-ζ)) * (f (cexp ζ) - Fp.eval (cexp (-ζ)))) *
          (polyEulerSub μ p).eval (cexp (-ζ)) +
        (κ * (f (cexp ζ) - Fp.eval (cexp (-ζ))) + (g (cexp ζ) - Gp.eval (cexp (-ζ)))) *
          p.eval (cexp (-ζ))) := by
  have h := residual_expEval f g κ μ p ζ
  have hzw : cexp ζ * cexp (-ζ) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : cexp (2 * ζ) = cexp ζ ^ 2 := by
    rw [← Complex.exp_natCast_mul]; norm_num
  have hE : cexp (κ * cexp ζ + (μ + 2) * ζ) = cexp (κ * cexp ζ + μ * ζ) * cexp ζ ^ 2 := by
    rw [← h2, ← Complex.exp_add]; ring_nf
  rw [h2, hE]
  simp only [residualPoly, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h ⊢
  -- multiply the identity for `e^{-2ζ}` times the residual by `e^{2ζ}`
  linear_combination (cexp ζ ^ 2) * h - (deriv (deriv (expEval κ μ p)) ζ +
    (cexp ζ * f (cexp ζ) - 1) * deriv (expEval κ μ p) ζ +
    cexp ζ ^ 2 * g (cexp ζ) * expEval κ μ p ζ) * (cexp ζ * cexp (-ζ) + 1) * hzw

/-- The polynomial operator with `F`, `G` truncated below degree `N + 1` agrees with the
operator applied to `p` below degree `N + 1`. -/
private lemma X_pow_dvd_residualPoly_sub_trunc (F G : ℂ⟦X⟧) (κ μ : ℂ) (p : Polynomial ℂ)
    (N : ℕ) : Polynomial.X ^ (N + 1) ∣ residualPoly κ μ (trunc (N + 1) F) (trunc (N + 1) G) p -
      trunc (N + 1) (rankOneOperator F G κ μ p) := by
  refine Polynomial.X_pow_dvd_iff.2 fun d hd ↦ ?_
  have h := X_pow_dvd_iff.1 (X_pow_dvd_rankOneOperator_sub_rankOneOperator
    (X_pow_dvd_sub_coe_trunc (N + 1) F) (X_pow_dvd_sub_coe_trunc (N + 1) G) κ μ p) d hd
  rw [map_sub, ← coe_residualPoly, Polynomial.coeff_coe, sub_eq_zero] at h
  rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left_of_eq_true _ _ (eq_true hd), h, sub_self]

/-- **The residual of a truncated formal solution.** Let `f(z) = ∑_{k ≤ N} fₖ z⁻ᵏ + O(z^{-N-1})`
and `g(z) = ∑_{k ≤ N} gₖ z⁻ᵏ + O(z^{-N-1})` as `z → ∞`, with `fₖ`, `gₖ` the coefficients of `F`
and `G`. In the logarithmic coordinate `z = e^ζ` the equation `w'' + f(z) w' + g(z) w = 0` reads
`W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0`. For arbitrary coefficients `aₛ`, the residual
of the truncation `exp(κ e^ζ + μ ζ) ∑_{s<N} aₛ e^{-sζ}` in this equation is
`exp(κ e^ζ + (μ + 2) ζ) ∑_{m ≤ N} cₘ e^{-mζ}`, where `cₘ` are the coefficients of the formal
operator `TauCeti.rankOneOperator` applied to the truncated series, up to an error
`O(exp(κ e^ζ + (μ + 1 - N) ζ))` as `Re ζ → +∞`, uniformly in `Im ζ`. -/
theorem isBigO_rankOneFormalSolution_residual_sub {f g : ℂ → ℂ} {F G : ℂ⟦X⟧} (κ μ : ℂ)
    (a : ℕ → ℂ) {N : ℕ}
    (hf : (fun z ↦ f z - ∑ k ∈ range (N + 1), coeff k F * z⁻¹ ^ k) =O[cobounded ℂ]
      fun z ↦ z⁻¹ ^ (N + 1))
    (hg : (fun z ↦ g z - ∑ k ∈ range (N + 1), coeff k G * z⁻¹ ^ k) =O[cobounded ℂ]
      fun z ↦ z⁻¹ ^ (N + 1)) :
    (fun ζ ↦ deriv (deriv (rankOneFormalSolution κ μ a N)) ζ +
        (cexp ζ * f (cexp ζ) - 1) * deriv (rankOneFormalSolution κ μ a N) ζ +
        cexp (2 * ζ) * g (cexp ζ) * rankOneFormalSolution κ μ a N ζ -
        cexp (κ * cexp ζ + (μ + 2) * ζ) * ∑ m ∈ range (N + 1),
          coeff m (rankOneOperator F G κ μ (trunc N (mk a))) * cexp (-(m * ζ)))
      =O[comap Complex.re atTop] fun ζ ↦ cexp (κ * cexp ζ + (μ + 1 - N) * ζ) := by
  set p := trunc N (mk a)
  have hR (ζ : ℂ) : (trunc (N + 1) (rankOneOperator F G κ μ (p : ℂ⟦X⟧))).eval (cexp (-ζ)) =
      ∑ m ∈ range (N + 1), coeff m (rankOneOperator F G κ μ p) * cexp (-(m * ζ)) := by
    rw [eval_trunc]
    exact sum_congr rfl fun m _ ↦ by rw [← Complex.exp_natCast_mul, mul_neg]
  have hTR := X_pow_dvd_residualPoly_sub_trunc F G κ μ p N
  -- each term of the remainder is `O(e^{-(N + 1) ζ})`
  have hf' := isBigO_comp_cexp_sub_eval_trunc hf
  have hg' := isBigO_comp_cexp_sub_eval_trunc hg
  have hbound := ((isBigO_eval_cexp_neg_of_X_pow_dvd hTR).sub
    ((((isBigO_eval_cexp_neg_one Polynomial.X).mul hf').mul
      (isBigO_eval_cexp_neg_one (polyEulerSub μ p))).congr_right fun ζ ↦ by ring)).add
    (((hf'.const_mul_left κ).add hg').mul (isBigO_eval_cexp_neg_one p) |>.congr_right
      fun ζ ↦ by ring)
  rw [rankOneFormalSolution_eq_expEval]
  refine (((isBigO_refl (fun ζ ↦ cexp (κ * cexp ζ + (μ + 2) * ζ)) _).mul hbound).congr
    (fun ζ ↦ ?_) fun ζ ↦ ?_)
  · rw [residual_expEval_eq f g κ μ p (trunc (N + 1) F) (trunc (N + 1) G), ← hR,
      Polynomial.eval_sub]
    ring
  rw [← Complex.exp_natCast_mul, ← Complex.exp_add]
  push_cast
  ring_nf

/-- If `κ² + κ f₀ + g₀ ≠ 0`, the first `N + 1` coefficients of the operator can only vanish when
`a₀ = ⋯ = a_N = 0`. -/
private lemma X_pow_dvd_of_coeff_rankOneOperator_eq_zero {F G : ℂ⟦X⟧} {κ μ : ℂ} {A : ℂ⟦X⟧}
    {N : ℕ} (hψ : κ ^ 2 + κ * coeff 0 F + coeff 0 G ≠ 0)
    (hres : ∀ m ≤ N, coeff m (rankOneOperator F G κ μ A) = 0) : X ^ (N + 1) ∣ A := by
  suffices h : ∀ m ≤ N + 1, X ^ m ∣ A from h _ le_rfl
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨R, hR⟩ := ih (by omega)
    have h := X_pow_dvd_iff.1 (X_pow_succ_dvd_rankOneOperator_sub F G κ μ ⟨R, hR⟩) m (by omega)
    have hX : ∀ Q : ℂ⟦X⟧, coeff m (X ^ m * Q) = constantCoeff Q := fun Q ↦ by
      simpa using coeff_X_pow_mul Q m 0
    rw [map_sub, hres m (by omega), zero_sub, neg_eq_zero, hR, mul_left_comm, hX,
      map_mul] at h
    have hR₀ : constantCoeff R = 0 := by
      refine (mul_eq_zero.1 h).resolve_left fun h' ↦ hψ ?_
      simpa [coeff_zero_eq_constantCoeff_apply] using h'
    rw [hR, pow_succ]
    exact mul_dvd_mul_left _ (X_dvd_iff.2 hR₀)

/-- If the first `N + 1` coefficients of the operator applied to `A` vanish, so do those of the
operator applied to the truncation of `A` below degree `N`. -/
private lemma coeff_rankOneOperator_trunc_eq_zero {F G : ℂ⟦X⟧} {κ μ : ℂ} {A : ℂ⟦X⟧} {N : ℕ}
    (hres : ∀ m ≤ N, coeff m (rankOneOperator F G κ μ A) = 0) {m : ℕ} (hm : m ≤ N) :
    coeff m (rankOneOperator F G κ μ (trunc N A)) = 0 := by
  by_cases hψ : κ ^ 2 + κ * coeff 0 F + coeff 0 G = 0
  · -- the operator is additive, and `A - trunc N A` is divisible by `X ^ N`
    have hdiv := X_pow_dvd_sub_coe_trunc N A
    have hsub : rankOneOperator F G κ μ A - rankOneOperator F G κ μ (trunc N A) =
        (rankOneOperator F G κ μ (A - trunc N A) -
          (C (κ ^ 2) + C κ * F + G) * (A - trunc N A)) +
        (C (κ ^ 2) + C κ * F + G) * (A - trunc N A) := by
      simp only [rankOneOperator, map_sub, mul_sub, ← smul_eq_C_mul, Derivation.map_smul]
      simp only [smul_eq_C_mul]; ring
    have hΨ : X ∣ C (κ ^ 2) + C κ * F + G :=
      X_dvd_iff.2 (by simpa [coeff_zero_eq_constantCoeff_apply] using hψ)
    have h := X_pow_dvd_iff.1 (hsub ▸ dvd_add (X_pow_succ_dvd_rankOneOperator_sub F G κ μ hdiv)
      (pow_succ' (X : ℂ⟦X⟧) N ▸ mul_dvd_mul hΨ hdiv)) m (by omega)
    rwa [map_sub, hres m hm, zero_sub, neg_eq_zero] at h
  · -- otherwise the truncation vanishes
    have hA := X_pow_dvd_of_coeff_rankOneOperator_eq_zero hψ hres
    have h : trunc N A = 0 := by
      ext d
      rw [coeff_trunc, Polynomial.coeff_zero]
      split_ifs with hd
      · exact X_pow_dvd_iff.1 hA d (by omega)
      · rfl
    simp [h, rankOneOperator]

/-- **The residual of a truncated formal solution**, sharp form. If the coefficients `aₛ` make the
first `N + 1` coefficients of the formal operator vanish, as those of a formal solution do, and
`f(z) = ∑_{k ≤ N} fₖ z⁻ᵏ + O(z^{-N-1})`, `g(z) = ∑_{k ≤ N} gₖ z⁻ᵏ + O(z^{-N-1})` as `z → ∞`,
then the truncation `exp(κ e^ζ + μ ζ) ∑_{s<N} aₛ e^{-sζ}` solves
`W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0` up to `O(exp(κ e^ζ + (μ + 1 - N) ζ))` as
`Re ζ → +∞`, uniformly in `Im ζ`. In the variable `z = e^ζ` this is a residual
`O(e^{κ z} z^{μ - N - 1})` of the original equation. -/
theorem isBigO_rankOneFormalSolution_residual {f g : ℂ → ℂ} {F G : ℂ⟦X⟧} {κ μ : ℂ}
    {a : ℕ → ℂ} {N : ℕ} (hres : ∀ m ≤ N, coeff m (rankOneOperator F G κ μ (mk a)) = 0)
    (hf : (fun z ↦ f z - ∑ k ∈ range (N + 1), coeff k F * z⁻¹ ^ k) =O[cobounded ℂ]
      fun z ↦ z⁻¹ ^ (N + 1))
    (hg : (fun z ↦ g z - ∑ k ∈ range (N + 1), coeff k G * z⁻¹ ^ k) =O[cobounded ℂ]
      fun z ↦ z⁻¹ ^ (N + 1)) :
    (fun ζ ↦ deriv (deriv (rankOneFormalSolution κ μ a N)) ζ +
        (cexp ζ * f (cexp ζ) - 1) * deriv (rankOneFormalSolution κ μ a N) ζ +
        cexp (2 * ζ) * g (cexp ζ) * rankOneFormalSolution κ μ a N ζ)
      =O[comap Complex.re atTop] fun ζ ↦ cexp (κ * cexp ζ + (μ + 1 - N) * ζ) := by
  have h := isBigO_rankOneFormalSolution_residual_sub κ μ a hf hg
  have hsum : ∀ ζ : ℂ, ∑ m ∈ range (N + 1),
      coeff m (rankOneOperator F G κ μ (trunc N (mk a))) * cexp (-(m * ζ)) = 0 := fun ζ ↦
    sum_eq_zero fun m hm ↦ by
      rw [coeff_rankOneOperator_trunc_eq_zero hres (Nat.lt_succ_iff.1 (mem_range.1 hm)), zero_mul]
  simpa only [hsum, mul_zero, sub_zero] using h

/-- The truncations of the normalized formal solution of DLMF 2.7.8, with the coefficients
`TauCeti.rankOneCoeff` of 2.7.11, solve the equation in logarithmic coordinates
`W'' + (e^ζ f(e^ζ) - 1) W' + e^{2ζ} g(e^ζ) W = 0` up to `O(exp(κ e^ζ + (μ + 1 - N) ζ))` as
`Re ζ → +∞`, whenever `f` and `g` have the expansions `∑ fₖ z⁻ᵏ` and `∑ gₖ z⁻ᵏ` to order `N`,
`κ` is a simple root of `κ² + f₀ κ + g₀ = 0` and `μ (f₀ + 2κ) = -(κ f₁ + g₁)`. -/
theorem isBigO_rankOneFormalSolution_rankOneCoeff_residual {f g : ℂ → ℂ} {F G : ℂ⟦X⟧}
    {κ μ : ℂ} {N : ℕ} (hκ : κ ^ 2 + κ * coeff 0 F + coeff 0 G = 0)
    (hne : coeff 0 F + 2 * κ ≠ 0) (hμ : μ * (coeff 0 F + 2 * κ) + κ * coeff 1 F + coeff 1 G = 0)
    (hf : (fun z ↦ f z - ∑ k ∈ range (N + 1), coeff k F * z⁻¹ ^ k) =O[cobounded ℂ]
      fun z ↦ z⁻¹ ^ (N + 1))
    (hg : (fun z ↦ g z - ∑ k ∈ range (N + 1), coeff k G * z⁻¹ ^ k) =O[cobounded ℂ]
      fun z ↦ z⁻¹ ^ (N + 1)) :
    (fun ζ ↦ deriv (deriv (rankOneFormalSolution κ μ (rankOneCoeff F G κ μ) N)) ζ +
        (cexp ζ * f (cexp ζ) - 1) * deriv (rankOneFormalSolution κ μ (rankOneCoeff F G κ μ) N) ζ +
        cexp (2 * ζ) * g (cexp ζ) * rankOneFormalSolution κ μ (rankOneCoeff F G κ μ) N ζ)
      =O[comap Complex.re atTop] fun ζ ↦ cexp (κ * cexp ζ + (μ + 1 - N) * ζ) :=
  isBigO_rankOneFormalSolution_residual
    (fun m _ ↦ by rw [rankOneOperator_mk_rankOneCoeff hκ hne hμ, map_zero]) hf hg

/-- The truncated formal solution is entire. -/
theorem differentiable_rankOneFormalSolution (κ μ : ℂ) (a : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (rankOneFormalSolution κ μ a N) := by
  rw [rankOneFormalSolution_eq_expEval]
  exact fun ζ ↦ (hasDerivAt_expEval κ μ _ ζ).differentiableAt


end Analytic

/-! ### A check -/

-- For `f(z) = -1 + 2z⁻²` and `g(z) = -z⁻² - 2z⁻³ + z⁻⁴` the characteristic roots are `0` and `1`,
-- both with `μ = 0`, and the solutions are `exp(1/z)` and `exp(z + 1/z)`; both normalized formal
-- series are the convergent nonterminating series `∑ z⁻ˢ/s!`.
example {κ : ℂ} (hκ : κ = 0 ∨ κ = 1) :
    rankOneCoeff (-1 + 2 * X ^ 2) (-X ^ 2 - 2 * X ^ 3 + X ^ 4) κ 0 =
      fun s ↦ ((s.factorial : ℂ))⁻¹ := by
  have hexp : (mk fun s ↦ ((s.factorial : ℂ))⁻¹) = PowerSeries.exp ℂ := by
    ext n
    simp [coeff_exp]
  have hE : d⁄dX (mk fun s ↦ ((s.factorial : ℂ))⁻¹) = mk fun s ↦ ((s.factorial : ℂ))⁻¹ := by
    rw [hexp, derivative_exp]
  have hne : coeff 0 (-1 + 2 * X ^ 2 : ℂ⟦X⟧) + 2 * κ ≠ 0 := by
    rcases hκ with rfl | rfl <;> norm_num [coeff_X_pow]
  refine (eq_rankOneCoeff_of_rankOneOperator_eq_zero ?_ (by simp) hne).symm
  simp only [rankOneOperator, map_sub, map_mul, Derivation.leibniz, derivative_X,
    smul_eq_mul, hE]
  rcases hκ with rfl | rfl <;> simp [map_ofNat] <;> ring

end TauCeti
