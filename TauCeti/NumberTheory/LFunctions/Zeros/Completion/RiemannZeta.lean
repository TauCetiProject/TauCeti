/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.Hadamard
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.FiniteOrder
public import TauCeti.NumberTheory.LFunctions.Zeros.Divisor

import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.Complex.Conformal.Reflection.LogDeriv
import TauCeti.Analysis.Complex.GrowthOrder.Logarithmic
import TauCeti.NumberTheory.LSeries.HurwitzZetaGrowth

/-!
# The entire completion of the Riemann zeta function

The explicit function `zetaEntireCompletion` is twice Riemann's ξ-function. It agrees with
`s * (s - 1) * completedRiemannZeta s` away from the two poles, but takes the value `1` at
both `0` and `1`. In particular, clearing the poles introduces no artificial zeros.

The identity with `riemannZetaData.entireCompletion` connects this formula and its reflection
symmetry to the general pole-clearing construction. Combining the Mellin growth bound for
`completedRiemannZeta₀`, nonvanishing on `1 ≤ Re s`, and the functional and conjugation symmetries
yields `OrderLE zetaEntireCompletion 1`, confinement of all zeros to `0 < Re ρ < 1`, Hadamard's
product `zetaEntireCompletion_hadamard`, and the cancelled real-part expansion of
`logDeriv zetaEntireCompletion`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §11 and §12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2 and §11.1.
-/

public section

open Complex ComplexConjugate Polynomial
open scoped BigOperators

namespace TauCeti.LFunctions

/-- Twice Riemann's ξ-function, with its removable values at `0` and `1` filled in. -/
noncomputable def zetaEntireCompletion (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

theorem zetaEntireCompletion_def (s : ℂ) :
    zetaEntireCompletion s = s * (s - 1) * completedRiemannZeta₀ s + 1 := (rfl)

/-- The explicit entire completion is entire. -/
@[fun_prop]
theorem differentiable_zetaEntireCompletion : Differentiable ℂ zetaEntireCompletion := by
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

@[simp]
theorem zetaEntireCompletion_zero : zetaEntireCompletion 0 = 1 := by
  simp [zetaEntireCompletion_def]

@[simp]
theorem zetaEntireCompletion_one : zetaEntireCompletion 1 = 1 := by
  simp [zetaEntireCompletion_def]

theorem zetaEntireCompletion_zero_ne_zero : zetaEntireCompletion 0 ≠ 0 := by
  simp

/-- The entire completion retains the reflection symmetry about the critical line. -/
theorem zetaEntireCompletion_one_sub (s : ℂ) :
    zetaEntireCompletion (1 - s) = zetaEntireCompletion s := by
  simp only [zetaEntireCompletion_def, completedRiemannZeta₀_one_sub]
  ring

/-- Away from the poles the explicit completion is the usual pole-cleared product. -/
theorem zetaEntireCompletion_eq_mul {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    zetaEntireCompletion s = s * (s - 1) * completedRiemannZeta s := by
  rw [zetaEntireCompletion_def, completedRiemannZeta_eq]
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- Conjugation commutes with `zetaEntireCompletion`. -/
theorem zetaEntireCompletion_conj (s : ℂ) :
    zetaEntireCompletion (conj s) = conj (zetaEntireCompletion s) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  rcases eq_or_ne s 1 with rfl | hs1
  · simp
  have hcs0 : conj s ≠ 0 := star_ne_zero.mpr hs0
  have hcs1 : conj s ≠ 1 := fun h ↦ hs1 ((starRingEnd ℂ).injective (by simpa using h))
  rw [zetaEntireCompletion_eq_mul hcs0 hcs1, zetaEntireCompletion_eq_mul hs0 hs1,
    completedRiemannZeta_conj]
  simp

/-- The Riemann zeta record clears precisely the simple poles at `0` and `1`. -/
@[simp]
theorem riemannZetaData_polarPolynomial :
    riemannZetaData.polarPolynomial = X * (X - 1) := by
  simp [AnalyticLFunctionData.polarPolynomial_def, Finsupp.prod_add_index', pow_add]

/-- The general removable extension recovers the explicit entire completion of zeta. -/
@[simp]
theorem riemannZetaData_entireCompletion :
    riemannZetaData.entireCompletion = zetaEntireCompletion := by
  symm
  apply riemannZetaData_hasMeromorphicContinuation.entireCompletion_unique
    differentiable_zetaEntireCompletion.continuous
  intro s hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  simpa using zetaEntireCompletion_eq_mul hs0 hs1

/-- The entire completion has a zero of positive multiplicity exactly where
`completedRiemannZeta` has one: clearing the poles at `0` and `1` creates no zeros. -/
theorem zero_lt_divisor_zetaEntireCompletion_iff {s : ℂ} :
    0 < MeromorphicOn.divisor zetaEntireCompletion Set.univ s ↔
      0 < MeromorphicOn.divisor completedRiemannZeta Set.univ s := by
  have h := riemannZetaData_hasMeromorphicContinuation.toNat_divisor_entireCompletion s
  rw [riemannZetaData_entireCompletion, riemannZetaData_completed] at h
  omega

/-! ### Growth order -/

/-- Mathlib's entire part `completedRiemannZeta₀` has growth order at most `1`. -/
theorem orderLE_completedRiemannZeta₀ : OrderLE completedRiemannZeta₀ 1 := by
  obtain ⟨C, -, hC⟩ := HurwitzZeta.exists_norm_completedHurwitzZetaEven₀_le_exp_mul_log 0
  exact orderLE_one_of_norm_le_exp_mul_log hC

/-- **Order at most one.** Twice Riemann's ξ-function `zetaEntireCompletion` is entire of order at
most `1`. -/
theorem orderLE_zetaEntireCompletion : OrderLE zetaEntireCompletion 1 := by
  have hpoly : OrderLE (fun s : ℂ ↦ s * (s - 1)) 1 := by
    have hp := ((X : Polynomial ℂ) * (X - 1)).orderLE_eval.mono zero_le_one
    simpa only [eval_mul, eval_sub, eval_X, eval_one] using hp
  exact ((hpoly.mul orderLE_completedRiemannZeta₀).add (orderLE_const 1 1))

/-- The Riemann zeta record has finite order. -/
theorem riemannZetaData_isFiniteOrder : riemannZetaData.IsFiniteOrder := by
  rw [AnalyticLFunctionData.IsFiniteOrder, riemannZetaData_entireCompletion]
  exact orderLE_zetaEntireCompletion.isFiniteOrder

/-! ### Location of the zeros -/

/-- `zetaEntireCompletion` has no zeros on `1 ≤ Re s`. -/
theorem zetaEntireCompletion_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    zetaEntireCompletion s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · simp
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  rw [zetaEntireCompletion_eq_mul hs0 hs1]
  refine mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) fun hΛ ↦ ?_
  apply riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]

/-- `zetaEntireCompletion` has no zeros on `Re s ≤ 0`. -/
theorem zetaEntireCompletion_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    zetaEntireCompletion s ≠ 0 := by
  rw [← sub_sub_cancel 1 s, zetaEntireCompletion_one_sub]
  exact zetaEntireCompletion_ne_zero_of_one_le_re (by simp only [sub_re, one_re]; linarith)

/-- Every zero of `zetaEntireCompletion` lies in the open critical strip `0 < Re ρ < 1`. -/
theorem re_mem_Ioo_of_zetaEntireCompletion_eq_zero {ρ : ℂ}
    (hρ : zetaEntireCompletion ρ = 0) : ρ.re ∈ Set.Ioo 0 1 := by
  by_contra h
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at h
  rcases h with h | h
  · exact zetaEntireCompletion_ne_zero_of_re_nonpos h hρ
  · exact zetaEntireCompletion_ne_zero_of_one_le_re h hρ

private theorem re_mem_Icc_of_zetaEntireCompletion_eq_zero (ρ : ℂ)
    (hρ : zetaEntireCompletion ρ = 0) : ρ.re ∈ Set.Icc 0 1 :=
  Set.Ioo_subset_Icc_self (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ)

private theorem zetaEntireCompletion_one_sub_eq_conj_conj (z : ℂ) :
    zetaEntireCompletion (1 - z) = 1 * conj (zetaEntireCompletion (conj z)) := by
  rw [one_mul, zetaEntireCompletion_one_sub, zetaEntireCompletion_conj, conj_conj]

/-! ### Hadamard factorization and logarithmic derivative -/

/-- **Hadamard factorization of `zetaEntireCompletion`.** Since `zetaEntireCompletion 0 = 1`,
`zetaEntireCompletion s = exp (logDeriv zetaEntireCompletion 0 * s) * divisorProductOne …`. -/
theorem zetaEntireCompletion_eq_cexp_logDeriv_mul_divisorProductOne (s : ℂ) :
    zetaEntireCompletion s =
      exp (logDeriv zetaEntireCompletion 0 * s) * divisorProductOne zetaEntireCompletion s := by
  have h := orderLE_zetaEntireCompletion.eq_mul_cexp_logDeriv_mul_divisorProductOne
    differentiable_zetaEntireCompletion zetaEntireCompletion_zero_ne_zero s
  simpa using h

/-- **Hadamard product for `zetaEntireCompletion`.** Twice Riemann's ξ-function factors globally as
`exp (a + b * s)` times the multipliable genus-one canonical product over its zeros. -/
theorem zetaEntireCompletion_hadamard :
    ∃ a b : ℂ, ∀ s : ℂ,
      Multipliable (fun ρ : ℂ ↦
        weierstrassFactorOne (s / ρ) ^
          (MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat) ∧
      zetaEntireCompletion s = exp (a + b * s) * ∏' ρ : ℂ,
        weierstrassFactorOne (s / ρ) ^
          (MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat :=
  hadamard_of_orderLE_one differentiable_zetaEntireCompletion orderLE_zetaEntireCompletion
    zetaEntireCompletion_zero_ne_zero

/-- Paired partial-fraction expansion of `logDeriv zetaEntireCompletion` off the zeros. -/
theorem logDeriv_zetaEntireCompletion_eq_add_tsum {s : ℂ} (hs : zetaEntireCompletion s ≠ 0) :
    logDeriv zetaEntireCompletion s = logDeriv zetaEntireCompletion 0 +
      ∑' ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support,
        ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℂ) *
          (1 / (s - ρ) + 1 / ρ) :=
  orderLE_zetaEntireCompletion.logDeriv_eq_add_tsum differentiable_zetaEntireCompletion
    zetaEntireCompletion_zero_ne_zero hs

/-- The real part of the Hadamard linear constant `logDeriv zetaEntireCompletion 0` equals
`-∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem re_logDeriv_zetaEntireCompletion_zero :
    (logDeriv zetaEntireCompletion 0).re =
      -∑' ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support,
        ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re :=
  orderLE_zetaEntireCompletion.re_logDeriv_zero_eq_neg_tsum differentiable_zetaEntireCompletion
    zetaEntireCompletion_zero_ne_zero re_mem_Icc_of_zetaEntireCompletion_eq_zero
    zetaEntireCompletion_one_sub_eq_conj_conj

/-- `logDeriv zetaEntireCompletion` is real on the real axis. -/
theorem im_logDeriv_zetaEntireCompletion_ofReal (σ : ℝ) :
    (logDeriv zetaEntireCompletion σ).im = 0 := by
  have hconj := logDeriv_conj_eq_conj_logDeriv_of_ne_zero (F := zetaEntireCompletion)
    one_ne_zero isOpen_univ (fun z _ ↦ by rw [one_mul, zetaEntireCompletion_conj])
    (Set.mem_univ (σ : ℂ))
  rw [conj_ofReal] at hconj
  exact conj_eq_iff_im.mp hconj.symm

/-- Cancelled real-part partial-fraction expansion of `logDeriv zetaEntireCompletion` off the
zeros: `Re (logDeriv zetaEntireCompletion s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))`. -/
theorem re_logDeriv_zetaEntireCompletion_eq_tsum {s : ℂ} (hs : zetaEntireCompletion s ≠ 0) :
    (logDeriv zetaEntireCompletion s).re =
      ∑' ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support,
        ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re :=
  orderLE_zetaEntireCompletion.re_logDeriv_eq_tsum differentiable_zetaEntireCompletion
    zetaEntireCompletion_zero_ne_zero re_mem_Icc_of_zetaEntireCompletion_eq_zero
    zetaEntireCompletion_one_sub_eq_conj_conj hs

/-- On `1 ≤ Re s`, `Re (logDeriv zetaEntireCompletion s)` is nonnegative. -/
theorem re_logDeriv_zetaEntireCompletion_nonneg {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ (logDeriv zetaEntireCompletion s).re := by
  rw [re_logDeriv_zetaEntireCompletion_eq_tsum (zetaEntireCompletion_ne_zero_of_one_le_re hs)]
  exact OrderLE.tsum_divisor_toNat_mul_re_one_div_sub_nonneg
    re_mem_Icc_of_zetaEntireCompletion_eq_zero differentiable_zetaEntireCompletion hs

end TauCeti.LFunctions
