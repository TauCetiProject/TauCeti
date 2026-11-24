/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic

import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
import TauCeti.NumberTheory.LFunctions.Zeros.Divisor
import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic

/-!
# The entire completion of the Riemann zeta function

The explicit function `zetaEntireCompletion` is twice Riemann's ξ-function. It agrees with
`s * (s - 1) * completedRiemannZeta s` away from the two poles, takes the value `1` at both `0` and
`1` (so clearing the poles introduces no artificial zeros), and satisfies the reflection and
conjugation symmetries `zetaEntireCompletion (1 - s) = zetaEntireCompletion s` and
`zetaEntireCompletion (conj s) = conj (zetaEntireCompletion s)` (hence is real on the real axis),
along with the matching logarithmic-derivative symmetries `logDeriv_zetaEntireCompletion_conj`,
`logDeriv_zetaEntireCompletion_one_sub`, and `im_logDeriv_zetaEntireCompletion_ofReal`.
On the positive half-plane its zero counts agree with those of `riemannZeta` (even across `1`),
and away from `1` their divisors agree.

The identity `riemannZetaData_entireCompletion` connects this explicit formula to the general
pole-clearing construction `riemannZetaData.entireCompletion`. Combining nonvanishing of
`riemannZeta` on `1 ≤ Re s` (`riemannZeta_ne_zero_of_one_le_re`) with the functional equation
confines all zeros of `zetaEntireCompletion` to the open critical strip `0 < Re ρ < 1`
(`re_mem_Ioo_of_zetaEntireCompletion_eq_zero`).

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §11 and §12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2 and §11.1.
-/

public section

open Complex ComplexConjugate Filter Polynomial
open scoped Topology

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

/-- Conjugation commutes with `zetaEntireCompletion`. -/
@[simp]
theorem zetaEntireCompletion_conj (s : ℂ) :
    zetaEntireCompletion (conj s) = conj (zetaEntireCompletion s) := by
  simpa using riemannZetaData_hasMeromorphicContinuation.dual_entireCompletion (conj s)

/-- `zetaEntireCompletion` is real on the real axis. -/
@[simp]
theorem im_zetaEntireCompletion_ofReal (σ : ℝ) :
    (zetaEntireCompletion σ).im = 0 := by
  refine conj_eq_iff_im.mp ?_
  simpa using (zetaEntireCompletion_conj σ).symm

/-- Conjugation commutes with `logDeriv zetaEntireCompletion`. -/
@[simp]
theorem logDeriv_zetaEntireCompletion_conj (s : ℂ) :
    logDeriv zetaEntireCompletion (conj s) = conj (logDeriv zetaEntireCompletion s) := by
  simpa using riemannZetaData_hasMeromorphicContinuation.logDeriv_dual_entireCompletion_conj s

/-- `logDeriv zetaEntireCompletion` is odd across the critical line `s ↦ 1 - s`. -/
theorem logDeriv_zetaEntireCompletion_one_sub (s : ℂ) :
    logDeriv zetaEntireCompletion (1 - s) = -logDeriv zetaEntireCompletion s := by
  simpa using riemannZetaData_hasFunctionalEquation.logDeriv_entireCompletion_one_sub
    riemannZetaData_hasMeromorphicContinuation s

/-- `logDeriv zetaEntireCompletion` is real on the real axis. -/
@[simp]
theorem im_logDeriv_zetaEntireCompletion_ofReal (σ : ℝ) :
    (logDeriv zetaEntireCompletion σ).im = 0 := by
  refine conj_eq_iff_im.mp ?_
  simpa using (logDeriv_zetaEntireCompletion_conj σ).symm

/-- The entire completion has a zero of positive multiplicity exactly where
`completedRiemannZeta` has one: clearing the poles at `0` and `1` creates no zeros. -/
theorem zero_lt_divisor_zetaEntireCompletion_iff {s : ℂ} :
    0 < MeromorphicOn.divisor zetaEntireCompletion Set.univ s ↔
      0 < MeromorphicOn.divisor completedRiemannZeta Set.univ s := by
  have h := riemannZetaData_hasMeromorphicContinuation.toNat_divisor_entireCompletion s
  rw [riemannZetaData_entireCompletion, riemannZetaData_completed] at h
  omega

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
  simpa only [riemannZetaData_entireCompletion] using
    riemannZetaData_hasFunctionalEquation.entireCompletion_ne_zero_of_re_nonpos
      riemannZetaData_hasMeromorphicContinuation
      (by simpa only [riemannZetaData_entireCompletion] using
        fun _ ↦ zetaEntireCompletion_ne_zero_of_one_le_re) hs

/-- Every zero of `zetaEntireCompletion` lies in the open critical strip `0 < Re ρ < 1`. -/
theorem re_mem_Ioo_of_zetaEntireCompletion_eq_zero {ρ : ℂ}
    (hρ : zetaEntireCompletion ρ = 0) : ρ.re ∈ Set.Ioo 0 1 :=
  riemannZetaData_hasFunctionalEquation.re_mem_Ioo_of_entireCompletion_eq_zero
    riemannZetaData_hasMeromorphicContinuation
    (by simpa only [riemannZetaData_entireCompletion] using
      fun _ ↦ zetaEntireCompletion_ne_zero_of_one_le_re)
    (by simpa only [riemannZetaData_entireCompletion] using hρ)

/-- On the positive half-plane, `zetaEntireCompletion` and `riemannZeta` have the same analytic
order (at the pole `1`, `zetaEntireCompletion 1 = 1 ≠ 0` and `riemannZeta` is not analytic, so both
analytic orders vanish). -/
theorem analyticOrderAt_zetaEntireCompletion_eq_riemannZeta {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt zetaEntireCompletion s = analyticOrderAt riemannZeta s := by
  rcases eq_or_ne s 1 with rfl | hs1
  · have hnot : ¬ AnalyticAt ℂ riemannZeta 1 := fun ha ↦ by
      have hm : (0 : WithTop ℤ) ≤ -1 :=
        meromorphicOrderAt_riemannZeta_one ▸ ha.meromorphicOrderAt_nonneg
      exact absurd hm (by decide)
    rw [(differentiable_zetaEntireCompletion.analyticAt 1).analyticOrderAt_eq_zero.mpr (by simp),
      analyticOrderAt_of_not_analyticAt hnot]
  · have hs0 : s ≠ 0 := by rintro rfl; simp at hs
    have hc : AnalyticAt ℂ (fun z : ℂ ↦ z * (z - 1)) s :=
      analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
    have hc0 : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
    have he : zetaEntireCompletion =ᶠ[𝓝 s] (fun z : ℂ ↦ z * (z - 1)) * completedRiemannZeta := by
      filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
      exact zetaEntireCompletion_eq_mul hz0 hz1
    rw [analyticOrderAt_congr he, analyticOrderAt_mul hc (analyticAt_completedRiemannZeta hs0 hs1),
      hc.analyticOrderAt_eq_zero.mpr hc0, zero_add,
      ← DirichletCharacter.completedLFunction_modOne_eq (χ := (1 : DirichletCharacter ℂ 1)),
      (1 : DirichletCharacter ℂ 1).analyticOrderAt_completedLFunction hs (.inl hs1),
      DirichletCharacter.LFunction_modOne_eq]

/-- On the positive half-plane away from `1`, `zetaEntireCompletion` and `riemannZeta` have the
same divisor. -/
theorem divisor_zetaEntireCompletion_eq_riemannZeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    MeromorphicOn.divisor zetaEntireCompletion Set.univ s =
      MeromorphicOn.divisor riemannZeta Set.univ s := by
  have hξ : AnalyticOnNhd ℂ zetaEntireCompletion Set.univ :=
    fun z _ ↦ differentiable_zetaEntireCompletion.analyticAt z
  rw [hξ.meromorphicOn.divisor_eq_analyticOrderNatAt (hξ s (Set.mem_univ s)) (Set.mem_univ s),
    meromorphic_riemannZeta.meromorphicOn.divisor_eq_analyticOrderNatAt
      (analyticOn_riemannZeta s hs1) (Set.mem_univ s)]
  simp only [analyticOrderNatAt, analyticOrderAt_zetaEntireCompletion_eq_riemannZeta hs]

/-- On any region in the positive half-plane, `zetaEntireCompletion` and `riemannZeta` have the
same zero count (at the pole `1`, both positive divisor multiplicities vanish). -/
theorem zeroCount_zetaEntireCompletion_eq_riemannZeta {R : Set ℂ}
    (hR : ∀ s ∈ R, 0 < s.re) :
    zeroCount zetaEntireCompletion Set.univ R = zeroCount riemannZeta Set.univ R :=
  zeroCount_congr_divisor fun s hs ↦ by
    rcases eq_or_ne s 1 with rfl | hs1
    · rw [(differentiable_zetaEntireCompletion.analyticAt 1).divisor_apply_eq_zero (by simp),
        (meromorphicOn_univ.2 meromorphic_riemannZeta).divisor_apply (Set.mem_univ 1),
        meromorphicOrderAt_riemannZeta_one]
      rfl
    · rw [divisor_zetaEntireCompletion_eq_riemannZeta (hR s hs) hs1]

end TauCeti.LFunctions
