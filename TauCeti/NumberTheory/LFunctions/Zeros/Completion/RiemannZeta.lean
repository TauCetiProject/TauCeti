/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.Zeros.Divisor

import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The entire completion of the Riemann zeta function

The explicit function `zetaEntireCompletion` is twice Riemann's ξ-function. It agrees with
`s * (s - 1) * completedRiemannZeta s` away from the two poles, but takes the value `1` at
both `0` and `1`. In particular, clearing the poles introduces no artificial zeros, every zero of
`zetaEntireCompletion` lies in the open critical strip `0 < Re s < 1`, on the positive half-plane
its zero counts agree with those of `riemannZeta` (even across `1`), and away from `1` their
divisors agree.

The identity with `riemannZetaData.entireCompletion` connects this formula and its reflection
symmetry to the general pole-clearing construction.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §12.
-/

public section

open Complex Filter Polynomial Topology

namespace TauCeti.LFunctions

/-- Twice Riemann's ξ-function, with its removable values at `0` and `1` filled in. -/
noncomputable def zetaEntireCompletion (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

theorem zetaEntireCompletion_def (s : ℂ) :
    zetaEntireCompletion s = s * (s - 1) * completedRiemannZeta₀ s + 1 := (rfl)

/-- The explicit entire completion is entire. -/
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

/-- The entire completion has a zero of positive multiplicity exactly where
`completedRiemannZeta` has one: clearing the poles at `0` and `1` creates no zeros. -/
theorem zero_lt_divisor_zetaEntireCompletion_iff {s : ℂ} :
    0 < MeromorphicOn.divisor zetaEntireCompletion Set.univ s ↔
      0 < MeromorphicOn.divisor completedRiemannZeta Set.univ s := by
  have h := riemannZetaData_hasMeromorphicContinuation.toNat_divisor_entireCompletion s
  rw [riemannZetaData_entireCompletion, riemannZetaData_completed] at h
  omega

/-- Reflection `s ↦ 1 - s` preserves the divisor of `zetaEntireCompletion`. -/
theorem divisor_zetaEntireCompletion_one_sub (s : ℂ) :
    MeromorphicOn.divisor zetaEntireCompletion Set.univ (1 - s) =
      MeromorphicOn.divisor zetaEntireCompletion Set.univ s := by
  simpa only [riemannZetaData_entireCompletion, riemannZetaData_dual] using
    riemannZetaData_hasFunctionalEquation.divisor_entireCompletion_one_sub
      riemannZetaData_hasMeromorphicContinuation s

/-- Every point of positive divisor of `zetaEntireCompletion` lies in the open critical strip. -/
theorem re_mem_Ioo_of_divisor_zetaEntireCompletion_pos {ρ : ℂ}
    (hρ : 0 < MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ) :
    ρ.re ∈ Set.Ioo 0 1 := by
  refine ⟨by_contra fun hle ↦ ?_, by_contra fun hge ↦ ?_⟩
  · have h1 : 1 ≤ (1 - ρ).re := by simp only [sub_re, one_re]; linarith [not_lt.mp hle]
    rw [← divisor_zetaEntireCompletion_one_sub, zero_lt_divisor_zetaEntireCompletion_iff,
      zero_lt_divisor_completedRiemannZeta_iff] at hρ
    exact riemannZeta_ne_zero_of_one_le_re h1 hρ.1
  · rw [zero_lt_divisor_zetaEntireCompletion_iff,
      zero_lt_divisor_completedRiemannZeta_iff] at hρ
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hρ.1

/-- On the positive half-plane, `zetaEntireCompletion` and `riemannZeta` have the same analytic
order (at the pole `1`, `zetaEntireCompletion 1 = 1 ≠ 0` and `riemannZeta` is not analytic, so both
analytic orders vanish). -/
theorem analyticOrderAt_zetaEntireCompletion_eq_riemannZeta {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt zetaEntireCompletion s = analyticOrderAt riemannZeta s := by
  rcases eq_or_ne s 1 with rfl | hs1
  · have hnot : ¬ AnalyticAt ℂ riemannZeta 1 := fun ha ↦ by
      have hm : ((0 : ℤ) : WithTop ℤ) ≤ (-1 : ℤ) :=
        meromorphicOrderAt_riemannZeta_one ▸ ha.meromorphicOrderAt_nonneg
      exact absurd (WithTop.coe_le_coe.mp hm) (by omega)
    rw [(differentiable_zetaEntireCompletion.analyticAt 1).analyticOrderAt_eq_zero.mpr (by simp),
      analyticOrderAt_of_not_analyticAt hnot]
  · have hs0 : s ≠ 0 := by rintro rfl; simp at hs
    have hΓ : AnalyticAt ℂ Gammaℝ s := by
      simpa only [Pi.inv_def, inv_inv] using
        (differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
    let c : ℂ → ℂ := fun z ↦ z * (z - 1) * Gammaℝ z
    have hc : AnalyticAt ℂ c s :=
      (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hΓ
    have hc0 : c s ≠ 0 :=
      mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (Gammaℝ_ne_zero_of_re_pos hs)
    have he : zetaEntireCompletion =ᶠ[𝓝 s] c * riemannZeta := by
      have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
        (isOpen_lt continuous_const continuous_re).inter isOpen_ne
      filter_upwards [hopen.mem_nhds ⟨hs, hs1⟩] with z ⟨hz, hz1⟩
      have hz0 : z ≠ 0 := by rintro rfl; simp at hz
      dsimp only [Pi.mul_apply, c]
      rw [zetaEntireCompletion_eq_mul hz0 hz1, riemannZeta_def_of_ne_zero hz0,
        mul_assoc (z * (z - 1)) (Gammaℝ z)]
      congr 1
      exact (mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hz)).symm
    rw [analyticOrderAt_congr he, analyticOrderAt_mul hc (analyticOn_riemannZeta s hs1),
      hc.analyticOrderAt_eq_zero.mpr hc0, zero_add]

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
        divisor_riemannZeta_one]
      rfl
    · rw [divisor_zetaEntireCompletion_eq_riemannZeta (hR s hs) hs1]

/-- On any region `R`, the zero count of `zetaEntireCompletion` is the zero count of `riemannZeta`
on the intersection of `R` with the open critical strip. -/
theorem zeroCount_zetaEntireCompletion_eq_riemannZeta_inter (R : Set ℂ) :
    zeroCount zetaEntireCompletion Set.univ R =
      zeroCount riemannZeta Set.univ (R ∩ {s | s.re ∈ Set.Ioo 0 1}) := by
  rw [← zeroCount_inter_eq_self (S := {s | s.re ∈ Set.Ioo 0 1})
    fun _ _ hρ ↦ re_mem_Ioo_of_divisor_zetaEntireCompletion_pos hρ]
  exact zeroCount_zetaEntireCompletion_eq_riemannZeta fun _ hs ↦ hs.2.1

end TauCeti.LFunctions
