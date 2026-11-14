/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Analysis.Calculus.LocalPotentials.PathIntegral

import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.MeasureTheory.Integral.CurveIntegral.Basic
import TauCeti.Order.Interval.Finite

/-!
# Comparison of local-potential curve integrals with Bochner curve integrals

When the target space `F` is complete and `γ : Path a b` has sufficient regularity for Mathlib's
Bochner curve integral `∫ᶜ x in γ, φ x` (`MeasureTheory.curveIntegral`) to apply, the subdivision
curve integral `TauCeti.localPotentialCurveIntegral φ γ` agrees with `∫ᶜ x in γ, φ x` by the
fundamental theorem of calculus along each adapted ball of a subdivision.

## Main results

* `TauCeti.HasLocalPotentialCurveIntegral.eq_curveIntegral_of_differentiableAt_off_countable`,
  `TauCeti.localPotentialCurveIntegral_eq_curveIntegral_of_differentiableAt_off_countable`:
  agreement with `curveIntegral` when `γ.extend` is differentiable off a countable set in `(0, 1)`
  and `CurveIntegrable φ γ` holds.
* `TauCeti.HasLocalPotentialCurveIntegral.eq_curveIntegral_of_differentiableOn`,
  `TauCeti.localPotentialCurveIntegral_eq_curveIntegral_of_differentiableOn`: specialization to
  paths differentiable throughout `(0, 1)`.
* `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_eq_curveIntegral`,
  `TauCeti.HasLocalPotentials.localPotentialCurveIntegral_eq_curveIntegral_of_contDiffOn`:
  agreement along piecewise `C¹` and `C¹` paths inside a domain where `φ` has local potentials.

## References

* Henri Cartan, *Elementary Theory of Analytic Functions of One or Several Complex Variables*,
  Chapter II, §1 (equivalence of potential-chain integrals and piecewise differentiable curve
  integrals).
* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, §§1.3, 4.3 (line integrals of locally
  exact differentials along piecewise smooth arcs).
-/

public section

open MeasureTheory Metric Set
open scoped ContDiff unitInterval

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {a b : E} {s : Set E} {φ : E → E →L[ℝ] F}

/-- If `γ.extend` is differentiable off a countable set `p` in `(0, 1)` and `φ` is
`CurveIntegrable` along `γ`, then any `HasLocalPotentialCurveIntegral` value equals Mathlib's
`curveIntegral φ γ`. -/
theorem HasLocalPotentialCurveIntegral.eq_curveIntegral_of_differentiableAt_off_countable
    {γ : Path a b} {v : F} {p : Set ℝ}
    (hφγ : HasLocalPotentialCurveIntegral φ γ v) (hp : p.Countable)
    (hdiff : ∀ τ ∈ Ioo (0 : ℝ) 1 \ p, DifferentiableAt ℝ γ.extend τ)
    (hint : CurveIntegrable φ γ) :
    v = ∫ᶜ x in γ, φ x := by
  rcases hasLocalPotentialCurveIntegral_iff.mp hφγ with
    ⟨n, t, z, r, g, ht0, htn, hle, hγ, hd, rfl⟩
  have hint_deriv := (curveIntegrable_iff_intervalIntegrable_deriv φ γ).mp hint
  have hint_sub : ∀ i < n,
      IntervalIntegrable (fun τ ↦ φ (γ.extend τ) (deriv γ.extend τ))
        volume (t i : ℝ) (t (i + 1) : ℝ) := by
    intro i hi
    refine hint_deriv.mono_set ?_
    rw [Set.uIcc_of_le (Subtype.coe_le_coe.mpr (hle i hi)), Set.uIcc_of_le zero_le_one]
    exact fun τ hτ ↦ ⟨(t i).2.1.trans hτ.1, hτ.2.trans (t (i + 1)).2.2⟩
  rw [curveIntegral_eq_intervalIntegral_deriv]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i ↦ (t i : ℝ)) hint_sub
  have ht0' : ((t 0 : I) : ℝ) = 0 := by simp [ht0]
  have htn' : ((t n : I) : ℝ) = 1 := by simp [htn]
  rw [ht0', htn'] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hin : i < n := Finset.mem_range.mp hi
  have hmem_ball : ∀ τ ∈ Icc (t i : ℝ) (t (i + 1) : ℝ), γ.extend τ ∈ ball (z i) (r i) := by
    intro τ hτ
    have hτI : τ ∈ I := ⟨(t i).2.1.trans hτ.1, hτ.2.trans (t (i + 1)).2.2⟩
    rw [γ.extend_apply hτI]
    exact hγ i hin ⟨Subtype.coe_le_coe.mp hτ.1, Subtype.coe_le_coe.mp hτ.2⟩
  have hgi_cont : ContinuousOn (g i) (ball (z i) (r i)) :=
    fun y hy ↦ (hd i hin y hy).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (g i ∘ γ.extend) (Icc (t i : ℝ) (t (i + 1) : ℝ)) :=
    hgi_cont.comp γ.continuous_extend.continuousOn hmem_ball
  have hderiv : ∀ τ ∈ Ioo (t i : ℝ) (t (i + 1) : ℝ) \ p,
      HasDerivAt (g i ∘ γ.extend) (φ (γ.extend τ) (deriv γ.extend τ)) τ := by
    intro τ hτ
    have hτ01 : τ ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt (t i).2.1 hτ.1.1, lt_of_lt_of_le hτ.1.2 (t (i + 1)).2.2⟩
    exact (hd i hin (γ.extend τ) (hmem_ball τ (Ioo_subset_Icc_self hτ.1))).comp_hasDerivAt τ
      (hdiff τ ⟨hτ01, hτ.2⟩).hasDerivAt
  rw [MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (g i ∘ γ.extend)
      (fun τ ↦ φ (γ.extend τ) (deriv γ.extend τ)) (Subtype.coe_le_coe.mpr (hle i hin))
      hp hcont hderiv (hint_sub i hin)]
  simp only [Function.comp_apply, γ.extend_extends']

/-- When `γ.extend` is differentiable off a countable set `p` in `(0, 1)` and `φ` is
`CurveIntegrable` along `γ` with a local-potential subdivision, `localPotentialCurveIntegral`
agrees with `curveIntegral`. -/
theorem localPotentialCurveIntegral_eq_curveIntegral_of_differentiableAt_off_countable
    {γ : Path a b} {p : Set ℝ}
    (hex : ∃ v, HasLocalPotentialCurveIntegral φ γ v) (hp : p.Countable)
    (hdiff : ∀ τ ∈ Ioo (0 : ℝ) 1 \ p, DifferentiableAt ℝ γ.extend τ)
    (hint : CurveIntegrable φ γ) :
    localPotentialCurveIntegral φ γ = ∫ᶜ x in γ, φ x := by
  obtain ⟨v, hv⟩ := hex
  rw [hv.localPotentialCurveIntegral_eq,
    hv.eq_curveIntegral_of_differentiableAt_off_countable hp hdiff hint]

/-- If `γ.extend` is differentiable on `(0, 1)` and `φ` is `CurveIntegrable` along `γ`, then any
`HasLocalPotentialCurveIntegral` value equals Mathlib's `curveIntegral φ γ`. -/
theorem HasLocalPotentialCurveIntegral.eq_curveIntegral_of_differentiableOn {γ : Path a b} {v : F}
    (hφγ : HasLocalPotentialCurveIntegral φ γ v)
    (hdiff : DifferentiableOn ℝ γ.extend (Ioo 0 1)) (hint : CurveIntegrable φ γ) :
    v = ∫ᶜ x in γ, φ x :=
  hφγ.eq_curveIntegral_of_differentiableAt_off_countable countable_empty
    (fun τ hτ ↦ (hdiff τ hτ.1).differentiableAt (Ioo_mem_nhds hτ.1.1 hτ.1.2)) hint

/-- When `γ.extend` is differentiable on `(0, 1)` and `φ` is `CurveIntegrable` along `γ` with a
local-potential subdivision, `localPotentialCurveIntegral` agrees with `curveIntegral`. -/
theorem localPotentialCurveIntegral_eq_curveIntegral_of_differentiableOn {γ : Path a b}
    (hex : ∃ v, HasLocalPotentialCurveIntegral φ γ v)
    (hdiff : DifferentiableOn ℝ γ.extend (Ioo 0 1)) (hint : CurveIntegrable φ γ) :
    localPotentialCurveIntegral φ γ = ∫ᶜ x in γ, φ x := by
  obtain ⟨v, hv⟩ := hex
  rw [hv.localPotentialCurveIntegral_eq, hv.eq_curveIntegral_of_differentiableOn hdiff hint]

omit [CompleteSpace F] in
private theorem curveIntegrable_of_isPiecewiseC1On (hφ : ContinuousOn φ s) {γ : Path a b}
    (hγ : IsPiecewiseC1On γ.extend 0 1) (hγs : ∀ t, γ t ∈ s) :
    CurveIntegrable φ γ := by
  rw [curveIntegrable_iff_intervalIntegrable_deriv]
  obtain ⟨p, -, hC1⟩ := hγ.exists_breakpoints
  refine Icc_induction_of_disjoint_Ioo (p := p) (s := uIcc (0 : ℝ) 1)
    (Q := fun c d ↦ IntervalIntegrable (fun t ↦ φ (γ.extend t) (deriv γ.extend t)) volume c d)
    (fun c d hcd hsub hdisj ↦ ?_) (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂)
    zero_le_one (uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)).symm.subset
  rcases eq_or_lt_of_le hcd with rfl | hlt
  · exact IntervalIntegrable.refl
  · have hsubI : Icc c d ⊆ I := hsub.trans (uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)).subset
    have hcont : ContinuousOn (fun t ↦ φ (γ.extend t) (derivWithin γ.extend (Icc c d) t))
        (Icc c d) := by
      refine ContinuousOn.clm_apply ?_
        ((hC1 c d hsub hdisj).continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl)
      exact hφ.comp γ.continuous_extend.continuousOn fun t ht ↦ by
        rw [γ.extend_apply (hsubI ht)]
        exact hγs ⟨t, hsubI ht⟩
    refine (hcont.intervalIntegrable_of_Icc hcd).congr_ae ?_
    rw [uIoc_of_le hcd, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Along any piecewise `C¹` path in `s`, `localPotentialCurveIntegral` agrees with Mathlib's
Bochner `curveIntegral` when `F` is complete. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_eq_curveIntegral
    (hφ : HasLocalPotentials s φ) {γ : Path a b}
    (hγ : IsPiecewiseC1On γ.extend 0 1) (hγs : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral φ γ = ∫ᶜ x in γ, φ x := by
  obtain ⟨p, hp, hdiff⟩ := hγ.exists_countable_differentiableAt
  rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hdiff
  exact localPotentialCurveIntegral_eq_curveIntegral_of_differentiableAt_off_countable
    (hφ.exists_hasLocalPotentialCurveIntegral hγs) hp hdiff
    (curveIntegrable_of_isPiecewiseC1On hφ.continuousOn hγ hγs)

/-- Along any `C¹` path in `s`, `localPotentialCurveIntegral` agrees with Mathlib's Bochner
`curveIntegral` when `F` is complete. -/
theorem HasLocalPotentials.localPotentialCurveIntegral_eq_curveIntegral_of_contDiffOn
    (hφ : HasLocalPotentials s φ) {γ : Path a b}
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγs : ∀ t, γ t ∈ s) :
    localPotentialCurveIntegral φ γ = ∫ᶜ x in γ, φ x :=
  hφ.localPotentialCurveIntegral_eq_curveIntegral
    (IsPiecewiseC1On.of_contDiffOn (by rwa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)])) hγs

end TauCeti
