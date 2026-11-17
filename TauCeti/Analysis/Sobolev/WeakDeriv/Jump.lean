/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Sobolev.Mollification.Interior

/-!
# Hyperplane jump indicators are not weakly differentiable

Let `E` be a finite-dimensional real normed space equipped with an additive Haar measure `μ`,
`φ : E →L[ℝ] ℝ` a nonzero continuous linear functional, and `c : F` a nonzero vector in a real
normed space `F`. The half-space jump indicator `u := {x | 0 < φ x}.indicator (fun _ => c)` is
locally constant on the two open half-spaces `{0 < φ}` and `{φ < 0}`, whose complement `ker φ` is
`μ`-null (`Measure.addHaar_submodule`).

Consequently:
1. Any weak Fréchet derivative `D` of `u` on an open set `Ω` vanishes `μ`-almost everywhere on `Ω`
   (`TauCeti.ae_eq_zero_of_hasWeakFDerivOn_indicator_pos`).
2. Whenever `Ω` contains a point `x₀ ∈ ker φ`, `u` admits no weak Fréchet derivative on `Ω`
   (`TauCeti.not_hasWeakFDerivOn_indicator_pos`). By interior mollification on a ball
   `ball x₀ r ⊆ Ω`, a weak derivative of `0` yields a smooth convolution whose Fréchet derivative
   vanishes everywhere on the convex ball `ball x₀ (r / 2)`; hence the convolution is constant
   there, contradicting that it equals `c` on the positive side and `0` on the negative side.

## Main declarations

* `TauCeti.ae_eq_zero_of_hasWeakFDerivOn_indicator_pos`: any weak Fréchet derivative of a
  half-space jump indicator vanishes almost everywhere on `Ω`.
* `TauCeti.not_hasWeakFDerivOn_indicator_pos`: a nonzero hyperplane jump indicator admits no weak
  Fréchet derivative on any open set meeting `ker φ`.
-/

public noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Convolution

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Any candidate weak Fréchet derivative of a half-space jump indicator vanishes almost
everywhere on `Ω`, because the indicator is locally constant on the two open half-spaces and the
separating hyperplane `ker φ` is Haar-null. -/
theorem ae_eq_zero_of_hasWeakFDerivOn_indicator_pos {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) {c : F}
    {Ω : Opens E} {D : E → E →L[ℝ] F}
    (hD : HasWeakFDerivOn μ Ω ({x : E | 0 < φ x}.indicator fun _ => c) D) :
    D =ᵐ[μ.restrict Ω] 0 := by
  have : CompleteSpace F := hD.completeSpace
  let Ωpos : Opens E := Ω ⊓ ⟨{x : E | 0 < φ x}, isOpen_lt continuous_const φ.continuous⟩
  let Ωneg : Opens E := Ω ⊓ ⟨{x : E | φ x < 0}, isOpen_lt φ.continuous continuous_const⟩
  have hpos : D =ᵐ[μ.restrict Ωpos] 0 := by
    have hc_eq : ({x : E | 0 < φ x}.indicator fun _ => c) =ᵐ[μ.restrict Ωpos] fun _ => c :=
      (ae_restrict_iff' Ωpos.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx =>
        indicator_of_mem hx.2 _
    have h0 : HasWeakFDerivOn μ Ωpos (fun _ : E => c) 0 :=
      hasWeakFDerivOn_iff.mpr fun _ => hasWeakLineDerivOn_const c
    exact ((hD.mono inf_le_left).congr_ae hc_eq).ae_eq h0
  have hneg : D =ᵐ[μ.restrict Ωneg] 0 := by
    have h0_eq : ({x : E | 0 < φ x}.indicator fun _ => c) =ᵐ[μ.restrict Ωneg] 0 :=
      (ae_restrict_iff' Ωneg.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx => by
        have hxlt : φ x < 0 := hx.2
        exact indicator_of_notMem (not_lt.2 hxlt.le) _
    have h0 : HasWeakFDerivOn μ Ωneg (fun _ : E => (0 : F)) 0 :=
      hasWeakFDerivOn_iff.mpr fun _ => hasWeakLineDerivOn_const 0
    exact ((hD.mono inf_le_left).congr_ae h0_eq).ae_eq h0
  have hker_ne : LinearMap.ker φ.toLinearMap ≠ ⊤ := by
    intro htop
    apply hφ
    ext x
    exact LinearMap.mem_ker.1 (htop ▸ Submodule.mem_top)
  have hker_zero : μ (LinearMap.ker φ.toLinearMap : Set E) = 0 :=
    Measure.addHaar_submodule μ _ hker_ne
  have hpos' := (ae_restrict_iff' Ωpos.isOpen.measurableSet).1 hpos
  have hneg' := (ae_restrict_iff' Ωneg.isOpen.measurableSet).1 hneg
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [hpos', hneg', compl_mem_ae_iff.2 hker_zero] with x hxp hxn hxker hxΩ
  rcases lt_trichotomy (φ x) 0 with hlt | heq | hgt
  · exact hxn ⟨hxΩ, hlt⟩
  · exact False.elim (hxker heq)
  · exact hxp ⟨hxΩ, hgt⟩

/-- **A nonzero hyperplane jump has no weak Fréchet derivative across the hyperplane.** If
`φ : E →L[ℝ] ℝ` is nonzero, `c : F` is nonzero, and `Ω` contains a point `x₀` on `ker φ`, then
`{x | 0 < φ x}.indicator (fun _ => c)` admits no weak Fréchet derivative on `Ω`. -/
theorem not_hasWeakFDerivOn_indicator_pos {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) {c : F} (hc : c ≠ 0)
    {Ω : Opens E} {x₀ : E} (hx₀ : x₀ ∈ (Ω : Set E)) (hφ₀ : φ x₀ = 0)
    (D : E → E →L[ℝ] F) :
    ¬ HasWeakFDerivOn μ Ω ({x : E | 0 < φ x}.indicator fun _ => c) D := by
  intro hD
  have : CompleteSpace F := hD.completeSpace
  let u : E → F := {x : E | 0 < φ x}.indicator fun _ => c
  have hD₀ : HasWeakFDerivOn μ Ω u 0 :=
    hD.congr_ae_deriv (ae_eq_zero_of_hasWeakFDerivOn_indicator_pos hφ hD)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen x₀ hx₀
  let B : Opens E := ⟨ball x₀ r, isOpen_ball⟩
  have hB_weak : HasWeakFDerivOn μ B u 0 := hD₀.mono hball
  have : IsFiniteMeasure (μ.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 (measure_ball_lt_top (μ := μ) (x := x₀) (r := r)).ne
  have hm : MeasurableSet {x : E | 0 < φ x} :=
    (isOpen_lt continuous_const φ.continuous).measurableSet
  have hu_lp : MemLp u 1 (μ.restrict B) := (memLp_const c).indicator hm.nullMeasurableSet
  -- Pick a direction `v` with `φ v > 0` and two symmetric points `xPos, xNeg ∈ ball x₀ (r / 2)`.
  obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
    by_contra! h0
    exact hφ (ContinuousLinearMap.ext h0)
  let v : E := if 0 < φ w then w else -w
  have hv_pos : 0 < φ v := by
    dsimp [v]
    split_ifs with h
    · exact h
    · simpa using lt_of_le_of_ne (not_lt.1 h) hw
  have hv_norm : 0 < ‖v‖ := norm_pos_iff.2 fun hv0 => by simp [hv0] at hv_pos
  let t : ℝ := r / (4 * ‖v‖)
  have ht_pos : 0 < t := div_pos hr (by positivity)
  have htv_norm : ‖t • v‖ = r / 4 := by
    rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
    dsimp [t]
    field_simp
  let xPos : E := x₀ + t • v
  let xNeg : E := x₀ - t • v
  have hxPos : xPos ∈ ball x₀ (r / 2) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, htv_norm]
    linarith
  have hxNeg : xNeg ∈ ball x₀ (r / 2) := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, htv_norm]
    linarith
  -- Choose a bump radius `δ` small enough that balls of radius `δ` around `ball x₀ (r / 2)` stay
  -- inside `B` and balls of radius `δ` around `xPos` and `xNeg` stay inside the two half-spaces.
  let δ : ℝ := min (r / 4) (t * φ v / (2 * ‖φ‖ + 1))
  have hδ_pos : 0 < δ := lt_min (by linarith) (div_pos (mul_pos ht_pos hv_pos) (by positivity))
  have hδ_r : δ ≤ r / 4 := min_le_left _ _
  have hδ_φ : ‖φ‖ * δ < t * φ v := by
    have hle : δ ≤ t * φ v / (2 * ‖φ‖ + 1) := min_le_right _ _
    have hden : 0 < 2 * ‖φ‖ + 1 := by positivity
    calc ‖φ‖ * δ ≤ ‖φ‖ * (t * φ v / (2 * ‖φ‖ + 1)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = (‖φ‖ / (2 * ‖φ‖ + 1)) * (t * φ v) := by ring
      _ < 1 * (t * φ v) :=
          mul_lt_mul_of_pos_right ((div_lt_one hden).2 (by linarith [norm_nonneg φ]))
            (mul_pos ht_pos hv_pos)
      _ = t * φ v := one_mul _
  let ρ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ_pos, half_lt_self hδ_pos⟩
  let g : E → F :=
    (B : Set E).indicator u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, μ]
      ρ.normed μ
  have h0_lp : MemLp (0 : E → E →L[ℝ] F) 1 (μ.restrict B) := memLp_const (0 : E →L[ℝ] F)
  -- On `ball x₀ (r / 2)`, `g` has classical derivative `0`, hence is constant.
  have hg_deriv : ∀ y ∈ ball x₀ (r / 2), HasFDerivAt g 0 y := fun y hy => by
    have hcb : closedBall y ρ.rOut ⊆ (B : Set E) := fun z hz => by
      have hz' : dist z y ≤ δ := mem_closedBall.1 hz
      have hy' : dist y x₀ < r / 2 := mem_ball.1 hy
      exact mem_ball.2 ((dist_triangle z y x₀).trans_lt (by linarith))
    have hd := hB_weak.hasFDerivAt_indicator_convolution_normed (p := 1) (q := 1) hu_lp h0_lp
      le_rfl le_rfl ρ y hcb
    have hzero : (((B : Set E).indicator (0 : E → E →L[ℝ] F)) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, μ]
        ρ.normed μ) y = 0 := by
      simp [convolution_def]
    simpa only [hzero] using hd
  have hconst : g xPos = g xNeg :=
    (convex_ball x₀ (r / 2)).is_const_of_fderivWithin_eq_zero
      (fun y hy => (hg_deriv y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [fderivWithin_of_isOpen isOpen_ball hy, (hg_deriv y hy).fderiv])
      hxPos hxNeg
  -- At `xPos`, the integrand equals `ρ.normed μ (xPos - y) • c`, so `g xPos = c`.
  have hg_pos : g xPos = c := by
    have hcb : closedBall xPos δ ⊆ (B : Set E) := fun z hz => by
      have hz' : dist z xPos ≤ δ := mem_closedBall.1 hz
      have hy' : dist xPos x₀ < r / 2 := mem_ball.1 hxPos
      exact mem_ball.2 ((dist_triangle z xPos x₀).trans_lt (by linarith))
    have hfun : (fun y : E => ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip)
        ((B : Set E).indicator u y) (ρ.normed μ (xPos - y))) =
        fun y : E => ρ.normed μ (xPos - y) • c := by
      funext y
      by_cases hy : y ∈ closedBall xPos δ
      · have hB_y : y ∈ (B : Set E) := hcb hy
        have hφ_y : 0 < φ y := by
          have hdiff : |φ (y - xPos)| ≤ ‖φ‖ * δ := by
            calc |φ (y - xPos)| = ‖φ (y - xPos)‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖φ‖ * ‖y - xPos‖ := φ.le_opNorm _
              _ ≤ ‖φ‖ * δ := mul_le_mul_of_nonneg_left
                  (by simpa [mem_closedBall, dist_eq_norm] using hy) (norm_nonneg _)
          have hφ_eq : φ y = t * φ v + φ (y - xPos) := by
            have : y = xPos + (y - xPos) := by abel
            conv_lhs => rw [this]
            simp [xPos, map_add, map_smul, hφ₀]
          linarith [(abs_le.1 hdiff).1]
        have hu_y : u y = c := indicator_of_mem hφ_y _
        simp [indicator_of_mem hB_y, hu_y]
      · have hnot : xPos - y ∉ tsupport (ρ.normed μ) := by
          rw [ρ.tsupport_normed_eq]
          intro hmem
          apply hy
          simpa [mem_closedBall, dist_eq_norm, norm_sub_rev, ρ] using hmem
        have hzero : ρ.normed μ (xPos - y) = 0 := image_eq_zero_of_notMem_tsupport hnot
        simp [hzero]
    calc g xPos = ∫ y, ρ.normed μ (xPos - y) • c ∂μ := by
            dsimp only [g]
            rw [convolution_def, hfun]
      _ = ∫ y, ρ.normed μ y • c ∂μ :=
          MeasureTheory.integral_sub_left_eq_self (fun y => ρ.normed μ y • c) μ xPos
      _ = c := ρ.integral_normed_smul μ c
  -- At `xNeg`, the support of the kernel stays in `{φ < 0}`, so `g xNeg = 0`.
  have hg_neg : g xNeg = 0 := by
    have hfun : (fun y : E => ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip)
        ((B : Set E).indicator u y) (ρ.normed μ (xNeg - y))) = fun _ : E => (0 : F) := by
      funext y
      by_cases hy : y ∈ closedBall xNeg δ
      · have hφ_y : φ y < 0 := by
          have hdiff : |φ (y - xNeg)| ≤ ‖φ‖ * δ := by
            calc |φ (y - xNeg)| = ‖φ (y - xNeg)‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖φ‖ * ‖y - xNeg‖ := φ.le_opNorm _
              _ ≤ ‖φ‖ * δ := mul_le_mul_of_nonneg_left
                  (by simpa [mem_closedBall, dist_eq_norm] using hy) (norm_nonneg _)
          have hφ_eq : φ y = -(t * φ v) + φ (y - xNeg) := by
            have : y = xNeg + (y - xNeg) := by abel
            conv_lhs => rw [this]
            simp [xNeg, map_sub, map_smul, hφ₀]
          linarith [(abs_le.1 hdiff).2]
        have hu0 : u y = 0 := indicator_of_notMem (not_lt.2 hφ_y.le) _
        simp [hu0]
      · have hnot : xNeg - y ∉ tsupport (ρ.normed μ) := by
          rw [ρ.tsupport_normed_eq]
          intro hmem
          apply hy
          simpa [mem_closedBall, dist_eq_norm, norm_sub_rev, ρ] using hmem
        have hzero : ρ.normed μ (xNeg - y) = 0 := image_eq_zero_of_notMem_tsupport hnot
        simp [hzero]
    dsimp only [g]
    rw [convolution_def, hfun, integral_zero]
  exact hc (hg_pos.symm.trans (hconst.trans hg_neg))

end TauCeti
