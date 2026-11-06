/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import TauCeti.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Interior value and derivative estimates from the harmonic `L¹` norm

The mean-value property controls harmonic values by an outer `L¹` norm. Applying the native
bounded-oscillation estimate on smaller balls then controls the actual Fréchet derivative by
the same outer norm. The constants depend only on the two radii and the domain dimension,
and the estimates hold for Banach-valued harmonic functions.

These are the harmonic-remainder estimates used after subtracting a particular solution of
the divergence-form Laplace equation in planar Cauchy–Riemann regularity.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.3 (interior derivative estimates).
-/

public noncomputable section

open InnerProductSpace MeasureTheory Metric Set Module
open scoped Topology NNReal ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {u : E → F}

/-- A harmonic value is bounded by the `L¹` norm on any containing open set, using a ball
of fixed radius around the evaluation point. -/
theorem InnerProductSpace.HarmonicOnNhd.norm_le_inv_measureReal_mul_integral_norm
    {s : Set E} (hu : HarmonicOnNhd u s) (hi : IntegrableOn u s μ) {x : E} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : closedBall x ρ ⊆ s) :
    ‖u x‖ ≤ (μ.real (ball (0 : E) ρ))⁻¹ * ∫ z in s, ‖u z‖ ∂μ := by
  have hV : 0 < μ.real (ball (0 : E) ρ) := measureReal_ball_pos μ 0 hρ
  have hmean := (hu.mono hx).setIntegral_ball_eq (μ := μ)
  have hbound : μ.real (ball (0 : E) ρ) * ‖u x‖ ≤ ∫ z in s, ‖u z‖ ∂μ := by
    calc
      _ = ‖∫ z in ball x ρ, u z ∂μ‖ := by
        rw [hmean, norm_smul, Real.norm_of_nonneg measureReal_nonneg,
          Measure.addHaar_real_ball_center μ x ρ]
      _ ≤ ∫ z in ball x ρ, ‖u z‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ z in s, ‖u z‖ ∂μ := setIntegral_mono_set hi.norm
        (ae_of_all _ fun _ ↦ norm_nonneg _) (ball_subset_closedBall.trans hx).eventuallyLE
  rw [inv_mul_eq_div, le_div_iff₀ hV, mul_comm]
  exact hbound

/-- The values and actual derivative of a harmonic function on an outer ball are uniformly
bounded on an inner closed ball by the outer `L¹` norm. The constants are independent of the
function and of its Banach codomain. -/
theorem InnerProductSpace.HarmonicOnNhd.exists_norm_and_norm_fderiv_le_integral_norm
    (c : E) {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ≥0, ∀ {u : E → F}, HarmonicOnNhd u (ball c R) → IntegrableOn u (ball c R) μ →
      ∀ x ∈ closedBall c r,
        ‖u x‖ ≤ C * ∫ z in ball c R, ‖u z‖ ∂μ ∧
          ‖fderiv ℝ u x‖ ≤ C * ∫ z in ball c R, ‖u z‖ ∂μ := by
  let ρ : ℝ := (R - r) / 4
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  let V : ℝ := μ.real (ball (0 : E) ρ)
  have hV : 0 < V := measureReal_ball_pos μ 0 hρ
  let A : ℝ := 2 ^ finrank ℝ E * finrank ℝ E / ρ
  have hA : 0 ≤ A := by positivity
  refine ⟨(V⁻¹ + A * V⁻¹).toNNReal, fun {u} hu hi x hx ↦ ?_⟩
  let I : ℝ := ∫ z in ball c R, ‖u z‖ ∂μ
  have hI : 0 ≤ I := integral_nonneg fun z ↦ norm_nonneg (u z)
  let M : ℝ := V⁻¹ * I
  have hM : 0 ≤ M := by positivity
  have hinner (y : E) (hy : dist y c < r + 2 * ρ) : closedBall y ρ ⊆ ball c R := by
    intro z hz
    rw [mem_ball]
    have hdist := dist_triangle z y c
    have hz' := mem_closedBall.mp hz
    dsimp only [ρ] at hy hz' ⊢
    linarith
  have hvalues (y : E) (hy : dist y c < r + 2 * ρ) : ‖u y‖ ≤ M :=
    hu.norm_le_inv_measureReal_mul_integral_norm hi hρ (hinner y hy)
  have hval : ‖u x‖ ≤ M := hvalues x (by linarith [mem_closedBall.mp hx])
  have hlip : LipschitzOnWith (A * M).toNNReal u (ball x (ρ / 2)) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro y hy z hz
    have hyx := mem_ball.mp hy
    have hzx := mem_ball.mp hz
    have hxc := mem_closedBall.mp hx
    have hyc : dist y c < r + ρ := by linarith [dist_triangle y x c]
    have hzc : dist z c < r + ρ := by linarith [dist_triangle z x c]
    have hyz : dist y z ≤ ρ := by
      have ht := dist_triangle y x z
      rw [dist_comm x z] at ht
      linarith
    have hbs : ∀ a, dist a c < r + ρ → closedBall a ρ ⊆ ball c R :=
      fun a ha ↦ hinner a (by linarith)
    have hN : ∀ w ∈ ball y ρ ∪ ball z ρ, ‖u w‖ ≤ M := by
      intro w hw
      apply hvalues
      rcases hw with hw | hw
      · linarith [mem_ball.mp hw, dist_triangle w y c]
      · linarith [mem_ball.mp hw, dist_triangle w z c]
    have h := (hu.mono (hbs y hyc)).norm_sub_le_of_norm_le (hu.mono (hbs z hzc)) hN hρ hyz
    rw [dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hA hM)]
    exact h.trans_eq (by dsimp only [A]; ring)
  have hD : ‖fderiv ℝ u x‖ ≤ A * M := by
    have h := norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds x (half_pos hρ)) hlip
    simpa only [Real.coe_toNNReal _ (mul_nonneg hA hM)] using h
  rw [Real.coe_toNNReal _ (by positivity)]
  constructor
  · exact hval.trans (by dsimp only [M]; nlinarith [mul_nonneg hA (mul_nonneg hV.le hI)])
  · exact hD.trans (by dsimp only [M]; nlinarith [inv_nonneg.mpr hV.le])

/-- The harmonic interior value and derivative estimates in every `Lᵖ` norm, including the
supremum norm. The right side uses the outer `L¹` norm and the inner-volume factor. -/
theorem InnerProductSpace.HarmonicOnNhd.exists_eLpNorm_and_eLpNorm_fderiv_le_integral_norm
    (c : E) {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ≥0, ∀ {u : E → F}, HarmonicOnNhd u (ball c R) → IntegrableOn u (ball c R) μ →
      ∀ p : ℝ≥0∞,
        eLpNorm u p (μ.restrict (ball c r)) ≤
          μ (ball c r) ^ p.toReal⁻¹ * ENNReal.ofReal (C * ∫ z in ball c R, ‖u z‖ ∂μ) ∧
        eLpNorm (fderiv ℝ u) p (μ.restrict (ball c r)) ≤
          μ (ball c r) ^ p.toReal⁻¹ * ENNReal.ofReal (C * ∫ z in ball c R, ‖u z‖ ∂μ) := by
  obtain ⟨C, hC⟩ := HarmonicOnNhd.exists_norm_and_norm_fderiv_le_integral_norm
    (F := F) (μ := μ) c hrR
  refine ⟨C, fun {u} hu hi p ↦ ?_⟩
  have hsub : ball c r ⊆ ball c R := ball_subset_ball hrR.le
  have hU : AEStronglyMeasurable u (μ.restrict (ball c r)) :=
    (hu.continuousOn.mono hsub).aestronglyMeasurable measurableSet_ball
  have hDc : ContinuousOn (fderiv ℝ u) (ball c r) :=
    (hu.contDiffOn.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).mono hsub
  have hD : AEStronglyMeasurable (fderiv ℝ u) (μ.restrict (ball c r)) :=
    hDc.aestronglyMeasurable measurableSet_ball
  have hval : ∀ᵐ x ∂μ.restrict (ball c r), ‖u x‖ ≤ C * ∫ z in ball c R, ‖u z‖ ∂μ :=
    ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦
      (hC hu hi x (ball_subset_closedBall hx)).1
  have hder : ∀ᵐ x ∂μ.restrict (ball c r),
      ‖fderiv ℝ u x‖ ≤ C * ∫ z in ball c R, ‖u z‖ ∂μ :=
    ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦
      (hC hu hi x (ball_subset_closedBall hx)).2
  exact ⟨by simpa only [Measure.restrict_apply_univ] using eLpNorm_le_of_ae_bound hU hval,
    by simpa only [Measure.restrict_apply_univ] using eLpNorm_le_of_ae_bound hD hder⟩
