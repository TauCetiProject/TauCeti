/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ScalarEquation
import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# Exponential decay of the curvature of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)`, curvature `F_a = i (∂₁ b₂ - ∂₂ b₁) ds ∧ dt` and section
`α = 2 (p + i q)`, so `|α|² = 4 (p² + q²)`. The curvature equation of a vortex reads
`∂₁ b₂ - ∂₂ b₁ = -(1 - |α|²) / 8`, so the curvature is controlled by the modulus defect
`1 - |α|²`.

For a vortex on the whole plane with `|α| → 1` at infinity, the modulus defect decays
exponentially at every rate `c < 1 / 2`: there is `K` with `1 - |α(z)|² ≤ K exp (-c |z|)`. Here
`1 / 2` is the mass of the vacuum, the square root of the constant `1 / 4` in
`L₀* L₀ = -Δ + 1 / 4` (`TauCeti.Vortex.temperedVacuumAdjoint_temperedVacuumOperator`). The proof
applies the exterior comparison principle `TauCeti.le_mul_exp_of_sq_mul_le_laplacian` to
`u = -log |α|²`: off the zeros of `α` the scalar equation
`Δ log |α|² = (|α|² - 1) / 4` (`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`) gives
`Δ u = (1 - |α|²) / 4 ≥ (|α|² / 4) u`, and `|α|² / 4 ≥ c²` outside a large disc. Since
`0 ≤ 1 - |α|² ≤ u`, the bound passes to the modulus defect, hence to the curvature, which is
therefore integrable for every additive Haar measure on the plane. This is the curvature
integrability needed to state the flux identity `(2π)⁻¹ ∫ i F_a = m`.

## Main results

* `TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`: `1 - |α|² ≤ K exp (-c |z|)` for every
  `c < 1 / 2`.
* `TauCeti.Vortex.exists_abs_curvature_le_mul_exp`: the same bound for the curvature coefficient
  `∂₁ b₂ - ∂₂ b₁`.
* `TauCeti.Vortex.integrable_one_sub_normSq`, `TauCeti.Vortex.integrable_curvature`: the modulus
  defect and the curvature are integrable.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric MeasureTheory Topology InnerProductSpace Laplacian

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- At a point where `4 c² ≤ |α|² ≤ 1` and `α ≠ 0`, the logarithmic modulus defect
`u = -log |α|²` of a vortex satisfies `c² u ≤ Δ u`: the scalar equation gives
`Δ u = (1 - |α|²) / 4`, and `|α|² u ≤ 1 - |α|²`. -/
private theorem sq_mul_neg_log_normSq_le_laplacian
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) {c : ℝ} {z : ℂ} (hc : 4 * c ^ 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2))
    (hpos : 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (hle : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 1) :
    c ^ 2 * -Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) ≤
      Δ (fun w ↦ -Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z := by
  set t := 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  have hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := fun h ↦ by simp [t, h] at hpos
  have hΔ : Δ (fun w ↦ -Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z = (1 - t) / 4 := by
    rw [← Pi.neg_def, congrFun laplacian_neg z,
      Pi.neg_apply, laplacian_log_normSq_of_equation_eq_zero hb₁.differentiableAt
        hb₂.differentiableAt hp.contDiffAt hq.contDiffAt hα (Eventually.of_forall hsol)]
    ring
  have hu₀ : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos hpos.le hle)
  -- `t (-log t) ≤ 1 - t`, from `1 - t⁻¹ ≤ log t`.
  have hut : t * -Real.log t ≤ 1 - t := by
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hpos) hpos.le
    rw [mul_sub, mul_inv_cancel₀ hpos.ne', mul_one] at h
    linarith
  have : c ^ 2 * -Real.log t ≤ t / 4 * -Real.log t :=
    mul_le_mul_of_nonneg_right (by linarith) hu₀
  rw [hΔ]
  linarith

/-- The case `0 ≤ c` of `exists_one_sub_normSq_le_mul_exp`, with a nonnegative constant. -/
private theorem exists_one_sub_normSq_le_mul_exp_of_nonneg
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K, 0 ≤ K ∧ ∀ z, 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ K * Real.exp (-(c * ‖z‖)) := by
  set s : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2) with hs
  have hs₁ : ∀ z, s z ≤ 1 := normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim
  have hs₀ : ∀ z, 0 ≤ s z := fun z ↦ by positivity
  have hscd : ContDiff ℝ 2 s := contDiff_const.mul ((hp.pow 2).add (hq.pow 2))
  -- Outside a disc of radius `R`, `|α|² > 4 c²`.
  have h4c : 4 * c ^ 2 < 1 := by nlinarith
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hlim.eventually (lt_mem_nhds h4c))
  set R := max R₀ 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hsR : ∀ z, R ≤ ‖z‖ → 4 * c ^ 2 < s z := fun z hz ↦ hR₀ ((le_max_left _ _).trans hz)
  have hpos : ∀ z, R ≤ ‖z‖ → 0 < s z := fun z hz ↦ (by positivity : 0 ≤ 4 * c ^ 2).trans_lt
    (hsR z hz)
  -- The logarithmic defect `u = -log |α|²` is a subsolution of `-Δ + c²` there.
  set u : ℂ → ℝ := fun z ↦ -Real.log (s z) with hu
  have hucont : ContinuousOn u {z | R ≤ ‖z‖} := fun z hz ↦
    (hscd.continuous.continuousAt.log (hpos z hz).ne').neg.continuousWithinAt
  have hucd : ∀ z, R < ‖z‖ → ContDiffAt ℝ 2 u z := fun z hz ↦
    (hscd.contDiffAt.log (hpos z hz.le).ne').neg
  have hsub : ∀ z, R < ‖z‖ → c ^ 2 * u z ≤ Δ u z := fun z hz ↦
    sq_mul_neg_log_normSq_le_laplacian hb₁ hb₂ hp hq hsol (hsR z hz.le).le (hpos z hz.le) (hs₁ z)
  have hulim : Tendsto u (cocompact ℂ) (𝓝 0) := by
    simpa [hu] using ((Real.continuousAt_log one_ne_zero).tendsto.comp hlim).neg
  -- A bound for `u` on the sphere of radius `R`.
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn
    (hucont.mono fun z hz ↦ by simp [mem_sphere_zero_iff_norm.mp hz])
  have hdecay : ∀ z, R ≤ ‖z‖ → u z ≤ max M 0 * Real.exp (-(c * (‖z‖ - R))) :=
    fun z hz ↦ TauCeti.le_mul_exp_of_sq_mul_le_laplacian hR hc₀ (le_max_right _ _) hucont hucd
      hsub (fun w hw ↦ ((le_abs_self _).trans (hM w (mem_sphere_zero_iff_norm.mpr hw))).trans
        (le_max_left _ _)) hulim hz
  -- Transfer to the modulus defect, using `1 - |α|² ≤ 1` inside the disc.
  refine ⟨max (max M 0 * Real.exp (c * R)) (Real.exp (c * R)),
    (Real.exp_pos _).le.trans (le_max_right _ _), fun z ↦ ?_⟩
  have hsplit : ∀ A : ℝ, A * Real.exp (c * R) * Real.exp (-(c * ‖z‖)) =
      A * Real.exp (-(c * (‖z‖ - R))) := fun A ↦ by
    rw [exp_neg_mul_sub, mul_assoc]
  rcases le_or_gt R ‖z‖ with hz | hz
  · calc 1 - s z ≤ u z := by linarith [Real.log_le_sub_one_of_pos (hpos z hz)]
      _ ≤ max M 0 * Real.exp (-(c * (‖z‖ - R))) := hdecay z hz
      _ = max M 0 * Real.exp (c * R) * Real.exp (-(c * ‖z‖)) := (hsplit _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · calc 1 - s z ≤ 1 := by linarith [hs₀ z]
      _ ≤ 1 * Real.exp (-(c * (‖z‖ - R))) := by
        rw [one_mul]
        exact Real.one_le_exp (by nlinarith)
      _ = 1 * Real.exp (c * R) * Real.exp (-(c * ‖z‖)) := (hsplit _).symm
      _ ≤ _ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- **Exponential decay of the modulus defect of a plane vortex.** A vortex on the whole plane
whose section satisfies `|α| → 1` at infinity has `1 - |α(z)|² ≤ K exp (-c |z|)` for every rate
`c < 1 / 2`, with a constant `K` depending on `c`. -/
theorem exists_one_sub_normSq_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z, 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK₀, hK⟩ := exists_one_sub_normSq_le_mul_exp_of_nonneg hb₁ hb₂ hp hq hsol hlim
    (le_max_right c 0) (max_lt hc (by norm_num))
  refine ⟨K, fun z ↦ (hK z).trans (mul_le_mul_of_nonneg_left ?_ hK₀)⟩
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg _)))

/-- **Exponential decay of the curvature of a plane vortex.** A vortex on the whole plane whose
section satisfies `|α| → 1` at infinity has curvature coefficient bounded by `K exp (-c |z|)` for
every rate `c < 1 / 2`. -/
theorem exists_abs_curvature_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z, |fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I| ≤
      K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := exists_one_sub_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc
  refine ⟨K / 8, fun z ↦ ?_⟩
  have h₀ : 0 ≤ 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by
    linarith [normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim z]
  rw [curvature_eq_of_equation_eq_zero (hsol z), abs_neg, abs_of_nonneg (by linarith)]
  linarith [hK z]

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure]

/-- The modulus defect `1 - |α|²` of a vortex on the whole plane with `|α| → 1` at infinity is
integrable. -/
theorem integrable_one_sub_normSq
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Integrable (fun z ↦ 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) μ := by
  obtain ⟨K, hK⟩ := exists_one_sub_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim
    (by norm_num : (1 / 4 : ℝ) < 1 / 2)
  have hint : Integrable (fun z : ℂ ↦ K * Real.exp (-(1 / 4 * ‖z‖))) μ :=
    (integrable_exp_neg_mul_norm μ (by norm_num : (0 : ℝ) < 1 / 4)).const_mul K
  have hcont : Continuous fun z ↦ 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    continuous_const.sub (continuous_const.mul ((hp.continuous.pow 2).add (hq.continuous.pow 2)))
  refine hint.mono' hcont.aestronglyMeasurable (.of_forall fun z ↦ ?_)
  have h₁ := normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim z
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  exact hK z

/-- **Integrability of the curvature of a plane vortex.** A vortex on the whole plane whose
section satisfies `|α| → 1` at infinity has integrable curvature coefficient `∂₁ b₂ - ∂₂ b₁`. -/
theorem integrable_curvature
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Integrable (fun z ↦ fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) μ := by
  refine ((integrable_one_sub_normSq μ hb₁ hb₂ hp hq hsol hlim).div_const 8).neg.congr
    (.of_forall fun z ↦ ?_)
  exact (curvature_eq_of_equation_eq_zero (hsol z)).symm

end TauCeti.Vortex
