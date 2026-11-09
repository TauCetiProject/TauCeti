/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Basic

/-!
# A Poincaré inequality for Schrödinger forms with a potential positive at infinity

On the whole of a finite-dimensional space no Poincaré inequality `‖u‖₂ ≤ C ‖Du‖₂` holds
(`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`). A nonnegative potential `P` that is
bounded below by a constant `a > 0` outside a ball restores it: there is `c > 0` with

`c ∫ ‖u‖² ≤ ∫ ‖Du‖² + ∫ P ‖u‖²`

for every compactly supported `C¹` map `u`. In other words the quadratic form of the
Schrödinger operator `-Δ + P` is bounded below by `c` times the squared `L²` norm, so `-Δ + P` has a
spectral gap, although `P` may vanish on a large set inside the ball. The constant depends on
`P` only through `a` and the radius of the ball.

Outside a ball `Ω` containing the ball where `P` may be small, the potential term alone controls
`‖u‖²`. Inside `Ω`, the Poincaré–Wirtinger inequality with the mean taken over the annulus
`S ⊆ Ω` on which `P ≥ a` controls the deviation of `u` from that mean by `Du`, and the mean itself
is controlled by the integral of `‖u‖²` over `S`, hence again by the potential term
(`TauCeti.setIntegral_norm_sq_le_of_convex`).

Such an estimate makes `L L*` coercive for a first-order operator `L` whose Weitzenböck formula
has a potential of this kind.

## Main results

* `TauCeti.exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq`:
  the inequality above.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16 (the Poincaré–Wirtinger inequality used inside the ball).
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Poincaré inequality for a Schrödinger form.** Let `P` be locally integrable, almost
everywhere nonnegative, and almost everywhere at least `a > 0` outside the closed ball of radius
`R`. Then there is `c > 0` such that `c ∫ ‖u‖² ≤ ∫ ‖Du‖² + ∫ P ‖u‖²` for every compactly
supported `C¹` map `u`. -/
theorem exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
    {P : E → ℝ} (hP : LocallyIntegrable P μ) (hP₀ : ∀ᵐ z ∂μ, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (haP : ∀ᵐ z ∂μ, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      c * ∫ z, ‖u z‖ ^ 2 ∂μ ≤ ∫ z, ‖fderiv ℝ u z‖ ^ 2 ∂μ + ∫ z, P z * ‖u z‖ ^ 2 ∂μ := by
  -- `Ω` is a ball beyond the radius `R`, and `S ⊆ Ω` the annulus on which `P ≥ a`.
  set ρ := max R 0
  set Ω := ball (0 : E) (ρ + 1)
  set S := Ω ∩ (closedBall (0 : E) ρ)ᶜ
  have hρ : 0 ≤ ρ := le_max_right R 0
  have hSΩ : S ⊆ Ω := inter_subset_left
  have hS : MeasurableSet S := measurableSet_ball.inter measurableSet_closedBall.compl
  have hρR : R ≤ ρ := le_max_left R 0
  have haS : ∀ᵐ z ∂μ, z ∈ S → a ≤ P z := haP.mono fun z h hz ↦
    h (hρR.trans_lt (by simpa using hz.2 : ρ < ‖z‖))
  have haΩ : ∀ᵐ z ∂μ, z ∈ Ωᶜ → a ≤ P z := haP.mono fun z h hz ↦ by
    have : ρ + 1 ≤ ‖z‖ := by simpa [Ω] using hz
    exact h (by linarith)
  have hS₀ : μ S ≠ 0 := by
    refine (isOpen_ball.inter isClosed_closedBall.isOpen_compl).measure_ne_zero μ ?_
    obtain ⟨v, hv⟩ := exists_norm_eq E (by positivity : 0 ≤ ρ + 1 / 2)
    exact ⟨v, by simp only [mem_ball_zero_iff, hv]; linarith,
      by simp only [mem_compl_iff, mem_closedBall_zero_iff, hv, not_le]; linarith⟩
  -- The constants of the Poincaré inequality on `Ω` relative to `S`.
  set A := (2 + 4 * μ.real Ω / μ.real S) *
    (μ.real (ball 0 1) * diam Ω ^ (finrank ℝ E + 1) / μ.real S) ^ 2
  set B := 4 * μ.real Ω / μ.real S
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  refine ⟨a / (a * A + B + 1), by positivity, fun u hu hc ↦ ?_⟩
  have hn : HasCompactSupport fun z ↦ ‖u z‖ ^ 2 := hc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp)
  have hI : Integrable (fun z ↦ ‖u z‖ ^ 2) μ :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hn
  have hDc : Continuous fun z ↦ ‖fderiv ℝ u z‖ ^ 2 := (hu.continuous_fderiv one_ne_zero).norm.pow 2
  have hDs : HasCompactSupport fun z ↦ ‖fderiv ℝ u z‖ ^ 2 :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L ↦ ‖L‖ ^ 2) (by simp)
  have hD : Integrable (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) μ := hDc.integrable_of_hasCompactSupport hDs
  have hQ : Integrable (fun z ↦ P z * ‖u z‖ ^ 2) μ :=
    hP.integrable_smul_right_of_hasCompactSupport (g := fun z ↦ ‖u z‖ ^ 2)
      (hu.continuous.norm.pow 2) hn
  have hQ₀ : ∀ᵐ z ∂μ, 0 ≤ P z * ‖u z‖ ^ 2 := hP₀.mono fun z h ↦ mul_nonneg h (by positivity)
  -- Inside `Ω`, the Poincaré inequality relative to `S`.
  have hΩ := setIntegral_norm_sq_le_of_convex (μ := μ) isOpen_ball (convex_ball 0 (ρ + 1))
    isBounded_ball hu hSΩ hS₀
  have hDΩ : ∫ z in Ω, ‖fderiv ℝ u z‖ ^ 2 ∂μ ≤ ∫ z, ‖fderiv ℝ u z‖ ^ 2 ∂μ :=
    setIntegral_le_integral hD (ae_of_all _ fun _ ↦ by positivity)
  -- Where `P ≥ a`, the potential term controls `‖u‖²`.
  have hpot {T : Set E} (hT : MeasurableSet T) (haT : ∀ᵐ z ∂μ, z ∈ T → a ≤ P z) :
      a * ∫ z in T, ‖u z‖ ^ 2 ∂μ ≤ ∫ z in T, P z * ‖u z‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on_ae (hI.integrableOn.const_mul a) hQ.integrableOn hT
      (haT.mono fun z h hz ↦ mul_le_mul_of_nonneg_right (h hz) (by positivity))
  have hYS := (hpot hS haS).trans (setIntegral_mono_set hQ.integrableOn (ae_restrict_of_ae hQ₀)
    hSΩ.eventuallyLE)
  have hYC := hpot measurableSet_ball.compl haΩ
  have hQΩ : 0 ≤ ∫ z in Ω, P z * ‖u z‖ ^ 2 ∂μ := integral_nonneg_of_ae (ae_restrict_of_ae hQ₀)
  have hQC : 0 ≤ ∫ z in Ωᶜ, P z * ‖u z‖ ^ 2 ∂μ := integral_nonneg_of_ae (ae_restrict_of_ae hQ₀)
  have hD₀ : 0 ≤ ∫ z, ‖fderiv ℝ u z‖ ^ 2 ∂μ := integral_nonneg fun _ ↦ by positivity
  -- Combine: `a ∫ ‖u‖² ≤ (a A + B + 1) (∫ ‖Du‖² + ∫ P ‖u‖²)`.
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity),
    ← integral_add_compl measurableSet_ball hI, ← integral_add_compl measurableSet_ball hQ]
  nlinarith [mul_le_mul_of_nonneg_left hΩ ha.le,
    mul_le_mul_of_nonneg_left hDΩ (mul_nonneg ha.le hA), mul_le_mul_of_nonneg_left hYS hB,
    mul_nonneg (by positivity : 0 ≤ a * A + 1) hQΩ,
    mul_nonneg (by positivity : 0 ≤ a * A + B) hQC, mul_nonneg (by positivity : 0 ≤ B + 1) hD₀]

end TauCeti
