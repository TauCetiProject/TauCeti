/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Almost everywhere equality from matching second moments

Two functions whose second moments and mixed moment all agree are almost everywhere equal: the
function `(g₂ - g₁)²` has integral `T - 2 T + T = 0`, hence vanishes almost everywhere
(`TauCeti.ae_eq_of_integral_mul_eq_of_integral_sq_eq`). The same holds for two a.e.-measurable
`ℝ≥0∞`-valued functions whose moments `∫⁻ u * u`, `∫⁻ u * v`, `∫⁻ v * v` all equal the same finite
value (`TauCeti.ae_eq_of_lintegral_mul_eq`).

The polarisation lemma `TauCeti.ae_eq_of_integral_mul_eq_of_integral_sq_eq` is adapted from
`cameronfreer/exchangeability` (`Probability/CondExp.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Two real functions with equal integrals of their squares (`∫ g₁² = ∫ g₂²`) and matching cross
integral (`∫ g₂ g₁ = ∫ g₁²`) are a.e. equal: the `L²` distance polarises to
`∫ (g₂ - g₁)² = ∫ g₂² - 2 ∫ g₂ g₁ + ∫ g₁² = 0`. The products `g₁²`, `g₂²`, `g₂ g₁` are assumed
integrable. -/
lemma ae_eq_of_integral_mul_eq_of_integral_sq_eq {g₁ g₂ : Ω → ℝ}
    (hg₁sq : Integrable (fun ω ↦ g₁ ω * g₁ ω) μ)
    (hg₂sq : Integrable (fun ω ↦ g₂ ω * g₂ ω) μ) (hg₂g₁ : Integrable (fun ω ↦ g₂ ω * g₁ ω) μ)
    (h_cross : ∫ ω, g₂ ω * g₁ ω ∂μ = ∫ ω, g₁ ω * g₁ ω ∂μ)
    (h_sq : ∫ ω, g₁ ω * g₁ ω ∂μ = ∫ ω, g₂ ω * g₂ ω ∂μ) :
    g₁ =ᵐ[μ] g₂ := by
  have h_L2_zero : ∫ ω, (g₂ ω - g₁ ω) ^ 2 ∂μ = 0 := by
    have h_expand : ∀ᵐ ω ∂μ,
        (g₂ ω - g₁ ω) ^ 2 = g₂ ω * g₂ ω - 2 * (g₂ ω * g₁ ω) + g₁ ω * g₁ ω := by
      filter_upwards with ω
      ring
    have hc2_int : Integrable (fun ω ↦ 2 * (g₂ ω * g₁ ω)) μ := hg₂g₁.const_mul 2
    have hsub_int : Integrable (fun ω ↦ g₂ ω * g₂ ω - 2 * (g₂ ω * g₁ ω)) μ := hg₂sq.sub hc2_int
    have h1 : ∫ ω, (g₂ ω - g₁ ω) ^ 2 ∂μ =
        ∫ ω, g₂ ω * g₂ ω ∂μ - 2 * ∫ ω, g₂ ω * g₁ ω ∂μ + ∫ ω, g₁ ω * g₁ ω ∂μ := by
      rw [integral_congr_ae h_expand, integral_add hsub_int hg₁sq,
        integral_sub hg₂sq hc2_int, integral_const_mul]
    rw [h1, h_cross, h_sq]
    ring
  have h_sq_int : Integrable (fun ω ↦ (g₂ ω - g₁ ω) ^ 2) μ := by
    have h_eq : (fun ω ↦ (g₂ ω - g₁ ω) ^ 2)
        = fun ω ↦ g₂ ω * g₂ ω - 2 * (g₂ ω * g₁ ω) + g₁ ω * g₁ ω := by
      funext ω
      ring
    rw [h_eq]
    exact (hg₂sq.sub (hg₂g₁.const_mul 2)).add hg₁sq
  have h_diff_zero : ∀ᵐ ω ∂μ, (g₂ ω - g₁ ω) ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ fun ω ↦ sq_nonneg _) h_sq_int).mp h_L2_zero
  filter_upwards [h_diff_zero] with ω hω
  exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hω)).symm

/-- Two almost everywhere measurable functions `u v : Ω → ℝ≥0∞` whose second moments `∫⁻ u * u`,
`∫⁻ v * v` and mixed moment `∫⁻ u * v` all equal the same finite number `T` are almost everywhere
equal. -/
theorem ae_eq_of_lintegral_mul_eq {u v : Ω → ℝ≥0∞} (hu : AEMeasurable u μ)
    (hv : AEMeasurable v μ) {T : ℝ≥0∞} (hT : T ≠ ∞)
    (huu : ∫⁻ ω, u ω * u ω ∂μ = T) (huv : ∫⁻ ω, u ω * v ω ∂μ = T)
    (hvv : ∫⁻ ω, v ω * v ω ∂μ = T) : u =ᵐ[μ] v := by
  have hI : ∀ {w w' : Ω → ℝ≥0∞}, AEMeasurable w μ → AEMeasurable w' μ →
      ∫⁻ ω, w ω * w' ω ∂μ = T →
      Integrable (fun ω => (w ω).toReal * (w' ω).toReal) μ ∧
        ∫ ω, (w ω).toReal * (w' ω).toReal ∂μ = T.toReal := by
    intro w w' hw hw' h
    simp only [← ENNReal.toReal_mul]
    exact ⟨integrable_toReal_of_lintegral_ne_top (hw.mul hw') (h ▸ hT),
      h ▸ integral_toReal (hw.mul hw') (ae_lt_top' (hw.mul hw') (h ▸ hT))⟩
  obtain ⟨i1, e1⟩ := hI hu hu huu
  obtain ⟨i2, e2⟩ := hI hu hv huv
  obtain ⟨i3, e3⟩ := hI hv hv hvv
  have hfin : ∀ {w : Ω → ℝ≥0∞}, AEMeasurable w μ → ∫⁻ ω, w ω * w ω ∂μ = T →
      ∀ᵐ ω ∂μ, w ω ≠ ∞ := fun hw h => by
    filter_upwards [ae_lt_top' (hw.mul hw) (h ▸ hT)] with ω hω hinf
    simp [hinf] at hω
  filter_upwards [ae_eq_of_integral_mul_eq_of_integral_sq_eq i1 i3
    (by simpa only [mul_comm] using i2) (by simpa only [mul_comm] using e2.trans e1.symm)
    (e1.trans e3.symm), hfin hu huu, hfin hv hvv] with ω hω hu' hv'
  exact (ENNReal.toReal_eq_toReal_iff' hu' hv').mp hω

end TauCeti
