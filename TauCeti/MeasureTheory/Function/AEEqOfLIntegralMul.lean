/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Almost everywhere equality from matching second moments

Two finite-valued measurable functions `u v : Ω → ℝ≥0∞` whose second moments and mixed moment all
equal one finite number are almost everywhere equal
(`TauCeti.ae_eq_of_lintegral_mul_eq`): the real-valued function `(u - v)²` has integral
`T - 2 T + T = 0`, hence vanishes almost everywhere.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Two finite-valued measurable functions `u v : Ω → ℝ≥0∞` whose second moments `∫⁻ u * u`,
`∫⁻ v * v` and mixed moment `∫⁻ u * v` all equal the same finite number `T` are almost everywhere
equal. -/
theorem ae_eq_of_lintegral_mul_eq {u v : Ω → ℝ≥0∞} (hu : Measurable u)
    (hv : Measurable v) (hu' : ∀ ω, u ω ≠ ∞) (hv' : ∀ ω, v ω ≠ ∞) {T : ℝ≥0∞} (hT : T ≠ ∞)
    (huu : ∫⁻ ω, u ω * u ω ∂μ = T) (huv : ∫⁻ ω, u ω * v ω ∂μ = T)
    (hvv : ∫⁻ ω, v ω * v ω ∂μ = T) : ∀ᵐ ω ∂μ, u ω = v ω := by
  have hI : ∀ {w w' : Ω → ℝ≥0∞}, Measurable w → Measurable w' → ∫⁻ ω, w ω * w' ω ∂μ = T →
      Integrable (fun ω => (w ω).toReal * (w' ω).toReal) μ ∧
        ∫ ω, (w ω).toReal * (w' ω).toReal ∂μ = T.toReal := by
    intro w w' hw hw' h
    simp only [← ENNReal.toReal_mul]
    exact ⟨integrable_toReal_of_lintegral_ne_top (hw.mul hw').aemeasurable (h ▸ hT),
      h ▸ integral_toReal (hw.mul hw').aemeasurable (ae_lt_top (hw.mul hw') (h ▸ hT))⟩
  obtain ⟨i1, e1⟩ := hI hu hu huu
  obtain ⟨i2, e2⟩ := hI hu hv huv
  obtain ⟨i3, e3⟩ := hI hv hv hvv
  have hexp : (fun ω => ((u ω).toReal - (v ω).toReal) ^ 2) = fun ω =>
      (u ω).toReal * (u ω).toReal - 2 * ((u ω).toReal * (v ω).toReal) +
        (v ω).toReal * (v ω).toReal := by
    funext ω; ring
  have i12 : Integrable (fun ω => (u ω).toReal * (u ω).toReal -
      2 * ((u ω).toReal * (v ω).toReal)) μ := i1.sub (i2.const_mul 2)
  have hzero : ∫ ω, ((u ω).toReal - (v ω).toReal) ^ 2 ∂μ = 0 := by
    rw [hexp, integral_add i12 i3, integral_sub i1 (i2.const_mul 2), integral_const_mul, e1, e2,
      e3]
    ring
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _)
    (hexp ▸ i12.add i3)).mp hzero] with ω hω
  rw [← ENNReal.toReal_eq_toReal_iff' (hu' ω) (hv' ω)]
  simpa [sub_eq_zero] using hω

end TauCeti
