/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Lebesgue integrals over a strip by exhaustion

The strip `ℝ × T` is exhausted by the increasing rectangles `[-n, n] × T`. If the integral of a
nonnegative function over `[-n, n] × T` is `F(n) - F(-n)` for a real function `F` with limits `A₁`
at `-∞` and `A₂` at `∞`, then its integral over the whole strip is `A₂ - A₁`
(`TauCeti.setLIntegral_univ_prod_eq_ofReal_of_tendsto`).

This is the passage from the energy identity on finite rectangles to the energy of a
holomorphic strip or a Floer cylinder, whose energy is the difference of the limiting actions at
its two ends.
-/

public section

namespace TauCeti

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- **Integrals over a strip by exhaustion.** If the integral of `f` over each rectangle
`[-n, n] × T` is `F(n) - F(-n)`, where `F` tends to `A₁` at `-∞` and to `A₂` at `∞`, then the
integral of `f` over the strip `ℝ × T` is `A₂ - A₁`. -/
theorem setLIntegral_univ_prod_eq_ofReal_of_tendsto {β : Type*} [MeasurableSpace β]
    {μ : Measure (ℝ × β)} {T : Set β} {f : ℝ × β → ℝ≥0∞} {F : ℝ → ℝ} {A₁ A₂ : ℝ}
    (hE : ∀ n : ℕ, ∫⁻ z in Icc (-(n : ℝ)) n ×ˢ T, f z ∂μ = ENNReal.ofReal (F n - F (-n)))
    (hbot : Tendsto F atBot (𝓝 A₁)) (htop : Tendsto F atTop (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ T, f z ∂μ = ENNReal.ofReal (A₂ - A₁) := by
  set R : ℕ → Set (ℝ × β) := fun n ↦ Icc (-(n : ℝ)) n ×ˢ T
  have hmono : Monotone R := fun m n hmn ↦ prod_mono
    (Icc_subset_Icc (neg_le_neg (Nat.cast_le.mpr hmn)) (Nat.cast_le.mpr hmn)) le_rfl
  have hunion : ⋃ n, R n = (univ : Set ℝ) ×ˢ T := by
    refine (iUnion_subset fun n ↦ prod_mono (subset_univ _) le_rfl).antisymm fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |z.1|
    exact mem_iUnion.mpr ⟨n, ⟨abs_le.mp hn, hz.2⟩⟩
  -- The integrals over the rectangles increase to the integral over the strip.
  have hlim : Tendsto (fun n ↦ ∫⁻ z in R n, f z ∂μ) atTop
      (𝓝 (∫⁻ z in (univ : Set ℝ) ×ˢ T, f z ∂μ)) := by
    rw [← hunion, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    exact tendsto_atTop_iSup fun m n hmn ↦ lintegral_mono' (Measure.restrict_mono (hmono hmn)
      le_rfl) le_rfl
  refine tendsto_nhds_unique hlim ?_
  simp only [R, hE]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    ((htop.comp tendsto_natCast_atTop_atTop).sub
      (hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)))

end TauCeti
