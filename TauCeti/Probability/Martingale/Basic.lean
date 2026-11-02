/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# Martingales frozen at a date, and bounded positions taken at a date

Two closure properties of martingales indexed by a linear order, the building blocks of the
elementary stochastic integral:

* a martingale `X` with values in a Banach space, frozen at a fixed date `w`, `t ↦ X (min w t)`,
  is a martingale (`MeasureTheory.Martingale.const_min`);
* if a real martingale `Y` vanishes up to a date `r`, then multiplying it by a bounded random
  variable known at time `r` gives a martingale (`MeasureTheory.Martingale.mul_left_of_eq_zero`).

Together they show that a bounded position chosen at `r`, times the change of a martingale over
`(r, r']`, is a martingale.
-/

public section

noncomputable section

open Filter

namespace MeasureTheory

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E} {Y : ι → Ω → ℝ}

/-- A martingale frozen at a fixed date `w`, `t ↦ X (min w t)`, is a martingale. -/
theorem Martingale.const_min [SigmaFiniteFiltration μ ℱ] (hX : Martingale X ℱ μ) (w : ι) :
    Martingale (fun t ↦ X (min w t)) ℱ μ := by
  refine ⟨fun t ↦ hX.stronglyAdapted.stronglyMeasurable_le (min_le_right _ _),
    fun s t hst ↦ ?_⟩
  beta_reduce
  rcases le_or_gt w s with hws | hsw
  · rw [min_eq_left (hws.trans hst), min_eq_left hws,
      condExp_of_stronglyMeasurable (ℱ.le s) ((hX.stronglyAdapted w).mono (ℱ.mono hws))
        (hX.integrable w)]
  · rw [min_eq_right hsw.le]
    exact hX.condExp_ae_eq (le_min hsw.le hst)

/-- If a martingale `Y` vanishes up to a date `r`, and `a` is a bounded random variable known at
time `r`, then `t ↦ a * Y t` is a martingale. -/
theorem Martingale.mul_left_of_eq_zero [SigmaFiniteFiltration μ ℱ] {a : Ω → ℝ} {r : ι}
    (hY : Martingale Y ℱ μ) (hY₀ : ∀ t ≤ r, Y t = 0) (ha : StronglyMeasurable[ℱ r] a)
    (ha_bdd : ∃ C, ∀ᵐ ω ∂μ, |a ω| ≤ C) : Martingale (fun t ↦ a * Y t) ℱ μ := by
  have hmul : ∀ t, Integrable (a * Y t) μ := fun t ↦ by
    obtain ⟨C, hC⟩ := ha_bdd
    exact (hY.integrable t).bdd_mul (ha.mono (ℱ.le r)).aestronglyMeasurable
      (hC.mono fun ω hω ↦ by rwa [Real.norm_eq_abs])
  -- Once `a` is known, it factors out of the conditional expectation.
  have hlate : ∀ s t, r ≤ s → s ≤ t → μ[a * Y t | ℱ s] =ᵐ[μ] a * Y s := fun s t hrs hst ↦
    (condExp_mul_of_stronglyMeasurable_left (ha.mono (ℱ.mono hrs)) (hmul t)
      (hY.integrable t)).trans ((EventuallyEq.refl _ _).mul (hY.condExp_ae_eq hst))
  refine ⟨fun t ↦ ?_, fun s t hst ↦ ?_⟩
  · rcases le_or_gt r t with hrt | htr
    · exact (ha.mono (ℱ.mono hrt)).mul (hY.stronglyMeasurable t)
    · simp only [hY₀ t htr.le, mul_zero]
      exact stronglyMeasurable_zero
  beta_reduce
  rcases le_or_gt r s with hrs | hsr
  · exact hlate s t hrs hst
  rw [hY₀ s hsr.le, mul_zero]
  rcases le_or_gt t r with htr | hrt
  · rw [hY₀ t htr, mul_zero, condExp_zero]
  -- Otherwise condition first on the information at `r`, where `Y` still vanishes.
  calc μ[a * Y t | ℱ s]
      =ᵐ[μ] μ[μ[a * Y t | ℱ r] | ℱ s] :=
        (condExp_condExp_of_le (ℱ.mono hsr.le) (ℱ.le r)).symm
    _ =ᵐ[μ] μ[a * Y r | ℱ s] := condExp_congr_ae (hlate r t le_rfl hrt.le)
    _ = 0 := by rw [hY₀ r le_rfl, mul_zero, condExp_zero]

end MeasureTheory
