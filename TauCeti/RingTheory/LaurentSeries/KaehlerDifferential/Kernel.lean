/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Basic
public import TauCeti.RingTheory.PowerSeries.Exp.Transcendental
import TauCeti.RingTheory.Kaehler.Transcendental
import TauCeti.RingTheory.LaurentSeries.RatFunc

/-!
# A nonzero algebraic differential killed by passage to continuous one-forms

For a field `K` of characteristic zero, put `g = exp(X)` in the Laurent series field `F`.
The transcendence of `g` over `K(X)` gives a derivation that vanishes on `K(X)` and sends
`g` to one. It detects the algebraic one-form `dg - g dX` and is discontinuous for the
valuation topology. Since the formal derivative of `g` is `g`, this one-form maps to zero
in the continuous differentials.
-/

public section

open HahnSeries
open scoped LaurentSeries RatFunc

variable (K : Type*) [Field K]

namespace TauCeti

private theorem derivation_single_one_eq_zero_of_ratFunc
    {δ : Derivation K K⸨X⸩ K⸨X⸩} (hrat : ∀ r : RatFunc K, δ r = 0) :
    δ (single 1 1) = 0 := by
  simpa only [RatFunc.coe_X] using hrat RatFunc.X

variable [CharZero K]

/-- There is a discontinuous derivation of the Laurent field vanishing on all rational
functions and sending the formal exponential to one. -/
theorem exists_not_continuous_derivation_laurentSeries :
    ∃ δ : Derivation K K⸨X⸩ K⸨X⸩, (∀ r : RatFunc K, δ r = 0) ∧
      δ (PowerSeries.exp K) = 1 ∧ ¬ Continuous δ := by
  obtain ⟨d, hd⟩ := (PowerSeries.transcendental_coe_exp K).exists_derivation_apply_eq_one
  let δ := d.restrictScalars K
  have hrat (r : RatFunc K) : δ r = 0 := by
    -- The Laurent series coercion of rational functions is the algebra map.
    change d.restrictScalars K (algebraMap (RatFunc K) K⸨X⸩ r) = 0
    rw [Derivation.restrictScalars_apply, d.map_algebraMap]
  have he : δ (PowerSeries.exp K) = 1 := by
    simpa only [δ, Derivation.restrictScalars_apply] using hd
  refine ⟨δ, hrat, he, fun hcont ↦ (one_ne_zero (α := K⸨X⸩)) ?_⟩
  have hX := derivation_single_one_eq_zero_of_ratFunc K hrat
  simpa only [he, hX, smul_zero] using
    δ.apply_eq_laurentSeriesDerivation_smul hcont (PowerSeries.exp K)

/-- The algebraic one-form `d(exp X) - exp(X) dX` is nonzero. -/
theorem D_coe_exp_ne_smul_D_single_one :
    KaehlerDifferential.D K K⸨X⸩ (PowerSeries.exp K) ≠
      (PowerSeries.exp K : K⸨X⸩) • KaehlerDifferential.D K K⸨X⸩ (single 1 1) := by
  obtain ⟨δ, hrat, he, _⟩ := exists_not_continuous_derivation_laurentSeries K
  have hX := derivation_single_one_eq_zero_of_ratFunc K hrat
  intro h
  exact (one_ne_zero (α := K⸨X⸩)) (by simpa [he, hX] using congrArg δ.liftKaehlerDifferential h)

/-- Passing from algebraic to continuous one-forms on the Laurent field has nontrivial kernel
in characteristic zero. -/
theorem ContinuousKaehlerDifferential.not_injective_mk :
    ¬ Function.Injective (mk K) := by
  have hD : D K (PowerSeries.exp K) = (PowerSeries.exp K : K⸨X⸩) • D K (single 1 1) := by
    simpa only [← PowerSeries.coe_derivative, PowerSeries.derivative_exp] using
      (derivative_smul_D_single_one K (PowerSeries.exp K)).symm
  intro hinj
  exact D_coe_exp_ne_smul_D_single_one K
    (hinj (by simpa only [D_apply, map_smul] using hD))

end TauCeti
