/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The `ℓ^p` product distance as a measurable function

For a positive finite exponent `p` the extended distance on `WithLp p (X × Y)` is the
`ℓ^p` combination `(d₁ ^ p + d₂ ^ p) ^ (1 / p)` of the two factor distances.
This file records the two facts that
make that distance usable as the ground distance of a measure-theoretic construction on the
product: raising it to the power `p` makes it additive in the two factors, and it is jointly
measurable for every exponent, including `0` and `∞`, as soon as the two factor distances are.

The measurable structure of `WithLp p (X × Y)` is the one pulled back from `X × Y`, so
measurability is a statement about the product measurable space and only the distance changes
along the type synonym.

## Main statements

* `TauCeti.edist_toLp_rpow` — the `p`-th power of the `ℓ^p` product distance is the sum of the
  `p`-th powers of the two factor distances;
* `TauCeti.measurable_edist_toLp_prod` — joint measurability of the `ℓ^p` product distance.
-/

public section

noncomputable section

open scoped ENNReal

namespace TauCeti

universe u v

variable {p : ℝ≥0∞} {X : Type u} {Y : Type v} [EDist X] [EDist Y]

/-- Raising the `ℓ^p` product distance to the power `p` makes it additive in the two factors. -/
theorem edist_toLp_rpow (hp : 0 < p.toReal) (z w : X × Y) :
    edist (WithLp.toLp p z) (WithLp.toLp p w) ^ p.toReal
      = edist z.1 w.1 ^ p.toReal + edist z.2 w.2 ^ p.toReal := by
  simp [WithLp.prod_edist_eq_add hp, one_div, hp.ne']

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- The `ℓ^p` product distance is jointly measurable for every exponent, including `0` and `∞`,
as soon as the two factor distances are. -/
theorem measurable_edist_toLp_prod
    (hdX : Measurable fun z : X × X ↦ edist z.1 z.2)
    (hdY : Measurable fun z : Y × Y ↦ edist z.1 z.2) :
    Measurable fun w : WithLp p (X × Y) × WithLp p (X × Y) ↦ edist w.1 w.2 := by
  have m₁ : Measurable fun w : WithLp p (X × Y) × WithLp p (X × Y) ↦ WithLp.ofLp w.1 :=
    (WithLp.measurable_ofLp p (X × Y)).comp measurable_fst
  have m₂ : Measurable fun w : WithLp p (X × Y) × WithLp p (X × Y) ↦ WithLp.ofLp w.2 :=
    (WithLp.measurable_ofLp p (X × Y)).comp measurable_snd
  have h₁ : Measurable fun w : WithLp p (X × Y) × WithLp p (X × Y) ↦
      edist w.1.fst w.2.fst := by
    simpa [Function.comp_def] using
      hdX.comp ((measurable_fst.comp m₁).prodMk (measurable_fst.comp m₂))
  have h₂ : Measurable fun w : WithLp p (X × Y) × WithLp p (X × Y) ↦
      edist w.1.snd w.2.snd := by
    simpa [Function.comp_def] using
      hdY.comp ((measurable_snd.comp m₁).prodMk (measurable_snd.comp m₂))
  by_cases hp0 : p = 0
  · subst p
    simp only [WithLp.prod_edist_eq_card]
    exact (Measurable.ite (h₁ (measurableSet_singleton 0)) measurable_const measurable_const).add
      (Measurable.ite (h₂ (measurableSet_singleton 0)) measurable_const measurable_const)
  by_cases hp_top : p = ∞
  · subst p
    simpa only [WithLp.prod_edist_eq_sup, Function.comp_def] using
      continuous_max.measurable.comp (h₁.prodMk h₂)
  simp only [WithLp.prod_edist_eq_add (ENNReal.toReal_pos hp0 hp_top)]
  exact (ENNReal.continuous_rpow_const.measurable).comp
    ((ENNReal.continuous_rpow_const.measurable.comp h₁).add
      (ENNReal.continuous_rpow_const.measurable.comp h₂))

end TauCeti
