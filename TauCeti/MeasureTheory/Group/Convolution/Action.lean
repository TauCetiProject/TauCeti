/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Convolution under a pair of monoid actions

`MeasureTheory.Measure.map_mconv_smul_prod_of_ae_smul_eq` computes a joint orbit law when
the second measure almost everywhere fixes one point, using Mathlib's product-measure map.
-/

public section

namespace MeasureTheory.Measure

/-- If `η` almost everywhere fixes `x`, the joint orbit law of `(x, y)` under `μ ∗ₘ η` can
be computed by pushing the `η` variable to the orbit of `y` before applying the `μ` variable. -/
theorem map_mconv_smul_prod_of_ae_smul_eq {M X Y : Type*} [Monoid M] [MulAction M X]
    [MulAction M Y] [MeasurableSpace M] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableMul₂ M] (μ : Measure M) {η : Measure M} [SFinite η] {x : X} {y : Y}
    (hx : Measurable (fun g : M ↦ g • x)) (hy : Measurable (fun p : M × Y ↦ p.1 • p.2))
    (hfix : ∀ᵐ g ∂η, g • x = x) :
    (μ ∗ₘ η).map (fun g ↦ (g • x, g • y)) =
      (μ.prod (η.map (fun g ↦ g • y))).map (fun p : M × Y ↦ (p.1 • x, p.1 • p.2)) := by
  have hη : Measurable (fun g : M ↦ g • y) := hy.comp (measurable_id.prodMk measurable_const)
  have happ : Measurable (fun p : M × Y ↦ (p.1 • x, p.1 • p.2)) :=
    (hx.comp measurable_fst).prodMk hy
  have hprod : (μ.prod η).map (Prod.map id fun g ↦ g • y) = μ.prod (η.map fun g ↦ g • y) := by
    simpa only [Measure.map_id] using (Measure.map_prod_map μ η measurable_id hη).symm
  rw [mconv, map_map (hx.prodMk hη) measurable_mul, ← hprod,
    map_map happ (measurable_id.prodMap hη)]
  apply map_congr
  filter_upwards [quasiMeasurePreserving_snd.ae hfix] with p hp
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, mul_smul, hp]

end MeasureTheory.Measure
