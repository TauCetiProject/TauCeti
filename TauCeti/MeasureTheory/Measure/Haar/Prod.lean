/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The canonical measure on a product of groups is a Haar measure

The measure space structure on `G × H` takes `volume` to be `volume.prod volume`. Mathlib proves
that a product of Haar measures is a Haar measure (`MeasureTheory.Measure.prod.instIsHaarMeasure`),
but instance search does not see through `volume` to the product measure. This file records the
instance for `volume` itself (`TauCeti.isHaarMeasure_volume_prod`, and its additive version
`TauCeti.isAddHaarMeasure_volume_prod`), so that for instance Lebesgue measure on `ℝ × ℝ` is known
to be translation invariant.
-/

public section

open MeasureTheory Measure

namespace TauCeti

/-- On a product of groups whose canonical measures are Haar measures, the canonical product
measure `volume = volume.prod volume` is a Haar measure. -/
@[to_additive /-- On a product of additive groups whose canonical measures are additive Haar
measures, the canonical product measure `volume = volume.prod volume` is an additive Haar measure;
for instance Lebesgue measure on `ℝ × ℝ`. -/]
instance isHaarMeasure_volume_prod {G H : Type*} [Group G] [TopologicalSpace G] [MeasureSpace G]
    [Group H] [TopologicalSpace H] [MeasureSpace H] [MeasurableMul G] [MeasurableMul H]
    [(volume : Measure G).IsHaarMeasure] [(volume : Measure H).IsHaarMeasure]
    [SFinite (volume : Measure H)] : (volume : Measure (G × H)).IsHaarMeasure :=
  by rw [volume_eq_prod]; infer_instance

end TauCeti

end
