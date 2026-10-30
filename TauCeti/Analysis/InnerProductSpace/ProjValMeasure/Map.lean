/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic

/-!
# Measurable reindexing of projection-valued measures

A measurable map `f : X → Y` transports a projection-valued measure on `X` to one on `Y`:
the projection of a measurable set `B` is the original projection of its preimage under `f`.
The diagonal scalar measures are the corresponding pushforward measures.

Identity and composition of measurable maps are respected by this construction.

The underlying projection-valued measure and its diagonal-measure representation come from
`TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic`, adapted from the Kitware DKPS
formalization and the Spectra formalization; see that module for source references.
-/

public section

open MeasureTheory

namespace TauCeti.ProjValMeasure

variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]
variable {Z : Type*} [MeasurableSpace Z]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Push a projection-valued measure forward along a measurable map. -/
noncomputable def map (P : ProjValMeasure X H) (f : X → Y) (hf : Measurable f) :
    ProjValMeasure Y H where
  proj B hB := P.proj (f ⁻¹' B) (hf hB)
  diag ξ := Measure.map f (P.diag ξ)
  diag_finite _ := inferInstance
  inner_proj B hB ξ := by
    simpa only [Measure.map_apply hf hB] using
      P.inner_proj (f ⁻¹' B) (hf hB) ξ
  proj_univ := by
    simpa only [Set.preimage_univ] using P.proj_univ
  proj_inter B C hB hC := by
    simpa only [Set.preimage_inter] using
      P.proj_inter (f ⁻¹' B) (f ⁻¹' C) (hf hB) (hf hC)

/-- Evaluating the transported PVM on a measurable set is evaluating its preimage. -/
@[simp]
theorem map_proj (P : ProjValMeasure X H) (f : X → Y) (hf : Measurable f)
    (B : Set Y) (hB : MeasurableSet B) :
    (P.map f hf).proj B hB = P.proj (f ⁻¹' B) (hf hB) :=
  (rfl)

/-- Diagonal scalar measures are pushed forward by the same measurable map. -/
@[simp]
theorem map_diag (P : ProjValMeasure X H) (f : X → Y) (hf : Measurable f) (ξ : H) :
    (P.map f hf).diag ξ = Measure.map f (P.diag ξ) :=
  (rfl)

/-- Transport along the identity measurable map leaves the PVM unchanged. -/
@[simp]
theorem map_id (P : ProjValMeasure X H) :
    P.map (id : X → X) measurable_id = P := by
  apply ProjValMeasure.ext
  intro B hB
  simp only [map_proj, Set.preimage_id]

/-- Transport along two measurable maps equals transport along their composition. -/
@[simp]
theorem map_map (P : ProjValMeasure X H) (f : X → Y) (g : Y → Z)
    (hf : Measurable f) (hg : Measurable g) :
    (P.map f hf).map g hg = P.map (g ∘ f) (hg.comp hf) := by
  apply ProjValMeasure.ext
  intro B hB
  simp only [map_proj, Set.preimage_comp]

end TauCeti.ProjValMeasure
