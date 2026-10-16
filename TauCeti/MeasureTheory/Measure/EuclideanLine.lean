/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Coordinate volume on a Euclidean line

The unique-coordinate projection identifies the existing Euclidean and real volume measures.
This follows from Mathlib's Euclidean-to-product normalization and product measure in one slot.
-/

public section

namespace TauCeti

open MeasureTheory EuclideanSpace

/-- Projection onto the unique coordinate of a Euclidean line preserves actual volume. -/
theorem volume_preserving_euclideanSpace_proj {ι : Type*} [hι : Fintype ι] [Unique ι] (i : ι) :
    MeasurePreserving (proj (𝕜 := ℝ) i) volume volume := by
  have he : hι = Unique.fintype := Subsingleton.elim _ _
  cases he
  have hm := (volume_preserving_funUnique ι ℝ).comp (PiLp.volume_preserving_ofLp ι)
  convert hm using 1
  funext z
  exact congrArg (fun j ↦ z j) (Subsingleton.elim i default)

/-- The unique-coordinate projection is a measurable embedding, so normalized volume
transport also applies to arbitrary restricted integrals. -/
theorem measurableEmbedding_euclideanSpace_proj {ι : Type*} [Unique ι] (i : ι) :
    MeasurableEmbedding (proj (𝕜 := ℝ) i) := by
  have hm := (PiLp.equivOfUnique 2 ℝ (fun _ : ι ↦ ℝ)).toHomeomorph.isClosedEmbedding
    |>.measurableEmbedding
  convert hm using 1
  funext z
  exact congrArg (fun j ↦ z j) (Subsingleton.elim i default)

end TauCeti
