/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Algebra.Group.Units
import TauCeti.Topology.Algebra.Group.Units

/-!
# Connectedness in the unit groups of archimedean completions

Let `w` be an infinite place of a number field `K`.  The completion `w.Completion` is isometric to
`ℝ` when `w` is real and to `ℂ` when `w` is complex.  Consequently the unit group `w.Completionˣ`
is connected at a complex place, being homeomorphic to `ℂˣ`, while at a real place the units of
positive real part form a preconnected set, homeomorphic to the positive half-line.

These are the archimedean inputs to the description of the open subgroups of the idele class
group: an open subgroup is also closed, so it contains every connected set of ideles through the
identity, and in particular the whole unit group at each complex place and the positive units at
each real place.

## Main results

* `NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex_apply` and
  `NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal_apply`: the isometries of a
  completion with `ℂ` and with `ℝ` evaluate to the extension embeddings.
* `NumberField.InfinitePlace.Completion.continuousMulEquivComplexOfIsComplex`: the continuous
  multiplicative isomorphism `w.Completion ≃ₜ* ℂ` of a complex place.
* `NumberField.InfinitePlace.Completion.connectedSpace_units_of_isComplex`: the unit group of a
  complex completion is connected.
* `NumberField.InfinitePlace.Completion.isPreconnected_setOf_extensionEmbeddingOfIsReal_pos`: the
  positive units of a real completion form a preconnected set.
-/

public section

namespace NumberField.InfinitePlace.Completion

variable {K : Type*} [Field K] {w : InfinitePlace K}

/-- The isometry `w.Completion ≃ᵢ ℂ` of a complex place evaluates to the extension embedding.
This records the definition of `isometryEquivComplexOfIsComplex`, whose underlying equivalence is
`ringEquivComplexOfIsComplex hw`. -/
@[simp]
theorem isometryEquivComplexOfIsComplex_apply (hw : w.IsComplex) (x : w.Completion) :
    isometryEquivComplexOfIsComplex hw x = extensionEmbedding w x := rfl

/-- The isometry `w.Completion ≃ᵢ ℝ` of a real place evaluates to the real extension embedding.
This records the definition of `isometryEquivRealOfIsReal`, whose underlying equivalence is
`ringEquivRealOfIsReal hw`. -/
@[simp]
theorem isometryEquivRealOfIsReal_apply (hw : w.IsReal) (x : w.Completion) :
    isometryEquivRealOfIsReal hw x = extensionEmbeddingOfIsReal hw x := rfl

/-- The continuous multiplicative isomorphism `w.Completion ≃ₜ* ℂ` of a complex place.  Its
underlying map is the ring isomorphism `ringEquivComplexOfIsComplex hw`, which respects open sets
because it is the isometry `isometryEquivComplexOfIsComplex hw`. -/
noncomputable def continuousMulEquivComplexOfIsComplex (hw : w.IsComplex) : w.Completion ≃ₜ* ℂ :=
  (ringEquivComplexOfIsComplex hw).toMulEquiv.toContinuousMulEquiv fun _ ↦
    (isometryEquivComplexOfIsComplex hw).toHomeomorph.isOpen_preimage

/-- The continuous multiplicative isomorphism `w.Completion ≃ₜ* ℂ` of a complex place evaluates
to the extension embedding. -/
@[simp]
theorem continuousMulEquivComplexOfIsComplex_apply (hw : w.IsComplex) (x : w.Completion) :
    continuousMulEquivComplexOfIsComplex hw x = extensionEmbedding w x := (rfl)

/-- **The unit group of a complex completion is connected**: it is homeomorphic to `ℂˣ` through
`continuousMulEquivComplexOfIsComplex hw`. -/
theorem connectedSpace_units_of_isComplex (hw : w.IsComplex) : ConnectedSpace w.Completionˣ :=
  (Units.mapContinuousMulEquiv
    (continuousMulEquivComplexOfIsComplex hw)).toHomeomorph.connectedSpace_iff.mpr inferInstance

/-- **The positive units of a real completion form a preconnected set**: they are homeomorphic to
the positive real half-line. -/
theorem isPreconnected_setOf_extensionEmbeddingOfIsReal_pos (hw : w.IsReal) :
    IsPreconnected {u : w.Completionˣ | 0 < extensionEmbeddingOfIsReal hw u} := by
  have h := (isometryEquivRealOfIsReal hw).toHomeomorph.isPreconnected_preimage.mpr
    (isPreconnected_Ioi (a := (0 : ℝ)))
  rw [IsometryEquiv.coe_toHomeomorph] at h
  have hset : {u : w.Completionˣ | 0 < extensionEmbeddingOfIsReal hw u} =
      Units.val ⁻¹' ((isometryEquivRealOfIsReal hw) ⁻¹' Set.Ioi 0) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, isometryEquivRealOfIsReal_apply]
  rw [hset]
  exact IsPreconnected.preimage_units_val h (by simp)

end NumberField.InfinitePlace.Completion
