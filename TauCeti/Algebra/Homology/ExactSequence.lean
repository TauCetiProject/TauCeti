/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exact sequences under functors

A functor which preserves zero morphisms and homology sends an exact sequence of composable arrows
to an exact sequence (`CategoryTheory.ComposableArrows.Exact.map`), extending Mathlib's
`CategoryTheory.ShortComplex.Exact.map` from short complexes to the sequences of
`Mathlib.Algebra.Homology.ExactSequence`.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.ComposableArrows

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A functor which preserves zero morphisms and homology sends an exact sequence of composable
arrows to an exact sequence. -/
lemma Exact.map {n : ℕ} {S : ComposableArrows C n} (hS : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesHomology] :
    ((F.mapComposableArrows n).obj S).Exact where
  zero i hi := by
    simpa only [Functor.mapComposableArrows_obj_map, Functor.map_comp, F.map_zero] using
      congrArg F.map (hS.zero i hi)
  exact i hi := (hS.exact i hi).map F

end CategoryTheory.ComposableArrows
