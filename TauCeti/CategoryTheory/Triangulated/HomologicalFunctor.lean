/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Composition of homological functors with homology-preserving functors

Postcomposing a homological functor `E : C ⥤ A` from a pretriangulated category to an abelian
category with a functor `G : A ⥤ B` preserving zero morphisms and homology yields a homological
functor `E ⋙ G : C ⥤ B`.

## Main results

* `CategoryTheory.Functor.instIsHomologicalComp`: `(E ⋙ G).IsHomological`.
-/

public section

namespace CategoryTheory.Functor

open CategoryTheory Pretriangulated Limits

/-- Postcomposing a homological functor with a functor preserving zero morphisms and homology
yields a homological functor. -/
instance instIsHomologicalComp {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B] [Abelian B]
    (E : C ⥤ A) [E.IsHomological] (G : A ⥤ B) [G.PreservesZeroMorphisms] [G.PreservesHomology] :
    (E ⋙ G).IsHomological where
  exact s hs := by
    simpa only [ShortComplex.map_comp] using (E.map_distinguished_exact s hs).map G

end CategoryTheory.Functor
