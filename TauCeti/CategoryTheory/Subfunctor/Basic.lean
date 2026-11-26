/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The distributive lattice of subfunctors, and restriction along a functor

The subfunctors of a functor `F : C ⥤ Type w` form a distributive lattice, since their suprema
and infima are computed objectwise as unions and intersections of sets.

A subfunctor `U` of `F` restricts along a functor `φ : C' ⥤ C` to the subfunctor
`CategoryTheory.Subfunctor.whiskerLeft φ U` of `φ ⋙ F`, with values `U(φ c')`.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Etale/Basic.lean` (declaration `CategoryTheory.Subfunctor.whisker`); Apache
  2.0, Copyright 2026 Anthropic, PBC. `CategoryTheory.Subfunctor.whiskerLeft` is adapted from it.
-/

public section

namespace CategoryTheory.Subfunctor

variable {C : Type*} [Category* C] {F : C ⥤ Type*}

/-- The subfunctors of a functor form a distributive lattice: suprema and infima are computed
objectwise as unions and intersections. -/
instance instDistribLattice : DistribLattice (Subfunctor F) :=
  DistribLattice.ofInfSupLe fun _ _ _ _ ↦ (inf_sup_left (α := Set _) _ _ _).le

/-- The restriction of a subfunctor `U` of `F` along `φ : C' ⥤ C`, as a subfunctor of `φ ⋙ F`. -/
def whiskerLeft {C' : Type*} [Category* C'] (φ : C' ⥤ C) (U : Subfunctor F) :
    Subfunctor (φ ⋙ F) where
  obj A := U.obj (φ.obj A)
  map f := U.map (φ.map f)

/-- The values of a restricted subfunctor are those of the original one. -/
@[simp]
lemma whiskerLeft_obj {C' : Type*} [Category* C'] (φ : C' ⥤ C) (U : Subfunctor F) (A : C') :
    (U.whiskerLeft φ).obj A = U.obj (φ.obj A) :=
  (rfl)

/-- An element lies in the restricted subfunctor exactly when it lies in the original one. -/
lemma mem_whiskerLeft_obj_iff {C' : Type*} [Category* C'] (φ : C' ⥤ C) (U : Subfunctor F)
    {A : C'} (x : F.obj (φ.obj A)) : x ∈ (U.whiskerLeft φ).obj A ↔ x ∈ U.obj (φ.obj A) :=
  Iff.rfl

end CategoryTheory.Subfunctor
