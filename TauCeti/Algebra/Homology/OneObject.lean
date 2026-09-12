/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# One-object homological complexes

A square-zero endomorphism of an object in a category with zero morphisms determines a
homological complex indexed by `Unit`, using the circular shape `ComplexShape.refl Unit`. This
file provides that construction and records its unique object and differential.

## Main definitions

* `TauCeti.oneObjectHomologicalComplex`: the homological complex associated to a square-zero
  endomorphism.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe u v

/-- The one-object homological complex associated to a square-zero endomorphism. -/
@[expose] def oneObjectHomologicalComplex {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X : C) (d : X ⟶ X) (d_comp_d : d ≫ d = 0) :
    HomologicalComplex C (ComplexShape.refl Unit) where
  X _ := X
  d _ _ := d
  d_comp_d' _ _ _ _ _ := d_comp_d

/-- The unique object of the one-object homological complex is its defining object. -/
@[simp]
theorem oneObjectHomologicalComplex_X {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X : C) (d : X ⟶ X) (d_comp_d : d ≫ d = 0) (i : Unit) :
    (oneObjectHomologicalComplex X d d_comp_d).X i = X :=
  rfl

/-- The unique differential of the one-object homological complex is its defining endomorphism,
transported across the canonical object equation. -/
@[simp]
theorem oneObjectHomologicalComplex_d {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X : C) (d : X ⟶ X) (d_comp_d : d ≫ d = 0) :
    (oneObjectHomologicalComplex X d d_comp_d).d () () =
      eqToHom (oneObjectHomologicalComplex_X X d d_comp_d ()) ≫ d ≫
        eqToHom (oneObjectHomologicalComplex_X X d d_comp_d ()).symm := by
  have h : oneObjectHomologicalComplex_X X d d_comp_d () = rfl :=
    Subsingleton.elim _ _
  rw [h]
  unfold oneObjectHomologicalComplex
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end TauCeti
