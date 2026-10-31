/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Prelax functors out of locally discrete bicategories

In a locally discrete bicategory every `2`-morphism `η : f ⟶ g` forces `f = g`, so a prelax
functor (in particular a pseudofunctor) sends `η` to an `eqToHom`. This lets the coherence
data of a pseudofunctor out of `LocallyDiscrete B₀`, such as `F.map₂ (α_ f g h).hom`, be
computed componentwise.
-/

@[expose] public section

namespace CategoryTheory.PrelaxFunctor

open Bicategory

/-- A prelax functor out of a locally discrete bicategory sends every `2`-morphism to an
`eqToHom`. -/
lemma map₂_eq_eqToHom {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (F : PrelaxFunctor B C) {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    F.map₂ η = eqToHom (by rw [obj_ext_of_isDiscrete η]) := by
  obtain rfl := obj_ext_of_isDiscrete η
  rw [Subsingleton.elim η (𝟙 f)]
  simp

/-- A prelax functor out of a locally discrete bicategory sends a composite of two `2`-morphisms
to the image of any `2`-morphism with the same source and target. -/
@[reassoc]
lemma map₂_comp_map₂ {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (F : PrelaxFunctor B C) {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (ι : f ⟶ h) :
    F.map₂ η ≫ F.map₂ θ = F.map₂ ι := by
  simp [map₂_eq_eqToHom]

end CategoryTheory.PrelaxFunctor
