/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Effective epimorphisms and Yoneda evaluation in subcanonical sites

In a subcanonical Grothendieck site `(C, J)`, every representable presheaf
`CategoryTheory.yoneda.obj W` is a `J`-sheaf. Consequently, any morphism `f : U ⟶ V` whose
singleton generates a `J`-covering sieve on `V` is an effective epimorphism
(`CategoryTheory.GrothendieckTopology.effectiveEpi_of_generate_singleton_mem`), and evaluating
`J.yoneda.map g` on a section `f` postcomposes `f` with `g`
(`CategoryTheory.GrothendieckTopology.yoneda_map_hom_app_apply`).
-/

public section

open CategoryTheory

namespace CategoryTheory.GrothendieckTopology

/-- In a subcanonical site, a morphism whose singleton generates a covering sieve is an effective
epimorphism. -/
theorem effectiveEpi_of_generate_singleton_mem {C : Type*} [Category* C]
    (J : GrothendieckTopology C) [J.Subcanonical] {U V : C} (f : U ⟶ V)
    (hf : Sieve.generate (.singleton f) ∈ J V) : EffectiveEpi f := by
  refine (Sieve.effectiveEpimorphic_singleton f).mp
    ((Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda _).mpr fun W ↦ ?_)
  rw [Presieve.isSheafFor_iff_generate]
  exact (Subcanonical.isSheaf_of_isRepresentable (J := J) (CategoryTheory.yoneda.obj W))
    (Sieve.generate (.singleton f)) hf

/-- Evaluating the sheaf Yoneda morphism `J.yoneda.map g` on a section `f : W.unop ⟶ X`
postcomposes `f` with `g`. -/
@[simp]
lemma yoneda_map_hom_app_apply {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [J.Subcanonical] {X Y : C} (g : X ⟶ Y) (W : Cᵒᵖ) (f : W.unop ⟶ X) :
    ((J.yoneda.map g).hom.app W) f = f ≫ g := by
  simp

end CategoryTheory.GrothendieckTopology
