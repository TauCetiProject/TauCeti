/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Whiskering

/-!
# Automorphisms of a functor precomposed with a right adjoint

Let `E ⊣ P` be an adjunction with `P : D ⥤ C` whose unit `𝟭 C ⟶ E ⋙ P` is an isomorphism, so
that `E` is fully faithful. For every functor `F : C ⥤ K`, precomposition with `P` is then an
isomorphism of automorphism groups `Aut F ≃* Aut (P ⋙ F)`. Its inverse precomposes with `E` and
conjugates by the isomorphism `F ≅ E ⋙ P ⋙ F` induced by the unit.

The inverse is a left inverse because automorphisms of `F` are natural with respect to the unit,
and a right inverse because automorphisms of `P ⋙ F` are natural with respect to the counit and
`P` carries the counit at `Y` to the inverse of the unit at `P.obj Y` (a triangle identity).

The main application is to étale fundamental groups: for a finite étale monomorphism `g`, such as
the inclusion of a clopen subscheme, base change along `g` has the fully faithful left adjoint
"composition with `g`", so it induces an isomorphism of fundamental groups.

## Main definitions

* `CategoryTheory.Adjunction.unitWhiskerIso adj F`: the isomorphism `F ≅ E ⋙ P ⋙ F` induced by
  an invertible unit.
* `CategoryTheory.Adjunction.mapAutWhiskeringLeftEquiv adj F`: the isomorphism
  `Aut F ≃* Aut (P ⋙ F)`, which is precomposition with `P`.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

/-- The inverse of conjugation by `α` on automorphism groups is conjugation by `α.symm`. -/
lemma Iso.conjAut_symm_apply {C : Type u₁} [Category.{v₁} C] {X Y : C} (α : X ≅ Y)
    (f : Aut Y) : α.conjAut.symm f = α.symm.conjAut f := by
  rw [MulEquiv.symm_apply_eq]
  ext1
  simp [Iso.conjAut_apply]

/-- The components of the automorphism of `P ⋙ F` obtained from an automorphism `σ` of `F` by
precomposition with `P` are those of `σ` at the objects `P.obj X`. Not `@[simp]`: its
left-hand side is not in simp normal form, and simp does not rewrite through `mapAut`. -/
lemma Functor.mapAut_whiskeringLeft_asIso_hom_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {K : Type u₃} [Category.{v₃} K] (P : D ⥤ C) (F : C ⥤ K) (σ : Aut F)
    (X : D) :
    ((Functor.mapAut F ((Functor.whiskeringLeft D C K).obj P)) σ).asIso.hom.app X =
      σ.asIso.hom.app (P.obj X) := by
  rw [Functor.mapAut_apply_asIso]
  simp

namespace Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {K : Type u₃} [Category.{v₃} K] {E : C ⥤ D} {P : D ⥤ C} (adj : E ⊣ P) [IsIso adj.unit]
  (F : C ⥤ K)

/-- For an adjunction `E ⊣ P` with invertible unit, the isomorphism `F ≅ E ⋙ P ⋙ F` obtained by
whiskering the unit with `F`. -/
noncomputable def unitWhiskerIso : F ≅ E ⋙ P ⋙ F :=
  (Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight (asIso adj.unit) F ≪≫
    Functor.associator E P F

/-- The components of `unitWhiskerIso adj F` are `F` applied to the unit. -/
@[simp]
lemma unitWhiskerIso_hom_app (X : C) :
    (adj.unitWhiskerIso F).hom.app X = F.map (adj.unit.app X) := by
  simp [unitWhiskerIso]

/-- The components of the inverse of `unitWhiskerIso adj F` are `F` applied to the inverse of
the unit. -/
@[simp]
lemma unitWhiskerIso_inv_app (X : C) :
    (adj.unitWhiskerIso F).inv.app X = F.map (inv (adj.unit.app X)) := by
  simp [unitWhiskerIso]

/-- **Precomposition with a right adjoint with invertible unit is an isomorphism of
automorphism groups.** For an adjunction `E ⊣ P` whose unit is an isomorphism, precomposition with
`P` is an isomorphism `Aut F ≃* Aut (P ⋙ F)`. The inverse precomposes with `E` and conjugates
by `F ≅ E ⋙ P ⋙ F`. -/
noncomputable def mapAutWhiskeringLeftEquiv : Aut F ≃* Aut (P ⋙ F) where
  toFun := ((Functor.whiskeringLeft D C K).obj P).mapAut F
  invFun τ := (adj.unitWhiskerIso F).symm.conjAut
    (((Functor.whiskeringLeft C D K).obj E).mapAut (P ⋙ F) τ)
  left_inv σ := by
    refine Aut.ext (Iso.ext (NatTrans.ext (funext fun X ↦ ?_)))
    simp only [Iso.conjAut_apply, Iso.symm_symm_eq, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app]
    rw [Functor.mapAut_whiskeringLeft_asIso_hom_app, Functor.mapAut_whiskeringLeft_asIso_hom_app]
    simp
  right_inv τ := by
    refine Aut.ext (Iso.ext (NatTrans.ext (funext fun Y ↦ ?_)))
    have h := τ.asIso.hom.naturality (adj.counit.app Y)
    simp only [Functor.comp_obj, Functor.comp_map] at h
    rw [Functor.mapAut_whiskeringLeft_asIso_hom_app]
    simp only [Iso.conjAut_apply, Iso.symm_symm_eq, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app]
    rw [Functor.mapAut_whiskeringLeft_asIso_hom_app, unitWhiskerIso_hom_app, unitWhiskerIso_inv_app,
      IsIso.inv_eq_of_hom_inv_id (adj.right_triangle_components Y), ← h,
      ← F.map_comp_assoc, adj.right_triangle_components]
    simp
  map_mul' := map_mul _

/-- The isomorphism `mapAutWhiskeringLeftEquiv adj F` is precomposition with `P`. -/
@[simp]
lemma mapAutWhiskeringLeftEquiv_apply (σ : Aut F) :
    adj.mapAutWhiskeringLeftEquiv F σ = ((Functor.whiskeringLeft D C K).obj P).mapAut F σ :=
  (rfl)

/-- The inverse of `mapAutWhiskeringLeftEquiv adj F` is precomposition with `E` followed by
conjugation by `F ≅ E ⋙ P ⋙ F`. -/
lemma mapAutWhiskeringLeftEquiv_symm_apply (τ : Aut (P ⋙ F)) :
    (adj.mapAutWhiskeringLeftEquiv F).symm τ = (adj.unitWhiskerIso F).symm.conjAut
      (((Functor.whiskeringLeft C D K).obj E).mapAut (P ⋙ F) τ) :=
  (rfl)

include adj in
/-- For an adjunction `E ⊣ P` with invertible unit, precomposition with `P` is bijective on
automorphism groups: `Aut F → Aut (P ⋙ F)`. -/
theorem mapAut_whiskeringLeft_bijective :
    Function.Bijective (((Functor.whiskeringLeft D C K).obj P).mapAut F) :=
  (adj.mapAutWhiskeringLeftEquiv F).bijective

end Adjunction

end CategoryTheory
