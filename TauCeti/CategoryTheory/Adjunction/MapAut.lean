/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import TauCeti.CategoryTheory.Aut.Basic

/-!
# Automorphisms of a functor precomposed with a right adjoint

Let `E ⊣ P` be an adjunction with `P : D ⥤ C` whose unit `𝟭 C ⟶ E ⋙ P` is an isomorphism, so
that `E` is fully faithful. Whiskering gives the adjunction `adj.whiskerLeft K` between
precomposition with `P` and precomposition with `E`, whose unit is again an isomorphism. So
precomposition with `P` is fully faithful, and for every functor `F : C ⥤ K` it is an isomorphism
of automorphism groups `Aut F ≃* Aut (P ⋙ F)`. Its inverse precomposes with `E` and conjugates by
the isomorphism `F ≅ E ⋙ P ⋙ F` given by the unit of `adj.whiskerLeft K` at `F`.

The main application is to étale fundamental groups: for a finite étale monomorphism `g`, such as
the inclusion of a clopen subscheme, base change along `g` has the fully faithful left adjoint
"composition with `g`", so it induces an isomorphism of fundamental groups.

## Main definitions

* `CategoryTheory.Adjunction.mapAutWhiskeringLeftEquiv adj F`: the isomorphism
  `Aut F ≃* Aut (P ⋙ F)`, which is precomposition with `P`.

## Main results

* `CategoryTheory.Adjunction.mapAutWhiskeringLeftEquiv_symm_apply`: its inverse is precomposition
  with `E` followed by conjugation by `F ≅ E ⋙ P ⋙ F`.
* `CategoryTheory.Adjunction.mapAut_whiskeringLeft_bijective`: precomposition with `P` is
  bijective on automorphism groups.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

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

/-- If the unit of `E ⊣ P` is an isomorphism, so is the unit of the whiskered adjunction between
precomposition with `P` and precomposition with `E`. -/
instance isIso_whiskerLeft_unit : IsIso (adj.whiskerLeft K).unit := by
  have (F : C ⥤ K) : IsIso ((adj.whiskerLeft K).unit.app F) := by
    have (X : C) : IsIso (((adj.whiskerLeft K).unit.app F).app X) := by
      rw [whiskerLeft_unit_app_app]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- **Precomposition with a right adjoint with invertible unit is an isomorphism of
automorphism groups.** For an adjunction `E ⊣ P` whose unit is an isomorphism, precomposition with
`P` is fully faithful, so it is an isomorphism `Aut F ≃* Aut (P ⋙ F)`. -/
noncomputable def mapAutWhiskeringLeftEquiv : Aut F ≃* Aut (P ⋙ F) :=
  (adj.whiskerLeft K).fullyFaithfulLOfIsIsoUnit.autMulEquivOfFullyFaithful F

/-- The isomorphism `mapAutWhiskeringLeftEquiv adj F` is precomposition with `P`. -/
@[simp]
lemma mapAutWhiskeringLeftEquiv_apply (σ : Aut F) :
    adj.mapAutWhiskeringLeftEquiv F σ = ((Functor.whiskeringLeft D C K).obj P).mapAut F σ :=
  (rfl)

/-- The inverse of `mapAutWhiskeringLeftEquiv adj F` is precomposition with `E` followed by
conjugation by the isomorphism `F ≅ E ⋙ P ⋙ F` given by the unit of `adj.whiskerLeft K`. -/
@[simp]
lemma mapAutWhiskeringLeftEquiv_symm_apply (τ : Aut (P ⋙ F)) :
    (adj.mapAutWhiskeringLeftEquiv F).symm τ = (asIso ((adj.whiskerLeft K).unit.app F)).symm.conjAut
      (((Functor.whiskeringLeft C D K).obj E).mapAut (P ⋙ F) τ) := by
  -- It is a right inverse because `P` sends the counit at `Y` to the inverse of the unit at
  -- `P.obj Y`.
  rw [MulEquiv.symm_apply_eq]
  refine Aut.ext (Iso.ext (NatTrans.ext (funext fun Y ↦ ?_)))
  have h := τ.asIso.hom.naturality (adj.counit.app Y)
  simp only [Functor.comp_obj, Functor.comp_map] at h
  rw [mapAutWhiskeringLeftEquiv_apply, Functor.mapAut_whiskeringLeft_asIso_hom_app]
  simp only [Iso.conjAut_apply, Iso.symm_symm_eq, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, asIso_hom, asIso_inv, NatIso.isIso_inv_app, whiskerLeft_unit_app_app]
  rw [Functor.mapAut_whiskeringLeft_asIso_hom_app, ← Functor.map_inv,
    IsIso.inv_eq_of_hom_inv_id (adj.right_triangle_components Y), ← h,
    ← F.map_comp_assoc, adj.right_triangle_components]
  simp

include adj in
/-- For an adjunction `E ⊣ P` with invertible unit, precomposition with `P` is bijective on
automorphism groups: `Aut F → Aut (P ⋙ F)`. -/
theorem mapAut_whiskeringLeft_bijective :
    Function.Bijective (((Functor.whiskeringLeft D C K).obj P).mapAut F) :=
  (adj.mapAutWhiskeringLeftEquiv F).bijective

end Adjunction

end CategoryTheory
