/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor

/-!
# Reindexing Čech complexes across universes

An equivalence of indexing types identifies the tuple Čech complexes of the corresponding
families. The coefficient objects and the site are unchanged.
-/

public noncomputable section

open CategoryTheory Limits Opposite

universe w₁ w₂ w₃ v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A]

variable [HasProducts.{w₁} A] [HasProducts.{w₂} A]
  {ι : Type w₁} {κ : Type w₂} (e : ι ≃ κ) (U : κ → C) (P : Cᵒᵖ ⥤ A)

/-- Reindex the product of sections indexed by tuples of members of a family. -/
private def cechReindexXIso (n : ℕ) :
    ((cechComplexFunctor (U ∘ e)).obj P).X n ≅ ((cechComplexFunctor U).obj P).X n :=
  cechXIso (U ∘ e) P n ≪≫
    Pi.reindex (Equiv.piCongrRight fun _ : Fin (n + 1) ↦ e)
    (fun a : Fin (n + 1) → κ ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))))
    ≪≫ (cechXIso U P n).symm

@[reassoc]
private lemma cechReindexXIso_hom_π (n : ℕ) (a : Fin (n + 1) → ι) :
    (cechReindexXIso e U P n).hom ≫ (cechXIso U P n).hom ≫ Pi.π _ (e ∘ a) =
      (cechXIso (U ∘ e) P n).hom ≫ Pi.π _ a := by
  -- Normalize the three defining iso components before applying the public product API.
  change ((cechXIso (U ∘ e) P n).hom ≫
      (Pi.reindex (Equiv.piCongrRight fun _ : Fin (n + 1) ↦ e)
        (fun b : Fin (n + 1) → κ ↦ P.obj (op (∏ᶜ fun j ↦ U (b j))))).hom ≫
      (cechXIso U P n).inv) ≫ (cechXIso U P n).hom ≫ Pi.π _ (e ∘ a) = _
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg ((cechXIso (U ∘ e) P n).hom ≫ ·) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact ((Pi.reindex _ _).hom ≫= (cechXIso U P n).inv_hom_id_assoc _).trans
    (Pi.reindex_hom_π _ _ a)

private lemma cechReindexXIso_hom_comp_d (n : ℕ) :
    (cechReindexXIso e U P n).hom ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      ((cechComplexFunctor (U ∘ e)).obj P).d n (n + 1) ≫
        (cechReindexXIso e U P (n + 1)).hom := by
  apply (cancel_mono (cechXIso U P (n + 1)).hom).mp
  refine Pi.hom_ext _ _ fun b ↦ ?_
  obtain ⟨a, rfl⟩ := (Equiv.piCongrRight fun _ : Fin (n + 2) ↦ e).surjective b
  -- FormalCoproduct.cech/rightOp hides this dependent tuple index at implicit transparency.
  change _ ≫ Pi.π _ (e ∘ a) = _ ≫ Pi.π _ (e ∘ a)
  simp only [Category.assoc, cechComplexFunctor_obj_d_comp_cechXIso_hom_π, Preadditive.comp_sum,
    Preadditive.comp_zsmul, cechReindexXIso_hom_π]
  refine Finset.sum_congr rfl fun m _ ↦ congrArg ((-1 : ℤ) ^ (m : ℕ) • ·) ?_
  exact cechReindexXIso_hom_π_assoc e U P n (a ∘ m.succAbove) _

/-- An equivalence of indexing types identifies the actual tuple Čech complexes, including
when the indexing types belong to different universes. -/
private def cechReindexObjIso :
    (cechComplexFunctor (U ∘ e)).obj P ≅ (cechComplexFunctor U).obj P :=
  HomologicalComplex.Hom.isoOfComponents (cechReindexXIso e U P)
    (fun n _ h ↦ by
      obtain rfl : n + 1 = _ := h
      exact cechReindexXIso_hom_comp_d e U P n)

/-- On a tuple the reindexing isomorphism reads the same section. -/
@[reassoc]
private theorem cechReindexObjIso_hom_f_π (n : ℕ) (a : Fin (n + 1) → ι) :
    (cechReindexObjIso e U P).hom.f n ≫ Pi.π _ (e ∘ a) = Pi.π _ a :=
  by
    dsimp only [cechReindexObjIso, HomologicalComplex.Hom.isoOfComponents_hom_f]
    -- The two native projection laws retain the dependent product codomains as terms.
    exact (_ ≫= (cechXIso_hom_π U P n (e ∘ a)).symm).trans
      ((cechReindexXIso_hom_π e U P n a).trans (cechXIso_hom_π (U ∘ e) P n a))

private lemma cechReindexObjIso_hom_naturality {Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) :
    (cechComplexFunctor (U ∘ e)).map φ ≫ (cechReindexObjIso e U Q).hom =
      (cechReindexObjIso e U P).hom ≫ (cechComplexFunctor U).map φ := by
  ext n : 2
  simp only [HomologicalComplex.comp_f]
  dsimp only [cechReindexObjIso, HomologicalComplex.Hom.isoOfComponents_hom_f]
  apply (cancel_mono (cechXIso U Q n).hom).mp
  refine Pi.hom_ext _ _ fun b ↦ ?_
  obtain ⟨a, rfl⟩ := (Equiv.piCongrRight fun _ : Fin (n + 1) ↦ e).surjective b
  -- Normalize the dependent native Čech tuple index before rewriting product readings.
  change _ ≫ Pi.π (fun b : Fin (n + 1) → κ ↦ Q.obj (op (∏ᶜ fun j ↦ U (b j))))
    (e ∘ a) = _
  simp only [Category.assoc, cechReindexXIso_hom_π, cechComplexFunctor_map_f_comp_cechXIso_hom_π]
  exact (cechReindexXIso_hom_π_assoc e U P n a _).symm

/-- Reindexing a family identifies its Čech complex functor, naturally in the presheaf. -/
def cechComplexReindexIso :
    cechComplexFunctor.{w₁} (A := A) (U ∘ e) ≅ cechComplexFunctor.{w₂} U :=
  NatIso.ofComponents (fun P ↦ cechReindexObjIso e U P)
    (fun φ ↦ cechReindexObjIso_hom_naturality e U _ φ)

/-- The component of the natural reindexing isomorphism preserves each tuple reading. -/
@[reassoc]
theorem cechComplexReindexIso_hom_app_f_π (n : ℕ) (a : Fin (n + 1) → ι) :
    ((cechComplexReindexIso e U).hom.app P).f n ≫ Pi.π _ (e ∘ a) = Pi.π _ a :=
  cechReindexObjIso_hom_f_π e U P n a

/-- The inverse reindexing isomorphism reads the tuple with inverse-transformed indices. -/
@[reassoc]
theorem cechComplexReindexIso_inv_app_f_π (n : ℕ) (a : Fin (n + 1) → ι) :
    ((cechComplexReindexIso e U).inv.app P).f n ≫ Pi.π _ a = Pi.π _ (e ∘ a) := by
  let j := (HomologicalComplex.eval A (ComplexShape.up ℕ) n).mapIso
    ((cechComplexReindexIso e U).app P)
  have h := j.inv ≫= cechComplexReindexIso_hom_app_f_π e U P n a
  exact h.symm.trans (j.inv_hom_id_assoc _)

/-- Reindexing preserves the native augmentation from sections on a terminal object. -/
@[reassoc]
theorem cechAugmentation_comp_cechComplexReindexIso [HasZeroObject A] {T : C} (hT : IsTerminal T) :
    cechAugmentation (U ∘ e) hT P ≫ (cechComplexReindexIso e U).hom.app P =
      cechAugmentation U hT P := by
  refine HomologicalComplex.from_single_hom_ext (Pi.hom_ext _ _ fun b ↦ ?_)
  obtain ⟨a, rfl⟩ := (Equiv.piCongrRight fun _ : Fin 1 ↦ e).surjective b
  simp only [HomologicalComplex.comp_f]
  erw [Category.assoc, cechComplexReindexIso_hom_app_f_π,
    cechAugmentation_f_zero_comp_π, cechAugmentation_f_zero_comp_π]
  -- The residual indices are the toFun field of piCongrRight, namely Pi.map of e.
  rfl

omit [HasProducts.{w₂} A] in
/-- Reindexing by the identity equivalence is the identity of the native complex functor. -/
@[simp]
theorem cechComplexReindexIso_refl (V : ι → C) :
    cechComplexReindexIso (A := A) (Equiv.refl ι) V = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  ext n : 2
  apply Pi.hom_ext
  intro a
  exact (cechComplexReindexIso_hom_app_f_π (Equiv.refl ι) V Q n a).trans
    (Category.id_comp _).symm

variable [HasProducts.{w₃} A] {τ : Type w₃}

/-- Successive changes of index agree with their composite, on the actual complex functor. -/
theorem cechComplexReindexIso_trans (f : ι ≃ κ) (g : κ ≃ τ) (V : τ → C) :
    cechComplexReindexIso (A := A) (f.trans g) V =
      cechComplexReindexIso f (V ∘ g) ≪≫ cechComplexReindexIso g V := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  ext n : 2
  simp only [cechComplexReindexIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    NatTrans.comp_app, HomologicalComplex.comp_f, cechReindexObjIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  apply (cancel_mono (cechXIso V Q n).hom).mp
  refine Pi.hom_ext _ _ fun b ↦ ?_
  obtain ⟨a, rfl⟩ := (Equiv.piCongrRight fun _ : Fin (n + 1) ↦ f.trans g).surjective b
  simp only [Category.assoc]
  -- The composite equivalence and tuple composition have the same dependent native index.
  change _ ≫ (cechXIso V Q n).hom ≫ Pi.π _ (g ∘ f ∘ a) = _
  have hleft := cechReindexXIso_hom_π (f.trans g) V Q n a
  have hright := ((cechReindexXIso f (V ∘ g) Q n).hom ≫=
    cechReindexXIso_hom_π g V Q n (f ∘ a)).trans
      (cechReindexXIso_hom_π f (V ∘ g) Q n a)
  simp only [Equiv.coe_trans, Function.comp_assoc, Category.assoc] at hleft hright ⊢
  exact hleft.trans hright.symm

end TauCeti.CategoryTheory
