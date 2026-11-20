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

section Term

universe z
variable {τ : Type z} [HasProducts.{z} A] (P : Cᵒᵖ ⥤ A)

/-- The actual Čech term, expressed as the product of its tuple readings. -/
private def cechTermIso (V : τ → C) (n : ℕ) :
    ((cechComplexFunctor V).obj P).X n ≅
      ∏ᶜ fun a : Fin (n + 1) → τ ↦ P.obj (op (∏ᶜ fun j ↦ V (a j))) :=
  Iso.refl _

@[reassoc]
private lemma cech_d_comp_term_π (V : τ → C)
    (n : ℕ) (a : Fin (n + 2) → τ) :
    ((cechComplexFunctor V).obj P).d n (n + 1) ≫
        (cechTermIso P V (n + 1)).hom ≫ Pi.π _ a =
      ∑ m : Fin (n + 2), (-1 : ℤ) ^ (m : ℕ) •
        ((cechTermIso P V n).hom ≫ Pi.π _ (a ∘ m.succAbove) ≫
          P.map (Pi.lift fun j ↦ Pi.π (fun l ↦ V (a l)) (m.succAbove j)).op) :=
  (_ ≫= Category.id_comp _).trans <| (cechComplexFunctor_obj_d_comp_π V P n a).trans <|
    Finset.sum_congr rfl fun _ _ ↦ congrArg _ (Category.id_comp _).symm

@[reassoc]
private lemma cech_map_f_comp_term_π (V : τ → C) {Q : Cᵒᵖ ⥤ A}
    (φ : P ⟶ Q) (n : ℕ) (a : Fin (n + 1) → τ) :
    ((cechComplexFunctor V).map φ).f n ≫ (cechTermIso Q V n).hom ≫ Pi.π _ a =
      (cechTermIso P V n).hom ≫ Pi.π _ a ≫ φ.app (op (∏ᶜ fun j ↦ V (a j))) :=
  (_ ≫= Category.id_comp _).trans <| (cechComplexFunctor_map_f_π V P φ n a).trans <|
    (Category.id_comp _).symm

end Term

variable [HasProducts.{w₁} A] [HasProducts.{w₂} A]
  {ι : Type w₁} {κ : Type w₂} (e : ι ≃ κ) (U : κ → C) (P : Cᵒᵖ ⥤ A)

/-- Reindex the product of sections indexed by tuples of members of a family. -/
private def cechReindexXIso (n : ℕ) :
    ((cechComplexFunctor (U ∘ e)).obj P).X n ≅ ((cechComplexFunctor U).obj P).X n :=
  cechTermIso P (U ∘ e) n ≪≫
    Pi.reindex (Equiv.piCongrRight fun _ : Fin (n + 1) ↦ e)
    (fun a : Fin (n + 1) → κ ↦ P.obj (op (∏ᶜ fun j ↦ U (a j))))
    ≪≫ (cechTermIso P U n).symm

@[reassoc]
private lemma cechReindexXIso_hom_π (n : ℕ) (a : Fin (n + 1) → ι) :
    (cechReindexXIso e U P n).hom ≫ (cechTermIso P U n).hom ≫ Pi.π _ (e ∘ a) =
      (cechTermIso P (U ∘ e) n).hom ≫ Pi.π _ a := by
  change ((cechTermIso P (U ∘ e) n).hom ≫
      (Pi.reindex (Equiv.piCongrRight fun _ : Fin (n + 1) ↦ e)
        (fun b : Fin (n + 1) → κ ↦ P.obj (op (∏ᶜ fun j ↦ U (b j))))).hom ≫
      (cechTermIso P U n).inv) ≫ (cechTermIso P U n).hom ≫ Pi.π _ (e ∘ a) = _
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg ((cechTermIso P (U ∘ e) n).hom ≫ ·) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact ((Pi.reindex _ _).hom ≫= (cechTermIso P U n).inv_hom_id_assoc _).trans
    (Pi.reindex_hom_π _ _ a)

private lemma cechReindexXIso_hom_comp_d (n : ℕ) :
    (cechReindexXIso e U P n).hom ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      ((cechComplexFunctor (U ∘ e)).obj P).d n (n + 1) ≫
        (cechReindexXIso e U P (n + 1)).hom := by
  apply (cancel_mono (cechTermIso P U (n + 1)).hom).mp
  refine Pi.hom_ext _ _ fun b ↦ ?_
  obtain ⟨a, rfl⟩ := (Equiv.piCongrRight fun _ : Fin (n + 2) ↦ e).surjective b
  change _ ≫ Pi.π _ (e ∘ a) = _ ≫ Pi.π _ (e ∘ a)
  simp only [Category.assoc, cech_d_comp_term_π, Preadditive.comp_sum,
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
    have h := cechReindexXIso_hom_π e U P n a
    dsimp only [cechTermIso, Iso.refl_hom] at h
    exact ((cechReindexXIso e U P n).hom ≫= Category.id_comp _).symm.trans <|
      h.trans (Category.id_comp _)

private lemma cechReindexObjIso_hom_naturality {Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) :
    (cechComplexFunctor (U ∘ e)).map φ ≫ (cechReindexObjIso e U Q).hom =
      (cechReindexObjIso e U P).hom ≫ (cechComplexFunctor U).map φ := by
  ext n : 2
  simp only [HomologicalComplex.comp_f]
  dsimp only [cechReindexObjIso, HomologicalComplex.Hom.isoOfComponents_hom_f]
  apply (cancel_mono (cechTermIso Q U n).hom).mp
  refine Pi.hom_ext _ _ fun b ↦ ?_
  obtain ⟨a, rfl⟩ := (Equiv.piCongrRight fun _ : Fin (n + 1) ↦ e).surjective b
  change _ ≫ Pi.π (fun b : Fin (n + 1) → κ ↦ Q.obj (op (∏ᶜ fun j ↦ U (b j))))
    (e ∘ a) = _
  simp only [Category.assoc, cechReindexXIso_hom_π, cech_map_f_comp_term_π]
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
  exact (Category.assoc _ _ _).trans
    ((_ ≫= cechComplexReindexIso_hom_app_f_π e U P 0 a).trans
      ((cechAugmentation_f_zero_comp_π (U ∘ e) hT P a).trans
        (cechAugmentation_f_zero_comp_π U hT P (e ∘ a)).symm))

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
  apply (cancel_mono (cechTermIso Q V n).hom).mp
  refine Pi.hom_ext _ _ fun b ↦ ?_
  obtain ⟨a, rfl⟩ := (Equiv.piCongrRight fun _ : Fin (n + 1) ↦ f.trans g).surjective b
  simp only [Category.assoc]
  change _ ≫ (cechTermIso Q V n).hom ≫ Pi.π _ (g ∘ f ∘ a) = _
  have hleft := cechReindexXIso_hom_π (f.trans g) V Q n a
  have hright := ((cechReindexXIso f (V ∘ g) Q n).hom ≫=
    cechReindexXIso_hom_π g V Q n (f ∘ a)).trans
      (cechReindexXIso_hom_π f (V ∘ g) Q n a)
  simp only [Equiv.coe_trans, Function.comp_assoc, Category.assoc] at hleft hright ⊢
  exact hleft.trans hright.symm

end TauCeti.CategoryTheory
