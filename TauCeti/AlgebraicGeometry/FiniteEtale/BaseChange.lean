/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap

/-!
# Base change of finite étale coordinate algebras and schemes

`specCompPullbackIso` identifies pullback of `FiniteEtaleScheme.spec (.of R)` along
`Spec (algebraMap R S)` with `(CommAlgCat.FiniteEtale.baseChange R S).op` followed by
`FiniteEtaleScheme.spec (.of S)`, built from `TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv`.
Consequently, essential surjectivity of scalar extension on finite étale algebras implies essential
surjectivity of scheme pullback (`essSurj_pullback_of_essSurj_baseChange`).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace TauCeti.FiniteEtaleScheme

private theorem spec_obj_eq_mk {R : Type u} [CommRing R] (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((spec (.of R)).obj A).obj = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj))) :=
  by rw [spec_obj_obj]; rfl
private theorem spec_map_hom_left {R : Type u} [CommRing R]
    {A₁ A₂ : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : A₁ ⟶ A₂) :
    ((spec (.of R)).map f).hom.left = eqToHom (congrArg Over.left (spec_obj_eq_mk A₁)) ≫
      Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) ≫
      eqToHom (congrArg Over.left (spec_obj_eq_mk A₂)).symm := by
  have h := congrArg Over.Hom.left (spec_map_hom (.of R) f)
  simp only [Over.comp_left, Over.eqToHom_left, algSpec_map_left, Quiver.Hom.unop_op,
    commAlgCatEquivUnder_functor_map, AlgHom.toUnder, Under.homMk_right] at h
  exact h

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Underlying scheme of
`(spec (.of R) ⋙ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj A`. -/
theorem pullback_spec_obj_left (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    (((spec (.of R) ⋙ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj A).obj).left =
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  simp only [Functor.comp_obj, pullback_obj_obj, spec_obj_eq_mk, Over.pullback_obj_left,
    Over.mk_hom]

/-- Underlying scheme of `((CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ spec (.of S)).obj A`. -/
theorem spec_baseChange_obj_left (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    (((CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ spec (.of S)).obj A).obj.left =
      Spec (.of (S ⊗[R] A.unop.obj)) := by rw [Functor.comp_obj, Functor.op_obj, spec_obj_obj]; rfl

private noncomputable def specCompPullbackAppIso (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    (spec (.of R) ⋙ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj A ≅
      ((CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ spec (.of S)).obj A :=
  ObjectProperty.isoMk _ (eqToIso (by rw [Functor.comp_obj, pullback_obj_obj, spec_obj_obj,
      Spec.algebraMap, Spec.algebraMap]; rfl) ≪≫
    TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv R A.unop.obj S _ AlgEquiv.refl ≪≫
    eqToIso (by rw [Functor.comp_obj, Functor.op_obj, spec_obj_obj, Spec.algebraMap]; rfl))
private theorem specCompPullbackAppIso_hom_left (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((specCompPullbackAppIso R S A).hom).hom.left = eqToHom (pullback_spec_obj_left R S A) ≫
      (Limits.pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom ≫
      (AlgebraicGeometry.pullbackSpecIso R S A.unop.obj).hom ≫
      eqToHom (spec_baseChange_obj_left R S A).symm := by simp [specCompPullbackAppIso]
private theorem pullback_spec_map_hom_left {A₁ A₂ : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ}
    (f : A₁ ⟶ A₂) :
    eqToHom (pullback_spec_obj_left R S A₁).symm ≫ ((pullback (Spec.map (CommRingCat.ofHom
        (algebraMap R S)))).map ((spec (.of R)).map f)).hom.left ≫
        eqToHom (pullback_spec_obj_left R S A₂) =
      Limits.pullback.lift
        (Limits.pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom))
        (Limits.pullback.snd _ _) (by rw [Category.assoc, ← Spec.map_comp,
          ← Limits.pullback.condition]; congr 2; ext x; exact f.unop.hom.hom.commutes x) := by
  rw [pullback_map_hom]
  refine (Over.pullback_map_left_of_eq_mk _ ((spec (.of R)).map f).hom
    (spec_obj_eq_mk A₁) (spec_obj_eq_mk A₂)).trans ?_
  apply Limits.pullback.hom_ext
  · simp only [Limits.pullback.lift_fst]; rw [spec_map_hom_left]; simp
  · simp
private theorem spec_baseChange_map_hom_left {A₁ A₂ : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ}
    (f : A₁ ⟶ A₂) :
    eqToHom (spec_baseChange_obj_left R S A₁).symm ≫ ((spec (.of S)).map
        (((CommAlgCat.FiniteEtale.baseChange.{u} R S).op).map f)).hom.left ≫
        eqToHom (spec_baseChange_obj_left R S A₂) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id S S) f.unop.hom.hom).toRingHom) := by
  rw [spec_map_hom_left]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, Functor.op_map, Quiver.Hom.unop_op,
    CommAlgCat.FiniteEtale.baseChange_map_hom]
  -- `((CommAlgCat.FiniteEtale.baseChange R S).obj A).obj` is definitionally `CommAlgCat.of S`
  -- of `S ⊗[R] A` with the same underlying `CommRing`, so both boundary `eqToHom`s are reflexive.
  change eqToHom rfl ≫ Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id S S) f.unop.hom.hom).toRingHom) ≫ eqToHom rfl = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Pulling `FiniteEtaleScheme.spec (.of R)` back along `Spec (algebraMap R S)` is naturally
isomorphic to `(CommAlgCat.FiniteEtale.baseChange R S).op` followed by
`FiniteEtaleScheme.spec (.of S)`. -/
noncomputable def specCompPullbackIso :
    spec (.of R) ⋙ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
      (CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ spec (.of S) :=
  NatIso.ofComponents (specCompPullbackAppIso R S) fun {A₁ A₂} f ↦ by
    -- Reduce naturality to underlying scheme morphisms and strip boundary `eqToHom` transports.
    apply ObjectProperty.hom_ext; ext1
    simp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
      specCompPullbackAppIso_hom_left]
    rw [← cancel_epi (eqToHom (pullback_spec_obj_left R S A₁).symm),
      ← cancel_mono (eqToHom (spec_baseChange_obj_left R S A₂))]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id, reassoc_of% pullback_spec_map_hom_left R S f,
      spec_baseChange_map_hom_left R S f]
    -- Cancel the pullback comparison isomorphisms and verify equality on the two projections.
    rw [← cancel_epi ((AlgebraicGeometry.pullbackSpecIso R S A₁.unop.obj).inv ≫
        (Limits.pullbackSymmetry _ _).inv),
      ← cancel_mono (AlgebraicGeometry.pullbackSpecIso R S A₂.unop.obj).inv]
    simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id]
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, Limits.pullbackSymmetry_hom_comp_fst, Limits.pullback.lift_snd,
        Limits.pullbackSymmetry_inv_comp_snd, AlgebraicGeometry.pullbackSpecIso_inv_fst,
        ← Spec.map_comp]; congr 1; ext x; simp
    · simp only [Category.assoc, Limits.pullbackSymmetry_hom_comp_snd, Limits.pullback.lift_fst,
        Limits.pullbackSymmetry_inv_comp_fst_assoc, AlgebraicGeometry.pullbackSpecIso_inv_snd_assoc,
        AlgebraicGeometry.pullbackSpecIso_inv_snd, ← Spec.map_comp]; congr 1

/-- Forward component of `specCompPullbackIso` on underlying schemes. -/
@[reassoc, simp]
theorem specCompPullbackIso_hom_app_hom_left (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((specCompPullbackIso R S).hom.app A).hom.left =
      eqToHom (pullback_spec_obj_left R S A) ≫
        (Limits.pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom ≫
        (AlgebraicGeometry.pullbackSpecIso R S A.unop.obj).hom ≫
        eqToHom (spec_baseChange_obj_left R S A).symm :=
  specCompPullbackAppIso_hom_left R S A

/-- Inverse component of `specCompPullbackIso` on underlying schemes. -/
@[reassoc, simp]
theorem specCompPullbackIso_inv_app_hom_left (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((specCompPullbackIso R S).inv.app A).hom.left =
      eqToHom (spec_baseChange_obj_left R S A) ≫
        (AlgebraicGeometry.pullbackSpecIso R S A.unop.obj).inv ≫
        (Limits.pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).inv ≫
        eqToHom (pullback_spec_obj_left R S A).symm := by
  have hhomInv : ((specCompPullbackIso R S).hom.app A).hom.left ≫
      ((specCompPullbackIso R S).inv.app A).hom.left = 𝟙 _ := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
      Over.comp_left, Over.id_left] using
      congrArg (·.hom.left) ((specCompPullbackIso R S).hom_inv_id_app A)
  rw [← cancel_epi ((specCompPullbackIso R S).hom.app A).hom.left, hhomInv,
    specCompPullbackIso_hom_app_hom_left_assoc]
  simp

/-- If scalar extension of finite étale algebras is essentially surjective, then so is
pullback of finite étale schemes along the corresponding affine morphism. -/
theorem essSurj_pullback_of_essSurj_baseChange
    [(CommAlgCat.FiniteEtale.baseChange.{u} R S).EssSurj] :
    (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).EssSurj := ⟨fun X ↦ by
  have := essSurj_spec (.of S)
  obtain ⟨A, ⟨eA⟩⟩ := Functor.EssSurj.mem_essImage (spec (.of S)) X
  obtain ⟨B, ⟨eB⟩⟩ := Functor.EssSurj.mem_essImage (CommAlgCat.FiniteEtale.baseChange R S) A.unop
  exact ⟨(spec (.of R)).obj (op B),
    ⟨(specCompPullbackIso R S).app (op B) ≪≫ (spec (.of S)).mapIso eB.symm.op ≪≫ eA⟩⟩⟩

end TauCeti.FiniteEtaleScheme
