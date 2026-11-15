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
surjectivity of actual scheme pullback over the corresponding affine bases
(`essSurj_pullback_of_essSurj_baseChange`), allowing algebraic lifting results to be used for
geometric restriction functors without introducing a second pullback functor or a choice of affine
presentation.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace TauCeti.FiniteEtaleScheme

private theorem spec_obj_eq_overMk (R : Type u) [CommRing R]
    (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((spec (.of R)).obj A).obj =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj))) := by
  rw [spec_obj_obj]; rfl

private theorem spec_map_hom_left {R : Type u} [CommRing R]
    {A₁ A₂ : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : A₁ ⟶ A₂) :
    ((spec (.of R)).map f).hom.left =
      eqToHom (congrArg Over.left (spec_obj_eq_overMk R A₁)) ≫
        Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) ≫
        eqToHom (congrArg Over.left (spec_obj_eq_overMk R A₂).symm) := by
  have h := congrArg Over.Hom.left (Functor.congr_hom (spec_comp_ι (.of R)) f)
  simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
    Functor.op_obj, Functor.op_map, Over.comp_left, Over.eqToHom_left] at h
  have hf : f.unop.hom = CommAlgCat.ofHom f.unop.hom.hom := rfl
  rw [h, hf, algSpec_map_left]
  simp only [commAlgCatEquivUnder, Quiver.Hom.unop_op, CommAlgCat.hom_ofHom, AlgHom.toUnder,
    Under.homMk_right]
  rfl

private noncomputable def specCompPullbackAppIso (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    (spec (.of R) ⋙ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj A ≅
      ((CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ spec (.of S)).obj A :=
  ObjectProperty.isoMk _
    (eqToIso (by
        rw [Functor.comp_obj, pullback_obj_obj, spec_obj_eq_overMk, Spec.algebraMap,
          Spec.algebraMap]
        rfl) ≪≫
      TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv
        R A.unop.obj S (S ⊗[R] A.unop.obj) AlgEquiv.refl ≪≫
      eqToIso (by
        rw [Functor.comp_obj, Functor.op_obj, spec_obj_eq_overMk, Spec.algebraMap]
        rfl))

private theorem specCompPullbackAppIso_hom_left (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((specCompPullbackAppIso R S A).hom).hom.left =
      eqToHom (by rw [Functor.comp_obj, pullback_obj_obj, spec_obj_eq_overMk]; rfl) ≫
        (Limits.pullbackSymmetry
          (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom ≫
        (AlgebraicGeometry.pullbackSpecIso R S A.unop.obj).hom ≫
        eqToHom (by rw [Functor.comp_obj, Functor.op_obj, spec_obj_eq_overMk]; rfl) := by
  have h : ((specCompPullbackAppIso R S A).hom).hom.left =
      eqToHom (by rw [Functor.comp_obj, pullback_obj_obj, spec_obj_eq_overMk, Spec.algebraMap,
          Spec.algebraMap]; rfl) ≫
        (Limits.pullbackSymmetry (Spec.algebraMap R A.unop.obj) (Spec.algebraMap R S)).hom ≫
        (AlgebraicGeometry.pullbackSpecIso R S A.unop.obj).hom ≫
        eqToHom (by rw [Functor.comp_obj, Functor.op_obj, spec_obj_eq_overMk]; rfl) := by
    simp [specCompPullbackAppIso]
  exact h

private theorem overPullback_map_left_eq {S T : Scheme.{u}} (g : T ⟶ S)
    {Y₁ Y₂ : Over S} (φ : Y₁ ⟶ Y₂) {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ S} {p₂ : X₂ ⟶ S}
    (h₁ : Y₁ = Over.mk p₁) (h₂ : Y₂ = Over.mk p₂) :
    eqToHom (by rw [h₁]; rfl : Limits.pullback p₁ g = ((Over.pullback g).obj Y₁).left) ≫
        ((Over.pullback g).map φ).left ≫
        eqToHom (by rw [h₂]; rfl : ((Over.pullback g).obj Y₂).left = Limits.pullback p₂ g) =
      Limits.pullback.lift
        (Limits.pullback.fst p₁ g ≫
          eqToHom (congrArg Over.left h₁.symm) ≫ φ.left ≫ eqToHom (congrArg Over.left h₂))
        (Limits.pullback.snd p₁ g)
        (by
          have hw := Over.w φ
          subst h₁; subst h₂
          simp only [Over.mk_left, Over.mk_hom] at hw
          simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc, hw,
            Limits.pullback.condition]) := by
  subst h₁; subst h₂
  simp

private theorem spec_pullback_map_left_eq (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {A₁ A₂ : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : A₁ ⟶ A₂) :
    eqToHom (by rw [Functor.comp_obj, pullback_obj_obj, spec_obj_eq_overMk]; rfl :
        Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A₁.unop.obj)))
            (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
          (((spec (.of R) ⋙ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
            A₁).obj).left) ≫
        ((pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
          ((spec (.of R)).map f)).hom.left ≫
        eqToHom (by rw [Functor.comp_obj, pullback_obj_obj, spec_obj_eq_overMk]; rfl :
          (((spec (.of R) ⋙ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
            A₂).obj).left =
            Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A₂.unop.obj)))
              (Spec.map (CommRingCat.ofHom (algebraMap R S)))) =
      Limits.pullback.lift
        (Limits.pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom))
        (Limits.pullback.snd _ _)
        (by
          rw [Category.assoc, ← Spec.map_comp, ← Limits.pullback.condition]
          congr 2; ext x; exact f.unop.hom.hom.commutes x) := by
  refine (overPullback_map_left_eq (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    ((spec (.of R)).map f).hom (spec_obj_eq_overMk R A₁) (spec_obj_eq_overMk R A₂)).trans ?_
  apply Limits.pullback.hom_ext <;> simp [spec_map_hom_left]

private theorem spec_map_baseChange_left (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {A₁ A₂ : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ} (f : A₁ ⟶ A₂) :
    eqToHom (by rw [Functor.comp_obj, Functor.op_obj, spec_obj_eq_overMk]; rfl :
        Spec (.of (S ⊗[R] A₁.unop.obj)) =
          (((CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ spec (.of S)).obj A₁).obj.left) ≫
        ((spec (.of S)).map (((CommAlgCat.FiniteEtale.baseChange.{u} R S).op).map f)).hom.left ≫
        eqToHom (by rw [Functor.comp_obj, Functor.op_obj, spec_obj_eq_overMk]; rfl :
          (((CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ spec (.of S)).obj A₂).obj.left =
            Spec (.of (S ⊗[R] A₂.unop.obj))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id S S) f.unop.hom.hom).toRingHom) := by
  rw [spec_map_hom_left]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  change eqToHom rfl ≫ Spec.map _ ≫ eqToHom rfl = _
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- Pulling `FiniteEtaleScheme.spec (.of R)` back along `Spec (algebraMap R S)` is naturally
isomorphic to `(CommAlgCat.FiniteEtale.baseChange R S).op` followed by
`FiniteEtaleScheme.spec (.of S)`. -/
noncomputable def specCompPullbackIso (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    spec (.of R) ⋙ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
      (CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ spec (.of S) :=
  NatIso.ofComponents (specCompPullbackAppIso R S) fun {A₁ A₂} f ↦ by
    apply ObjectProperty.hom_ext
    ext1
    simp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
      specCompPullbackAppIso_hom_left]
    have hL := spec_pullback_map_left_eq R S f
    have hR := spec_map_baseChange_left R S f
    rw [← cancel_epi (eqToHom (by rw [Functor.comp_obj, pullback_obj_obj, spec_obj_eq_overMk]; rfl :
        Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A₁.unop.obj)))
            (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
          (((spec (.of R) ⋙ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
            A₁).obj).left)),
      ← cancel_mono (eqToHom (by rw [Functor.comp_obj, Functor.op_obj, spec_obj_eq_overMk]; rfl :
        (((CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ spec (.of S)).obj A₂).obj.left =
          Spec (.of (S ⊗[R] A₂.unop.obj))))]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id]
    rw [reassoc_of% hL, hR]
    rw [← cancel_epi ((AlgebraicGeometry.pullbackSpecIso R S A₁.unop.obj).inv ≫
        (Limits.pullbackSymmetry _ _).inv),
      ← cancel_mono (AlgebraicGeometry.pullbackSpecIso R S A₂.unop.obj).inv]
    simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id]
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, Limits.pullbackSymmetry_hom_comp_fst, Limits.pullback.lift_snd,
        Limits.pullbackSymmetry_inv_comp_snd, AlgebraicGeometry.pullbackSpecIso_inv_fst,
        ← Spec.map_comp]
      congr 1
      ext x
      simp
    · simp only [Category.assoc, Limits.pullbackSymmetry_hom_comp_snd, Limits.pullback.lift_fst,
        Limits.pullbackSymmetry_inv_comp_fst_assoc,
        AlgebraicGeometry.pullbackSpecIso_inv_snd_assoc,
        AlgebraicGeometry.pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1

/-- The forward component of `specCompPullbackIso` on underlying schemes is
`Limits.pullbackSymmetry` followed by `AlgebraicGeometry.pullbackSpecIso`, up to the
`spec_obj_obj` identifications of the carrier presentations. -/
@[reassoc, simp]
theorem specCompPullbackIso_hom_app_hom_left (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((specCompPullbackIso R S).hom.app A).hom.left =
      eqToHom (by rw [Functor.comp_obj, pullback_obj_obj, spec_obj_eq_overMk]; rfl) ≫
        (Limits.pullbackSymmetry
          (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom ≫
        (AlgebraicGeometry.pullbackSpecIso R S A.unop.obj).hom ≫
        eqToHom (by rw [Functor.comp_obj, Functor.op_obj, spec_obj_eq_overMk]; rfl) :=
  specCompPullbackAppIso_hom_left R S A

/-- The inverse component of `specCompPullbackIso` on underlying schemes is the inverse of
`AlgebraicGeometry.pullbackSpecIso` followed by the inverse of `Limits.pullbackSymmetry`, up to the
`spec_obj_obj` identifications of the carrier presentations. -/
@[reassoc, simp]
theorem specCompPullbackIso_inv_app_hom_left (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    ((specCompPullbackIso R S).inv.app A).hom.left =
      eqToHom (by rw [Functor.comp_obj, Functor.op_obj, spec_obj_eq_overMk]; rfl) ≫
        (AlgebraicGeometry.pullbackSpecIso R S A.unop.obj).inv ≫
        (Limits.pullbackSymmetry
          (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).inv ≫
        eqToHom (by rw [Functor.comp_obj, pullback_obj_obj, spec_obj_eq_overMk]; rfl) := by
  rw [← cancel_epi ((specCompPullbackIso R S).hom.app A).hom.left]
  have hid : ((specCompPullbackIso R S).hom.app A).hom.left ≫
      ((specCompPullbackIso R S).inv.app A).hom.left = 𝟙 _ :=
    congr(($((specCompPullbackIso R S).hom_inv_id_app A)).hom.left)
  rw [hid, specCompPullbackIso_hom_app_hom_left_assoc]
  simp

/-- If scalar extension of finite étale algebras is essentially surjective, then so is
pullback of finite étale schemes along the corresponding affine morphism. -/
theorem essSurj_pullback_of_essSurj_baseChange (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [(CommAlgCat.FiniteEtale.baseChange.{u} R S).EssSurj] :
    (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).EssSurj := by
  constructor
  intro X
  -- Synthesis does not find the exported instance for `spec (.of S)`; apply it explicitly.
  have := essSurj_spec (.of S)
  obtain ⟨A, ⟨eA⟩⟩ := Functor.EssSurj.mem_essImage (spec (.of S)) X
  obtain ⟨B, ⟨eB⟩⟩ := Functor.EssSurj.mem_essImage
    (CommAlgCat.FiniteEtale.baseChange R S) A.unop
  exact ⟨(spec (.of R)).obj (op B),
    ⟨(specCompPullbackIso R S).app (op B) ≪≫ (spec (.of S)).mapIso eB.symm.op ≪≫ eA⟩⟩

end TauCeti.FiniteEtaleScheme
