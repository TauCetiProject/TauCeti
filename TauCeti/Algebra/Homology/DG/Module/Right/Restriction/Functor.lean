/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Basic

/-!
# Restriction functors for differential graded right modules

Restriction along a DG algebra morphism defines a faithful linear functor between the categories
of right DG modules. Restriction along the identity is naturally isomorphic to the identity
functor, and restriction along a composite is naturally isomorphic to successive restriction, so
restriction along an isomorphism of DG algebras is an equivalence of categories
(`TauCeti.DGRightModuleCat.restrictScalarsEquivalence`).
These comparisons identify the carrier wrappers introduced by restriction, and preserve both the
internal grading and the differential. They provide the ordinary categorical restriction side
of extension/restriction of scalars. Restriction changes neither the underlying complexes nor the
underlying chain maps, so it preserves and reflects quasi-isomorphisms
(`TauCeti.DGRightModuleCat.isQuasiIso_restrictScalars_map_iff`).

The construction follows the change-of-rings interface of Mathlib's
`ModuleCat.restrictScalarsId` and `ModuleCat.restrictScalarsComp`, with the additional grading and
differential conditions of DG modules. Restriction also carries homotopy retract data to homotopy
retract data (`TauCeti.DGRightModuleCat.restrictScalars_homotopyRetract`). A map of underlying
modules that is semilinear along the algebra morphism is a morphism into the restricted module
(`TauCeti.DGRightModuleCat.restrictScalarsHomMk`), as for Mathlib's
`ModuleCat.semilinearMapAddEquiv`.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti
namespace DGRightModuleCat

universe uR uA uB uC uM

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}

/-- Restriction of scalars along a DG algebra morphism, on the ordinary categories of DG modules.
The action on each image object is given by the original action through the algebra morphism. -/
noncomputable def restrictScalars (f : DGAlgHom hA hB) :
    DGRightModuleCat.{uR, uB, uM} hB ⥤ DGRightModuleCat.{uR, uA, uM} hA where
  obj M := of (M.isDGRightModule.restrictScalars f)
  map g := g.restrictScalars f
  map_id _ := DGRightModuleHom.restrictScalars_id f
  map_comp g k := DGRightModuleHom.restrictScalars_comp f k g

/-- Restriction of scalars preserves the underlying module over the ground ring. -/
noncomputable def restrictScalarsEquiv (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB) : (restrictScalars f).obj M ≃ₗ[R] M :=
  DGRightModule.RestrictScalars.linearEquiv f M

/-- The restricted action is the original action through the algebra morphism. -/
@[simp]
theorem restrictScalarsEquiv_smul (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB) (a : Aᵐᵒᵖ)
    (x : (restrictScalars f).obj M) :
    restrictScalarsEquiv f M (a • x) = op (f a.unop) • restrictScalarsEquiv f M x := by
  exact (DGRightModule.RestrictScalars.linearEquiv_apply f M _).trans
    ((DGRightModule.RestrictScalars.val_smul_eq f M a x).trans
      (congrArg (op (f a.unop) • ·)
        (DGRightModule.RestrictScalars.linearEquiv_apply f M x).symm))

/-- Restricted morphisms act by the original morphism on underlying elements. -/
@[simp]
theorem restrictScalars_map_apply (f : DGAlgHom hA hB)
    {M N : DGRightModuleCat.{uR, uB, uM} hB} (g : M ⟶ N)
    (x : (restrictScalars f).obj M) :
    restrictScalarsEquiv f N ((restrictScalars f).map g x) =
      g (restrictScalarsEquiv f M x) := by
  exact (DGRightModule.RestrictScalars.linearEquiv_apply f N _).trans
    ((DGRightModuleHom.val_restrictScalars f g x).trans
      (congrArg g (DGRightModule.RestrictScalars.linearEquiv_apply f M x).symm))

/-- Restriction preserves the homogeneous pieces on underlying elements. -/
@[simp]
theorem mem_restrictScalars_obj_grading (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB) (q : ℤ) (x : (restrictScalars f).obj M) :
    x ∈ ((restrictScalars f).obj M).grading q ↔ restrictScalarsEquiv f M x ∈ M.grading q :=
  IsDGRightModule.mem_restrictScalarsGrading_iff f

/-- Restriction preserves the differential on underlying elements. -/
@[simp]
theorem restrictScalarsEquiv_differential (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB) (x : (restrictScalars f).obj M) :
    restrictScalarsEquiv f M (((restrictScalars f).obj M).differential x) =
      M.differential (restrictScalarsEquiv f M x) := by
  exact (DGRightModule.RestrictScalars.linearEquiv_apply f M _).trans
    ((IsDGRightModule.val_restrictScalarsDifferential f x).trans
      (congrArg M.differential (DGRightModule.RestrictScalars.linearEquiv_apply f M x).symm))

/-- **Restriction of scalars preserves and reflects quasi-isomorphisms**: it changes neither the
underlying complexes nor the underlying chain maps. -/
@[simp]
theorem isQuasiIso_restrictScalars_map_iff (f : DGAlgHom hA hB)
    {M N : DGRightModuleCat.{uR, uB, uM} hB} (g : M ⟶ N) :
    IsQuasiIso ((restrictScalars f).map g) ↔ IsQuasiIso g := by
  set eM := restrictScalarsEquiv f M
  set eN := restrictScalarsEquiv f N
  simp only [IsQuasiIso, DGRightModuleHom.isQuasiIso_iff_forall_exists]
  constructor
  · intro H x y hx hgx
    obtain ⟨u, v, hu, huv⟩ := H (eM.symm x) (eN.symm y)
      (eM.injective (by rw [restrictScalarsEquiv_differential, LinearEquiv.apply_symm_apply, hx,
        map_zero]))
      (eN.injective (by rw [restrictScalars_map_apply, restrictScalarsEquiv_differential,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hgx]))
    refine ⟨eM u, eN v, ?_, ?_⟩
    · rw [← restrictScalarsEquiv_differential, hu, LinearEquiv.apply_symm_apply]
    · rw [← restrictScalars_map_apply, ← restrictScalarsEquiv_differential, ← map_add, huv,
        LinearEquiv.apply_symm_apply]
  · intro H x y hx hgx
    obtain ⟨u, v, hu, huv⟩ := H (eM x) (eN y)
      (by rw [← restrictScalarsEquiv_differential, hx, map_zero])
      (by rw [← restrictScalars_map_apply, hgx, restrictScalarsEquiv_differential])
    refine ⟨eM.symm u, eN.symm v, eM.injective ?_, eN.injective ?_⟩
    · rw [restrictScalarsEquiv_differential, LinearEquiv.apply_symm_apply, hu]
    · rw [map_add, restrictScalars_map_apply, restrictScalarsEquiv_differential,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, huv]

/-- The inverse of `restrictScalarsEquiv` preserves the differential. -/
@[simp]
theorem restrictScalarsEquiv_symm_differential (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB) (x : M) :
    ((restrictScalars f).obj M).differential ((restrictScalarsEquiv f M).symm x) =
      (restrictScalarsEquiv f M).symm (M.differential x) :=
  (restrictScalarsEquiv f M).injective <| by
    rw [restrictScalarsEquiv_differential, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]

/-- A **morphism into a restriction of scalars** `M ⟶ f^* N`, from a map of the underlying modules
over the ground ring that is semilinear along `f` for the actions, `φ (x · a) = φ x · f a`,
preserves the degrees and commutes with the differentials. -/
noncomputable def restrictScalarsHomMk (f : DGAlgHom hA hB) {M : DGRightModuleCat.{uR, uA, uM} hA}
    {N : DGRightModuleCat.{uR, uB, uM} hB} (φ : M →ₗ[R] N)
    (hsmul : ∀ (a : A) (x : M), φ (op a • x) = op (f a) • φ x)
    (hmem : ∀ (q : ℤ) (x : M), x ∈ M.grading q → φ x ∈ N.grading q)
    (hd : ∀ x, φ (M.differential x) = N.differential (φ x)) :
    M ⟶ (restrictScalars f).obj N where
  toLinearMap :=
    { toFun x := (restrictScalarsEquiv f N).symm (φ x)
      map_add' x y := by rw [map_add, map_add]
      map_smul' a x := by
        apply (restrictScalarsEquiv f N).injective
        rw [RingHom.id_apply, restrictScalarsEquiv_smul, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply, ← hsmul, op_unop] }
  map_mem' hx := (mem_restrictScalars_obj_grading f N _ _).2 <| by
    simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply] using hmem _ _ hx
  map_d' x := (restrictScalarsEquiv_symm_differential f N (φ x)).trans (congrArg _ (hd x).symm)

/-- The morphism `restrictScalarsHomMk f φ` is `φ` on underlying elements. -/
@[simp]
theorem restrictScalarsEquiv_restrictScalarsHomMk_apply (f : DGAlgHom hA hB)
    {M : DGRightModuleCat.{uR, uA, uM} hA} {N : DGRightModuleCat.{uR, uB, uM} hB} (φ : M →ₗ[R] N)
    (hsmul : ∀ (a : A) (x : M), φ (op a • x) = op (f a) • φ x)
    (hmem : ∀ (q : ℤ) (x : M), x ∈ M.grading q → φ x ∈ N.grading q)
    (hd : ∀ x, φ (M.differential x) = N.differential (φ x)) (x : M) :
    restrictScalarsEquiv f N (restrictScalarsHomMk f φ hsmul hmem hd x) = φ x :=
  (restrictScalarsEquiv f N).apply_symm_apply (φ x)

/-- Transporting an element along an equality of restrictions of scalars, coming from an equality
`f = f'` of DG algebra morphisms, does not change the underlying element. -/
@[simp]
theorem restrictScalarsEquiv_eqToHom_apply {f f' : DGAlgHom hA hB} (hf : f = f')
    (M : DGRightModuleCat.{uR, uB, uM} hB)
    (h : (restrictScalars f).obj M = (restrictScalars f').obj M) (x : (restrictScalars f).obj M) :
    restrictScalarsEquiv f' M (eqToHom h x) = restrictScalarsEquiv f M x := by
  subst hf
  rw [eqToHom_refl, id_apply]

/-- The bundled restricted object is the object obtained by bundling the unbundled restriction.
This is the identity isomorphism; it is named because `restrictScalars` is not exposed, so the
identification is only visible inside this module. -/
noncomputable def restrictScalarsObjIso (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB) :
    (restrictScalars f).obj M ≅ of (M.isDGRightModule.restrictScalars f) :=
  Iso.refl _

/-- The canonical restricted-object isomorphism acts by the carrier equivalence. -/
@[simp]
theorem restrictScalarsObjIso_hom_apply (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB) (x : (restrictScalars f).obj M) :
    (restrictScalarsObjIso f M).hom x =
      DGRightModule.RestrictScalars.mk (restrictScalarsEquiv f M x) := by
  apply DGRightModule.RestrictScalars.ext
  -- Retype the identity morphism at its own endpoints.
  change ((𝟙 ((restrictScalars f).obj M) : (restrictScalars f).obj M ⟶ _) x).val = _
  rw [id_apply]
  exact (DGRightModule.RestrictScalars.linearEquiv_apply f M x).symm

/-- The inverse canonical restricted-object isomorphism inverts the carrier equivalence. -/
@[simp]
theorem restrictScalarsObjIso_inv_apply (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB)
    (x : of (M.isDGRightModule.restrictScalars f)) :
    (restrictScalarsObjIso f M).inv x = (restrictScalarsEquiv f M).symm x.val := by
  apply (restrictScalarsEquiv f M).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := restrictScalarsObjIso_hom_apply f M ((restrictScalarsObjIso f M).inv x)
  rw [← comp_apply, Iso.inv_hom_id, id_apply] at h
  exact congrArg DGRightModule.RestrictScalars.val h.symm

/-- The canonical restricted-object isomorphisms are natural in the module. -/
theorem restrictScalarsObjIso_hom_naturality (f : DGAlgHom hA hB)
    {M N : DGRightModuleCat.{uR, uB, uM} hB} (g : M ⟶ N) :
    (restrictScalars f).map g ≫ (restrictScalarsObjIso f N).hom =
      (restrictScalarsObjIso f M).hom ≫ g.restrictScalars f := by
  apply hom_ext
  intro x
  rw [comp_apply, comp_apply, restrictScalarsObjIso_hom_apply, restrictScalarsObjIso_hom_apply]
  apply DGRightModule.RestrictScalars.ext
  rw [DGRightModuleHom.val_restrictScalars]
  exact restrictScalars_map_apply f g x

/-- The inverses of the canonical restricted-object isomorphisms are natural in the module. -/
theorem restrictScalarsObjIso_inv_naturality (f : DGAlgHom hA hB)
    {M N : DGRightModuleCat.{uR, uB, uM} hB} (g : M ⟶ N) :
    (restrictScalarsObjIso f M).inv ≫ (restrictScalars f).map g =
      g.restrictScalars f ≫ (restrictScalarsObjIso f N).inv := by
  rw [← cancel_mono (restrictScalarsObjIso f N).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    restrictScalarsObjIso_hom_naturality, Iso.inv_hom_id_assoc]

instance (f : DGAlgHom hA hB) : (restrictScalars.{uR, uA, uB, uM} f).Faithful where
  map_injective {M N} g k hgk := by
    apply hom_ext
    intro x
    have hx := congrArg
      (fun l : (restrictScalars f).obj M ⟶ (restrictScalars f).obj N ↦
        restrictScalarsEquiv f N (l ((restrictScalarsEquiv f M).symm x))) hgk
    simpa only [restrictScalars_map_apply, LinearEquiv.apply_symm_apply] using hx

instance (f : DGAlgHom hA hB) : (restrictScalars.{uR, uA, uB, uM} f).Additive where
  map_add {M N} g k := by
    apply hom_ext
    intro x
    apply (restrictScalarsEquiv f N).injective
    simp only [add_apply, restrictScalars_map_apply, map_add]

instance (f : DGAlgHom hA hB) : (restrictScalars.{uR, uA, uB, uM} f).Linear R where
  map_smul {M N} g r := by
    apply hom_ext
    intro x
    apply (restrictScalarsEquiv f N).injective
    simp only [smul_apply, restrictScalars_map_apply, map_smul]

/-- Restricting along the identity DG algebra morphism recovers the original module. -/
noncomputable def restrictScalarsIdApp (M : DGRightModuleCat.{uR, uA, uM} hA) :
    (restrictScalars (DGAlgHom.id hA)).obj M ≅ M where
  hom :=
    { toLinearMap :=
        { toFun := restrictScalarsEquiv (DGAlgHom.id hA) M
          map_add' := map_add _
          map_smul' := by
            intro a x
            simp only [restrictScalarsEquiv_smul, DGAlgHom.id_apply, op_unop,
              RingHom.id_apply] }
      map_mem' hx := (mem_restrictScalars_obj_grading _ M _ _).mp hx
      map_d' x := (restrictScalarsEquiv_differential _ M x).symm }
  inv :=
    { toLinearMap :=
        { toFun := (restrictScalarsEquiv (DGAlgHom.id hA) M).symm
          map_add' := map_add _
          map_smul' := by
            intro a x
            apply (restrictScalarsEquiv (DGAlgHom.id hA) M).injective
            simp only [restrictScalarsEquiv_smul, LinearEquiv.apply_symm_apply,
              DGAlgHom.id_apply, op_unop, RingHom.id_apply] }
      map_mem' hx := by
        apply (mem_restrictScalars_obj_grading _ M _ _).mpr
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply] using hx
      map_d' x := by
        apply (restrictScalarsEquiv (DGAlgHom.id hA) M).injective
        simp only [LinearMap.coe_mk, AddHom.coe_mk, restrictScalarsEquiv_differential,
          LinearEquiv.apply_symm_apply] }
  hom_inv_id := by
    ext x
    rw [comp_apply, id_apply]
    -- Reduce the freshly constructed morphisms to their underlying functions.
    change (restrictScalarsEquiv (DGAlgHom.id hA) M).symm
      (restrictScalarsEquiv (DGAlgHom.id hA) M x) = x
    exact (restrictScalarsEquiv (DGAlgHom.id hA) M).symm_apply_apply x
  inv_hom_id := by
    ext x
    rw [comp_apply, id_apply]
    -- Reduce the freshly constructed morphisms to their underlying functions.
    change restrictScalarsEquiv (DGAlgHom.id hA) M
      ((restrictScalarsEquiv (DGAlgHom.id hA) M).symm x) = x
    exact (restrictScalarsEquiv (DGAlgHom.id hA) M).apply_symm_apply x

@[simp]
theorem restrictScalarsIdApp_hom_apply (M : DGRightModuleCat.{uR, uA, uM} hA)
    (x : (restrictScalars (DGAlgHom.id hA)).obj M) :
    (restrictScalarsIdApp M).hom x = restrictScalarsEquiv (DGAlgHom.id hA) M x := (rfl)

@[simp]
theorem restrictScalarsIdApp_inv_apply (M : DGRightModuleCat.{uR, uA, uM} hA) (x : M) :
    restrictScalarsEquiv (DGAlgHom.id hA) M ((restrictScalarsIdApp M).inv x) = x :=
  (restrictScalarsEquiv (DGAlgHom.id hA) M).apply_symm_apply x

/-- Restriction along the identity is naturally isomorphic to the identity functor. -/
noncomputable def restrictScalarsId :
    restrictScalars.{uR, uA, uA, uM} (DGAlgHom.id hA) ≅ 𝟭 _ :=
  NatIso.ofComponents restrictScalarsIdApp (by
    intro M N g
    ext x
    simp)

@[simp]
theorem restrictScalarsId_app (M : DGRightModuleCat.{uR, uA, uM} hA) :
    restrictScalarsId.app M = restrictScalarsIdApp M := (rfl)

/-- Restriction along a composite agrees with successive restriction on each module. -/
noncomputable def restrictScalarsCompApp (f : DGAlgHom hA hB) (g : DGAlgHom hB hC)
    (M : DGRightModuleCat.{uR, uC, uM} hC) :
    (restrictScalars (g.comp f)).obj M ≅ (restrictScalars f).obj ((restrictScalars g).obj M) := by
  -- Compose the carrier identifications, then verify that both directions respect the DG data.
  let e : (restrictScalars (g.comp f)).obj M ≃ₗ[R]
      (restrictScalars f).obj ((restrictScalars g).obj M) :=
    (restrictScalarsEquiv (g.comp f) M).trans
      ((restrictScalarsEquiv g M).symm.trans
        (restrictScalarsEquiv f ((restrictScalars g).obj M)).symm)
  let hom : (restrictScalars (g.comp f)).obj M ⟶
      (restrictScalars f).obj ((restrictScalars g).obj M) :=
    { toLinearMap :=
        { toFun := e
          map_add' := map_add e
          map_smul' := by
            intro a x
            apply (restrictScalarsEquiv f _).injective
            apply (restrictScalarsEquiv g M).injective
            simp only [e, LinearEquiv.trans_apply, restrictScalarsEquiv_smul,
              LinearEquiv.apply_symm_apply, DGAlgHom.comp_apply, unop_op,
              RingHom.id_apply] }
      map_mem' hx := by
        apply (mem_restrictScalars_obj_grading f _ _ _).mpr
        apply (mem_restrictScalars_obj_grading g M _ _).mpr
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, e, LinearEquiv.trans_apply,
          LinearEquiv.apply_symm_apply] using
          (mem_restrictScalars_obj_grading (g.comp f) M _ _).mp hx
      map_d' x := by
        apply (restrictScalarsEquiv f _).injective
        apply (restrictScalarsEquiv g M).injective
        simp only [LinearMap.coe_mk, AddHom.coe_mk, e, LinearEquiv.trans_apply,
          restrictScalarsEquiv_differential, LinearEquiv.apply_symm_apply] }
  let inv : (restrictScalars f).obj ((restrictScalars g).obj M) ⟶
      (restrictScalars (g.comp f)).obj M :=
    { toLinearMap :=
        { toFun := e.symm
          map_add' := map_add e.symm
          map_smul' := by
            intro a x
            apply (restrictScalarsEquiv (g.comp f) M).injective
            simp only [e, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
              restrictScalarsEquiv_smul, LinearEquiv.apply_symm_apply,
              DGAlgHom.comp_apply, unop_op, RingHom.id_apply] }
      map_mem' hx := by
        apply (mem_restrictScalars_obj_grading (g.comp f) M _ _).mpr
        simpa only [LinearMap.coe_mk, AddHom.coe_mk, e, LinearEquiv.symm_trans_apply,
          LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply] using
          (mem_restrictScalars_obj_grading g M _ _).mp
            ((mem_restrictScalars_obj_grading f _ _ _).mp hx)
      map_d' x := by
        apply (restrictScalarsEquiv (g.comp f) M).injective
        simp only [LinearMap.coe_mk, AddHom.coe_mk, e, LinearEquiv.symm_trans_apply,
          LinearEquiv.symm_symm, restrictScalarsEquiv_differential,
          LinearEquiv.apply_symm_apply] }
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply hom_ext
        intro x
        rw [comp_apply, id_apply]
        -- Reduce the local morphism constructors; the inverse law is that of `e`.
        change e.symm (e x) = x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply hom_ext
        intro x
        rw [comp_apply, id_apply]
        -- Reduce the local morphism constructors; the inverse law is that of `e`.
        change e (e.symm x) = x
        exact e.apply_symm_apply x }

@[simp]
theorem restrictScalarsCompApp_hom_apply (f : DGAlgHom hA hB) (g : DGAlgHom hB hC)
    (M : DGRightModuleCat.{uR, uC, uM} hC) (x : (restrictScalars (g.comp f)).obj M) :
    restrictScalarsEquiv g M
        (restrictScalarsEquiv f _ ((restrictScalarsCompApp f g M).hom x)) =
      restrictScalarsEquiv (g.comp f) M x := by
  -- Evaluate the defining component map before canceling the carrier equivalences.
  change restrictScalarsEquiv g M (restrictScalarsEquiv f _
    ((restrictScalarsEquiv f _).symm ((restrictScalarsEquiv g M).symm _))) = _
  simp only [LinearEquiv.apply_symm_apply]
  rfl

@[simp]
theorem restrictScalarsCompApp_inv_apply (f : DGAlgHom hA hB) (g : DGAlgHom hB hC)
    (M : DGRightModuleCat.{uR, uC, uM} hC)
    (x : (restrictScalars f).obj ((restrictScalars g).obj M)) :
    restrictScalarsEquiv (g.comp f) M ((restrictScalarsCompApp f g M).inv x) =
      restrictScalarsEquiv g M (restrictScalarsEquiv f _ x) :=
  (restrictScalarsEquiv (g.comp f) M).apply_symm_apply _

/-- Restriction along a composite is naturally isomorphic to successive restriction. -/
noncomputable def restrictScalarsComp (f : DGAlgHom hA hB) (g : DGAlgHom hB hC) :
    restrictScalars.{uR, uA, uC, uM} (g.comp f) ≅ restrictScalars g ⋙ restrictScalars f :=
  NatIso.ofComponents (restrictScalarsCompApp f g) (by
    intro M N k
    apply hom_ext
    intro x
    apply (restrictScalarsEquiv f _).injective
    apply (restrictScalarsEquiv g N).injective
    simp)

@[simp]
theorem restrictScalarsComp_app (f : DGAlgHom hA hB) (g : DGAlgHom hB hC)
    (M : DGRightModuleCat.{uR, uC, uM} hC) :
    (restrictScalarsComp f g).app M = restrictScalarsCompApp f g M := (rfl)

section Equivalence

/-- **Restriction along an isomorphism of DG algebras is an equivalence**: if `f` and `g` are
mutually inverse DG algebra morphisms, then restriction along `g` is inverse to restriction along
`f`. The unit and counit come from `restrictScalarsId` and `restrictScalarsComp`. This is the DG
analogue of Mathlib's `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`. -/
@[expose]
noncomputable def restrictScalarsEquivalence (f : DGAlgHom hA hB) (g : DGAlgHom hB hA)
    (hfg : f.comp g = DGAlgHom.id hB) (hgf : g.comp f = DGAlgHom.id hA) :
    DGRightModuleCat.{uR, uB, uM} hB ≌ DGRightModuleCat.{uR, uA, uM} hA where
  functor := restrictScalars f
  inverse := restrictScalars g
  unitIso := restrictScalarsId.symm ≪≫ eqToIso (by rw [hfg]) ≪≫ restrictScalarsComp g f
  counitIso := (restrictScalarsComp f g).symm ≪≫ eqToIso (by rw [hgf]) ≪≫ restrictScalarsId
  functor_unitIso_comp M := by
    ext x
    apply (restrictScalarsEquiv f M).injective
    simp [← Iso.app_hom, ← Iso.app_inv, restrictScalarsEquiv_eqToHom_apply hgf,
      restrictScalarsEquiv_eqToHom_apply hfg.symm]

variable (f : DGAlgHom hA hB) (g : DGAlgHom hB hA) (hfg : f.comp g = DGAlgHom.id hB)
  (hgf : g.comp f = DGAlgHom.id hA)

@[simp]
theorem restrictScalarsEquivalence_functor :
    (restrictScalarsEquivalence.{uR, uA, uB, uM} f g hfg hgf).functor = restrictScalars f :=
  (rfl)

@[simp]
theorem restrictScalarsEquivalence_inverse :
    (restrictScalarsEquivalence.{uR, uA, uB, uM} f g hfg hgf).inverse = restrictScalars g :=
  (rfl)

/-- The component of the unit of `restrictScalarsEquivalence` at `M`. -/
@[simp]
theorem restrictScalarsEquivalence_unitIso_hom_app (M : DGRightModuleCat.{uR, uB, uM} hB) :
    (restrictScalarsEquivalence f g hfg hgf).unitIso.hom.app M =
      (restrictScalarsIdApp M).inv ≫ eqToHom (by rw [hfg]) ≫
        (restrictScalarsCompApp g f M).hom := by
  simp [restrictScalarsEquivalence, ← Iso.app_hom, ← Iso.app_inv]

/-- The component of the inverse of the unit of `restrictScalarsEquivalence` at `M`. -/
@[simp]
theorem restrictScalarsEquivalence_unitIso_inv_app (M : DGRightModuleCat.{uR, uB, uM} hB) :
    (restrictScalarsEquivalence f g hfg hgf).unitIso.inv.app M =
      (restrictScalarsCompApp g f M).inv ≫ eqToHom (by rw [hfg]) ≫
        (restrictScalarsIdApp M).hom := by
  simp [restrictScalarsEquivalence, ← Iso.app_hom, ← Iso.app_inv]

/-- The component of the counit of `restrictScalarsEquivalence` at `M`. -/
@[simp]
theorem restrictScalarsEquivalence_counitIso_hom_app (M : DGRightModuleCat.{uR, uA, uM} hA) :
    (restrictScalarsEquivalence f g hfg hgf).counitIso.hom.app M =
      (restrictScalarsCompApp f g M).inv ≫ eqToHom (by rw [hgf]) ≫
        (restrictScalarsIdApp M).hom := by
  simp [restrictScalarsEquivalence, ← Iso.app_hom, ← Iso.app_inv]

/-- The component of the inverse of the counit of `restrictScalarsEquivalence` at `M`. -/
@[simp]
theorem restrictScalarsEquivalence_counitIso_inv_app (M : DGRightModuleCat.{uR, uA, uM} hA) :
    (restrictScalarsEquivalence f g hfg hgf).counitIso.inv.app M =
      (restrictScalarsIdApp M).inv ≫ eqToHom (by rw [hgf]) ≫
        (restrictScalarsCompApp f g M).hom := by
  simp [restrictScalarsEquivalence, ← Iso.app_hom, ← Iso.app_inv]

end Equivalence

/-- **Restriction of scalars carries homotopy retracts.** If `M` is a homotopy retract of a
complex `M₀` over the ground ring, through chain maps `i : M → M₀` and `r : M₀ → M` with
`r ∘ i = 1 + d K + K d`, then so is its restriction, through `i ∘ e`, `e⁻¹ ∘ r` and `e⁻¹ ∘ K ∘ e`
for `e = restrictScalarsEquiv f M`. The three conclusions are the hypotheses on the restricted
side of `TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyRetract`. -/
theorem restrictScalars_homotopyRetract (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB) {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {d₀ : M₀ →ₗ[R] M₀} {i : M →ₗ[R] M₀} {r : M₀ →ₗ[R] M} {K : M →ₗ[R] M}
    (hi : ∀ x, d₀ (i x) = i (M.differential x)) (hr : ∀ x, M.differential (r x) = r (d₀ x))
    (hK : ∀ x, r (i x) = x + M.differential (K x) + K (M.differential x)) :
    (∀ x, d₀ ((i ∘ₗ (restrictScalarsEquiv f M).toLinearMap) x) =
        (i ∘ₗ (restrictScalarsEquiv f M).toLinearMap)
          (((restrictScalars f).obj M).differential x)) ∧
      (∀ x, ((restrictScalars f).obj M).differential
          (((restrictScalarsEquiv f M).symm.toLinearMap ∘ₗ r) x) =
        ((restrictScalarsEquiv f M).symm.toLinearMap ∘ₗ r) (d₀ x)) ∧
      ∀ x, ((restrictScalarsEquiv f M).symm.toLinearMap ∘ₗ r)
          ((i ∘ₗ (restrictScalarsEquiv f M).toLinearMap) x) =
        x + ((restrictScalars f).obj M).differential
            (((restrictScalarsEquiv f M).symm.toLinearMap ∘ₗ K ∘ₗ
              (restrictScalarsEquiv f M).toLinearMap) x) +
          ((restrictScalarsEquiv f M).symm.toLinearMap ∘ₗ K ∘ₗ
            (restrictScalarsEquiv f M).toLinearMap) (((restrictScalars f).obj M).differential x) :=
  ⟨fun x ↦ by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hi,
      restrictScalarsEquiv_differential],
    fun x ↦ by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      restrictScalarsEquiv_symm_differential, hr],
    fun x ↦ by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hK, map_add,
      LinearEquiv.symm_apply_apply, restrictScalarsEquiv_symm_differential,
      restrictScalarsEquiv_differential]⟩

end DGRightModuleCat
end TauCeti
