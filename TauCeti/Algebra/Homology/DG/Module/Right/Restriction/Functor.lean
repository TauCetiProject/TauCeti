/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Basic

/-!
# Restriction functors for differential graded right modules

Restriction along a DG algebra morphism defines a faithful linear functor between the categories
of right DG modules. Restriction along the identity is naturally isomorphic to the identity
functor, and restriction along a composite is naturally isomorphic to successive restriction.
These comparisons identify the carrier wrappers introduced by restriction, and preserve both the
internal grading and the differential. They provide the ordinary categorical restriction side
of extension/restriction of scalars.

The construction follows the change-of-rings interface of Mathlib's
`ModuleCat.restrictScalarsId` and `ModuleCat.restrictScalarsComp`, with the additional grading and
differential conditions of DG modules.

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

end DGRightModuleCat
end TauCeti
