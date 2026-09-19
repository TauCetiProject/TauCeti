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
The body is exposed so the carrier of an image object is the existing restriction wrapper. -/
@[expose]
noncomputable def restrictScalars (f : DGAlgHom hA hB) :
    DGRightModuleCat.{uR, uB, uM} hB ⥤ DGRightModuleCat.{uR, uA, uM} hA where
  obj M := of (M.isDGRightModule.restrictScalars f)
  map g := g.restrictScalars f
  map_id _ := DGRightModuleHom.restrictScalars_id f
  map_comp g k := DGRightModuleHom.restrictScalars_comp f k g

/-- Restricted morphisms act by the original morphism on underlying elements. -/
@[simp]
theorem restrictScalars_map_apply (f : DGAlgHom hA hB)
    {M N : DGRightModuleCat.{uR, uB, uM} hB} (g : M ⟶ N)
    (x : (restrictScalars f).obj M) :
    ((restrictScalars f).map g x).val = g x.val :=
  DGRightModuleHom.val_restrictScalars f g x

/-- Restriction preserves the homogeneous pieces on underlying elements. -/
@[simp]
theorem mem_restrictScalars_obj_grading (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB) (q : ℤ) (x : (restrictScalars f).obj M) :
    x ∈ ((restrictScalars f).obj M).grading q ↔ x.val ∈ M.grading q := by
  exact (IsDGRightModule.mem_restrictScalarsGrading_iff f).trans
    (congrArg (fun y ↦ y ∈ M.grading q)
      (DGRightModule.RestrictScalars.linearEquiv_apply f M x)).to_iff

/-- Restriction preserves the differential on underlying elements. -/
@[simp]
theorem val_restrictScalars_obj_differential (f : DGAlgHom hA hB)
    (M : DGRightModuleCat.{uR, uB, uM} hB) (x : (restrictScalars f).obj M) :
    (((restrictScalars f).obj M).differential x).val = M.differential x.val :=
  IsDGRightModule.val_restrictScalarsDifferential f x

instance (f : DGAlgHom hA hB) : (restrictScalars.{uR, uA, uB, uM} f).Faithful where
  map_injective {M N} g k hgk := by
    apply DGRightModuleHom.ext
    intro x
    have hx := congrArg (fun l ↦ (l (DGRightModule.RestrictScalars.mk x)).val) hgk
    dsimp +instances only [restrictScalars, of] at hx
    exact (restrictScalars_map_apply f g ⟨x⟩).symm.trans
      (hx.trans (restrictScalars_map_apply f k ⟨x⟩))

instance (f : DGAlgHom hA hB) : (restrictScalars.{uR, uA, uB, uM} f).Additive where
  map_add {M N} g k := by
    apply DGRightModuleHom.ext
    intro x
    apply DGRightModule.RestrictScalars.ext
    rw [add_apply, restrictScalars_map_apply, add_apply]
    exact ((DGRightModule.RestrictScalars.val_add f N
      ((restrictScalars f).map g x) ((restrictScalars f).map k x)).trans
      (congrArg₂ (· + ·) (restrictScalars_map_apply f g x)
        (restrictScalars_map_apply f k x))).symm

instance (f : DGAlgHom hA hB) : (restrictScalars.{uR, uA, uB, uM} f).Linear R where
  map_smul {M N} g r := by
    apply DGRightModuleHom.ext
    intro x
    apply DGRightModule.RestrictScalars.ext
    rw [smul_apply, restrictScalars_map_apply, smul_apply]
    exact ((DGRightModule.RestrictScalars.val_smul f N r
      ((restrictScalars f).map g x)).trans
      (congrArg (r • ·) (restrictScalars_map_apply f g x))).symm

/-- Restricting along the identity DG algebra morphism recovers the original module. -/
noncomputable def restrictScalarsIdApp (M : DGRightModuleCat.{uR, uA, uM} hA) :
    (restrictScalars (DGAlgHom.id hA)).obj M ≅ M where
  hom :=
    { toLinearMap :=
        { toFun := fun x ↦ x.val
          map_add' := by intros; rfl
          map_smul' := by
            intro a x
            dsimp +instances only [restrictScalars, of, RingHom.id_apply] at *
            simpa only [op_unop, DGAlgHom.id_apply] using! DGRightModule.RestrictScalars.val_op_smul
              (DGAlgHom.id hA) M a.unop x }
      map_mem' {q} {x} hx := by
        -- The structure field still contains the linear-map constructor; expose its value.
        change x.val ∈ M.grading q
        exact (mem_restrictScalars_obj_grading _ M q x).mp hx
      map_d' x := (IsDGRightModule.val_restrictScalarsDifferential (DGAlgHom.id hA) x).symm }
  inv :=
    { toLinearMap :=
        { toFun := DGRightModule.RestrictScalars.mk
          map_add' := by intros; rfl
          map_smul' := by
            intro a x
            dsimp +instances only [restrictScalars, of, RingHom.id_apply] at *
            apply DGRightModule.RestrictScalars.ext
            simpa only [op_unop, DGAlgHom.id_apply] using!
              (DGRightModule.RestrictScalars.val_op_smul
              (DGAlgHom.id hA) M a.unop (DGRightModule.RestrictScalars.mk x)).symm }
      map_mem' {q} {x} hx := by
        -- The structure field still contains the linear-map constructor; expose its value.
        change DGRightModule.RestrictScalars.mk x ∈
          ((restrictScalars (DGAlgHom.id hA)).obj M).grading q
        exact (mem_restrictScalars_obj_grading _ M q _).mpr hx
      map_d' x := by
        apply DGRightModule.RestrictScalars.ext
        exact IsDGRightModule.val_restrictScalarsDifferential (DGAlgHom.id hA)
          (DGRightModule.RestrictScalars.mk x) }
  hom_inv_id := by
    ext x
    simp only [comp_apply, id_apply]
    rfl
  inv_hom_id := by
    ext x
    simp only [comp_apply, id_apply]
    rfl

@[simp]
theorem restrictScalarsIdApp_hom_apply (M : DGRightModuleCat.{uR, uA, uM} hA)
    (x : (restrictScalars (DGAlgHom.id hA)).obj M) :
    (restrictScalarsIdApp M).hom x = x.val := (rfl)

@[simp]
theorem restrictScalarsIdApp_inv_apply (M : DGRightModuleCat.{uR, uA, uM} hA) (x : M) :
    ((restrictScalarsIdApp M).inv x).val = x := (rfl)

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
    (restrictScalars (g.comp f)).obj M ≅ (restrictScalars f).obj ((restrictScalars g).obj M) where
  hom :=
    { toLinearMap :=
        { toFun := fun x ↦ ⟨⟨x.val⟩⟩
          map_add' := by intros; rfl
          map_smul' := by
            intro a x
            dsimp +instances only [restrictScalars, of, RingHom.id_apply] at *
            apply DGRightModule.RestrictScalars.ext
            apply DGRightModule.RestrictScalars.ext
            simp only [DGRightModule.RestrictScalars.val_smul_eq]
            exact congrArg (fun b : Cᵐᵒᵖ ↦ b • x.val)
                (congrArg op (DGAlgHom.comp_apply g f a.unop)) }
      map_mem' {q} {x} hx := by
        -- The structure field still contains the linear-map constructor; expose its value.
        change (⟨⟨x.val⟩⟩ : (restrictScalars f).obj ((restrictScalars g).obj M)) ∈
          ((restrictScalars f).obj ((restrictScalars g).obj M)).grading q
        exact (mem_restrictScalars_obj_grading f _ q _).mpr
          ((mem_restrictScalars_obj_grading g M q _).mpr
            ((mem_restrictScalars_obj_grading (g.comp f) M q x).mp hx))
      map_d' x := by
        apply DGRightModule.RestrictScalars.ext
        apply DGRightModule.RestrictScalars.ext
        exact (congrArg DGRightModule.RestrictScalars.val
          (val_restrictScalars_obj_differential f ((restrictScalars g).obj M) ⟨⟨x.val⟩⟩)).trans
            ((val_restrictScalars_obj_differential g M ⟨x.val⟩).trans
              (val_restrictScalars_obj_differential (g.comp f) M x).symm) }
  inv :=
    { toLinearMap :=
        { toFun := fun x ↦ ⟨x.val.val⟩
          map_add' := by intros; rfl
          map_smul' := by
            intro a x
            dsimp +instances only [restrictScalars, of, RingHom.id_apply] at *
            apply DGRightModule.RestrictScalars.ext
            simp only [DGRightModule.RestrictScalars.val_smul_eq]
            exact congrArg (fun b : Cᵐᵒᵖ ↦ b • x.val.val)
                (congrArg op (DGAlgHom.comp_apply g f a.unop)).symm }
      map_mem' {q} {x} hx := by
        -- The structure field still contains the linear-map constructor; expose its value.
        change (⟨x.val.val⟩ : (restrictScalars (g.comp f)).obj M) ∈
          ((restrictScalars (g.comp f)).obj M).grading q
        exact (mem_restrictScalars_obj_grading (g.comp f) M q _).mpr
          ((mem_restrictScalars_obj_grading g M q _).mp
            ((mem_restrictScalars_obj_grading f _ q x).mp hx))
      map_d' x := by
        apply DGRightModule.RestrictScalars.ext
        exact (val_restrictScalars_obj_differential (g.comp f) M ⟨x.val.val⟩).trans
          ((val_restrictScalars_obj_differential g M x.val).symm.trans
            (congrArg DGRightModule.RestrictScalars.val
              (val_restrictScalars_obj_differential f _ x)).symm) }
  hom_inv_id := by
    ext x
    simp only [comp_apply, id_apply]
    rfl
  inv_hom_id := by
    ext x
    simp only [comp_apply, id_apply]
    rfl

@[simp]
theorem restrictScalarsCompApp_hom_apply (f : DGAlgHom hA hB) (g : DGAlgHom hB hC)
    (M : DGRightModuleCat.{uR, uC, uM} hC) (x : (restrictScalars (g.comp f)).obj M) :
    ((restrictScalarsCompApp f g M).hom x).val.val = x.val := (rfl)

@[simp]
theorem restrictScalarsCompApp_inv_apply (f : DGAlgHom hA hB) (g : DGAlgHom hB hC)
    (M : DGRightModuleCat.{uR, uC, uM} hC)
    (x : (restrictScalars f).obj ((restrictScalars g).obj M)) :
    ((restrictScalarsCompApp f g M).inv x).val = x.val.val := (rfl)

/-- Restriction along a composite is naturally isomorphic to successive restriction. -/
noncomputable def restrictScalarsComp (f : DGAlgHom hA hB) (g : DGAlgHom hB hC) :
    restrictScalars.{uR, uA, uC, uM} (g.comp f) ≅ restrictScalars g ⋙ restrictScalars f :=
  NatIso.ofComponents (restrictScalarsCompApp f g) (by
    intro M N k
    apply hom_ext
    intro x
    apply DGRightModule.RestrictScalars.ext
    apply DGRightModule.RestrictScalars.ext
    simp)

@[simp]
theorem restrictScalarsComp_app (f : DGAlgHom hA hB) (g : DGAlgHom hB hC)
    (M : DGRightModuleCat.{uR, uC, uM} hC) :
    (restrictScalarsComp f g).app M = restrictScalarsCompApp f g M := (rfl)

end DGRightModuleCat
end TauCeti
