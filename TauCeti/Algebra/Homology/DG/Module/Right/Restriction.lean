/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Module.TransferInstance
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.DG.Module.Right.Hom

/-!
# Restriction of scalars for differential graded right modules

A morphism `f : A ⟶ B` of differential graded algebras turns every right DG `B`-module into
a right DG `A`-module by the action `x · a = x · f(a)`.  This file packages that construction
without installing a global module instance depending on `f`: the carrier is the wrapper
`TauCeti.DGRightModule.RestrictScalars f M`.

Restriction preserves the underlying grading and differential.  A morphism of right DG
`B`-modules is therefore also a morphism after restriction, and this operation preserves identity
maps and composition.  These constructions are the underived restriction-of-scalars input for
the DG categories of modules and their later derived functors.

## Main definitions

* `TauCeti.DGRightModule.RestrictScalars`: the carrier of a module restricted along a DG algebra
  morphism.
* `TauCeti.IsDGRightModule.restrictScalars`: the restricted right DG module structure.
* `TauCeti.DGRightModuleHom.restrictScalars`: restriction of a right DG module morphism.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.
-/

public section

open MulOpposite

namespace TauCeti

universe uR uA uB uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

namespace DGRightModule

/-- The carrier of a right module after restriction of scalars along a DG algebra morphism.

The wrapper keeps the restricted `Aᵐᵒᵖ`-module instance local to the chosen morphism `f`.
Its additive group and `R`-module structures are those of `M`. -/
structure RestrictScalars (_f : DGAlgHom hA hB) (M : Type uM) where
  /-- The element of the original module underlying a restricted element. -/
  val : M

/-- Restricted elements are equal when their underlying elements are equal. -/
@[ext]
theorem RestrictScalars.ext {f : DGAlgHom hA hB} {M : Type uM}
    {x y : RestrictScalars f M} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

namespace RestrictScalars

variable (f : DGAlgHom hA hB) (M : Type uM)
  [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]

instance : AddCommGroup (RestrictScalars f M) :=
  Equiv.addCommGroup
    { toFun := RestrictScalars.val, invFun := RestrictScalars.mk
      left_inv _ := rfl, right_inv _ := rfl }

instance : Module R (RestrictScalars f M) :=
  AddEquiv.module R
    { toFun := RestrictScalars.val, invFun := RestrictScalars.mk
      left_inv _ := rfl, right_inv _ := rfl, map_add' _ _ := rfl }

/-- The restricted right action: `a : A` acts through `f a : B`. -/
instance : Module Aᵐᵒᵖ (RestrictScalars f M) :=
  letI : Module Aᵐᵒᵖ M :=
    Module.compHom M (AlgHom.op f.toGradedAlgHom.toAlgHom).toRingHom
  AddEquiv.module Aᵐᵒᵖ
    { toFun := RestrictScalars.val, invFun := RestrictScalars.mk
      left_inv _ := rfl, right_inv _ := rfl, map_add' _ _ := rfl }

/-- The identity `R`-linear equivalence from a restricted module to its original carrier. -/
def linearEquiv : RestrictScalars f M ≃ₗ[R] M where
  toFun := RestrictScalars.val
  invFun := RestrictScalars.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M] in
@[simp]
theorem val_zero : (0 : RestrictScalars f M).val = 0 := rfl

omit [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M] in
@[simp]
theorem val_add (x y : RestrictScalars f M) : (x + y).val = x.val + y.val := rfl

omit [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M] in
@[simp]
theorem val_zsmul (n : ℤ) (x : RestrictScalars f M) : (n • x).val = n • x.val := rfl

omit [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M] in
@[simp]
theorem val_smul (r : R) (x : RestrictScalars f M) : (r • x).val = r • x.val := rfl

omit [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M] in
@[simp]
theorem linearEquiv_apply (x : RestrictScalars f M) : linearEquiv f M x = x.val := by rfl

omit [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M] in
@[simp]
theorem linearEquiv_symm_apply (x : M) :
    (linearEquiv f M).symm x = RestrictScalars.mk x := by rfl

omit [Module R M] [IsScalarTower R Bᵐᵒᵖ M] in
/-- On underlying elements, restricted scalar multiplication is multiplication by the image
under `f`. -/
@[simp]
theorem val_op_smul (a : A) (x : RestrictScalars f M) :
    (op a • x).val = op (f a) • x.val := rfl

omit [Module R M] [IsScalarTower R Bᵐᵒᵖ M] in
/-- On underlying elements, an opposite scalar acts through its image under `f`. -/
theorem val_smul_eq (a : Aᵐᵒᵖ) (x : RestrictScalars f M) :
    (a • x).val = AlgHom.op f.toGradedAlgHom.toAlgHom a • x.val := rfl

instance : IsScalarTower R Aᵐᵒᵖ (RestrictScalars f M) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    rw [MulOpposite.algebraMap_apply]
    apply RestrictScalars.ext
    rw [val_op_smul, val_smul]
    have hf : f (algebraMap R A r) = algebraMap R B r := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
        Algebra.algebraMap_eq_smul_one]
    rw [hf]
    simpa only [MulOpposite.algebraMap_apply] using algebraMap_smul Bᵐᵒᵖ r x.val

end RestrictScalars

end DGRightModule

namespace IsDGRightModule

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R Bᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [DirectSum.Decomposition ℳ]
  {dM : M →ₗ[R] M}

variable (f : DGAlgHom hA hB)

/-- The grading of a module does not change under restriction of scalars. -/
noncomputable def restrictScalarsGrading (q : ℤ) :
    Submodule R (DGRightModule.RestrictScalars f M) :=
  ((InternalGrading.ofDecomposition ℳ).map
    (DGRightModule.RestrictScalars.linearEquiv f M).symm).piece q

omit [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ] in
@[simp]
theorem mem_restrictScalarsGrading_iff {q : ℤ} {x : DGRightModule.RestrictScalars f M} :
    x ∈ restrictScalarsGrading (ℳ := ℳ) f q ↔
      DGRightModule.RestrictScalars.linearEquiv f M x ∈ ℳ q := by
  simpa only [restrictScalarsGrading, LinearEquiv.symm_symm,
    InternalGrading.ofDecomposition_piece] using
      (InternalGrading.ofDecomposition ℳ).mem_map_piece_iff
        (DGRightModule.RestrictScalars.linearEquiv f M).symm q x

/- The grading is by definition the transported grading `InternalGrading.map`, which already
carries a decomposition; we read the instance off that definition. -/
noncomputable instance : DirectSum.Decomposition (restrictScalarsGrading (ℳ := ℳ) f) :=
  inferInstanceAs (DirectSum.Decomposition
    (((InternalGrading.ofDecomposition ℳ).map
      (DGRightModule.RestrictScalars.linearEquiv f M).symm).piece))

noncomputable instance : SetLike.GradedSMul
    (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (restrictScalarsGrading (ℳ := ℳ) f) where
  smul_mem {i j a x} ha hx := by
    rw [mem_restrictScalarsGrading_iff] at hx ⊢
    rw [DGRightModule.RestrictScalars.linearEquiv_apply] at hx ⊢
    rw [DGRightModule.RestrictScalars.val_smul_eq]
    have ha' : AlgHom.op f.toGradedAlgHom.toAlgHom a ∈
        (InternalGrading.ofDecomposition ℬ).opposite.piece i := by
      rw [(InternalGrading.ofDecomposition ℬ).mem_opposite_piece_iff]
      have haA : a.unop ∈ 𝒜 i := by
        simpa only [InternalGrading.ofDecomposition_piece] using
          ((InternalGrading.ofDecomposition 𝒜).mem_opposite_piece_iff i a).mp ha
      simpa [InternalGrading.ofDecomposition_piece] using
        Graded.map_mem f haA
    exact SetLike.GradedSMul.smul_mem ha' hx

/-- The differential of a restricted module is its original differential. -/
def restrictScalarsDifferential :
    DGRightModule.RestrictScalars f M →ₗ[R] DGRightModule.RestrictScalars f M :=
  (DGRightModule.RestrictScalars.linearEquiv f M).symm.toLinearMap ∘ₗ dM ∘ₗ
    (DGRightModule.RestrictScalars.linearEquiv f M).toLinearMap

omit [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M] in
@[simp]
theorem val_restrictScalarsDifferential (x : DGRightModule.RestrictScalars f M) :
    (restrictScalarsDifferential (dM := dM) f x).val = dM x.val := by rfl

/-- Restrict a right DG module along a morphism of DG algebras. -/
theorem restrictScalars (hM : IsDGRightModule hB ℳ dM) :
    IsDGRightModule hA (restrictScalarsGrading (ℳ := ℳ) f)
      (restrictScalarsDifferential (dM := dM) f) where
  isHomogeneous := by
    rw [LinearMap.isHomogeneous_def]
    intro q x hx
    rw [mem_restrictScalarsGrading_iff] at hx ⊢
    rw [DGRightModule.RestrictScalars.linearEquiv_apply] at hx ⊢
    rw [val_restrictScalarsDifferential]
    exact hM.isHomogeneous.map_mem hx
  sq_zero x := by
    apply DGRightModule.RestrictScalars.ext
    rw [val_restrictScalarsDifferential, val_restrictScalarsDifferential, hM.sq_zero,
      DGRightModule.RestrictScalars.val_zero]
  leibniz {q x} hx a := by
    apply DGRightModule.RestrictScalars.ext
    rw [val_restrictScalarsDifferential, DGRightModule.RestrictScalars.val_op_smul,
      DGRightModule.RestrictScalars.val_add, DGRightModule.RestrictScalars.val_op_smul,
      val_restrictScalarsDifferential, Units.smul_def,
      DGRightModule.RestrictScalars.val_zsmul, DGRightModule.RestrictScalars.val_op_smul,
      ← DGAlgHom.map_d]
    exact hM.leibniz
      ((mem_restrictScalarsGrading_iff (ℳ := ℳ) (f := f)).mp hx) (f a)

end IsDGRightModule

namespace DGRightModuleHom

variable {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module Bᵐᵒᵖ P] [IsScalarTower R Bᵐᵒᵖ P]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {ℳP : ℤ → Submodule R P}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳP]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition ℳP]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P}
  {hM : IsDGRightModule hB ℳ dM} {hN : IsDGRightModule hB 𝒩 dN}
  {hP : IsDGRightModule hB ℳP dP}

variable (f : DGAlgHom hA hB)

/-- Restrict a morphism of right DG modules along a morphism of DG algebras. -/
noncomputable def restrictScalars (g : DGRightModuleHom hM hN) :
    DGRightModuleHom (hM.restrictScalars f) (hN.restrictScalars f) :=
  let map : DGRightModule.RestrictScalars f M →ₗ[Aᵐᵒᵖ] DGRightModule.RestrictScalars f N :=
    { toFun := fun x ↦ DGRightModule.RestrictScalars.mk (g x.val)
      map_add' := fun x y ↦ by
        apply DGRightModule.RestrictScalars.ext
        rw [DGRightModule.RestrictScalars.val_add,
          DGRightModule.RestrictScalars.val_add]
        exact map_add g x.val y.val
      map_smul' := fun a x ↦ by
        apply DGRightModule.RestrictScalars.ext
        rw [DGRightModule.RestrictScalars.val_smul_eq,
          DGRightModule.RestrictScalars.val_smul_eq]
        exact map_smul g (AlgHom.op f.toGradedAlgHom.toAlgHom a) x.val }
  have val_map (x : DGRightModule.RestrictScalars f M) : (map x).val = g x.val := rfl
  { toLinearMap := map
    map_mem' hx := by
      rw [IsDGRightModule.mem_restrictScalarsGrading_iff] at hx ⊢
      exact Graded.map_mem g hx
    map_d' x := by
      apply DGRightModule.RestrictScalars.ext
      rw [IsDGRightModule.val_restrictScalarsDifferential, val_map, val_map,
        IsDGRightModule.val_restrictScalarsDifferential]
      exact g.map_d x.val }

@[simp]
theorem val_restrictScalars (g : DGRightModuleHom hM hN)
    (x : DGRightModule.RestrictScalars f M) :
    (g.restrictScalars f x).val = g x.val := by rfl

/-- Restriction of scalars preserves identity morphisms. -/
@[simp]
theorem restrictScalars_id :
    (DGRightModuleHom.id hM).restrictScalars f =
      DGRightModuleHom.id (hM.restrictScalars f) := by
  apply DGRightModuleHom.ext
  intro x
  apply DGRightModule.RestrictScalars.ext
  rw [val_restrictScalars, DGRightModuleHom.id_apply, DGRightModuleHom.id_apply]

/-- Restriction of scalars preserves composition. -/
@[simp]
theorem restrictScalars_comp (g : DGRightModuleHom hN hP) (k : DGRightModuleHom hM hN) :
    (g.comp k).restrictScalars f = (g.restrictScalars f).comp (k.restrictScalars f) := by
  apply DGRightModuleHom.ext
  intro x
  apply DGRightModule.RestrictScalars.ext
  rw [val_restrictScalars, DGRightModuleHom.comp_apply, DGRightModuleHom.comp_apply,
    val_restrictScalars, val_restrictScalars]

end DGRightModuleHom

end TauCeti
