/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Lattice
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# Integral pairings and their dual lattices

An integral pairing gives an inclusion of the original lattice into its dual after scalar
extension. The pairing map into the linear dual represents this inclusion. In the nondegenerate
case this gives the perfect-pairing criterion for self-duality and the Gram determinant formula
for the relative index.
-/

public section

open scoped TensorProduct
open Module

namespace LinearMap.BilinForm

/-- The unit-tensor image of an integral bilinear form is contained in its dual lattice. -/
theorem range_mk_one_le_dualSubmodule {R K M : Type*}
    [CommRing R] [Field K] [Algebra R K] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) :
    let N := LinearMap.range (TensorProduct.mk R K M 1)
    N ≤ (B.baseChange K).dualSubmodule N := by
  dsimp only
  rintro _ ⟨x, rfl⟩
  refine (mem_dualSubmodule (B.baseChange K)
    (N := LinearMap.range (TensorProduct.mk R K M 1))).2 ?_
  rintro _ ⟨y, rfl⟩
  exact Submodule.mem_one.2 ⟨B x y, by simp [Algebra.algebraMap_eq_smul_one]⟩

section FractionField

variable {R K M : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Under `dualSubmoduleEquivDual` and `TensorProduct.unitTmulEquiv`, the inclusion into the
fraction-field dual lattice is the integral pairing map. -/
theorem dualSubmoduleEquivDual_comp_inclusion_range_mk_one [Module.Flat R M]
    (B : LinearMap.BilinForm R M) (hB : (B.baseChange K).Nondegenerate) :
    let N := LinearMap.range (TensorProduct.mk R K M 1)
    let u := TensorProduct.unitTmulEquiv R K M
    let e := ((B.baseChange K).dualSubmoduleEquivDual hB N).trans u.dualMap
    e.toLinearMap.comp ((Submodule.inclusion (B.range_mk_one_le_dualSubmodule (K := K))).comp
      u.toLinearMap) = B := by
  ext x y
  apply FaithfulSMul.algebraMap_injective R K
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
    LinearEquiv.dualMap_apply, dualSubmoduleEquivDual_apply, dualSubmoduleToDual_apply_apply,
    dualSubmodulePairing_spec, Submodule.coe_inclusion, TensorProduct.coe_unitTmulEquiv_apply]
  simp [Algebra.algebraMap_eq_smul_one]

/-- An integral form with nondegenerate scalar extension identifies the original module with its
linear dual exactly when the integral lattice in the fraction-field extension is self-dual.
The inclusion is identified with the pairing map by `dualSubmoduleEquivDual` and
`TensorProduct.unitTmulEquiv`. -/
theorem dualSubmodule_range_mk_eq_self_iff_isPerfPair [Module.Flat R M] [Module.IsReflexive R M]
    (B : LinearMap.BilinForm R M) (hB : (B.baseChange K).Nondegenerate) :
    let N := LinearMap.range (TensorProduct.mk R K M 1)
    (B.baseChange K).dualSubmodule N = N ↔ B.IsPerfPair := by
  let N := LinearMap.range (TensorProduct.mk R K M 1)
  let D := (B.baseChange K).dualSubmodule N
  have hND : N ≤ D := B.range_mk_one_le_dualSubmodule
  let i := Submodule.inclusion hND
  let u := TensorProduct.unitTmulEquiv R K M
  let e := ((B.baseChange K).dualSubmoduleEquivDual hB N).trans u.dualMap
  have hcomp : e.toLinearMap.comp (i.comp u.toLinearMap) = B :=
    B.dualSubmoduleEquivDual_comp_inclusion_range_mk_one hB
  constructor
  · intro h
    have hD : D = N := h
    have hs : Function.Bijective i :=
      ⟨Submodule.inclusion_injective hND, fun x ↦ ⟨⟨x, hD ▸ x.property⟩, Subtype.ext rfl⟩⟩
    exact .of_bijective B (hcomp ▸ e.bijective.comp (hs.comp u.bijective))
  · intro h
    apply le_antisymm (fun x hx ↦ ?_) hND
    obtain ⟨y, hy⟩ := h.bijective_left.surjective (e ⟨x, hx⟩)
    have hxy : i (u y) = ⟨x, hx⟩ := e.injective (by
      simpa only [← hcomp, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hy)
    have heq : (u y : K ⊗[R] M) = x := congrArg Subtype.val hxy
    exact heq ▸ (u y).property

end FractionField

section Int

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- The relative index of the unit-tensor lattice in its rational dual is the absolute Gram
determinant. The argument uses the dual-basis computation in Andrew Yang's
`NumberField.absNorm_differentIdeal` in Mathlib, expressed here in the integral bases via
`dualSubmoduleEquivDual`. -/
theorem relIndex_dualSubmodule_range_mk_one_eq_natAbs_det (B : LinearMap.BilinForm ℤ M)
    (hB : (B.baseChange ℚ).Nondegenerate) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ M) :
    let N := LinearMap.range (TensorProduct.mk ℤ ℚ M 1)
    N.toAddSubgroup.relIndex ((B.baseChange ℚ).dualSubmodule N).toAddSubgroup =
      (B.toMatrix b).det.natAbs := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  let N := LinearMap.range (TensorProduct.mk ℤ ℚ M 1)
  let D := (B.baseChange ℚ).dualSubmodule N
  have hND : N ≤ D := B.range_mk_one_le_dualSubmodule
  let u := TensorProduct.unitTmulEquiv ℤ ℚ M
  let e := ((B.baseChange ℚ).dualSubmoduleEquivDual hB N).trans u.dualMap
  have hcomp : e.toLinearMap.comp ((Submodule.inclusion hND).comp u.toLinearMap) = B :=
    B.dualSubmoduleEquivDual_comp_inclusion_range_mk_one hB
  have hindex : N.toAddSubgroup.relIndex D.toAddSubgroup =
      ((b.dualBasis.map e.symm).det fun i ↦ Submodule.inclusion hND (b.map u i)).natAbs :=
    AddSubgroup.relIndex_eq_natAbs_det N.toAddSubgroup D.toAddSubgroup hND (b.map u)
      (b.dualBasis.map e.symm)
  dsimp only
  rw [hindex, Basis.det_apply, Basis.toMatrix_map]
  have hm : e.symm.symm ∘ (fun i ↦ Submodule.inclusion hND (b.map u i)) = B ∘ b := by
    funext i
    simpa only [Function.comp_apply, LinearEquiv.symm_symm, Basis.map_apply, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap] using congr($hcomp (b i))
  rw [hm, ← LinearMap.toMatrix_eq_basisToMatrix, Basis.toMatrix_dualBasis_eq_transpose_toMatrix₂,
    Matrix.det_transpose]
  rfl

/-- A nondegenerate integral form on a finite free module has positive dual-lattice index. -/
theorem relIndex_dualSubmodule_range_mk_one_pos [Module.Free ℤ M] [Module.Finite ℤ M]
    (B : LinearMap.BilinForm ℤ M) (hB : B.Nondegenerate) :
    let N := LinearMap.range (TensorProduct.mk ℤ ℚ M 1)
    0 < N.toAddSubgroup.relIndex ((B.baseChange ℚ).dualSubmodule N).toAddSubgroup := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  dsimp only
  rw [B.relIndex_dualSubmodule_range_mk_one_eq_natAbs_det
    (hB.baseChange_of_isLocalization ℚ (nonZeroDivisors ℤ)) b]
  exact Int.natAbs_pos.mpr ((nondegenerate_iff_det_ne_zero b).mp hB)

end Int

end LinearMap.BilinForm
