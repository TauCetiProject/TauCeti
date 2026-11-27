/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.Algebra.Module.Torsion.Localization
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Lattice
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.LinearAlgebra.SesquilinearForm.TorsionFree

/-!
# Integral pairings and their dual lattices

An integral pairing gives an inclusion of the original lattice into its dual after scalar
extension. The pairing map into the linear dual represents this inclusion. In the nondegenerate
case this gives the perfect-pairing criterion for self-duality and the Gram determinant formula
for the relative index.

## References

* The Gram determinant proof adapts Andrew Yang's dual-basis computation in Mathlib's
  `NumberField.absNorm_differentIdeal`.
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

/-- Under `dualSubmoduleEquivDual` and the equivalence onto the unit-tensor image of a
torsion-free module, the inclusion into the fraction-field dual lattice is the integral
pairing map. -/
theorem dualSubmoduleEquivDual_comp_inclusion_range_mk_one [IsTorsionFree R M]
    (B : LinearMap.BilinForm R M) (hB : (B.baseChange K).Nondegenerate) :
    let N := LinearMap.range (TensorProduct.mk R K M 1)
    let u := LinearEquiv.ofInjective (TensorProduct.mk R K M 1)
      (IsTorsionFree.mk_one_injective_of_isFractionRing K)
    let e := ((B.baseChange K).dualSubmoduleEquivDual hB N).trans u.dualMap
    e.toLinearMap.comp ((Submodule.inclusion (B.range_mk_one_le_dualSubmodule (K := K))).comp
      u.toLinearMap) = B := by
  ext x y
  apply FaithfulSMul.algebraMap_injective R K
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
    LinearEquiv.dualMap_apply, dualSubmoduleEquivDual_apply, dualSubmoduleToDual_apply_apply,
    dualSubmodulePairing_spec, Submodule.coe_inclusion, LinearEquiv.ofInjective_apply,
    TensorProduct.mk_apply]
  simp [Algebra.algebraMap_eq_smul_one]

/-- An integral form on a finite reflexive module with nondegenerate scalar extension is
perfect exactly when the integral lattice in the fraction-field extension is self-dual. -/
theorem dualSubmodule_range_mk_eq_self_iff_isPerfPair [Module.IsReflexive R M]
    (B : LinearMap.BilinForm R M) (hB : (B.baseChange K).Nondegenerate) :
    let N := LinearMap.range (TensorProduct.mk R K M 1)
    (B.baseChange K).dualSubmodule N = N ↔ B.IsPerfPair := by
  let N := LinearMap.range (TensorProduct.mk R K M 1)
  let D := (B.baseChange K).dualSubmodule N
  have hND : N ≤ D := B.range_mk_one_le_dualSubmodule
  let i := Submodule.inclusion hND
  let u := LinearEquiv.ofInjective (TensorProduct.mk R K M 1)
    (IsTorsionFree.mk_one_injective_of_isFractionRing K)
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

/-- For an integral pairing with nondegenerate rational extension, the relative index of the
unit-tensor lattice in its rational dual is the absolute Gram determinant. -/
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
  let u := LinearEquiv.ofInjective (TensorProduct.mk ℤ ℚ M 1)
    (IsTorsionFree.mk_one_injective_of_isFractionRing ℚ)
  let e := ((B.baseChange ℚ).dualSubmoduleEquivDual hB N).trans u.dualMap
  have hcomp : e.toLinearMap.comp ((Submodule.inclusion hND).comp u.toLinearMap) = B :=
    B.dualSubmoduleEquivDual_comp_inclusion_range_mk_one hB
  have hindex : N.toAddSubgroup.relIndex D.toAddSubgroup =
      ((b.dualBasis.map e.symm).det fun i ↦ Submodule.inclusion hND (b.map u i)).natAbs :=
    AddSubgroup.relIndex_eq_natAbs_det N.toAddSubgroup D.toAddSubgroup hND (b.map u)
      (b.dualBasis.map e.symm)
  have hm : e.symm.symm ∘ (fun i ↦ Submodule.inclusion hND (b.map u i)) = B ∘ b := by
    funext i
    simpa only [Function.comp_apply, LinearEquiv.symm_symm, Basis.map_apply, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap] using congr($hcomp (b i))
  have hmatrix : (b.dualBasis.map e.symm).toMatrix
      (fun i ↦ Submodule.inclusion hND (b.map u i)) = (B.toMatrix b).transpose := by
    rw [Basis.toMatrix_map, hm, ← LinearMap.toMatrix_eq_basisToMatrix,
      Basis.toMatrix_dualBasis_eq_transpose_toMatrix₂]
    ext i j
    simp only [Matrix.transpose_apply, LinearMap.toMatrix₂_apply, toMatrix_apply]
  simpa only [Basis.det_apply, hmatrix, Matrix.det_transpose] using hindex

/-- A nondegenerate integral form on a finite module has positive dual-lattice index. -/
theorem relIndex_dualSubmodule_range_mk_one_pos [Module.Finite ℤ M]
    (B : LinearMap.BilinForm ℤ M) (hB : B.Nondegenerate) :
    let N := LinearMap.range (TensorProduct.mk ℤ ℚ M 1)
    0 < N.toAddSubgroup.relIndex ((B.baseChange ℚ).dualSubmodule N).toAddSubgroup := by
  classical
  have := hB.1.isTorsionFree
  let b := Module.Free.chooseBasis ℤ M
  dsimp only
  rw [B.relIndex_dualSubmodule_range_mk_one_eq_natAbs_det
    (hB.baseChange_of_isLocalization ℚ (nonZeroDivisors ℤ)) b]
  exact Int.natAbs_pos.mpr ((nondegenerate_iff_det_ne_zero b).mp hB)

end Int

end LinearMap.BilinForm
