/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import TauCeti.LinearAlgebra.Dimension.Prod
public import TauCeti.LinearAlgebra.LinearEquiv.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Involutions and the doubling of kernels, cokernels and indices

Let `σ_X` and `σ_Y` be continuous linear involutions of topological vector spaces `X` and `Y`
over a field in which `2 ≠ 0`, and let `J_X`, `J_Y` be continuous linear maps with `J² = -1` that
anticommute with them. A continuous linear operator `T : X →L Y` commuting with `σ` maps each
eigenspace `ker (σ_X - μ)` into `ker (σ_Y - μ)`. Splitting `X` and `Y` into their `±1`-eigenspaces
conjugates `T` to the product of its two restrictions, and `J` exchanges the two eigenspaces. If `T`
also commutes with `J`, this conjugates the restriction to the `1`-eigenspaces to the restriction to
the `-1`-eigenspaces. Hence the kernel and the cokernel of `T` have twice the dimension of those of
its restriction to the `1`-eigenspaces, and the index doubles. None of this needs any Fredholm
hypothesis; the corresponding statement about Fredholmness is
`TauCeti.Analysis.Fredholm.Involution`.

This is the abstract form of the doubling step for real Cauchy–Riemann operators with totally real
boundary conditions, McDuff–Salamon, *J-holomorphic Curves and Symplectic Topology*, proof of
Theorem C.1.10: the operator on the doubled bundle commutes with the lifted reflection `τ` and
with multiplication by `i`, which anticommutes with `τ`, and the `τ`-invariant part is the operator
with the boundary condition.

## Main declarations

* `ContinuousLinearMap.restrictEigenspace`: the restriction of an intertwining operator to
  eigenspaces with the same eigenvalue.
* `ContinuousLinearMap.equivEigenspaceProd`: the splitting `X ≃L ker (σ - 1) × ker (σ + 1)` of a
  space by a continuous linear involution, and `ContinuousLinearMap.equivEigenspaceProd_comp`,
  which conjugates an intertwining operator to the product of its restrictions.
* `ContinuousLinearMap.eigenspaceNegEquiv`: a map `J` with `J² = -1` anticommuting with `σ`
  identifies the `μ`- and `-μ`-eigenspaces of `σ`, and
  `ContinuousLinearMap.restrictEigenspace_comp_eigenspaceNegEquiv` intertwines the restrictions.
* `ContinuousLinearMap.finrank_ker_eq_two_mul_finrank_ker_restrictEigenspace`,
  `ContinuousLinearMap.finrank_coker_eq_two_mul_finrank_coker_restrictEigenspace` and
  `ContinuousLinearMap.index_eq_two_mul_index_restrictEigenspace`: the kernel, cokernel and index
  double.
-/

public section

namespace ContinuousLinearMap

open Module Module.End

section Restrict

variable {𝕜 X Y : Type*} [CommRing 𝕜]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]

/-- An operator `T` intertwining `σX` and `σY` maps the `μ`-eigenspace of `σX` into the
`μ`-eigenspace of `σY`; this is the restricted operator. -/
def restrictEigenspace (T : X →L[𝕜] Y) {σX : X →L[𝕜] X} {σY : Y →L[𝕜] Y}
    (hT : T.comp σX = σY.comp T) (μ : 𝕜) :
    eigenspace (σX : End 𝕜 X) μ →L[𝕜] eigenspace (σY : End 𝕜 Y) μ :=
  T.restrict fun _ hx ↦
    mapsTo_genEigenspace_of_comp (T : X →ₗ[𝕜] Y) congr(toLinearMap $hT.symm) μ 1 hx

@[simp]
lemma coe_restrictEigenspace_apply (T : X →L[𝕜] Y) {σX : X →L[𝕜] X} {σY : Y →L[𝕜] Y}
    (hT : T.comp σX = σY.comp T) (μ : 𝕜) (x : eigenspace (σX : End 𝕜 X) μ) :
    (T.restrictEigenspace hT μ x : Y) = T x := by
  rfl

end Restrict

section Involution

variable {𝕜 X : Type*} [Field 𝕜] [NeZero (2 : 𝕜)]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [IsTopologicalAddGroup X]
variable [ContinuousConstSMul 𝕜 X]

/-- A continuous linear involution `σ` splits `X` as the product of its `1`- and
`-1`-eigenspaces, through `x ↦ (2⁻¹ • (x + σ x), 2⁻¹ • (x - σ x))`. -/
noncomputable def equivEigenspaceProd (σ : X →L[𝕜] X) (hσ : Function.Involutive σ) :
    X ≃L[𝕜] eigenspace (σ : End 𝕜 X) 1 × eigenspace (σ : End 𝕜 X) (-1) :=
  ContinuousLinearEquiv.equivOfInverse
    ((((2 : 𝕜)⁻¹ • (ContinuousLinearMap.id 𝕜 X + σ)).codRestrict _ fun x ↦ by
        rw [mem_eigenspace_iff]
        simp [hσ x, add_comm]).prod
      (((2 : 𝕜)⁻¹ • (ContinuousLinearMap.id 𝕜 X - σ)).codRestrict _ fun x ↦ by
        rw [mem_eigenspace_iff]
        simp [hσ x, smul_sub]
        abel))
    ((Submodule.subtypeL _).coprod (Submodule.subtypeL _))
    (fun x ↦ by
      have h2 : x + σ x + (x - σ x) = (2 : 𝕜) • x := by module
      simp only [coprod_apply, prod_apply, Submodule.subtypeL_apply, coe_codRestrict_apply,
        smul_apply, add_apply, sub_apply, id_apply]
      rw [← smul_add, h2, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul])
    (fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ by
      rw [mem_eigenspace_iff] at ha hb
      simp only [coe_coe, one_smul, neg_smul] at ha hb
      ext <;>
      simp [ha, hb, ← add_smul, ← two_mul, mul_inv_cancel₀ (two_ne_zero (α := 𝕜))])

@[simp]
lemma coe_equivEigenspaceProd_fst (σ : X →L[𝕜] X) (hσ : Function.Involutive σ) (x : X) :
    ((equivEigenspaceProd σ hσ x).1 : X) = (2 : 𝕜)⁻¹ • (x + σ x) := by
  rfl

@[simp]
lemma coe_equivEigenspaceProd_snd (σ : X →L[𝕜] X) (hσ : Function.Involutive σ) (x : X) :
    ((equivEigenspaceProd σ hσ x).2 : X) = (2 : 𝕜)⁻¹ • (x - σ x) := by
  rfl

@[simp]
lemma equivEigenspaceProd_symm_apply (σ : X →L[𝕜] X) (hσ : Function.Involutive σ)
    (p : eigenspace (σ : End 𝕜 X) 1 × eigenspace (σ : End 𝕜 X) (-1)) :
    (equivEigenspaceProd σ hσ).symm p = (p.1 : X) + p.2 := by
  rfl

variable {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
variable [ContinuousConstSMul 𝕜 Y]

/-- Splitting by the involutions conjugates an intertwining operator to the product of its
restrictions to the `1`- and `-1`-eigenspaces. -/
lemma equivEigenspaceProd_comp (T : X →L[𝕜] Y) {σX : X →L[𝕜] X} {σY : Y →L[𝕜] Y}
    (hσX : Function.Involutive σX) (hσY : Function.Involutive σY) (hT : T.comp σX = σY.comp T) :
    (equivEigenspaceProd σY hσY : Y →L[𝕜] _).comp T =
      ((T.restrictEigenspace hT 1).prodMap (T.restrictEigenspace hT (-1))).comp
        (equivEigenspaceProd σX hσX : X →L[𝕜] _) := by
  have hTx (x : X) : T (σX x) = σY (T x) := congr($hT x)
  ext x
  · simp [hTx]
  · simp [hTx]

end Involution

section Anticommute

variable {𝕜 X : Type*} [CommRing 𝕜]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [IsTopologicalAddGroup X]

/-- A continuous linear map `J` with `J² = -1` anticommuting with `σ` maps the `μ`-eigenspace of
`σ` isomorphically onto its `-μ`-eigenspace, with inverse `-J`. -/
def eigenspaceNegEquiv {σ J : X →L[𝕜] X} (hJ : J.comp J = -ContinuousLinearMap.id 𝕜 X)
    (hJσ : σ.comp J = -J.comp σ) (μ : 𝕜) :
    eigenspace (σ : End 𝕜 X) μ ≃L[𝕜] eigenspace (σ : End 𝕜 X) (-μ) :=
  have hJσx (x : X) : σ (J x) = -J (σ x) := congr($hJσ x)
  ContinuousLinearEquiv.equivOfInverse
    (J.restrict fun x hx ↦ by
      rw [mem_eigenspace_iff] at hx ⊢
      simp only [coe_coe] at hx ⊢
      rw [hJσx, hx, map_smul, neg_smul])
    ((-J).restrict fun x hx ↦ by
      rw [mem_eigenspace_iff] at hx ⊢
      simp only [coe_coe, neg_apply, map_neg] at hx ⊢
      rw [hJσx, hx, map_smul, neg_smul, neg_neg, smul_neg])
    (fun x ↦ Subtype.ext <| by simpa using congr(-$hJ x))
    (fun x ↦ Subtype.ext <| by simpa using congr(-$hJ x))

@[simp]
lemma coe_eigenspaceNegEquiv_apply {σ J : X →L[𝕜] X}
    (hJ : J.comp J = -ContinuousLinearMap.id 𝕜 X) (hJσ : σ.comp J = -J.comp σ) (μ : 𝕜)
    (x : eigenspace (σ : End 𝕜 X) μ) :
    (eigenspaceNegEquiv hJ hJσ μ x : X) = J x := by
  rfl

@[simp]
lemma coe_eigenspaceNegEquiv_symm_apply {σ J : X →L[𝕜] X}
    (hJ : J.comp J = -ContinuousLinearMap.id 𝕜 X) (hJσ : σ.comp J = -J.comp σ) (μ : 𝕜)
    (y : eigenspace (σ : End 𝕜 X) (-μ)) :
    ((eigenspaceNegEquiv hJ hJσ μ).symm y : X) = -J y := by
  rfl

variable {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- An operator commuting with `σ` and `J` intertwines its restrictions to the `μ`- and
`-μ`-eigenspaces through `eigenspaceNegEquiv`. -/
lemma restrictEigenspace_comp_eigenspaceNegEquiv (T : X →L[𝕜] Y) {σX JX : X →L[𝕜] X}
    {σY JY : Y →L[𝕜] Y} (hJX : JX.comp JX = -ContinuousLinearMap.id 𝕜 X)
    (hJσX : σX.comp JX = -JX.comp σX) (hJY : JY.comp JY = -ContinuousLinearMap.id 𝕜 Y)
    (hJσY : σY.comp JY = -JY.comp σY) (hT : T.comp σX = σY.comp T)
    (hTJ : T.comp JX = JY.comp T) (μ : 𝕜) :
    (T.restrictEigenspace hT (-μ)).comp (eigenspaceNegEquiv hJX hJσX μ : _ →L[𝕜] _) =
      (eigenspaceNegEquiv hJY hJσY μ : _ →L[𝕜] _).comp (T.restrictEigenspace hT μ) := by
  ext x
  simpa using congr($hTJ x)

end Anticommute

section Doubling

variable {𝕜 X Y : Type*} [Field 𝕜] [NeZero (2 : 𝕜)]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [IsTopologicalAddGroup X]
variable [ContinuousConstSMul 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
variable [ContinuousConstSMul 𝕜 Y]
variable {σX JX : X →L[𝕜] X} {σY JY : Y →L[𝕜] Y}

/-- The kernel of an operator commuting with the involutions `σ` and the anticommuting maps `J`
has twice the dimension of the kernel of its restriction to the `1`-eigenspaces. If the kernel is
infinite-dimensional, both sides vanish. -/
theorem finrank_ker_eq_two_mul_finrank_ker_restrictEigenspace (T : X →L[𝕜] Y)
    (hσX : Function.Involutive σX) (hσY : Function.Involutive σY)
    (hJX : JX.comp JX = -ContinuousLinearMap.id 𝕜 X) (hJσX : σX.comp JX = -JX.comp σX)
    (hJY : JY.comp JY = -ContinuousLinearMap.id 𝕜 Y) (hJσY : σY.comp JY = -JY.comp σY)
    (hT : T.comp σX = σY.comp T) (hTJ : T.comp JX = JY.comp T) :
    finrank 𝕜 T.ker = 2 * finrank 𝕜 (T.restrictEigenspace hT 1).ker := by
  have hconj := congr(toLinearMap $(equivEigenspaceProd_comp T hσX hσY hT))
  have hswap :=
    congr(toLinearMap $(restrictEigenspace_comp_eigenspaceNegEquiv T hJX hJσX hJY hJσY hT hTJ 1))
  simp only [toLinearMap_comp, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
    at hconj hswap
  rw [(LinearMap.kerEquivOfComp _ _ hconj).finrank_eq, coe_prodMap, LinearMap.ker_prodMap,
    (Submodule.prodEquiv _ _).finrank_eq,
    ((LinearEquiv.refl 𝕜 _).prodCongr (LinearMap.kerEquivOfComp _ _ hswap.symm).symm).finrank_eq,
    finrank_prod_self]

/-- The cokernel of an operator commuting with the involutions `σ` and the anticommuting maps `J`
has twice the dimension of the cokernel of its restriction to the `1`-eigenspaces. If the cokernel
is infinite-dimensional, both sides vanish. -/
theorem finrank_coker_eq_two_mul_finrank_coker_restrictEigenspace (T : X →L[𝕜] Y)
    (hσX : Function.Involutive σX) (hσY : Function.Involutive σY)
    (hJX : JX.comp JX = -ContinuousLinearMap.id 𝕜 X) (hJσX : σX.comp JX = -JX.comp σX)
    (hJY : JY.comp JY = -ContinuousLinearMap.id 𝕜 Y) (hJσY : σY.comp JY = -JY.comp σY)
    (hT : T.comp σX = σY.comp T) (hTJ : T.comp JX = JY.comp T) :
    finrank 𝕜 (Y ⧸ T.range) =
      2 * finrank 𝕜 (eigenspace (σY : End 𝕜 Y) 1 ⧸ (T.restrictEigenspace hT 1).range) := by
  have hconj := congr(toLinearMap $(equivEigenspaceProd_comp T hσX hσY hT))
  have hswap :=
    congr(toLinearMap $(restrictEigenspace_comp_eigenspaceNegEquiv T hJX hJσX hJY hJσY hT hTJ 1))
  simp only [toLinearMap_comp, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
    at hconj hswap
  rw [(LinearMap.cokerEquivOfComp _ _ hconj).finrank_eq, coe_prodMap, LinearMap.range_prodMap,
    (Submodule.quotientProdEquiv _ _).finrank_eq,
    ((LinearEquiv.refl 𝕜 _).prodCongr
      (LinearMap.cokerEquivOfComp _ _ hswap.symm).symm).finrank_eq,
    finrank_prod_self]

/-- The index of an operator commuting with the involutions `σ` and the anticommuting maps `J` is
twice the index of its restriction to the `1`-eigenspaces. -/
theorem index_eq_two_mul_index_restrictEigenspace (T : X →L[𝕜] Y)
    (hσX : Function.Involutive σX) (hσY : Function.Involutive σY)
    (hJX : JX.comp JX = -ContinuousLinearMap.id 𝕜 X) (hJσX : σX.comp JX = -JX.comp σX)
    (hJY : JY.comp JY = -ContinuousLinearMap.id 𝕜 Y) (hJσY : σY.comp JY = -JY.comp σY)
    (hT : T.comp σX = σY.comp T) (hTJ : T.comp JX = JY.comp T) :
    T.index = 2 * (T.restrictEigenspace hT 1).index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub,
    finrank_ker_eq_two_mul_finrank_ker_restrictEigenspace T hσX hσY hJX hJσX hJY hJσY hT hTJ,
    finrank_coker_eq_two_mul_finrank_coker_restrictEigenspace T hσX hσY hJX hJσX hJY hJσY hT hTJ]
  push_cast
  ring

end Doubling

end ContinuousLinearMap
