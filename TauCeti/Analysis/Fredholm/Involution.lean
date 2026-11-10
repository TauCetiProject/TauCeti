/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Involutions and the doubling of the Fredholm index

Let `σ_X` and `σ_Y` be continuous linear involutions of topological vector spaces `X` and `Y`
over a field in which `2 ≠ 0`, and let `J_X`, `J_Y` be continuous linear maps with `J² = -1` that
anticommute with them. A continuous linear operator `T : X →L Y` commuting with `σ` maps each
eigenspace `ker (σ_X - μ)` into `ker (σ_Y - μ)`. Splitting `X` and `Y` into their `±1`-eigenspaces
conjugates `T` to the product of its two restrictions, and `J` exchanges the two eigenspaces. If `T`
also commutes with `J`, this conjugates the restriction to the `1`-eigenspaces to the restriction to
the `-1`-eigenspaces. Hence the kernel and the cokernel of `T` have twice the dimension of those of
its restriction to the `1`-eigenspaces, `T` is Fredholm exactly when that restriction is, and the
index doubles.

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
  double. These hold without any Fredholm hypothesis.
* `ContinuousLinearMap.isFredholm_iff_isFredholm_restrictEigenspace`: Fredholmness is detected on
  the `1`-eigenspaces.
-/

@[expose] public section

namespace ContinuousLinearMap

open Module Module.End

section Conjugation

variable {𝕜 E E' F F' : Type*} [Field 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F']

/-- Conjugate operators have linearly equivalent kernels. -/
private def kerEquivOfComp (T : E →L[𝕜] F) (S : E' →L[𝕜] F') (e : E ≃L[𝕜] E')
    (e' : F ≃L[𝕜] F') (h : (e' : F →L[𝕜] F').comp T = S.comp (e : E →L[𝕜] E')) :
    T.ker ≃ₗ[𝕜] S.ker :=
  (e.toLinearEquiv.submoduleMap T.ker).trans <| LinearEquiv.ofEq _ _ <| by
    ext y
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    have := congr($h (e.symm y))
    simp only [coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
      ContinuousLinearEquiv.apply_symm_apply] at this
    change T (e.symm y) = 0 ↔ S y = 0
    rw [← this, map_eq_zero_iff e' e'.injective]

/-- Conjugate operators have linearly equivalent cokernels. -/
private def cokerEquivOfComp (T : E →L[𝕜] F) (S : E' →L[𝕜] F') (e : E ≃L[𝕜] E')
    (e' : F ≃L[𝕜] F') (h : (e' : F →L[𝕜] F').comp T = S.comp (e : E →L[𝕜] E')) :
    (F ⧸ T.range) ≃ₗ[𝕜] F' ⧸ S.range :=
  Submodule.Quotient.equiv _ _ e'.toLinearEquiv <| by
    have h' := congr(ContinuousLinearMap.toLinearMap $h)
    simp only [toLinearMap_comp, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap] at h'
    rw [← LinearMap.range_comp, h',
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 e.surjective)]

/-- `finrank (M × N) = 2 * finrank M` when `M ≃ N`, including when both are infinite-dimensional
and the `finrank`s vanish. -/
private lemma finrank_prod_eq_two_mul {M N : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] (e : M ≃ₗ[𝕜] N) :
    finrank 𝕜 (M × N) = 2 * finrank 𝕜 M := by
  by_cases hM : Module.Finite 𝕜 M
  · have := Module.Finite.equiv e
    rw [Module.finrank_prod, ← e.finrank_eq]
    ring
  · have hMN : ¬ Module.Finite 𝕜 (M × N) := fun h ↦
      hM (Module.Finite.of_surjective (LinearMap.fst 𝕜 M N) LinearMap.fst_surjective)
    rw [finrank_of_not_finite hM, finrank_of_not_finite hMN]

end Conjugation

section FredholmConjugation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Conjugate operators are simultaneously Fredholm. -/
private lemma isFredholm_iff_of_comp_eq {E E' F F' : Type*}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F']
    {T : E →L[𝕜] F} {S : E' →L[𝕜] F'} (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] F')
    (h : (e' : F →L[𝕜] F').comp T = S.comp (e : E →L[𝕜] E')) : IsFredholm T ↔ IsFredholm S := by
  have hS : S = ((e' : F →L[𝕜] F').comp T).comp (e.symm : E' →L[𝕜] E) := by
    rw [h]
    ext x
    simp
  have hT : T = ((e'.symm : F' →L[𝕜] F).comp S).comp (e : E →L[𝕜] E') := by
    rw [hS]
    ext x
    simp
  refine ⟨fun hT' ↦ ?_, fun hS' ↦ ?_⟩
  · rw [hS]
    exact (hT'.equiv_comp e').comp_equiv e.symm
  · rw [hT]
    exact (hS'.equiv_comp e'.symm).comp_equiv e

end FredholmConjugation

section Restrict

variable {𝕜 X Y : Type*} [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]

/-- An operator `T` intertwining `σX` and `σY` maps the `μ`-eigenspace of `σX` into the
`μ`-eigenspace of `σY`; this is the restricted operator. -/
def restrictEigenspace (T : X →L[𝕜] Y) {σX : X →L[𝕜] X} {σY : Y →L[𝕜] Y}
    (hT : T.comp σX = σY.comp T) (μ : 𝕜) :
    eigenspace (σX : End 𝕜 X) μ →L[𝕜] eigenspace (σY : End 𝕜 Y) μ :=
  T.restrict fun x hx ↦ by
    rw [mem_eigenspace_iff] at hx ⊢
    have := congr($hT x)
    simp only [coe_comp, Function.comp_apply] at this
    simp only [coe_coe] at hx ⊢
    rw [← this, hx, map_smul]

@[simp]
lemma coe_restrictEigenspace_apply (T : X →L[𝕜] Y) {σX : X →L[𝕜] X} {σY : Y →L[𝕜] Y}
    (hT : T.comp σX = σY.comp T) (μ : 𝕜) (x : eigenspace (σX : End 𝕜 X) μ) :
    (T.restrictEigenspace hT μ x : Y) = T x :=
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
      simp only [coprod_apply, prod_apply, Submodule.subtypeL_apply, coe_codRestrict_apply,
        smul_apply, add_apply, sub_apply, id_apply]
      rw [← smul_add, show x + σ x + (x - σ x) = (2 : 𝕜) • x by module, smul_smul,
        inv_mul_cancel₀ two_ne_zero, one_smul])
    (fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ by
      rw [mem_eigenspace_iff] at ha hb
      simp only [coe_coe, one_smul, neg_smul] at ha hb
      ext <;>
      simp [ha, hb, ← add_smul, ← two_mul, mul_inv_cancel₀ (two_ne_zero (α := 𝕜))])

@[simp]
lemma coe_equivEigenspaceProd_fst (σ : X →L[𝕜] X) (hσ : Function.Involutive σ) (x : X) :
    ((equivEigenspaceProd σ hσ x).1 : X) = (2 : 𝕜)⁻¹ • (x + σ x) :=
  rfl

@[simp]
lemma coe_equivEigenspaceProd_snd (σ : X →L[𝕜] X) (hσ : Function.Involutive σ) (x : X) :
    ((equivEigenspaceProd σ hσ x).2 : X) = (2 : 𝕜)⁻¹ • (x - σ x) :=
  rfl

@[simp]
lemma equivEigenspaceProd_symm_apply (σ : X →L[𝕜] X) (hσ : Function.Involutive σ)
    (p : eigenspace (σ : End 𝕜 X) 1 × eigenspace (σ : End 𝕜 X) (-1)) :
    (equivEigenspaceProd σ hσ).symm p = (p.1 : X) + p.2 :=
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

variable {𝕜 X : Type*} [Field 𝕜]
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
    (eigenspaceNegEquiv hJ hJσ μ x : X) = J x :=
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
  set A := T.restrictEigenspace hT 1
  set B := T.restrictEigenspace hT (-1)
  have hB : A.ker ≃ₗ[𝕜] B.ker := kerEquivOfComp A B _ _
    (restrictEigenspace_comp_eigenspaceNegEquiv T hJX hJσX hJY hJσY hT hTJ 1).symm
  rw [(kerEquivOfComp T (A.prodMap B) _ _ (equivEigenspaceProd_comp T hσX hσY hT)).finrank_eq,
    coe_prodMap, LinearMap.ker_prodMap, (Submodule.prodEquiv _ _).finrank_eq,
    finrank_prod_eq_two_mul hB]

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
  set A := T.restrictEigenspace hT 1
  set B := T.restrictEigenspace hT (-1)
  have hB := cokerEquivOfComp A B _ _
    (restrictEigenspace_comp_eigenspaceNegEquiv T hJX hJσX hJY hJσY hT hTJ 1).symm
  rw [(cokerEquivOfComp T (A.prodMap B) _ _ (equivEigenspaceProd_comp T hσX hσY hT)).finrank_eq,
    coe_prodMap, LinearMap.range_prodMap, (Submodule.quotientProdEquiv _ _).finrank_eq,
    finrank_prod_eq_two_mul hB]

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

section Fredholm

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NeZero (2 : 𝕜)]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [IsTopologicalAddGroup X]
variable [ContinuousSMul 𝕜 X] [T2Space X]
variable [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
variable [ContinuousSMul 𝕜 Y] [T2Space Y]
variable {σX JX : X →L[𝕜] X} {σY JY : Y →L[𝕜] Y}

/-- An operator commuting with the involutions `σ` and the anticommuting maps `J` is Fredholm if
and only if its restriction to the `1`-eigenspaces is. -/
theorem isFredholm_iff_isFredholm_restrictEigenspace (T : X →L[𝕜] Y)
    (hσX : Function.Involutive σX) (hσY : Function.Involutive σY)
    (hJX : JX.comp JX = -ContinuousLinearMap.id 𝕜 X) (hJσX : σX.comp JX = -JX.comp σX)
    (hJY : JY.comp JY = -ContinuousLinearMap.id 𝕜 Y) (hJσY : σY.comp JY = -JY.comp σY)
    (hT : T.comp σX = σY.comp T) (hTJ : T.comp JX = JY.comp T) :
    IsFredholm T ↔ IsFredholm (T.restrictEigenspace hT 1) := by
  set A := T.restrictEigenspace hT 1
  set B := T.restrictEigenspace hT (-1)
  have hconj := equivEigenspaceProd_comp T hσX hσY hT
  have hswap := restrictEigenspace_comp_eigenspaceNegEquiv T hJX hJσX hJY hJσY hT hTJ 1
  rw [isFredholm_iff_of_comp_eq _ _ hconj, isFredholm_prodMap_iff,
    ← isFredholm_iff_of_comp_eq _ _ hswap.symm, and_self]

end Fredholm

end ContinuousLinearMap
