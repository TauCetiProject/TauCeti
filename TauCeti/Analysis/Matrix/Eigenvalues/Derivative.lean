/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Group.Subgroup
public import TauCeti.Analysis.Matrix.Eigenvalues.Projector
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Topology.Algebra.Module.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Star
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous

/-!
# Smoothness and Hadamard variation of simple Hermitian eigenvalues and projectors

At any Hermitian matrix `A` over an `RCLike` field `𝕜` whose `k`-th sorted eigenvalue `λₖ(A)` is
simple (`∀ j ≠ k, λⱼ(A) ≠ λₖ(A)`), both `X ↦ λₖ(X)` and `X ↦ Pₖ(X)` are real-analytic (`C^ω`) near
`A` in `selfAdjoint (Matrix n n 𝕜)`, and hence on `{X | StrictAnti X.2.isHermitian.eigenvalues₀}`.
Differentiating via an implicit-function eigenvector branch yields Hadamard's first and second
variation formulas.

## Main definitions and results

* `Matrix.traceCLM`, `Matrix.isOpen_setOf_forall_eigenvalues₀_ne`, and
  `Matrix.isOpen_setOf_strictAnti_eigenvalues₀`.
* `TauCeti.contDiffAt_rankOneHermitianProjector`, `Matrix.contDiffAt_eigenprojector₀`,
  `Matrix.contDiffAt_eigenvalues₀`, `Matrix.contDiffOn_eigenprojector₀_strictAnti`, and
  `Matrix.contDiffOn_eigenvalues₀_strictAnti`.
* `Matrix.hasStrictFDerivAt_eigenprojector₀`, `Matrix.hasStrictFDerivAt_eigenvalues₀`,
  `Matrix.hasStrictFDerivAt_fderiv_eigenvalues₀`, and directional derivatives along `t ↦ A + t • B`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices* (2010), §4.3.1.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter II, §1–§2.
-/

public section

noncomputable section

open scoped ContDiff Topology Matrix.Norms.L2Operator ComplexOrder

/-- Local `ℝ`-normed algebra structure on `Matrix n n 𝕜` induced by the Euclidean operator norm. -/
local instance matrixNormedAlgebraReal {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] :
    NormedAlgebra ℝ (Matrix n n 𝕜) :=
  Matrix.l2OpNormedAlgebraReal

section FiniteBilinear

variable (𝕜 : Type*) {E F G : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

private def mkCLM₂ (f : E →ₗ[𝕜] F →ₗ[𝕜] G) : E →L[𝕜] F →L[𝕜] G :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (F →ₗ[𝕜] G) ≃ₗ[𝕜] (F →L[𝕜] G)).toLinearMap.comp f)

@[simp]
private theorem mkCLM₂_apply (f : E →ₗ[𝕜] F →ₗ[𝕜] G) (x : E) (y : F) :
    mkCLM₂ 𝕜 f x y = f x y := rfl

end FiniteBilinear

section DiagBilinear

variable {𝕜 E G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

private theorem contDiff_diag_clm₂ (B : E →L[𝕜] E →L[𝕜] G) {m : ℕ∞ω} :
    ContDiff 𝕜 m (fun x : E ↦ B x x) :=
  B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)

private theorem hasStrictFDerivAt_diag_clm₂ (B : E →L[𝕜] E →L[𝕜] G) (x : E) :
    HasStrictFDerivAt (fun v : E ↦ B v v) (B x + B.flip x) x := by
  refine (B.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id x)
    (hasStrictFDerivAt_id x)).congr_fderiv ?_
  ext y; simp

end DiagBilinear

namespace Matrix

section Openness

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The sorted eigenvalue map is continuous on `selfAdjoint (Matrix n n 𝕜)`. -/
@[fun_prop]
theorem continuous_selfAdjoint_eigenvalues₀ :
    Continuous (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀) :=
  continuous_eigenvalues₀.comp (continuous_subtype_val.subtype_mk fun X ↦ X.2.isHermitian)

/-- Self-adjoint matrices whose `k`-th sorted eigenvalue is simple form an open set. -/
theorem isOpen_setOf_forall_eigenvalues₀_ne (k : Fin (Fintype.card n)) :
    IsOpen {X : selfAdjoint (Matrix n n 𝕜) |
      ∀ j ≠ k, X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k} := by
  have heq : {X : selfAdjoint (Matrix n n 𝕜) |
      ∀ j ≠ k, X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k} =
      ⋂ j ∈ Finset.univ.erase k, {X : selfAdjoint (Matrix n n 𝕜) |
        X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k} := by
    ext X; simp [Finset.mem_erase]
  rw [heq]
  exact isOpen_biInter_finset fun j _ ↦ isOpen_ne_fun
    ((continuous_apply j).comp continuous_selfAdjoint_eigenvalues₀)
    ((continuous_apply k).comp continuous_selfAdjoint_eigenvalues₀)

/-- The open Weyl chamber `{X | StrictAnti X.2.isHermitian.eigenvalues₀}` is open. -/
theorem isOpen_setOf_strictAnti_eigenvalues₀ :
    IsOpen {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.2.isHermitian.eigenvalues₀} := by
  have heq : {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.2.isHermitian.eigenvalues₀} =
      ⋂ i : Fin (Fintype.card n), ⋂ j : {j : Fin (Fintype.card n) // i < j},
        {X : selfAdjoint (Matrix n n 𝕜) |
          X.2.isHermitian.eigenvalues₀ j.1 < X.2.isHermitian.eigenvalues₀ i} := by
    ext X; simp [StrictAnti, Subtype.forall]
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦ isOpen_lt
    ((continuous_apply j.1).comp continuous_selfAdjoint_eigenvalues₀)
    ((continuous_apply i).comp continuous_selfAdjoint_eigenvalues₀)

end Openness

section TraceCLM

variable (𝕜 n : Type*) [RCLike 𝕜] [Fintype n] [DecidableEq n]

private def entryCLM (i j : n) : Matrix n n 𝕜 →L[𝕜] 𝕜 :=
  (Matrix.entryLinearMap 𝕜 𝕜 i j).mkContinuous 1 fun M ↦ by
    simpa using M.norm_apply_le_l2_opNorm i j

/-- Matrix trace as a continuous `𝕜`-linear map under the Euclidean operator norm. -/
def traceCLM : Matrix n n 𝕜 →L[𝕜] 𝕜 := ∑ i : n, entryCLM 𝕜 n i i

/-- Applying `Matrix.traceCLM` evaluates `Matrix.trace`. -/
@[simp]
theorem traceCLM_apply {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (M : Matrix n n 𝕜) : traceCLM 𝕜 n M = M.trace := by
  simp [traceCLM, entryCLM, Matrix.trace]

end TraceCLM

end Matrix

section RankOneProjectorCalculus

open Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

private def dotProductLeftCLM (w : n → 𝕜) : (n → 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap (dotProductBilin 𝕜 𝕜 w)

@[simp]
private theorem dotProductLeftCLM_apply (w y : n → 𝕜) : dotProductLeftCLM w y = w ⬝ᵥ y := rfl

private def reInnerBilin (𝕜 n : Type*) [RCLike 𝕜] [Fintype n] :
    (n → 𝕜) →L[ℝ] (n → 𝕜) →L[ℝ] ℝ :=
  mkCLM₂ ℝ <| LinearMap.mk₂ ℝ (fun u v ↦ RCLike.re (star u ⬝ᵥ v))
    (fun u₁ u₂ v ↦ by rw [star_add, add_dotProduct, map_add])
    (fun c u v ↦ by rw [star_smul, star_trivial, smul_dotProduct, RCLike.smul_re, smul_eq_mul])
    (fun u v₁ v₂ ↦ by rw [dotProduct_add, map_add])
    (fun c u v ↦ by rw [dotProduct_smul, RCLike.smul_re, smul_eq_mul])

@[simp]
private theorem reInnerBilin_apply (u v : n → 𝕜) :
    reInnerBilin 𝕜 n u v = RCLike.re (star u ⬝ᵥ v) := rfl

private theorem re_dotProduct_star_self_eq (v : n → 𝕜) :
    ((RCLike.re (star v ⬝ᵥ v) : ℝ) : 𝕜) = star v ⬝ᵥ v :=
  RCLike.conj_eq_iff_re.mp (star_dotProduct v v).symm

private theorem rankOneHermitianProjector_eq_real_smul (v : n → 𝕜) :
    TauCeti.rankOneHermitianProjector v =
      (RCLike.re (star v ⬝ᵥ v))⁻¹ • Matrix.vecMulVec v (star v) := by
  rw [TauCeti.rankOneHermitianProjector_def, RCLike.real_smul_eq_coe_smul (K := 𝕜),
    RCLike.ofReal_inv, re_dotProduct_star_self_eq]

private theorem hasStrictFDerivAt_re_dotProduct_star_self (u : n → 𝕜) :
    HasStrictFDerivAt (fun v : n → 𝕜 ↦ RCLike.re (star v ⬝ᵥ v))
      ((2 : ℝ) • reInnerBilin 𝕜 n u) u := by
  refine (hasStrictFDerivAt_diag_clm₂ (reInnerBilin 𝕜 n) u).congr_fderiv ?_
  ext y
  have hsymm : RCLike.re (star y ⬝ᵥ u) = RCLike.re (star u ⬝ᵥ y) := by
    rw [← RCLike.conj_re (star u ⬝ᵥ y), ← RCLike.star_def, star_dotProduct]
  simp [hsymm, two_mul]

section WithDecidableEq

variable [DecidableEq n]

private def vecMulVecStarBilin (𝕜 n : Type*) [RCLike 𝕜] [Fintype n] [DecidableEq n] :
    (n → 𝕜) →L[ℝ] (n → 𝕜) →L[ℝ] Matrix n n 𝕜 :=
  mkCLM₂ ℝ <| LinearMap.mk₂ ℝ (fun u v ↦ Matrix.vecMulVec u (star v))
    (fun u₁ u₂ v ↦ by ext i j; simp [vecMulVec_apply, add_mul])
    (fun c u v ↦ by ext i j; simp [vecMulVec_apply, RCLike.real_smul_eq_coe_mul, mul_assoc])
    (fun u v₁ v₂ ↦ by ext i j; simp [vecMulVec_apply, mul_add])
    (fun c u v ↦ by ext i j; simp [vecMulVec_apply, RCLike.real_smul_eq_coe_mul, mul_left_comm])

@[simp]
private theorem vecMulVecStarBilin_apply (u v : n → 𝕜) :
    vecMulVecStarBilin 𝕜 n u v = Matrix.vecMulVec u (star v) := rfl

private theorem hasStrictFDerivAt_rankOneHermitianProjector_unit
    {u : n → 𝕜} (hu : star u ⬝ᵥ u = 1) :
    HasStrictFDerivAt (TauCeti.rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜)
      ((vecMulVecStarBilin 𝕜 n).flip u + vecMulVecStarBilin 𝕜 n u -
        ((2 : ℝ) • reInnerBilin 𝕜 n u).smulRight (Matrix.vecMulVec u (star u))) u := by
  rw [funext rankOneHermitianProjector_eq_real_smul]
  have hre : RCLike.re (star u ⬝ᵥ u) = 1 := by simp [hu]
  have hinv := (hasStrictDerivAt_inv (by simp [hre] : RCLike.re (star u ⬝ᵥ u) ≠ 0))
    |>.comp_hasStrictFDerivAt u (hasStrictFDerivAt_re_dotProduct_star_self u)
  refine (hinv.smul (hasStrictFDerivAt_diag_clm₂ (vecMulVecStarBilin 𝕜 n) u)).congr_fderiv ?_
  ext y i j; simp [hre, sub_eq_add_neg, add_comm]

namespace TauCeti

/-- `TauCeti.rankOneHermitianProjector` is `C^m` over `ℝ` at every nonzero vector `v : n → 𝕜`. -/
theorem contDiffAt_rankOneHermitianProjector {v : n → 𝕜} (hv : v ≠ 0) {m : ℕ∞ω} :
    ContDiffAt ℝ m (TauCeti.rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜) v := by
  rw [funext rankOneHermitianProjector_eq_real_smul]
  have hne : RCLike.re (star v ⬝ᵥ v) ≠ 0 := fun h0 ↦
    dotProduct_star_self_eq_zero.not.mpr hv
      (by rw [← re_dotProduct_star_self_eq v, h0, RCLike.ofReal_zero])
  exact ((contDiff_diag_clm₂ (reInnerBilin 𝕜 n) (m := m)).contDiffAt.inv hne).smul
    (contDiff_diag_clm₂ (vecMulVecStarBilin 𝕜 n) (m := m)).contDiffAt

end TauCeti

end WithDecidableEq

end RankOneProjectorCalculus

namespace Matrix

section ImplicitBranch

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

private def mulVecCLM₂ (𝕜 n : Type*) [RCLike 𝕜] [Fintype n] [DecidableEq n] :
    Matrix n n 𝕜 →L[𝕜] (n → 𝕜) →L[𝕜] (n → 𝕜) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 mulVec add_mulVec smul_mulVec mulVec_add fun c M v ↦ mulVec_smul M c v)
    (Fintype.card n) fun M y ↦ (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i ↦ by
      calc ‖(M *ᵥ y) i‖ ≤ ∑ j, ‖M i j * y j‖ := norm_sum_le _ _
        _ ≤ ∑ _j : n, ‖M‖ * ‖y‖ := Finset.sum_le_sum fun j _ ↦ by
            rw [norm_mul]
            exact mul_le_mul (M.norm_apply_le_l2_opNorm i j) (norm_le_pi_norm y j)
              (norm_nonneg _) (norm_nonneg _)
        _ = Fintype.card n * ‖M‖ * ‖y‖ := by simp [mul_assoc]

@[simp]
private theorem mulVecCLM₂_apply (M : Matrix n n 𝕜) (y : n → 𝕜) :
    mulVecCLM₂ 𝕜 n M y = M *ᵥ y := rfl

private def eigNormMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : Fin (Fintype.card n))
    (p : Matrix n n 𝕜 × (n → 𝕜)) : n → 𝕜 :=
  let u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  (1 - hA.eigenprojector₀ k) *ᵥ (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2) +
    (star u₀ ⬝ᵥ p.2) • u₀

private theorem eigNormMap_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) : eigNormMap hA k (A, 0) = 0 := by
  simp [eigNormMap, hA.mulVec_eigenvectorBasis₀_coe, sub_mulVec, mulVec_smul,
    hA.eigenprojector₀_mulVec_eigenvectorBasis₀_self]

private theorem eigNormMap_eq_zero_imp {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) {B : Matrix n n 𝕜} {w : n → 𝕜} (h0 : eigNormMap hA k (B, w) = 0) :
    star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ w = 0 ∧
      B *ᵥ (⇑(hA.eigenvectorBasis₀ k) + w) =
        (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (B *ᵥ (⇑(hA.eigenvectorBasis₀ k) + w))) •
          (⇑(hA.eigenvectorBasis₀ k) + w) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set P₀ : Matrix n n 𝕜 := hA.eigenprojector₀ k
  have horth : ∀ y : n → 𝕜, star u₀ ⬝ᵥ ((1 - P₀) *ᵥ y) = 0 := fun y ↦ by
    rw [sub_mulVec, one_mulVec, hA.eigenprojector₀_mulVec, dotProduct_sub, dotProduct_smul,
      hA.dotProduct_star_eigenvectorBasis₀_self, smul_eq_mul, mul_one, sub_self]
  have hw : star u₀ ⬝ᵥ w = 0 := by
    simpa [eigNormMap, u₀, P₀, dotProduct_add, dotProduct_smul, horth,
      hA.dotProduct_star_eigenvectorBasis₀_self] using congrArg (star u₀ ⬝ᵥ ·) h0
  refine ⟨hw, sub_eq_zero.mp ?_⟩
  set α : 𝕜 := star u₀ ⬝ᵥ (B *ᵥ (u₀ + w))
  have hsub : (1 - P₀) *ᵥ u₀ = 0 := by
    rw [sub_mulVec, one_mulVec, hA.eigenprojector₀_mulVec_eigenvectorBasis₀_self, sub_self]
  have hproj : (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) = 0 := by
    rw [smul_add, add_comm (α • u₀), ← sub_sub, mulVec_sub, mulVec_smul, hsub, smul_zero, sub_zero]
    simpa [eigNormMap, u₀, P₀, α, hw] using h0
  have hsc : star u₀ ⬝ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_add,
      hA.dotProduct_star_eigenvectorBasis₀_self, hw, add_zero, smul_eq_mul, mul_one, sub_self]
  calc B *ᵥ (u₀ + w) - α • (u₀ + w)
      = (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) +
          (star u₀ ⬝ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w))) • u₀ := by
        rw [sub_mulVec, one_mulVec, hA.eigenprojector₀_mulVec, sub_add_cancel]
    _ = 0 := by rw [hproj, hsc, zero_smul, add_zero]

private theorem contDiff_mulVec_uncurry {m : ℕ∞ω} :
    ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ p.2) :=
  (mulVecCLM₂ 𝕜 n).isBoundedBilinearMap.contDiff

private theorem contDiff_eigNormMap {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) {m : ℕ∞ω} : ContDiff 𝕜 m (eigNormMap hA k) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  have hBw : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ (u₀ + p.2)) :=
    contDiff_mulVec_uncurry.comp (contDiff_fst.prodMk (contDiff_const.add contDiff_snd))
  have hdot : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) :=
    ((dotProductLeftCLM (star u₀)).contDiff (n := m)).comp hBw
  have hpart1 : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      mulVecCLM₂ 𝕜 n (1 - hA.eigenprojector₀ k)
        (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2)) :=
    ((mulVecCLM₂ 𝕜 n (1 - hA.eigenprojector₀ k)).contDiff (n := m)).comp
      (hBw.sub (hdot.smul contDiff_snd))
  have hdot2 : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ p.2) :=
    ((dotProductLeftCLM (star u₀)).contDiff (n := m)).comp contDiff_snd
  exact hpart1.add (hdot2.smul contDiff_const)

private theorem eigNormMap_linear_simplify {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) (H : Matrix n n 𝕜) (y : n → 𝕜) :
    (1 - hA.eigenprojector₀ k) *ᵥ
        (H *ᵥ ⇑(hA.eigenvectorBasis₀ k) + A *ᵥ y - (hA.eigenvalues₀ k : 𝕜) • y) +
      (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ y) • ⇑(hA.eigenvectorBasis₀ k) =
      (1 - hA.eigenprojector₀ k) *ᵥ (H *ᵥ ⇑(hA.eigenvectorBasis₀ k)) +
        (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) *ᵥ y := by
  have hPAy : hA.eigenprojector₀ k *ᵥ (A *ᵥ y - (hA.eigenvalues₀ k : 𝕜) • y) = 0 := by
    rw [mulVec_sub, hA.eigenprojector₀_mulVec, dotProduct_mulVec,
      hA.star_eigenvectorBasis₀_vecMul, smul_dotProduct, smul_eq_mul, mulVec_smul,
      hA.eigenprojector₀_mulVec, ← mul_smul, sub_self]
  rw [add_sub_assoc, mulVec_add, sub_mulVec (1 : Matrix n n 𝕜) _ (A *ᵥ y - _), one_mulVec, hPAy,
    sub_zero, add_assoc]
  congr 1
  rw [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, hA.eigenprojector₀_mulVec]

private theorem fderiv_eigNormMap_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    fderiv 𝕜 (eigNormMap hA k) (A, 0) =
      ((mulVecCLM₂ 𝕜 n (1 - hA.eigenprojector₀ k)).comp
        ((mulVecCLM₂ 𝕜 n).flip ⇑(hA.eigenvectorBasis₀ k))).comp
          (ContinuousLinearMap.fst 𝕜 (Matrix n n 𝕜) (n → 𝕜)) +
      (mulVecCLM₂ 𝕜 n (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k)).comp
        (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  let fst := ContinuousLinearMap.fst 𝕜 (Matrix n n 𝕜) (n → 𝕜)
  let snd := ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)
  have hBw : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ (u₀ + p.2))
      (((mulVecCLM₂ 𝕜 n).flip u₀).comp fst + (mulVecCLM₂ 𝕜 n A).comp snd) (A, 0) := by
    refine ((mulVecCLM₂ 𝕜 n).hasFDerivAt_of_bilinear fst.hasFDerivAt
      ((hasFDerivAt_const u₀ (A, 0)).add snd.hasFDerivAt)).congr_fderiv
      (ContinuousLinearMap.ext fun ⟨H, y⟩ ↦ ?_)
    ext i; simp [fst, snd, add_comm]
  have hsc := (dotProductLeftCLM (star u₀)).hasFDerivAt.comp (A, 0) hBw
  have hsmul : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2) ((hA.eigenvalues₀ k : 𝕜) • snd) (A, 0) := by
    refine (hsc.smul snd.hasFDerivAt).congr_fderiv <| ContinuousLinearMap.ext fun p ↦ ?_
    ext i; simp [u₀, snd, hA.mulVec_eigenvectorBasis₀_coe, RCLike.real_smul_eq_coe_mul (K := 𝕜)]
  have hpart1 := (mulVecCLM₂ 𝕜 n (1 - hA.eigenprojector₀ k)).hasFDerivAt.comp (A, 0)
    (hBw.sub hsmul)
  let L2 := ((dotProductLeftCLM (star u₀)).comp snd).smulRight u₀
  refine (hpart1.add L2.hasFDerivAt).fderiv.trans <| ContinuousLinearMap.ext fun ⟨H, y⟩ ↦ ?_
  simp only [u₀, L2, fst, snd, add_apply, ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', mulVecCLM₂_apply,
    dotProductLeftCLM_apply]
  exact eigNormMap_linear_simplify hA k H y

private def reducedResolventPlusProj {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) : Matrix n n 𝕜 :=
  hA.eigenprojector₀ k + ∑ j ∈ Finset.univ.erase k,
    (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j

private theorem mul_reducedResolventPlusProj {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) *
      reducedResolventPlusProj hA k = 1 := by
  have hterm_k : (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) *
      hA.eigenprojector₀ k = hA.eigenprojector₀ k := by
    rw [add_mul, sub_mul, hA.mul_eigenprojector₀, Matrix.smul_mul, one_mul, sub_self, zero_add,
      hA.eigenprojector₀_mul_self]
  have hterm_j : ∀ j ∈ Finset.univ.erase k,
      (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) *
        ((((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j) =
      hA.eigenprojector₀ j := fun j hj ↦ by
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    have hinv : (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) *
        ((hA.eigenvalues₀ j : 𝕜) - (hA.eigenvalues₀ k : 𝕜)) = 1 := by
      exact_mod_cast inv_mul_cancel₀ (sub_ne_zero.mpr (hk j hjk))
    rw [Matrix.mul_smul, add_mul, sub_mul, hA.mul_eigenprojector₀, Matrix.smul_mul, one_mul,
      hA.eigenprojector₀_mul_of_ne hjk.symm, add_zero, ← sub_smul, smul_smul, hinv, one_smul]
  rw [reducedResolventPlusProj, mul_add, hterm_k, Matrix.mul_sum,
    Finset.sum_congr rfl hterm_j, Finset.add_sum_erase _ _ (Finset.mem_univ k),
    hA.sum_eigenprojector₀]

private theorem reducedResolventPlusProj_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    reducedResolventPlusProj hA k *
      (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) = 1 := by
  simpa [reducedResolventPlusProj, conjTranspose_sum, conjTranspose_smul, hA.eq,
    (hA.isHermitian_eigenprojector₀ _).eq, RCLike.star_def] using
    congrArg conjTranspose (mul_reducedResolventPlusProj hA hk)

private theorem comp_reducedResolventPlusProj_id {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    ((fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
        ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)).comp
      (mulVecCLM₂ 𝕜 n (reducedResolventPlusProj hA k)) = ContinuousLinearMap.id 𝕜 (n → 𝕜)) ∧
      ((mulVecCLM₂ 𝕜 n (reducedResolventPlusProj hA k)).comp
        (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
          ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)) =
        ContinuousLinearMap.id 𝕜 (n → 𝕜)) := by
  have hinr : fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
      ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜) =
      mulVecCLM₂ 𝕜 n (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) := by
    ext y i; simp [fderiv_eigNormMap_self hA k]
  rw [hinr]
  constructor
  · exact ContinuousLinearMap.ext fun y ↦ by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, mulVecCLM₂_apply,
        mulVec_mulVec, mul_reducedResolventPlusProj hA hk, one_mulVec]
  · exact ContinuousLinearMap.ext fun y ↦ by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, mulVecCLM₂_apply,
        mulVec_mulVec, reducedResolventPlusProj_mul hA hk, one_mulVec]

private theorem isInvertible_fderiv_eigNormMap_inr {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
      ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (comp_reducedResolventPlusProj_id hA hk).1 (comp_reducedResolventPlusProj_id hA hk).2

private def localEigPerturb {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    Matrix n n 𝕜 → (n → 𝕜) :=
  ((contDiff_eigNormMap hA k (m := ω)).contDiffAt (x := (A, 0))).implicitFunction
    (by decide) (isInvertible_fderiv_eigNormMap_inr hA hk)

private theorem localEigPerturb_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    localEigPerturb hA hk A = 0 :=
  ContDiffAt.implicitFunction_apply_self _ _ _

private theorem contDiffAt_localEigPerturb {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    ContDiffAt 𝕜 ω (localEigPerturb hA hk) A :=
  ContDiffAt.contDiffAt_implicitFunction _ _ _

private theorem eventually_eigNormMap_localEigPerturb {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    ∀ᶠ B in 𝓝 A, eigNormMap hA k (B, localEigPerturb hA hk B) = 0 := by
  simpa only [localEigPerturb, eigNormMap_self] using ContDiffAt.eventually_apply_implicitFunction
    ((contDiff_eigNormMap hA k (m := ω)).contDiffAt (x := (A, 0)))
    (by decide) (isInvertible_fderiv_eigNormMap_inr hA hk)

private theorem hasStrictFDerivAt_localEigPerturb {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    HasStrictFDerivAt (localEigPerturb hA hk)
      (∑ j ∈ Finset.univ.erase k,
        (((hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ : ℝ) : 𝕜) •
          (mulVecCLM₂ 𝕜 n (hA.eigenprojector₀ j)).comp
            ((mulVecCLM₂ 𝕜 n).flip ⇑(hA.eigenvectorBasis₀ k))) A := by
  have hraw : HasStrictFDerivAt (localEigPerturb hA hk) _ A :=
    ContDiffAt.hasStrictFDerivAt_implicitFunction
      ((contDiff_eigNormMap hA k (m := ω)).contDiffAt (x := (A, 0)))
      (by decide) (isInvertible_fderiv_eigNormMap_inr hA hk)
  have hinv_eq : (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
      ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)).inverse =
      mulVecCLM₂ 𝕜 n (reducedResolventPlusProj hA k) :=
    ContinuousLinearMap.inverse_eq
      (comp_reducedResolventPlusProj_id hA hk).1 (comp_reducedResolventPlusProj_id hA hk).2
  refine hraw.congr_fderiv ?_
  ext H i
  rw [hinv_eq]
  simp only [neg_apply, ContinuousLinearMap.comp_apply, sum_apply, smul_apply,
    fderiv_eigNormMap_self hA k, add_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.flip_apply,
    mulVecCLM₂_apply, mulVec_zero, add_zero]
  have hRproj : reducedResolventPlusProj hA k * (1 - hA.eigenprojector₀ k) =
      ∑ j ∈ Finset.univ.erase k,
        (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j := by
    rw [reducedResolventPlusProj, add_mul, mul_sub, mul_one, hA.eigenprojector₀_mul_self,
      sub_self, zero_add, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [Matrix.smul_mul, mul_sub, mul_one,
        hA.eigenprojector₀_mul_of_ne (Finset.mem_erase.mp hj).1, sub_zero]
  have hvec : -(reducedResolventPlusProj hA k *ᵥ
      ((1 - hA.eigenprojector₀ k) *ᵥ (H *ᵥ ⇑(hA.eigenvectorBasis₀ k)))) =
      ∑ j ∈ Finset.univ.erase k,
        (((hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ : ℝ) : 𝕜) •
          (hA.eigenprojector₀ j *ᵥ (H *ᵥ ⇑(hA.eigenvectorBasis₀ k))) := by
    rw [mulVec_mulVec, hRproj, sum_mulVec, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [smul_mulVec, ← neg_smul]; congr 1; push_cast; rw [← inv_neg, neg_sub]
  simpa [Finset.sum_apply] using congrFun hvec i

private theorem exists_eigenvalues₀_eq_of_mulVec {X : Matrix n n 𝕜} (hX : X.IsHermitian)
    {v : n → 𝕜} (hv_ne : v ≠ 0) {β : 𝕜} (hv : X *ᵥ v = β • v) :
    ∃ m : Fin (Fintype.card n), β = (hX.eigenvalues₀ m : 𝕜) := by
  have hex : ∃ m : Fin (Fintype.card n), star ⇑(hX.eigenvectorBasis₀ m) ⬝ᵥ v ≠ 0 := by
    by_contra! hall
    exact hv_ne (by rw [← hX.sum_dotProduct_smul_eigenvectorBasis₀ v]; simp [hall])
  obtain ⟨m, hm⟩ := hex
  refine ⟨m, mul_right_cancel₀ hm ?_⟩
  calc β * (star ⇑(hX.eigenvectorBasis₀ m) ⬝ᵥ v)
      = star ⇑(hX.eigenvectorBasis₀ m) ⬝ᵥ (X *ᵥ v) := by rw [hv, dotProduct_smul, smul_eq_mul]
    _ = (star ⇑(hX.eigenvectorBasis₀ m) ᵥ* X) ⬝ᵥ v := dotProduct_mulVec _ _ _
    _ = (hX.eigenvalues₀ m : 𝕜) * (star ⇑(hX.eigenvectorBasis₀ m) ⬝ᵥ v) := by
      rw [hX.star_eigenvectorBasis₀_vecMul, smul_dotProduct, smul_eq_mul]

private theorem eventually_localEigRayleigh_ne {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k) :
    ∀ᶠ X : selfAdjoint (Matrix n n 𝕜) in 𝓝 A,
      ∀ j : Fin (Fintype.card n), j ≠ k →
        RCLike.re (star ⇑(A.2.isHermitian.eigenvectorBasis₀ k) ⬝ᵥ
          (X.1 *ᵥ (⇑(A.2.isHermitian.eigenvectorBasis₀ k) +
            localEigPerturb A.2.isHermitian hk X.1))) ≠ X.2.isHermitian.eigenvalues₀ j := by
  set hA := A.2.isHermitian
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set α : selfAdjoint (Matrix n n 𝕜) → ℝ :=
    fun X ↦ reInnerBilin 𝕜 n u₀ (X.1 *ᵥ (u₀ + localEigPerturb hA hk X.1))
  have hw_cont : ContinuousAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦ localEigPerturb hA hk X.1) A :=
    (contDiffAt_localEigPerturb hA hk).continuousAt.comp continuous_subtype_val.continuousAt
  have hα_cont : ContinuousAt α A :=
    (reInnerBilin 𝕜 n u₀).continuous.continuousAt.comp
      ((contDiff_mulVec_uncurry (𝕜 := 𝕜) (n := n) (m := ω)).continuous.continuousAt.comp
        (continuous_subtype_val.continuousAt.prodMk (continuousAt_const.add hw_cont)))
  have hαA : α A = hA.eigenvalues₀ k := by
    simp [α, u₀, localEigPerturb_self hA hk, hA.mulVec_eigenvectorBasis₀_coe, RCLike.smul_re]
  refine Filter.eventually_all.mpr fun j ↦ ?_
  by_cases hjk : j = k
  · exact Filter.Eventually.of_forall fun _ h ↦ (h hjk).elim
  · have hj_cont : ContinuousAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦
        X.2.isHermitian.eigenvalues₀ j) A :=
      ((continuous_apply j).comp continuous_selfAdjoint_eigenvalues₀).continuousAt
    have hne : α A - hA.eigenvalues₀ j ≠ 0 := sub_ne_zero.mpr (hαA.symm ▸ (hk j hjk).symm)
    exact ((hα_cont.sub hj_cont).eventually_ne hne).mono fun X hX _ ↦
      sub_ne_zero.mp (by simpa only [Pi.sub_apply, α, u₀, reInnerBilin_apply] using hX)

private theorem eventuallyEq_eigenprojector₀_rankOne {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k) :
    (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k) =ᶠ[𝓝 A]
      fun X : selfAdjoint (Matrix n n 𝕜) ↦ TauCeti.rankOneHermitianProjector
        (⇑(A.2.isHermitian.eigenvectorBasis₀ k) + localEigPerturb A.2.isHermitian hk X.1) := by
  set hA := A.2.isHermitian
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set v : selfAdjoint (Matrix n n 𝕜) → (n → 𝕜) := fun X ↦ u₀ + localEigPerturb hA hk X.1
  filter_upwards [continuous_subtype_val.continuousAt.eventually
      (eventually_eigNormMap_localEigPerturb hA hk),
    eventually_localEigRayleigh_ne hk,
    (isOpen_setOf_forall_eigenvalues₀_ne k).mem_nhds hk] with X hG hgap hsimple
  obtain ⟨hw_orth, heig⟩ := eigNormMap_eq_zero_imp hA k hG
  have hv_ne : v X ≠ 0 := fun hv0 ↦ by
    have h1 : star u₀ ⬝ᵥ v X = 1 := by simp [v, u₀, dotProduct_add, hw_orth]
    simp [hv0] at h1
  obtain ⟨m, hm⟩ := exists_eigenvalues₀_eq_of_mulVec X.2.isHermitian hv_ne heig
  obtain rfl : m = k := by
    by_contra hmk; exact hgap m hmk (by simpa [v, u₀] using congrArg RCLike.re hm)
  rw [hm] at heig
  exact X.2.isHermitian.eigenprojector₀_eq_rankOneHermitianProjector_of_mulVec hsimple hv_ne heig

end ImplicitBranch

section SmoothAndVariation

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **Analyticity and smoothness of simple spectral projectors** over `ℝ` for every `m : ℕ∞ω`. -/
theorem contDiffAt_eigenprojector₀ {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k) {m : ℕ∞ω} :
    ContDiffAt ℝ m (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k) A := by
  have hu_ne : ⇑(A.2.isHermitian.eigenvectorBasis₀ k) +
      localEigPerturb A.2.isHermitian hk A.1 ≠ 0 := by
    rw [localEigPerturb_self A.2.isHermitian hk, add_zero]
    intro h0; simpa [h0] using A.2.isHermitian.dotProduct_star_eigenvectorBasis₀_self k
  have hv_smooth : ContDiffAt ℝ ω (fun X : selfAdjoint (Matrix n n 𝕜) ↦
      ⇑(A.2.isHermitian.eigenvectorBasis₀ k) + localEigPerturb A.2.isHermitian hk X.1) A :=
    contDiffAt_const.add (((contDiffAt_localEigPerturb A.2.isHermitian hk).restrict_scalars ℝ).comp
      A (selfAdjoint.contDiff_subtype_val ℝ).contDiffAt)
  exact (((TauCeti.contDiffAt_rankOneHermitianProjector hu_ne).comp A hv_smooth)
    |>.congr_of_eventuallyEq (eventuallyEq_eigenprojector₀_rankOne hk)).of_le le_top

/-- **Analyticity and smoothness of simple sorted eigenvalues** over `ℝ` for every `m : ℕ∞ω`. -/
theorem contDiffAt_eigenvalues₀ {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k) {m : ℕ∞ω} :
    ContDiffAt ℝ m (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) A := by
  have hfn : (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) =
      fun X ↦ RCLike.reCLM (traceCLM 𝕜 n (X.2.isHermitian.eigenprojector₀ k * X.1)) := by
    ext X; simp
  rw [hfn]
  exact ((RCLike.reCLM.comp ((traceCLM 𝕜 n).restrictScalars ℝ)).contDiff (n := m)).contDiffAt.comp
    A ((contDiffAt_eigenprojector₀ hk).mul (selfAdjoint.contDiff_subtype_val ℝ).contDiffAt)

/-- On the open Weyl chamber, each spectral projector is `C^m` over `ℝ` for every `m : ℕ∞ω`. -/
theorem contDiffOn_eigenprojector₀_strictAnti (k : Fin (Fintype.card n)) {m : ℕ∞ω} :
    ContDiffOn ℝ m (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k)
      {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.2.isHermitian.eigenvalues₀} :=
  fun _ hX ↦ (contDiffAt_eigenprojector₀ fun _ hjk ↦ hX.injective.ne hjk).contDiffWithinAt

/-- On the open Weyl chamber, each sorted eigenvalue is `C^m` over `ℝ` for every `m : ℕ∞ω`. -/
theorem contDiffOn_eigenvalues₀_strictAnti (k : Fin (Fintype.card n)) {m : ℕ∞ω} :
    ContDiffOn ℝ m (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k)
      {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.2.isHermitian.eigenvalues₀} :=
  fun _ hX ↦ (contDiffAt_eigenvalues₀ fun _ hjk ↦ hX.injective.ne hjk).contDiffWithinAt

private theorem rankOneProjector_deriv_sum_eq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : Fin (Fintype.card n)) :
    let u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
    let dy : n → 𝕜 := ∑ j ∈ Finset.univ.erase k,
      (((hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ : ℝ) : 𝕜) •
        (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀))
    vecMulVec dy (star u₀) + vecMulVec u₀ (star dy) -
        (2 * RCLike.re (star u₀ ⬝ᵥ dy)) • vecMulVec u₀ (star u₀) =
      ∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
        (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j +
          hA.eigenprojector₀ j * B * hA.eigenprojector₀ k) := by
  intro u₀ dy
  have horth : star u₀ ⬝ᵥ dy = 0 := by
    rw [dotProduct_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [dotProduct_smul, hA.eigenprojector₀_mulVec, dotProduct_smul,
      hA.dotProduct_star_eigenvectorBasis₀_of_ne (Finset.mem_erase.mp hj).1.symm, smul_zero,
      smul_zero]
  rw [horth, RCLike.zero_re, mul_zero, zero_smul, sub_zero]
  have hlhs : vecMulVec dy (star u₀) + vecMulVec u₀ (star dy) =
      ∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
        (vecMulVec (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀)) (star u₀) +
          vecMulVec u₀ (star (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀)))) := by
    ext a b
    simp [dy, vecMulVec_apply, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
      RCLike.real_smul_eq_coe_smul (K := 𝕜), mul_assoc, mul_left_comm]
  rw [hlhs]
  refine Finset.sum_congr rfl fun j _ ↦ congrArg _ ?_
  have h1 : vecMulVec (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀)) (star u₀) =
      hA.eigenprojector₀ j * B * hA.eigenprojector₀ k := by
    dsimp only [u₀]; rw [hA.eigenprojector₀_def k, mulVec_mulVec, ← mul_vecMulVec]
  have h2 : vecMulVec u₀ (star (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀))) =
      hA.eigenprojector₀ k * B * hA.eigenprojector₀ j := by
    simpa [conjTranspose_vecMulVec, star_star, conjTranspose_mul, Matrix.mul_assoc,
      hB.eq, (hA.isHermitian_eigenprojector₀ j).eq, (hA.isHermitian_eigenprojector₀ k).eq] using
      congrArg Matrix.conjTranspose h1
  rw [h1, h2, add_comm]

/-- **Hadamard's first variation of a simple spectral projector** on
`selfAdjoint (Matrix n n 𝕜)`. -/
theorem hasStrictFDerivAt_eigenprojector₀ {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k) :
    HasStrictFDerivAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k)
      (∑ j ∈ Finset.univ.erase k,
        (A.2.isHermitian.eigenvalues₀ k - A.2.isHermitian.eigenvalues₀ j)⁻¹ •
          ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜)
              (A.2.isHermitian.eigenprojector₀ k) (A.2.isHermitian.eigenprojector₀ j) +
            ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜)
              (A.2.isHermitian.eigenprojector₀ j) (A.2.isHermitian.eigenprojector₀ k)).comp
            (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)))) A := by
  have hw_deriv := ((hasStrictFDerivAt_localEigPerturb A.2.isHermitian hk).restrictScalars ℝ).comp
    A (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)).hasStrictFDerivAt
  have hv_deriv := ((hasStrictFDerivAt_const ⇑(A.2.isHermitian.eigenvectorBasis₀ k) A).add
    hw_deriv).congr_fderiv (zero_add _)
  have hu_unit : star (⇑(A.2.isHermitian.eigenvectorBasis₀ k) +
      localEigPerturb A.2.isHermitian hk A.1) ⬝ᵥ
      (⇑(A.2.isHermitian.eigenvectorBasis₀ k) + localEigPerturb A.2.isHermitian hk A.1) = 1 := by
    rw [localEigPerturb_self A.2.isHermitian hk, add_zero,
      A.2.isHermitian.dotProduct_star_eigenvectorBasis₀_self]
  refine ((hasStrictFDerivAt_rankOneHermitianProjector_unit hu_unit).comp A hv_deriv
    |>.congr_of_eventuallyEq (eventuallyEq_eigenprojector₀_rankOne hk).symm).congr_fderiv ?_
  ext B : 1
  simp only [localEigPerturb_self A.2.isHermitian hk, add_zero, ContinuousLinearMap.comp_apply,
    sub_apply, add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, sum_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.flip_apply,
    selfAdjoint.subtypeL_apply, vecMulVecStarBilin_apply, reInnerBilin_apply, mulVecCLM₂_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul]
  exact rankOneProjector_deriv_sum_eq A.2.isHermitian B.2.isHermitian k

/-- Applied Fréchet derivative of `X ↦ X.2.isHermitian.eigenprojector₀ k` at a simple eigenvalue. -/
theorem fderiv_eigenprojector₀_apply {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k)
    (B : selfAdjoint (Matrix n n 𝕜)) :
    fderiv ℝ (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k) A B =
      ∑ j ∈ Finset.univ.erase k,
        (A.2.isHermitian.eigenvalues₀ k - A.2.isHermitian.eigenvalues₀ j)⁻¹ •
          (A.2.isHermitian.eigenprojector₀ k * (B : Matrix n n 𝕜) *
              A.2.isHermitian.eigenprojector₀ j +
            A.2.isHermitian.eigenprojector₀ j * (B : Matrix n n 𝕜) *
              A.2.isHermitian.eigenprojector₀ k) :=
  (congrFun (congrArg DFunLike.coe (hasStrictFDerivAt_eigenprojector₀ hk).hasFDerivAt.fderiv)
    B).trans (by simp)

private theorem trace_eigenprojector₀_sandwich_mul_self_of_ne {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {i j : Fin (Fintype.card n)} (hij : i ≠ j) (M : Matrix n n 𝕜) :
    (hA.eigenprojector₀ i * M * hA.eigenprojector₀ j * A).trace = 0 := by
  rw [Matrix.mul_assoc _ (hA.eigenprojector₀ j), hA.eigenprojector₀_mul j, Matrix.mul_smul,
    trace_smul, trace_mul_comm (hA.eigenprojector₀ i * M), ← Matrix.mul_assoc,
    hA.eigenprojector₀_mul_of_ne hij.symm, zero_mul, trace_zero, smul_zero]

/-- **Hadamard's first variation of a simple sorted eigenvalue** (Hellmann–Feynman theorem). -/
theorem hasStrictFDerivAt_eigenvalues₀ {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k) :
    HasStrictFDerivAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k)
      (RCLike.reCLM.comp (((traceCLM 𝕜 n).restrictScalars ℝ).comp
        ((ContinuousLinearMap.mul ℝ (Matrix n n 𝕜) (A.2.isHermitian.eigenprojector₀ k)).comp
          (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜))))) A := by
  have hfn : (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) =
      fun X ↦ RCLike.reCLM (traceCLM 𝕜 n (X.2.isHermitian.eigenprojector₀ k * X.1)) := by
    ext X; simp
  rw [hfn]
  refine ((RCLike.reCLM.comp ((traceCLM 𝕜 n).restrictScalars ℝ)).hasStrictFDerivAt.comp A
    ((hasStrictFDerivAt_eigenprojector₀ hk).fun_mul'
      (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)).hasStrictFDerivAt)).congr_fderiv ?_
  ext B
  set hA := A.2.isHermitian
  have hdPA : ((∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
      (hA.eigenprojector₀ k * B.1 * hA.eigenprojector₀ j +
        hA.eigenprojector₀ j * B.1 * hA.eigenprojector₀ k)) * A.1).trace = 0 := by
    rw [Matrix.sum_mul, trace_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    rw [Matrix.smul_mul, trace_smul, add_mul, trace_add,
      trace_eigenprojector₀_sandwich_mul_self_of_ne hA hjk.symm,
      trace_eigenprojector₀_sandwich_mul_self_of_ne hA hjk, add_zero, smul_zero]
  simp only [ContinuousLinearMap.comp_apply, add_apply, sum_apply, smul_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.mul_apply',
    selfAdjoint.subtypeL_apply, ContinuousLinearMap.coe_restrictScalars', traceCLM_apply,
    RCLike.reCLM_apply]
  change RCLike.re (hA.eigenprojector₀ k * B.1 + _ * A.1).trace =
    RCLike.re (hA.eigenprojector₀ k * B.1).trace
  rw [trace_add, hdPA, add_zero]

/-- Applied Fréchet derivative of `X ↦ X.2.isHermitian.eigenvalues₀ k` at a simple eigenvalue. -/
theorem fderiv_eigenvalues₀_apply {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k)
    (B : selfAdjoint (Matrix n n 𝕜)) :
    fderiv ℝ (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) A B =
      RCLike.re (A.2.isHermitian.eigenprojector₀ k * (B : Matrix n n 𝕜)).trace :=
  (congrFun (congrArg DFunLike.coe (hasStrictFDerivAt_eigenvalues₀ hk).hasFDerivAt.fderiv)
    B).trans (by simp)

/-- **Hadamard's second variation of a simple sorted eigenvalue** on
`selfAdjoint (Matrix n n 𝕜)`. -/
theorem hasStrictFDerivAt_fderiv_eigenvalues₀ {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k)
    (C : selfAdjoint (Matrix n n 𝕜)) :
    HasStrictFDerivAt
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦
        fderiv ℝ (fun Y : selfAdjoint (Matrix n n 𝕜) ↦ Y.2.isHermitian.eigenvalues₀ k) X C)
      ((2 : ℝ) • ∑ j ∈ Finset.univ.erase k,
        (A.2.isHermitian.eigenvalues₀ k - A.2.isHermitian.eigenvalues₀ j)⁻¹ •
          RCLike.reCLM.comp (((traceCLM 𝕜 n).restrictScalars ℝ).comp
            (((ContinuousLinearMap.mul ℝ (Matrix n n 𝕜)).flip (C : Matrix n n 𝕜)).comp
              ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜)
                  (A.2.isHermitian.eigenprojector₀ k) (A.2.isHermitian.eigenprojector₀ j)).comp
                (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)))))) A := by
  let hlin : Matrix n n 𝕜 →L[ℝ] ℝ :=
    RCLike.reCLM.comp (((traceCLM 𝕜 n).restrictScalars ℝ).comp
      ((ContinuousLinearMap.mul ℝ (Matrix n n 𝕜)).flip C.1))
  have hev : (fun X : selfAdjoint (Matrix n n 𝕜) ↦
      fderiv ℝ (fun Y : selfAdjoint (Matrix n n 𝕜) ↦ Y.2.isHermitian.eigenvalues₀ k) X C) =ᶠ[𝓝 A]
      fun X : selfAdjoint (Matrix n n 𝕜) ↦ hlin (X.2.isHermitian.eigenprojector₀ k) := by
    filter_upwards [(isOpen_setOf_forall_eigenvalues₀_ne k).mem_nhds hk] with X hX
    simp [hlin, fderiv_eigenvalues₀_apply hX C]
  refine ((hlin.hasStrictFDerivAt.comp A (hasStrictFDerivAt_eigenprojector₀ hk))
    |>.congr_of_eventuallyEq hev.symm).congr_fderiv ?_
  ext B
  set hA := A.2.isHermitian
  have hsymm_tr : ∀ j : Fin (Fintype.card n),
      RCLike.re (hA.eigenprojector₀ j * B.1 * hA.eigenprojector₀ k * C.1).trace =
        RCLike.re (hA.eigenprojector₀ k * B.1 * hA.eigenprojector₀ j * C.1).trace := fun j ↦ by
    have hconj : (hA.eigenprojector₀ j * B.1 * hA.eigenprojector₀ k * C.1).trace =
        star (hA.eigenprojector₀ k * B.1 * hA.eigenprojector₀ j * C.1).trace := by
      rw [← trace_conjTranspose]
      simp only [conjTranspose_mul, C.2.isHermitian.eq, B.2.isHermitian.eq,
        (hA.isHermitian_eigenprojector₀ j).eq, (hA.isHermitian_eigenprojector₀ k).eq]
      rw [trace_mul_comm, Matrix.mul_assoc]
    rw [hconj, RCLike.star_def, RCLike.conj_re]
  simp only [hlin, ContinuousLinearMap.comp_apply, smul_apply, sum_apply, add_apply,
    selfAdjoint.subtypeL_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.coe_restrictScalars',
    map_sum, RCLike.reCLM_apply, traceCLM_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.smul_mul, trace_smul, RCLike.smul_re, add_mul, trace_add, map_add, hsymm_tr]
  ring

/-- Applied second Fréchet derivative of `X ↦ X.2.isHermitian.eigenvalues₀ k`. -/
theorem fderiv_fderiv_eigenvalues₀_apply {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k)
    (B C : selfAdjoint (Matrix n n 𝕜)) :
    fderiv ℝ (fun X : selfAdjoint (Matrix n n 𝕜) ↦
        fderiv ℝ (fun Y : selfAdjoint (Matrix n n 𝕜) ↦ Y.2.isHermitian.eigenvalues₀ k) X C) A B =
      2 * ∑ j ∈ Finset.univ.erase k,
        (A.2.isHermitian.eigenvalues₀ k - A.2.isHermitian.eigenvalues₀ j)⁻¹ *
          RCLike.re (A.2.isHermitian.eigenprojector₀ k * (B : Matrix n n 𝕜) *
            A.2.isHermitian.eigenprojector₀ j * (C : Matrix n n 𝕜)).trace :=
  (congrFun (congrArg DFunLike.coe (hasStrictFDerivAt_fderiv_eigenvalues₀ hk C).hasFDerivAt.fderiv)
    B).trans (by simp)

namespace IsHermitian

private theorem eigenvalues₀_congr {M₁ M₂ : Matrix n n 𝕜}
    (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian) (h : M₁ = M₂) (k : Fin (Fintype.card n)) :
    h₁.eigenvalues₀ k = h₂.eigenvalues₀ k := by subst h; rfl

private theorem eigenprojector₀_congr {M₁ M₂ : Matrix n n 𝕜}
    (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian) (h : M₁ = M₂) (k : Fin (Fintype.card n)) :
    h₁.eigenprojector₀ k = h₂.eigenprojector₀ k := by subst h; rfl

/-- Directional derivative of `t ↦ (A + t • B).eigenprojector₀ k` at `t = 0` for simple `λₖ(A)`. -/
theorem hasDerivAt_add_smul_eigenprojector₀ {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    HasDerivAt (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenprojector₀ k)
      (∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
        (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j +
          hA.eigenprojector₀ j * B * hA.eigenprojector₀ k)) 0 := by
  let A' : selfAdjoint (Matrix n n 𝕜) := ⟨A, hA.isSelfAdjoint⟩
  let B' : selfAdjoint (Matrix n n 𝕜) := ⟨B, hB.isSelfAdjoint⟩
  have hfn : (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenprojector₀ k) =
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k) ∘
        fun t : ℝ ↦ A' + t • B' :=
    funext fun t ↦ eigenprojector₀_congr _ (A' + t • B').2.isHermitian (by simp [A', B']) k
  rw [hfn]
  have hline : HasDerivAt (fun t : ℝ ↦ A' + t • B') B' 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const B').const_add A'
  have hf := (congrArg (HasFDerivAt _ _) (by simp : A' + (0 : ℝ) • B' = A').symm).mp
    (hasStrictFDerivAt_eigenprojector₀ (A := A') hk).hasFDerivAt
  refine (hf.comp_hasDerivAt 0 hline).congr_deriv ?_
  dsimp only [A', B']; simp [smul_add]

/-- Directional derivative of `t ↦ (A + t • B).eigenvalues₀ k` at `t = 0` for simple `λₖ(A)`. -/
theorem hasDerivAt_add_smul_eigenvalues₀ {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    HasDerivAt (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k)
      (RCLike.re (hA.eigenprojector₀ k * B).trace) 0 := by
  let A' : selfAdjoint (Matrix n n 𝕜) := ⟨A, hA.isSelfAdjoint⟩
  let B' : selfAdjoint (Matrix n n 𝕜) := ⟨B, hB.isSelfAdjoint⟩
  have hfn : (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k) =
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) ∘
        fun t : ℝ ↦ A' + t • B' :=
    funext fun t ↦ eigenvalues₀_congr _ (A' + t • B').2.isHermitian (by simp [A', B']) k
  rw [hfn]
  have hline : HasDerivAt (fun t : ℝ ↦ A' + t • B') B' 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const B').const_add A'
  have hf := (congrArg (HasFDerivAt _ _) (by simp : A' + (0 : ℝ) • B' = A').symm).mp
    (hasStrictFDerivAt_eigenvalues₀ (A := A') hk).hasFDerivAt
  refine (hf.comp_hasDerivAt 0 hline).congr_deriv ?_
  dsimp only [A', B']; simp

/-- **Hadamard's second directional variation** (projector-trace form) at `t = 0`. -/
theorem iteratedDeriv_two_add_smul_eigenvalues₀ {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    iteratedDeriv 2 (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k) 0 =
      2 * ∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ *
        RCLike.re (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j * B).trace := by
  let A' : selfAdjoint (Matrix n n 𝕜) := ⟨A, hA.isSelfAdjoint⟩
  let B' : selfAdjoint (Matrix n n 𝕜) := ⟨B, hB.isSelfAdjoint⟩
  let γ : ℝ → selfAdjoint (Matrix n n 𝕜) := fun t ↦ A' + t • B'
  have hfn : (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k) =
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) ∘ γ :=
    funext fun t ↦ eigenvalues₀_congr _ (γ t).2.isHermitian (by simp [γ, A', B']) k
  rw [hfn]
  have hγ_cont : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hopen : ∀ᶠ t : ℝ in 𝓝 0,
      ∀ j ≠ k, (γ t).2.isHermitian.eigenvalues₀ j ≠ (γ t).2.isHermitian.eigenvalues₀ k := by
    have hmem : A' ∈ {X : selfAdjoint (Matrix n n 𝕜) |
        ∀ j ≠ k, X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k} := hk
    exact hγ_cont.continuousAt.eventually ((by simp [γ] : γ 0 = A').symm ▸
      (isOpen_setOf_forall_eigenvalues₀_ne k).mem_nhds hmem)
  have hderiv_ev : deriv ((fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) ∘
      γ) =ᶠ[𝓝 0] fun t : ℝ ↦
        fderiv ℝ (fun Y : selfAdjoint (Matrix n n 𝕜) ↦ Y.2.isHermitian.eigenvalues₀ k)
          (γ t) B' := by
    filter_upwards [hopen] with t ht
    have hline_t : HasDerivAt γ B' t := by
      simpa [γ] using ((hasDerivAt_id t).smul_const B').const_add A'
    have hf_t := (hasStrictFDerivAt_eigenvalues₀ (A := γ t) ht).hasFDerivAt
    exact (hf_t.comp_hasDerivAt t hline_t).deriv.trans (by rw [hf_t.fderiv])
  have hline0 : HasDerivAt γ B' 0 := by
    simpa [γ] using ((hasDerivAt_id (0 : ℝ)).smul_const B').const_add A'
  have hf2 := (congrArg (HasFDerivAt _ _) (by simp [γ] : γ 0 = A').symm).mp
    (hasStrictFDerivAt_fderiv_eigenvalues₀ (A := A') hk B').hasFDerivAt
  have h2 := (hf2.comp_hasDerivAt 0 hline0).congr_of_eventuallyEq hderiv_ev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ (𝕜 := ℝ), iteratedDeriv_one (𝕜 := ℝ),
    h2.deriv]
  dsimp only [A', B']; simp

/-- **Hadamard's second directional variation** (eigenvector matrix-element form, Anderson–Guionnet–
Zeitouni Lemma 4.3.4): `(d²/dt²)|₀ λₖ(A + t • B) = 2 * ∑ j ≠ k, (λₖ(A) - λⱼ(A))⁻¹ * ‖uⱼ* B uₖ‖²`. -/
theorem iteratedDeriv_two_add_smul_eigenvalues₀_eq_sum_norm_sq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    iteratedDeriv 2 (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k) 0 =
      2 * ∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ *
        ‖star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ k))‖ ^ 2 := by
  rw [hA.iteratedDeriv_two_add_smul_eigenvalues₀ hB hk]
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun j _ ↦ congrArg _ ?_)
  rw [hA.trace_eigenprojector₀_mul_eigenprojector₀_mul j k B B]
  have hconj : star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ j)) =
      star (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ k))) := by
    rw [dotProduct_comm, ← star_dotProduct, star_mulVec, dotProduct_comm, hB.eq,
      ← dotProduct_mulVec]
  rw [hconj, RCLike.star_def, RCLike.conj_mul]
  norm_cast

end IsHermitian

end SmoothAndVariation

end Matrix
