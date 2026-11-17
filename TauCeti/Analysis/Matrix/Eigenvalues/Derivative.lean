/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Group.Subgroup
public import TauCeti.Analysis.Matrix.Eigenvalues.Projector
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Topology.Algebra.Module.Matrix
public import TauCeti.Topology.Algebra.Module.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Calculus.ContDiff.Star
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.Analysis.Matrix.ContDiff
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Analysis.Matrix.HermitianProjector

/-!
# Smoothness and Hadamard variation of simple Hermitian eigenvalues and projectors

At any Hermitian matrix `A` over an `RCLike` field `𝕜` whose `k`-th sorted eigenvalue `λₖ(A)` is
simple (`∀ j ≠ k, λⱼ(A) ≠ λₖ(A)`), both `X ↦ λₖ(X)` and `X ↦ Pₖ(X)` are real-analytic (`C^ω`) near
`A` in `selfAdjoint (Matrix n n 𝕜)`, and hence on the open simple-spectrum locus
`{X | StrictAnti X.2.isHermitian.eigenvalues₀}`. These smoothness results and Hadamard's first and
second variation formulas supply the multivariable chain rules and `C²` regularity needed for
deterministic perturbation theory and Itô calculus on simple eigenvalues of Hermitian matrix
processes.

To state or use the normed calculus declarations in this file,
`open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`.

## Main results

* `Matrix.contDiffAt_eigenprojector₀`, `Matrix.contDiffAt_eigenvalues₀`,
  `Matrix.contDiffOn_eigenprojector₀_setOf_strictAnti_eigenvalues₀`, and
  `Matrix.contDiffOn_eigenvalues₀_setOf_strictAnti_eigenvalues₀`.
* `Matrix.hasStrictFDerivAt_eigenprojector₀`, `Matrix.fderiv_eigenprojector₀_apply`,
  `Matrix.hasStrictFDerivAt_eigenvalues₀`, and `Matrix.fderiv_eigenvalues₀_apply`.
* `Matrix.hasStrictFDerivAt_fderiv_eigenvalues₀`, `Matrix.fderiv_fderiv_eigenvalues₀_apply`, and
  directional derivatives `Matrix.IsHermitian.hasDerivAt_eigenprojector₀_add_smul`,
  `Matrix.IsHermitian.hasDerivAt_eigenvalues₀_add_smul`,
  `Matrix.IsHermitian.iteratedDeriv_two_eigenvalues₀_add_smul`, and
  `Matrix.IsHermitian.iteratedDeriv_two_eigenvalues₀_add_smul_eq_sum_norm_sq`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices* (2010), §4.3.1.
* R. Bhatia, *Matrix Analysis*, Springer (1997), §V.3.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter II, §1–§2.
* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §1.3.4.
-/

public section

noncomputable section

open scoped ContDiff Topology Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Matrix.l2OpNormedAlgebraReal

namespace Matrix

section ImplicitBranch

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

private def mulVecCLM (𝕜 n : Type*) [RCLike 𝕜] [Fintype n] :
    Matrix n n 𝕜 →L[𝕜] (n → 𝕜) →L[𝕜] (n → 𝕜) :=
  (Matrix.mulVecBilin 𝕜 𝕜).toContinuousBilinearMap

@[simp]
private theorem mulVecCLM_apply (M : Matrix n n 𝕜) (v : n → 𝕜) :
    mulVecCLM 𝕜 n M v = M *ᵥ v :=
  rfl

private theorem hasFDerivAt_mulVec_add (A : Matrix n n 𝕜) (u₀ : n → 𝕜) :
    open scoped Classical in
    HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ (u₀ + p.2))
      (((mulVecCLM 𝕜 n).flip u₀).comp (ContinuousLinearMap.fst 𝕜 (Matrix n n 𝕜) (n → 𝕜)) +
        (mulVecCLM 𝕜 n A).comp (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜))) (A, 0) := by
  classical
  refine ((mulVecCLM 𝕜 n).hasFDerivAt_of_bilinear
    (ContinuousLinearMap.fst 𝕜 (Matrix n n 𝕜) (n → 𝕜)).hasFDerivAt
    ((hasFDerivAt_const u₀ (A, 0)).add
      (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)).hasFDerivAt)).congr_fderiv
    (ContinuousLinearMap.ext fun ⟨H, y⟩ ↦ ?_)
  ext i; simp [add_comm]

variable [DecidableEq n]

private def eigNormMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : Fin (Fintype.card n))
    (p : Matrix n n 𝕜 × (n → 𝕜)) : n → 𝕜 :=
  let u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  (1 - hA.eigenprojector₀ k) *ᵥ (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2) +
    (star u₀ ⬝ᵥ p.2) • u₀

private theorem eigNormMap_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) : eigNormMap hA k (A, 0) = 0 := by
  simp [eigNormMap, hA.mulVec_eigenvectorBasis₀_coe, sub_mulVec, mulVec_smul]

private theorem eigNormMap_eq_zero_imp {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) {B : Matrix n n 𝕜} {w : n → 𝕜} (h0 : eigNormMap hA k (B, w) = 0) :
    star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ w = 0 ∧
      B *ᵥ (⇑(hA.eigenvectorBasis₀ k) + w) =
        (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (B *ᵥ (⇑(hA.eigenvectorBasis₀ k) + w))) •
          (⇑(hA.eigenvectorBasis₀ k) + w) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set P₀ : Matrix n n 𝕜 := hA.eigenprojector₀ k
  have horth : ∀ y : n → 𝕜, star u₀ ⬝ᵥ ((1 - P₀) *ᵥ y) = 0 := fun y ↦ by
    simp [sub_mulVec, P₀, u₀, hA.eigenprojector₀_mulVec]
  have hw : star u₀ ⬝ᵥ w = 0 := by
    simpa [eigNormMap, u₀, P₀, horth] using congrArg (star u₀ ⬝ᵥ ·) h0
  refine ⟨hw, sub_eq_zero.mp ?_⟩
  set α : 𝕜 := star u₀ ⬝ᵥ (B *ᵥ (u₀ + w))
  have hsub : (1 - P₀) *ᵥ u₀ = 0 := by
    simp [sub_mulVec, P₀, u₀]
  have hproj : (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) = 0 := by
    rw [smul_add, add_comm (α • u₀), ← sub_sub, mulVec_sub, mulVec_smul, hsub, smul_zero, sub_zero]
    simpa [eigNormMap, u₀, P₀, α, hw] using h0
  have hsc : star u₀ ⬝ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) = 0 := by
    simp [α, u₀, hw]
  calc B *ᵥ (u₀ + w) - α • (u₀ + w)
      = (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) +
          (star u₀ ⬝ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w))) • u₀ := by
        rw [sub_mulVec, one_mulVec, hA.eigenprojector₀_mulVec, sub_add_cancel]
    _ = 0 := by rw [hproj, hsc, zero_smul, add_zero]

private theorem contDiff_eigNormMap {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) {m : ℕ∞ω} : ContDiff 𝕜 m (eigNormMap hA k) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  have hBw : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ (u₀ + p.2)) :=
    (mulVecCLM 𝕜 n).isBoundedBilinearMap.contDiff.comp₂
      contDiff_fst (contDiff_const.add contDiff_snd)
  have hdot : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) :=
    contDiff_const.dotProduct hBw
  have hpart1 : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      (1 - hA.eigenprojector₀ k) *ᵥ
        (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2)) :=
    (mulVecCLM 𝕜 n (1 - hA.eigenprojector₀ k)).contDiff.comp (hBw.sub (hdot.smul contDiff_snd))
  exact hpart1.add ((contDiff_const.dotProduct contDiff_snd).smul contDiff_const)

private theorem eigNormMap_linear_simplify {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) (H : Matrix n n 𝕜) (y : n → 𝕜) :
    (1 - hA.eigenprojector₀ k) *ᵥ
        (H *ᵥ ⇑(hA.eigenvectorBasis₀ k) + A *ᵥ y - (hA.eigenvalues₀ k : 𝕜) • y) +
      (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ y) • ⇑(hA.eigenvectorBasis₀ k) =
      (1 - hA.eigenprojector₀ k) *ᵥ (H *ᵥ ⇑(hA.eigenvectorBasis₀ k)) +
        (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) *ᵥ y := by
  have hPAy : hA.eigenprojector₀ k *ᵥ (A *ᵥ y - (hA.eigenvalues₀ k : 𝕜) • y) = 0 := by
    simp [hA.eigenprojector₀_mulVec, dotProduct_mulVec, hA.star_eigenvectorBasis₀_vecMul]
  rw [add_sub_assoc, mulVec_add, sub_mulVec (1 : Matrix n n 𝕜) _ (A *ᵥ y - _), one_mulVec, hPAy,
    sub_zero, add_assoc]
  congr 1
  rw [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, hA.eigenprojector₀_mulVec]

private theorem hasFDerivAt_rayleigh_smul_snd {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    HasFDerivAt
      (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
        (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ
          (p.1 *ᵥ (⇑(hA.eigenvectorBasis₀ k) + p.2))) • p.2)
      ((hA.eigenvalues₀ k : 𝕜) • ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)) (A, 0) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  let dotu : (n → 𝕜) →L[𝕜] 𝕜 := (dotProductBilin 𝕜 𝕜 (star u₀)).toContinuousLinearMap
  have hsc : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2)))
      (dotu.comp (((mulVecCLM 𝕜 n).flip u₀).comp
          (ContinuousLinearMap.fst 𝕜 (Matrix n n 𝕜) (n → 𝕜)) +
        (mulVecCLM 𝕜 n A).comp (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)))) (A, 0) := by
    have hdotu : (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) =
        ⇑dotu ∘ fun p ↦ p.1 *ᵥ (u₀ + p.2) := by
      ext p; simp [dotu]
    rw [hdotu]
    exact dotu.hasFDerivAt.comp (A, 0) (hasFDerivAt_mulVec_add A u₀)
  refine (hsc.smul
    (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)).hasFDerivAt).congr_fderiv <|
    ContinuousLinearMap.ext fun p ↦ ?_
  ext i
  simp [dotu, u₀, hA.mulVec_eigenvectorBasis₀_coe, RCLike.real_smul_eq_coe_mul (K := 𝕜)]

private theorem fderiv_eigNormMap_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    fderiv 𝕜 (eigNormMap hA k) (A, 0) =
      ((mulVecCLM 𝕜 n (1 - hA.eigenprojector₀ k)).comp
          ((mulVecCLM 𝕜 n).flip ⇑(hA.eigenvectorBasis₀ k))).comp
        (ContinuousLinearMap.fst 𝕜 (Matrix n n 𝕜) (n → 𝕜)) +
      (mulVecCLM 𝕜 n (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k)).comp
        (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)) := by
  -- Decompose `eigNormMap (B, w) = (1 - P₀)(B(u₀ + w) - ⟨u₀, B(u₀ + w)⟩ w) + ⟨u₀, w⟩ u₀`.
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  let fst := ContinuousLinearMap.fst 𝕜 (Matrix n n 𝕜) (n → 𝕜)
  let snd := ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)
  let dotu : (n → 𝕜) →L[𝕜] 𝕜 := (dotProductBilin 𝕜 𝕜 (star u₀)).toContinuousLinearMap
  have hpart1 : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      (1 - hA.eigenprojector₀ k) *ᵥ
        (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2))
      ((mulVecCLM 𝕜 n (1 - hA.eigenprojector₀ k)).comp
        (((mulVecCLM 𝕜 n).flip u₀).comp fst + (mulVecCLM 𝕜 n A).comp snd -
          (hA.eigenvalues₀ k : 𝕜) • snd)) (A, 0) :=
    (mulVecCLM 𝕜 n (1 - hA.eigenprojector₀ k)).hasFDerivAt.comp (A, 0)
      ((hasFDerivAt_mulVec_add A u₀).sub (hasFDerivAt_rayleigh_smul_snd hA k))
  let L2 := (dotu.comp snd).smulRight u₀
  have heq : eigNormMap hA k =
      (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
        (1 - hA.eigenprojector₀ k) *ᵥ
          (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2)) + ⇑L2 := by
    ext p i; simp [eigNormMap, u₀, L2, dotu, snd]
  rw [heq]
  refine (hpart1.add L2.hasFDerivAt).fderiv.trans <| ContinuousLinearMap.ext fun ⟨H, y⟩ ↦ ?_
  simp only [dotu, u₀, L2, fst, snd, add_apply, ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', mulVecCLM_apply,
    LinearMap.coe_toContinuousLinearMap', dotProductBilin_apply_apply]
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
    simp [add_mul, sub_mul]
  have hterm_j : ∀ j ∈ Finset.univ.erase k,
      (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) *
        ((((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j) =
      hA.eigenprojector₀ j := fun j hj ↦ by
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    have hinv : (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) *
        ((hA.eigenvalues₀ j : 𝕜) - (hA.eigenvalues₀ k : 𝕜)) = 1 := by
      exact_mod_cast inv_mul_cancel₀ (sub_ne_zero.mpr (hk j hjk))
    rw [add_mul, sub_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, one_mul, hA.mul_eigenprojector₀, hA.eigenprojector₀_mul_of_ne hjk.symm,
      smul_zero, add_zero, ← smul_sub, ← sub_smul, smul_smul, hinv, one_smul]
  rw [reducedResolventPlusProj, mul_add, hterm_k, Matrix.mul_sum,
    Finset.sum_congr rfl hterm_j, Finset.add_sum_erase _ _ (Finset.mem_univ k),
    hA.sum_eigenprojector₀]

private theorem reducedResolventPlusProj_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    reducedResolventPlusProj hA k *
      (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) = 1 := by
  simpa [reducedResolventPlusProj, conjTranspose_sum, conjTranspose_smul, hA.eq,
    RCLike.star_def] using
    congrArg conjTranspose (mul_reducedResolventPlusProj hA hk)

private theorem comp_reducedResolventPlusProj_id {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    ((fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
        ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)).comp
      (mulVecCLM 𝕜 n (reducedResolventPlusProj hA k)) = ContinuousLinearMap.id 𝕜 (n → 𝕜)) ∧
      ((mulVecCLM 𝕜 n (reducedResolventPlusProj hA k)).comp
        (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
          ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)) =
        ContinuousLinearMap.id 𝕜 (n → 𝕜)) := by
  have hinr : fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
      ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜) =
      mulVecCLM 𝕜 n (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) := by
    ext y i; simp [fderiv_eigNormMap_self hA k]
  rw [hinr]
  constructor
  · refine ContinuousLinearMap.ext fun y ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, mulVecCLM_apply, ContinuousLinearMap.id_apply]
    rw [mulVec_mulVec, mul_reducedResolventPlusProj hA hk, one_mulVec]
  · refine ContinuousLinearMap.ext fun y ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, mulVecCLM_apply, ContinuousLinearMap.id_apply]
    rw [mulVec_mulVec, reducedResolventPlusProj_mul hA hk, one_mulVec]

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
          (mulVecCLM 𝕜 n (hA.eigenprojector₀ j)).comp
            ((mulVecCLM 𝕜 n).flip ⇑(hA.eigenvectorBasis₀ k))) A := by
  have hraw : HasStrictFDerivAt (localEigPerturb hA hk) _ A :=
    ContDiffAt.hasStrictFDerivAt_implicitFunction
      ((contDiff_eigNormMap hA k (m := ω)).contDiffAt (x := (A, 0)))
      (by decide) (isInvertible_fderiv_eigNormMap_inr hA hk)
  have hinv_eq : (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
      ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)).inverse =
      mulVecCLM 𝕜 n (reducedResolventPlusProj hA k) :=
    ContinuousLinearMap.inverse_eq
      (comp_reducedResolventPlusProj_id hA hk).1 (comp_reducedResolventPlusProj_id hA hk).2
  refine hraw.congr_fderiv ?_
  ext H i
  rw [hinv_eq]
  simp only [neg_apply, ContinuousLinearMap.comp_apply, sum_apply, smul_apply,
    fderiv_eigNormMap_self hA k, add_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.flip_apply,
    mulVecCLM_apply, mulVec_zero, add_zero]
  have hRproj : reducedResolventPlusProj hA k * (1 - hA.eigenprojector₀ k) =
      ∑ j ∈ Finset.univ.erase k,
        (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j := by
    rw [reducedResolventPlusProj, add_mul, mul_sub, mul_one, hA.eigenprojector₀_mul_self,
      sub_self, zero_add, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
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
    fun X ↦ RCLike.re (star u₀ ⬝ᵥ (X.1 *ᵥ (u₀ + localEigPerturb hA hk X.1)))
  let dotu : (n → 𝕜) →L[𝕜] 𝕜 := (dotProductBilin 𝕜 𝕜 (star u₀)).toContinuousLinearMap
  have hw_cont : ContinuousAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦ localEigPerturb hA hk X.1) A :=
    (contDiffAt_localEigPerturb hA hk).continuousAt.comp continuous_subtype_val.continuousAt
  have hα_eq : α = RCLike.re ∘ dotu ∘
      (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ mulVecCLM 𝕜 n p.1 p.2) ∘
      fun X : selfAdjoint (Matrix n n 𝕜) ↦ (X.1, u₀ + localEigPerturb hA hk X.1) := by
    ext X; simp [α, dotu]
  have hα_cont : ContinuousAt α A := by
    rw [hα_eq]
    exact RCLike.continuous_re.continuousAt.comp <| dotu.continuous.continuousAt.comp <|
      (mulVecCLM 𝕜 n).isBoundedBilinearMap.continuous.continuousAt.comp
        (continuous_subtype_val.continuousAt.prodMk (continuousAt_const.add hw_cont))
  have hαA : α A = hA.eigenvalues₀ k := by
    simp [α, u₀, localEigPerturb_self hA hk, hA.mulVec_eigenvectorBasis₀_coe, RCLike.smul_re]
  refine Filter.eventually_all.mpr fun j ↦ ?_
  by_cases hjk : j = k
  · exact Filter.Eventually.of_forall fun _ h ↦ (h hjk).elim
  · have hj_cont : ContinuousAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦
        X.2.isHermitian.eigenvalues₀ j) A :=
      ((continuous_apply j).comp continuous_eigenvalues₀_selfAdjoint).continuousAt
    have hne : α A - hA.eigenvalues₀ j ≠ 0 := sub_ne_zero.mpr (hαA.symm ▸ (hk j hjk).symm)
    exact ((hα_cont.sub hj_cont).eventually_ne hne).mono fun X hX _ ↦
      sub_ne_zero.mp (by simpa only [Pi.sub_apply, α, u₀] using hX)

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
  obtain ⟨m, hm⟩ := X.2.isHermitian.exists_eigenvalues₀_eq_of_mulVec_eq_smul hv_ne heig
  obtain rfl : m = k := by
    by_contra hmk; exact hgap m hmk (by simpa [v, u₀] using congrArg RCLike.re hm)
  rw [hm] at heig
  exact
    X.2.isHermitian.eigenprojector₀_eq_rankOneHermitianProjector_of_mulVec_eq_smul hsimple hv_ne
      heig

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
      fun X ↦ RCLike.reCLM (traceCLM n ℝ 𝕜 (X.2.isHermitian.eigenprojector₀ k * X.1)) := by
    ext X; simp
  rw [hfn]
  exact ((RCLike.reCLM.comp (traceCLM n ℝ 𝕜)).contDiff (n := m)).contDiffAt.comp
    A ((contDiffAt_eigenprojector₀ hk).mul (selfAdjoint.contDiff_subtype_val ℝ).contDiffAt)

/-- On the open simple-spectrum locus, each spectral projector is `C^m` over `ℝ` for every
`m : ℕ∞ω`. -/
theorem contDiffOn_eigenprojector₀_setOf_strictAnti_eigenvalues₀ (k : Fin (Fintype.card n))
    {m : ℕ∞ω} :
    ContDiffOn ℝ m (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k)
      {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.2.isHermitian.eigenvalues₀} :=
  fun _ hX ↦ (contDiffAt_eigenprojector₀ fun _ hjk ↦ hX.injective.ne hjk).contDiffWithinAt

/-- On the open simple-spectrum locus, each sorted eigenvalue is `C^m` over `ℝ` for every
`m : ℕ∞ω`. -/
theorem contDiffOn_eigenvalues₀_setOf_strictAnti_eigenvalues₀ (k : Fin (Fintype.card n))
    {m : ℕ∞ω} :
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
    dsimp only [dy]
    rw [dotProduct_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [dotProduct_smul, hA.eigenprojector₀_mulVec, dotProduct_smul,
      hA.dotProduct_star_eigenvectorBasis₀_of_ne (Finset.mem_erase.mp hj).1.symm,
      smul_zero, smul_zero]
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
    simpa [conjTranspose_vecMulVec, star_star, conjTranspose_mul, Matrix.mul_assoc, hB.eq] using
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
  have hsub : HasStrictFDerivAt (Subtype.val : selfAdjoint (Matrix n n 𝕜) → Matrix n n 𝕜)
      (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)) A := by
    rw [← selfAdjoint.coe_subtypeL ℝ (Matrix n n 𝕜)]
    exact (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)).hasStrictFDerivAt
  have hw_deriv := ((hasStrictFDerivAt_localEigPerturb A.2.isHermitian hk).restrictScalars ℝ).comp
    A hsub
  have hv_deriv := ((hasStrictFDerivAt_const ⇑(A.2.isHermitian.eigenvectorBasis₀ k) A).add
    hw_deriv).congr_fderiv (zero_add _)
  set u : n → 𝕜 := ⇑(A.2.isHermitian.eigenvectorBasis₀ k) + localEigPerturb A.2.isHermitian hk A.1
  have hu_unit : star u ⬝ᵥ u = 1 := by
    dsimp only [u]
    rw [localEigPerturb_self A.2.isHermitian hk, add_zero,
      A.2.isHermitian.dotProduct_star_eigenvectorBasis₀_self]
  have hu_ne : u ≠ 0 := fun h0 ↦ by simp [h0] at hu_unit
  refine ((TauCeti.hasStrictFDerivAt_rankOneHermitianProjector hu_ne).comp A hv_deriv
    |>.congr_of_eventuallyEq (eventuallyEq_eigenprojector₀_rankOne hk).symm).congr_fderiv ?_
  ext B : 1
  simp only [u, localEigPerturb_self A.2.isHermitian hk, add_zero,
    A.2.isHermitian.dotProduct_star_eigenvectorBasis₀_self, RCLike.one_re, inv_one, one_smul,
    TauCeti.rankOneHermitianProjector_eq_real_smul, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply, sum_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.flip_apply, selfAdjoint.subtypeL_apply,
    LinearMap.coe_toContinuousLinearMap', LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.flip_apply,
    LinearMap.smulRight_apply, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    starL'_apply, RCLike.reLm_coe, dotProductBilin_apply_apply, vecMulVecBilin_apply_apply,
    mulVecCLM_apply, ContinuousLinearMap.mulLeftRight_apply, smul_smul]
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
      (RCLike.reCLM.comp ((traceCLM n ℝ 𝕜).comp
        ((ContinuousLinearMap.mul ℝ (Matrix n n 𝕜) (A.2.isHermitian.eigenprojector₀ k)).comp
          (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜))))) A := by
  have hfn : (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) =
      (RCLike.reCLM.comp (traceCLM n ℝ 𝕜)) ∘ fun X : selfAdjoint (Matrix n n 𝕜) ↦
        X.2.isHermitian.eigenprojector₀ k * selfAdjoint.subtypeL ℝ (Matrix n n 𝕜) X := by
    ext X; simp
  rw [hfn]
  refine ((RCLike.reCLM.comp (traceCLM n ℝ 𝕜)).hasStrictFDerivAt.comp A
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
    simp [add_mul, trace_eigenprojector₀_sandwich_mul_self_of_ne hA hjk.symm,
      trace_eigenprojector₀_sandwich_mul_self_of_ne hA hjk]
  simp only [ContinuousLinearMap.comp_apply, add_apply, sum_apply, smul_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.mul_apply',
    selfAdjoint.subtypeL_apply, traceCLM_apply, RCLike.reCLM_apply,
    smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
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
          RCLike.reCLM.comp ((traceCLM n ℝ 𝕜).comp
            (((ContinuousLinearMap.mul ℝ (Matrix n n 𝕜)).flip (C : Matrix n n 𝕜)).comp
              ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜)
                  (A.2.isHermitian.eigenprojector₀ k) (A.2.isHermitian.eigenprojector₀ j)).comp
                (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)))))) A := by
  let hlin : Matrix n n 𝕜 →L[ℝ] ℝ :=
    RCLike.reCLM.comp ((traceCLM n ℝ 𝕜).comp
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
        hA.conjTranspose_eigenprojector₀]
      rw [trace_mul_comm, Matrix.mul_assoc]
    rw [hconj, RCLike.star_def, RCLike.conj_re]
  simp only [hlin, ContinuousLinearMap.comp_apply, smul_apply, sum_apply, add_apply,
    selfAdjoint.subtypeL_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.mulLeftRight_apply, map_sum, RCLike.reCLM_apply, traceCLM_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.smul_mul, trace_smul, RCLike.smul_re, add_mul, trace_add, map_add, hsymm_tr]
  ring

/-- Applied second Fréchet derivative of `X ↦ X.2.isHermitian.eigenvalues₀ k` at a simple
eigenvalue. -/
theorem fderiv_fderiv_eigenvalues₀_apply {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k)
    (B C : selfAdjoint (Matrix n n 𝕜)) :
    fderiv ℝ (fderiv ℝ (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k))
        A B C =
      2 * ∑ j ∈ Finset.univ.erase k,
        (A.2.isHermitian.eigenvalues₀ k - A.2.isHermitian.eigenvalues₀ j)⁻¹ *
          RCLike.re (A.2.isHermitian.eigenprojector₀ k * (B : Matrix n n 𝕜) *
            A.2.isHermitian.eigenprojector₀ j * (C : Matrix n n 𝕜)).trace := by
  have h1 := ((contDiffAt_eigenvalues₀ (m := 2) hk).hasFDerivAt_fderiv_apply le_rfl C).unique
    (hasStrictFDerivAt_fderiv_eigenvalues₀ hk C).hasFDerivAt
  simpa using congrFun (congrArg DFunLike.coe h1) B

namespace IsHermitian

private theorem eigenprojector₀_add_smul_eq_selfAdjoint {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : Fin (Fintype.card n)) :
    (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenprojector₀ k) =
      fun t : ℝ ↦
        ((⟨A, hA.isSelfAdjoint⟩ : selfAdjoint (Matrix n n 𝕜)) +
          t • ⟨B, hB.isSelfAdjoint⟩).2.isHermitian.eigenprojector₀ k :=
  funext fun t ↦ congrFun
    ((hA.add (hB.smul (IsSelfAdjoint.all t))).eigenprojector₀_congr _ (by simp)) k

private theorem eigenvalues₀_add_smul_eq_selfAdjoint {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : Fin (Fintype.card n)) :
    (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k) =
      fun t : ℝ ↦
        ((⟨A, hA.isSelfAdjoint⟩ : selfAdjoint (Matrix n n 𝕜)) +
          t • ⟨B, hB.isSelfAdjoint⟩).2.isHermitian.eigenvalues₀ k :=
  funext fun t ↦ congrFun
    ((hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀_congr _ (by simp)) k

/-- Directional derivative of `t ↦ (A + t • B).eigenprojector₀ k` at `t = 0` for simple `λₖ(A)`. -/
theorem hasDerivAt_eigenprojector₀_add_smul {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    HasDerivAt (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenprojector₀ k)
      (∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
        (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j +
          hA.eigenprojector₀ j * B * hA.eigenprojector₀ k)) 0 := by
  let A' : selfAdjoint (Matrix n n 𝕜) := ⟨A, hA.isSelfAdjoint⟩
  let B' : selfAdjoint (Matrix n n 𝕜) := ⟨B, hB.isSelfAdjoint⟩
  rw [eigenprojector₀_add_smul_eq_selfAdjoint hA hB k]
  refine ((hasStrictFDerivAt_eigenprojector₀ (A := A') hk).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const B').const_add A') (by simp)).congr_deriv ?_
  dsimp only [A', B']; simp [smul_add]

/-- Directional derivative of `t ↦ (A + t • B).eigenvalues₀ k` at `t = 0` for simple `λₖ(A)`. -/
theorem hasDerivAt_eigenvalues₀_add_smul {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    HasDerivAt (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k)
      (RCLike.re (hA.eigenprojector₀ k * B).trace) 0 := by
  let A' : selfAdjoint (Matrix n n 𝕜) := ⟨A, hA.isSelfAdjoint⟩
  let B' : selfAdjoint (Matrix n n 𝕜) := ⟨B, hB.isSelfAdjoint⟩
  rw [eigenvalues₀_add_smul_eq_selfAdjoint hA hB k]
  refine ((hasStrictFDerivAt_eigenvalues₀ (A := A') hk).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const B').const_add A') (by simp)).congr_deriv ?_
  dsimp only [A', B']; simp

/-- **Hadamard's second directional variation** (projector-trace form) at `t = 0`. -/
theorem iteratedDeriv_two_eigenvalues₀_add_smul {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    iteratedDeriv 2 (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k) 0 =
      2 * ∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ *
        RCLike.re (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j * B).trace := by
  let A' : selfAdjoint (Matrix n n 𝕜) := ⟨A, hA.isSelfAdjoint⟩
  let B' : selfAdjoint (Matrix n n 𝕜) := ⟨B, hB.isSelfAdjoint⟩
  have hc : ContDiffAt ℝ 2
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k)
      (A' + (0 : ℝ) • B') := by
    simpa using contDiffAt_eigenvalues₀ (A := A') (m := 2) hk
  rw [eigenvalues₀_add_smul_eq_selfAdjoint hA hB k, show (2 : ℕ) = 1 + 1 from rfl,
    iteratedDeriv_succ, iteratedDeriv_one, hc.deriv_deriv_comp_add_smul]
  simpa [A', B'] using fderiv_fderiv_eigenvalues₀_apply (A := A') hk B' B'

/-- **Hadamard's second directional variation** (eigenvector matrix-element form, Anderson–Guionnet–
Zeitouni Lemma 4.3.4): `(d²/dt²)|₀ λₖ(A + t • B) = 2 * ∑ j ≠ k, (λₖ(A) - λⱼ(A))⁻¹ * ‖uⱼ* B uₖ‖²`. -/
theorem iteratedDeriv_two_eigenvalues₀_add_smul_eq_sum_norm_sq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    iteratedDeriv 2 (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k) 0 =
      2 * ∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ *
        ‖star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ k))‖ ^ 2 := by
  rw [hA.iteratedDeriv_two_eigenvalues₀_add_smul hB hk]
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun j _ ↦ congrArg _ ?_)
  rw [hA.trace_eigenprojector₀_mul_mul_eigenprojector₀_mul j k B B]
  have hconj : star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ j)) =
      star (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ k))) := by
    rw [dotProduct_comm, ← star_dotProduct, star_mulVec, dotProduct_comm, hB.eq,
      ← dotProduct_mulVec]
  rw [hconj, RCLike.star_def, RCLike.conj_mul]
  norm_cast

end IsHermitian

end SmoothAndVariation

end Matrix
