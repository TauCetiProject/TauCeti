/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Mul
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
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Star
import TauCeti.Analysis.Calculus.FDeriv.Congr
import TauCeti.Analysis.Calculus.FDeriv.Star
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Analysis.Matrix.HermitianProjector

/-!
# Smoothness and Hadamard variation of simple spectral projectors and eigenvalues

At any Hermitian matrix `A` over an `RCLike` field `𝕜` whose `k`-th sorted eigenvalue `λₖ(A)` is
simple (`∀ j ≠ k, λⱼ(A) ≠ λₖ(A)`), the rank-one spectral projector `X ↦ Pₖ(X)` is real-analytic
(`C^ω`) near `A` in `selfAdjoint (Matrix n n 𝕜)`, and hence on the open simple-spectrum locus
`{X | StrictAnti X.property.isHermitian.eigenvalues₀}`. Complementing the family smoothness and
first variation of simple eigenvalues in `TauCeti.Analysis.Matrix.Eigenvalues.Smooth` and the curve
second variation in eigenvector coordinates in
`TauCeti.Analysis.Matrix.Eigenvalues.SecondVariation`, this file proves Hadamard's first variation
formula for `Pₖ`, together with the basis-free projector-trace strict Fréchet first and bilinear
second variations of `λₖ` on `selfAdjoint (Matrix n n 𝕜)`, supplying the multivariable `C²` chain
rules needed for Itô calculus on simple eigenvalues of Hermitian matrix processes.

To state or use the normed calculus declarations in this file,
`open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`.

## Main results

* `Matrix.contDiffAt_eigenprojector₀`, `Matrix.contDiffAt_eigenvalues₀_selfAdjoint`,
  `Matrix.contDiffOn_eigenprojector₀_setOf_strictAnti_eigenvalues₀`, and
  `Matrix.contDiffOn_eigenvalues₀_setOf_strictAnti_eigenvalues₀`.
* `Matrix.hasStrictFDerivAt_eigenprojector₀`, `Matrix.fderiv_eigenprojector₀_apply`,
  `Matrix.IsHermitian.hasDerivAt_eigenprojector₀_add_smul`,
  `Matrix.hasStrictFDerivAt_eigenvalues₀_selfAdjoint`, and
  `Matrix.fderiv_eigenvalues₀_selfAdjoint_apply`.
* `Matrix.hasStrictFDerivAt_fderiv_eigenvalues₀`, `Matrix.fderiv_fderiv_eigenvalues₀_apply`, and
  `Matrix.IsHermitian.iteratedDeriv_two_eigenvalues₀_add_smul`.

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

/-! ### Implicit-function eigenvector branch

Around a Hermitian matrix `A` whose `k`-th sorted eigenvalue `λₖ(A)` is simple, choose the unit
eigenvector `u₀ = hA.eigenvectorBasis₀ k` and rank-one projector `P₀ = hA.eigenprojector₀ k`. We
construct a real-analytic local eigenvector branch `B ↦ u₀ + localEigPerturb hA hk B` in three
steps:

1. `eigNormMap` encodes the normalized eigen-equation
   `(1 - P₀) (B (u₀ + w) - ⟨u₀, B (u₀ + w)⟩ w) + ⟨u₀, w⟩ u₀ = 0`, whose vanishing forces both the
   normalization `⟨u₀, w⟩ = 0` and the eigenvalue equation
   `B (u₀ + w) = ⟨u₀, B (u₀ + w)⟩ (u₀ + w)` (`eigNormMap_eq_zero_imp`).
2. At `(A, 0)`, the `w`-partial Fréchet derivative of `eigNormMap` is left multiplication by
   `A - λₖ(A) • 1 + P₀` (`fderiv_eigNormMap_inr`), inverted when `λₖ(A)` is simple by
   `reducedResolventPlusProj`. Applying `ContDiffAt.implicitFunction` produces the analytic branch
   `localEigPerturb` and its strict derivative (`hasStrictFDerivAt_localEigPerturb`).
3. Continuity of the Rayleigh quotient and of `eigenvalues₀` keeps the branch's eigenvalue distinct
   from `λⱼ(X)` for every `j ≠ k` near `A` (`eventually_localEigRayleigh_ne`), identifying the
   associated rank-one projector with `Pₖ(X)` (`eventuallyEq_eigenprojector₀_rankOne`). -/

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Normalized eigenvector residual `(B, w) ↦ (1 - P₀)(B(u₀ + w) - ⟨u₀, B(u₀ + w)⟩ w) + ⟨u₀, w⟩ u₀`
around `u₀ = hA.eigenvectorBasis₀ k` and `P₀ = hA.eigenprojector₀ k`. -/
private def eigNormMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : Fin (Fintype.card n))
    (p : Matrix n n 𝕜 × (n → 𝕜)) : n → 𝕜 :=
  let u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  (1 - hA.eigenprojector₀ k) *ᵥ (p.fst *ᵥ (u₀ + p.snd) - (star u₀ ⬝ᵥ (p.fst *ᵥ (u₀ + p.snd))) •
    p.snd) + (star u₀ ⬝ᵥ p.snd) • u₀

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
  have horth (y : n → 𝕜) : star u₀ ⬝ᵥ ((1 - P₀) *ᵥ y) = 0 := by
    simp [sub_mulVec, P₀, u₀, hA.eigenprojector₀_mulVec]
  have hw : star u₀ ⬝ᵥ w = 0 := by
    simpa [eigNormMap, u₀, P₀, horth] using congrArg (star u₀ ⬝ᵥ ·) h0
  refine ⟨hw, sub_eq_zero.mp ?_⟩
  set α : 𝕜 := star u₀ ⬝ᵥ (B *ᵥ (u₀ + w))
  have hsub : (1 - P₀) *ᵥ u₀ = 0 := by simp [sub_mulVec, P₀, u₀]
  have h0' : (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • w) = 0 := by
    simpa [eigNormMap, u₀, P₀, α, hw] using h0
  have hsplit : B *ᵥ (u₀ + w) - α • (u₀ + w) = (B *ᵥ (u₀ + w) - α • w) - α • u₀ := by module
  have hproj : (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) = 0 := by
    rw [hsplit, mulVec_sub, h0', mulVec_smul, hsub, smul_zero, sub_zero]
  have hsc : star u₀ ⬝ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) = 0 := by simp [α, u₀, hw]
  calc B *ᵥ (u₀ + w) - α • (u₀ + w)
      = (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) +
          (star u₀ ⬝ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w))) • u₀ := by
        rw [sub_mulVec, one_mulVec, hA.eigenprojector₀_mulVec, sub_add_cancel]
    _ = 0 := by rw [hproj, hsc, zero_smul, add_zero]

private theorem contDiff_eigNormMap {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) {m : ℕ∞ω} : ContDiff 𝕜 m (eigNormMap hA k) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  have hBw : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.fst *ᵥ (u₀ + p.snd)) := by
    simpa only [mulVecBilinCLM_apply, mulVecCLM_apply] using
      (mulVecBilinCLM n n 𝕜).isBoundedBilinearMap.contDiff.comp₂
        (n := m) contDiff_fst (contDiff_const.add contDiff_snd)
  have hdot :
      ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ (p.fst *ᵥ (u₀ + p.snd))) := by
    simpa only [Function.comp_def, TauCeti.dotProductCLM_apply] using
      ((TauCeti.dotProductCLM (star u₀)).contDiff (n := m)).comp hBw
  have hsub : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      p.fst *ᵥ (u₀ + p.snd) - (star u₀ ⬝ᵥ (p.fst *ᵥ (u₀ + p.snd))) • p.snd) :=
    hBw.sub (hdot.smul contDiff_snd)
  have hpart1 : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      (1 - hA.eigenprojector₀ k) *ᵥ
        (p.fst *ᵥ (u₀ + p.snd) - (star u₀ ⬝ᵥ (p.fst *ᵥ (u₀ + p.snd))) • p.snd)) := by
    simpa only [Function.comp_def, mulVecCLM_apply] using
      ((1 - hA.eigenprojector₀ k).mulVecCLM.contDiff (n := m)).comp hsub
  have hdot2 : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ p.snd) := by
    simpa only [Function.comp_def, TauCeti.dotProductCLM_apply] using
      ((TauCeti.dotProductCLM (star u₀)).contDiff (n := m)).comp contDiff_snd
  exact hpart1.add (hdot2.smul contDiff_const)

private theorem eigNormMap_linear_simplify {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) (H : Matrix n n 𝕜) (y : n → 𝕜) :
    (1 - hA.eigenprojector₀ k) *ᵥ
        (H *ᵥ ⇑(hA.eigenvectorBasis₀ k) + A *ᵥ y - (hA.eigenvalues₀ k : 𝕜) • y) +
      (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ y) • ⇑(hA.eigenvectorBasis₀ k) =
      (1 - hA.eigenprojector₀ k) *ᵥ (H *ᵥ ⇑(hA.eigenvectorBasis₀ k)) +
        (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) *ᵥ y := by
  have hPAy : hA.eigenprojector₀ k *ᵥ (A *ᵥ y - (hA.eigenvalues₀ k : 𝕜) • y) = 0 := by
    simp [hA.eigenprojector₀_mulVec, dotProduct_mulVec, hA.star_eigenvectorBasis₀_vecMul]
  simp only [add_sub_assoc, mulVec_add, add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, hPAy,
    sub_zero, hA.eigenprojector₀_mulVec, add_assoc]

private abbrev eigFst (n 𝕜 : Type*) [RCLike 𝕜] :=
  ContinuousLinearMap.fst 𝕜 (Matrix n n 𝕜) (n → 𝕜)

private abbrev eigSnd (n 𝕜 : Type*) [RCLike 𝕜] :=
  ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)

private abbrev eigInr (n 𝕜 : Type*) [RCLike 𝕜] :=
  ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)

private theorem hasFDerivAt_eigPerturbMulVec {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.fst *ᵥ (⇑(hA.eigenvectorBasis₀ k) + p.snd))
      (((mulVecBilinCLM n n 𝕜).flip ⇑(hA.eigenvectorBasis₀ k)).comp (eigFst n 𝕜) +
        A.mulVecCLM.comp (eigSnd n 𝕜)) (A, 0) := by
  have h := (mulVecBilinCLM n n 𝕜).hasFDerivAt_of_bilinear (eigFst n 𝕜).hasFDerivAt
    ((hasFDerivAt_const ⇑(hA.eigenvectorBasis₀ k) (A, 0)).add (eigSnd n 𝕜).hasFDerivAt)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ by simp)).congr_fderiv
    (ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by ext; simp [add_comm])

private theorem hasFDerivAt_rayleigh_smul_snd {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
        (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (p.fst *ᵥ (⇑(hA.eigenvectorBasis₀ k) + p.snd))) • p.snd)
      ((hA.eigenvalues₀ k : 𝕜) • eigSnd n 𝕜) (A, 0) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  have hsc : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ (p.fst *ᵥ (u₀ + p.snd)))
      ((TauCeti.dotProductCLM (star u₀)).comp
        (((mulVecBilinCLM n n 𝕜).flip u₀).comp (eigFst n 𝕜) + A.mulVecCLM.comp (eigSnd n 𝕜)))
      (A, 0) := by
    simpa only [Function.comp_def, TauCeti.dotProductCLM_apply] using
      (TauCeti.dotProductCLM (star u₀)).hasFDerivAt.comp (A, 0) (hasFDerivAt_eigPerturbMulVec hA k)
  refine (hsc.smul (eigSnd n 𝕜).hasFDerivAt).congr_fderiv <| ContinuousLinearMap.ext fun _ ↦ by
    ext; simp [u₀, hA.mulVec_eigenvectorBasis₀_coe, RCLike.real_smul_eq_coe_mul (K := 𝕜)]

private theorem fderiv_eigNormMap_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    fderiv 𝕜 (eigNormMap hA k) (A, 0) =
      (((1 - hA.eigenprojector₀ k).mulVecCLM).comp
          ((mulVecBilinCLM n n 𝕜).flip ⇑(hA.eigenvectorBasis₀ k))).comp (eigFst n 𝕜) +
      ((A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k).mulVecCLM).comp (eigSnd n 𝕜) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  have hpart1 : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      (1 - hA.eigenprojector₀ k) *ᵥ
        (p.fst *ᵥ (u₀ + p.snd) - (star u₀ ⬝ᵥ (p.fst *ᵥ (u₀ + p.snd))) • p.snd))
      (((1 - hA.eigenprojector₀ k).mulVecCLM).comp
        (((mulVecBilinCLM n n 𝕜).flip u₀).comp (eigFst n 𝕜) + A.mulVecCLM.comp (eigSnd n 𝕜) -
          (hA.eigenvalues₀ k : 𝕜) • eigSnd n 𝕜)) (A, 0) := by
    simpa only [Function.comp_def, Pi.sub_apply, mulVecCLM_apply] using
      (1 - hA.eigenprojector₀ k).mulVecCLM.hasFDerivAt.comp (A, 0)
        ((hasFDerivAt_eigPerturbMulVec hA k).sub (hasFDerivAt_rayleigh_smul_snd hA k))
  let L2 := ((TauCeti.dotProductCLM (star u₀)).comp (eigSnd n 𝕜)).smulRight u₀
  have heq : eigNormMap hA k =
      (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ (1 - hA.eigenprojector₀ k) *ᵥ
        (p.fst *ᵥ (u₀ + p.snd) - (star u₀ ⬝ᵥ (p.fst *ᵥ (u₀ + p.snd))) • p.snd)) + ⇑L2 := by
    ext p i; simp [eigNormMap, u₀, L2]
  rw [heq]
  refine (hpart1.add L2.hasFDerivAt).fderiv.trans <| ContinuousLinearMap.ext fun ⟨H, y⟩ ↦ ?_
  simpa [u₀, L2, mulVec_add, mulVec_sub, mulVec_smul, add_mulVec] using
    eigNormMap_linear_simplify hA k H y

/-- Sum of `Pₖ` and the reduced resolvent `∑_{j ≠ k} (λⱼ - λₖ)⁻¹ Pⱼ`, which inverts
`A - λₖ • 1 + Pₖ` when `λₖ` is simple. -/
private def reducedResolventPlusProj {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) : Matrix n n 𝕜 :=
  hA.eigenprojector₀ k + ∑ j ∈ Finset.univ.erase k,
    (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j

private theorem mul_reducedResolventPlusProj {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) *
      reducedResolventPlusProj hA k = 1 := by
  have hterm_k : (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) *
      hA.eigenprojector₀ k = hA.eigenprojector₀ k := by simp [add_mul, sub_mul]
  have hterm_j : ∀ j ∈ Finset.univ.erase k,
      (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) *
        ((((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j) =
      hA.eigenprojector₀ j := fun j hj ↦ by
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).left
    simp [add_mul, sub_mul, hA.eigenprojector₀_mul_of_ne hjk.symm, ← sub_smul,
      -map_inv₀, -map_sub, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr (hk j hjk))]
  rw [reducedResolventPlusProj, mul_add, hterm_k, Matrix.mul_sum,
    Finset.sum_congr rfl hterm_j, Finset.add_sum_erase _ _ (Finset.mem_univ k),
    hA.sum_eigenprojector₀]

private theorem reducedResolventPlusProj_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    reducedResolventPlusProj hA k *
      (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) = 1 := by
  simpa [reducedResolventPlusProj, conjTranspose_sum, conjTranspose_smul, hA.eq,
    RCLike.star_def] using congrArg conjTranspose (mul_reducedResolventPlusProj hA hk)

private theorem reducedResolventPlusProj_mul_one_sub_eigenprojector₀ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    reducedResolventPlusProj hA k * (1 - hA.eigenprojector₀ k) =
      ∑ j ∈ Finset.univ.erase k,
        (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j := by
  have hzero : (∑ j ∈ Finset.univ.erase k,
      (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j) *
      hA.eigenprojector₀ k = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun j hj ↦ by
      simp [hA.eigenprojector₀_mul_of_ne (Finset.mem_erase.mp hj).left]
  rw [reducedResolventPlusProj, mul_sub, mul_one, add_mul, hzero]
  simp

private theorem fderiv_eigNormMap_inr {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L eigInr n 𝕜 =
      (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k).mulVecCLM := by
  ext y i; simp [fderiv_eigNormMap_self hA k]

private theorem fderiv_inr_comp_reducedResolvent {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L eigInr n 𝕜).comp
      (reducedResolventPlusProj hA k).mulVecCLM = ContinuousLinearMap.id 𝕜 (n → 𝕜) := by
  rw [fderiv_eigNormMap_inr, ← mulVecCLM_mul, mul_reducedResolventPlusProj hA hk, mulVecCLM_one]

private theorem reducedResolvent_comp_fderiv_inr {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    (reducedResolventPlusProj hA k).mulVecCLM.comp
      (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L eigInr n 𝕜) = ContinuousLinearMap.id 𝕜 (n → 𝕜) := by
  rw [fderiv_eigNormMap_inr, ← mulVecCLM_mul, reducedResolventPlusProj_mul hA hk, mulVecCLM_one]

private theorem isInvertible_fderiv_eigNormMap_inr {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L eigInr n 𝕜).IsInvertible :=
  .of_inverse (fderiv_inr_comp_reducedResolvent hA hk) (reducedResolvent_comp_fderiv_inr hA hk)

/-- Analytic local eigenvector perturbation `B ↦ w(B)` solving `eigNormMap hA k (B, w(B)) = 0` near
`A` via the implicit function theorem. -/
private def localEigPerturb {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    Matrix n n 𝕜 → (n → 𝕜) :=
  ((contDiff_eigNormMap hA k (m := ω)).contDiffAt (x := (A, 0))).implicitFunction
    (by decide) (isInvertible_fderiv_eigNormMap_inr hA hk)

private theorem localEigPerturb_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    localEigPerturb hA hk A = 0 := ContDiffAt.implicitFunction_apply_self _ _ _

private theorem contDiffAt_localEigPerturb {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    ContDiffAt 𝕜 ω (localEigPerturb hA hk) A := ContDiffAt.contDiffAt_implicitFunction _ _ _

private theorem eventually_eigNormMap_localEigPerturb {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    ∀ᶠ B in 𝓝 A, eigNormMap hA k (B, localEigPerturb hA hk B) = 0 := by
  simpa only [localEigPerturb, eigNormMap_self] using ContDiffAt.eventually_apply_implicitFunction
    ((contDiff_eigNormMap hA k (m := ω)).contDiffAt (x := (A, 0)))
    (by decide) (isInvertible_fderiv_eigNormMap_inr hA hk)

/-- Candidate strict `𝕜`-Fréchet derivative `H ↦ ∑_{j ≠ k} (λₖ - λⱼ)⁻¹ Pⱼ (H uₖ)` of
`localEigPerturb` at `A`. -/
private def localEigPerturbFDeriv {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) : Matrix n n 𝕜 →L[𝕜] (n → 𝕜) :=
  ∑ j ∈ Finset.univ.erase k, (((hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ : ℝ) : 𝕜) •
    ((hA.eigenprojector₀ j).mulVecCLM).comp
      ((mulVecBilinCLM n n 𝕜).flip ⇑(hA.eigenvectorBasis₀ k))

private theorem localEigPerturbFDeriv_apply {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) (H : Matrix n n 𝕜) :
    localEigPerturbFDeriv hA k H =
      ∑ j ∈ Finset.univ.erase k, (((hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ : ℝ) : 𝕜) •
        (hA.eigenprojector₀ j *ᵥ (H *ᵥ ⇑(hA.eigenvectorBasis₀ k))) := by
  simp [localEigPerturbFDeriv, mulVec_mulVec]

private theorem hasStrictFDerivAt_localEigPerturb {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    HasStrictFDerivAt (localEigPerturb hA hk) (localEigPerturbFDeriv hA k) A := by
  have hraw := ContDiffAt.hasStrictFDerivAt_implicitFunction
    ((contDiff_eigNormMap hA k (m := ω)).contDiffAt (x := (A, 0)))
    (by decide) (isInvertible_fderiv_eigNormMap_inr hA hk)
  have hinv_eq := ContinuousLinearMap.inverse_eq
    (fderiv_inr_comp_reducedResolvent hA hk) (reducedResolvent_comp_fderiv_inr hA hk)
  dsimp only [eigInr] at hinv_eq
  have hvec (H : Matrix n n 𝕜) :
      -(reducedResolventPlusProj hA k *ᵥ
          ((1 - hA.eigenprojector₀ k) *ᵥ (H *ᵥ ⇑(hA.eigenvectorBasis₀ k)))) =
        localEigPerturbFDeriv hA k H := by
    rw [localEigPerturbFDeriv_apply]
    simp [mulVec_mulVec, ← Matrix.mul_assoc, reducedResolventPlusProj_mul_one_sub_eigenprojector₀,
      Matrix.sum_mul, sum_mulVec, smul_mulVec, ← Finset.sum_neg_distrib, ← neg_smul, ← inv_neg,
      neg_sub]
  refine hraw.congr_fderiv (ContinuousLinearMap.ext fun H ↦ ?_)
  rw [hinv_eq]
  simpa [fderiv_eigNormMap_self hA k, ← mulVec_mulVec] using hvec H

/-- Near `A`, the Rayleigh quotient of the implicit eigenvector branch stays distinct from every
other sorted eigenvalue `λⱼ(X)` (`j ≠ k`). -/
private theorem eventually_localEigRayleigh_ne {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.property.isHermitian.eigenvalues₀ j ≠ A.property.isHermitian.eigenvalues₀ k) :
    ∀ᶠ X : selfAdjoint (Matrix n n 𝕜) in 𝓝 A, ∀ j : Fin (Fintype.card n), j ≠ k →
      RCLike.re (star ⇑(A.property.isHermitian.eigenvectorBasis₀ k) ⬝ᵥ
        (X.val *ᵥ (⇑(A.property.isHermitian.eigenvectorBasis₀ k) +
          localEigPerturb A.property.isHermitian hk X.val))) ≠
        X.property.isHermitian.eigenvalues₀ j := by
  set hA := A.property.isHermitian; set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set α : selfAdjoint (Matrix n n 𝕜) → ℝ :=
    fun X ↦ RCLike.re (star u₀ ⬝ᵥ (X.val *ᵥ (u₀ + localEigPerturb hA hk X.val)))
  have hw_cont :
      ContinuousAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦ localEigPerturb hA hk X.val) A :=
    (contDiffAt_localEigPerturb hA hk).continuousAt.comp continuous_subtypeVal.continuousAt
  have hα_cont : ContinuousAt α A := by
    have hα_eq : α = RCLike.re ∘ TauCeti.dotProductCLM (star u₀) ∘
        (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ mulVecBilinCLM n n 𝕜 p.fst p.snd) ∘
        fun X : selfAdjoint (Matrix n n 𝕜) ↦ (X.val, u₀ + localEigPerturb hA hk X.val) := by
      ext X; simp [α]
    rw [hα_eq]
    exact RCLike.continuous_re.continuousAt.comp <|
      (TauCeti.dotProductCLM (star u₀)).continuous.continuousAt.comp <|
      (mulVecBilinCLM n n 𝕜).isBoundedBilinearMap.continuous.continuousAt.comp
        (continuous_subtypeVal.continuousAt.prodMk (continuousAt_const.add hw_cont))
  have hαA : α A = hA.eigenvalues₀ k := by
    simp [α, u₀, localEigPerturb_self hA hk, hA.mulVec_eigenvectorBasis₀_coe, RCLike.smul_re]
  refine Filter.eventually_all.mpr fun j ↦ ?_
  by_cases hjk : j = k
  · exact Filter.Eventually.of_forall fun _ h ↦ (h hjk).elim
  · have hj_cont : ContinuousAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦
        X.property.isHermitian.eigenvalues₀ j) A :=
      ((continuous_apply j).comp continuous_eigenvalues₀_selfAdjoint).continuousAt
    have hne : α A - hA.eigenvalues₀ j ≠ 0 := sub_ne_zero.mpr (hαA.symm ▸ (hk j hjk).symm)
    exact ((hα_cont.sub hj_cont).eventually_ne hne).mono fun X hX _ ↦
      sub_ne_zero.mp (by simpa only [Pi.sub_apply, α, u₀] using hX)

/-- Near `A`, the `k`-th sorted spectral projector agrees with the rank-one projector onto the
implicit eigenvector branch `u₀ + localEigPerturb hA hk X.val`. -/
private theorem eventuallyEq_eigenprojector₀_rankOne {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.property.isHermitian.eigenvalues₀ j ≠ A.property.isHermitian.eigenvalues₀ k) :
    (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenprojector₀ k) =ᶠ[𝓝 A]
      fun X : selfAdjoint (Matrix n n 𝕜) ↦ TauCeti.rankOneHermitianProjector
        (⇑(A.property.isHermitian.eigenvectorBasis₀ k) +
          localEigPerturb A.property.isHermitian hk X.val) := by
  set hA := A.property.isHermitian; set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set v : selfAdjoint (Matrix n n 𝕜) → (n → 𝕜) := fun X ↦ u₀ + localEigPerturb hA hk X.val
  filter_upwards [continuous_subtypeVal.continuousAt.eventually
      (eventually_eigNormMap_localEigPerturb hA hk),
    eventually_localEigRayleigh_ne hk,
    (isOpen_setOf_forall_eigenvalues₀_ne k).mem_nhds hk] with X hG hgap hsimple
  obtain ⟨hw_orth, heig⟩ := eigNormMap_eq_zero_imp hA k hG
  have hv_ne : v X ≠ 0 := fun hv0 ↦ by
    have h1 : star u₀ ⬝ᵥ v X = 1 := by simp [v, u₀, dotProduct_add, hw_orth]
    simp [hv0] at h1
  obtain ⟨m, hm⟩ := X.property.isHermitian.exists_eigenvalues₀_eq_of_mulVec_eq_smul hv_ne heig
  obtain rfl : m = k := by
    by_contra hmk; exact hgap m hmk (by simpa [v, u₀] using congrArg RCLike.re hm)
  rw [hm] at heig
  exact X.property.isHermitian.eigenprojector₀_eq_rankOneHermitianProjector_of_mulVec_eq_smul
    hsimple hv_ne heig

end ImplicitBranch

section SmoothAndVariation

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **Analyticity and smoothness of simple spectral projectors** over `ℝ` for every `m : ℕ∞ω`. -/
theorem contDiffAt_eigenprojector₀ {A : selfAdjoint (Matrix n n 𝕜)} {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.property.isHermitian.eigenvalues₀ j ≠ A.property.isHermitian.eigenvalues₀ k)
    {m : ℕ∞ω} :
    ContDiffAt ℝ m
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenprojector₀ k) A := by
  have hu_ne : ⇑(A.property.isHermitian.eigenvectorBasis₀ k) +
      localEigPerturb A.property.isHermitian hk A.val ≠ 0 := by
    rw [localEigPerturb_self A.property.isHermitian hk, add_zero]
    intro h0; simpa [h0] using A.property.isHermitian.dotProduct_star_eigenvectorBasis₀_self k
  have hv_smooth : ContDiffAt ℝ ω (fun X : selfAdjoint (Matrix n n 𝕜) ↦
      ⇑(A.property.isHermitian.eigenvectorBasis₀ k) +
        localEigPerturb A.property.isHermitian hk X.val) A :=
    contDiffAt_const.add (((contDiffAt_localEigPerturb A.property.isHermitian hk).restrict_scalars
      ℝ).comp A (selfAdjoint.contDiff_subtype_val ℝ).contDiffAt)
  -- Both `contDiffAt_rankOneHermitianProjector` and this file use `Matrix.l2OpNormedAlgebraReal`.
  exact (((TauCeti.contDiffAt_rankOneHermitianProjector hu_ne).comp A hv_smooth)
    |>.congr_of_eventuallyEq (eventuallyEq_eigenprojector₀_rankOne hk)).of_le le_top

/-- **Analyticity and smoothness of simple sorted eigenvalues** on `selfAdjoint (Matrix n n 𝕜)`
for every `m : ℕ∞ω`. -/
theorem contDiffAt_eigenvalues₀_selfAdjoint {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.property.isHermitian.eigenvalues₀ j ≠ A.property.isHermitian.eigenvalues₀ k)
    {m : ℕ∞ω} :
    ContDiffAt ℝ m
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenvalues₀ k) A := by
  have hfn : (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenvalues₀ k) =
      fun X ↦ RCLike.reCLM (traceCLM n ℝ 𝕜 (X.property.isHermitian.eigenprojector₀ k * X.val)) :=
    funext fun X ↦ by
      rw [RCLike.reCLM_apply, traceCLM_apply,
        X.property.isHermitian.re_trace_eigenprojector₀_mul_eq_eigenvalues₀]
  rw [hfn]
  exact ((RCLike.reCLM.comp (traceCLM n ℝ 𝕜)).contDiff (n := m)).contDiffAt.comp A
    ((contDiffAt_eigenprojector₀ hk).mul (selfAdjoint.contDiff_subtype_val ℝ).contDiffAt)

/-- On the open simple-spectrum locus, each spectral projector is `C^m` over `ℝ`. -/
theorem contDiffOn_eigenprojector₀_setOf_strictAnti_eigenvalues₀ (k : Fin (Fintype.card n))
    {m : ℕ∞ω} :
    ContDiffOn ℝ m (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenprojector₀ k)
      {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.property.isHermitian.eigenvalues₀} :=
  fun _ hX ↦ (contDiffAt_eigenprojector₀ fun _ hjk ↦ hX.injective.ne hjk).contDiffWithinAt

/-- On the open simple-spectrum locus, each sorted eigenvalue is `C^m` over `ℝ`. -/
theorem contDiffOn_eigenvalues₀_setOf_strictAnti_eigenvalues₀ (k : Fin (Fintype.card n))
    {m : ℕ∞ω} :
    ContDiffOn ℝ m (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenvalues₀ k)
      {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.property.isHermitian.eigenvalues₀} :=
  fun _ hX ↦
    (contDiffAt_eigenvalues₀_selfAdjoint fun _ hjk ↦ hX.injective.ne hjk).contDiffWithinAt

private theorem rankOneProjector_deriv_sum_eq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : Fin (Fintype.card n)) :
    vecMulVec (localEigPerturbFDeriv hA k B) (star ⇑(hA.eigenvectorBasis₀ k)) +
        vecMulVec ⇑(hA.eigenvectorBasis₀ k) (star (localEigPerturbFDeriv hA k B)) -
        (2 * RCLike.re (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ localEigPerturbFDeriv hA k B)) •
          vecMulVec ⇑(hA.eigenvectorBasis₀ k) (star ⇑(hA.eigenvectorBasis₀ k)) =
      ∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
        (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j +
          hA.eigenprojector₀ j * B * hA.eigenprojector₀ k) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set dy : n → 𝕜 := localEigPerturbFDeriv hA k B
  have hdy : dy = ∑ j ∈ Finset.univ.erase k,
      (((hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ : ℝ) : 𝕜) •
        (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀)) := localEigPerturbFDeriv_apply hA k B
  have horth : star u₀ ⬝ᵥ dy = 0 := by
    rw [hdy, dotProduct_sum]
    exact Finset.sum_eq_zero fun j hj ↦ by
      simp [u₀, hA.eigenprojector₀_mulVec,
        hA.dotProduct_star_eigenvectorBasis₀_of_ne (Finset.mem_erase.mp hj).left.symm]
  rw [horth, RCLike.zero_re, mul_zero, zero_smul, sub_zero]
  have hlhs : vecMulVec dy (star u₀) + vecMulVec u₀ (star dy) =
      ∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
        (vecMulVec (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀)) (star u₀) +
          vecMulVec u₀ (star (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀)))) := by
    ext a b
    simp [hdy, vecMulVec_apply, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
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

/-- **Hadamard's first variation of a simple spectral projector** on self-adjoint matrices. -/
theorem hasStrictFDerivAt_eigenprojector₀ {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.property.isHermitian.eigenvalues₀ j ≠ A.property.isHermitian.eigenvalues₀ k) :
    HasStrictFDerivAt
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenprojector₀ k)
      (∑ j ∈ Finset.univ.erase k,
        (A.property.isHermitian.eigenvalues₀ k - A.property.isHermitian.eigenvalues₀ j)⁻¹ •
          ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜)
              (A.property.isHermitian.eigenprojector₀ k)
              (A.property.isHermitian.eigenprojector₀ j) +
            ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜)
              (A.property.isHermitian.eigenprojector₀ j)
              (A.property.isHermitian.eigenprojector₀ k)).comp
            (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)))) A := by
  have hw_deriv := ((hasStrictFDerivAt_localEigPerturb A.property.isHermitian hk).restrictScalars
    ℝ).comp A (selfAdjoint.hasStrictFDerivAt_subtype_val ℝ)
  have hv_deriv := ((hasStrictFDerivAt_const ⇑(A.property.isHermitian.eigenvectorBasis₀ k) A).add
    hw_deriv).congr_fderiv (zero_add _)
  set u : n → 𝕜 := ⇑(A.property.isHermitian.eigenvectorBasis₀ k) +
    localEigPerturb A.property.isHermitian hk A.val
  have hu_unit : star u ⬝ᵥ u = 1 := by
    dsimp only [u]; rw [localEigPerturb_self A.property.isHermitian hk, add_zero,
      A.property.isHermitian.dotProduct_star_eigenvectorBasis₀_self]
  have hu_ne : u ≠ 0 := fun h0 ↦ by simp [h0] at hu_unit
  -- Move the composed strict derivative from `instTopologicalSpaceMatrix` into the file's local
  -- `Matrix.l2OpNormedAlgebraReal` topology and `ℝ`-module structure.
  have hcomp_l2 : HasStrictFDerivAt
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦ TauCeti.rankOneHermitianProjector
        (⇑(A.property.isHermitian.eigenvectorBasis₀ k) +
          localEigPerturb A.property.isHermitian hk X.val))
      (∑ j ∈ Finset.univ.erase k,
        (A.property.isHermitian.eigenvalues₀ k - A.property.isHermitian.eigenvalues₀ j)⁻¹ •
          ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜)
              (A.property.isHermitian.eigenprojector₀ k)
              (A.property.isHermitian.eigenprojector₀ j) +
            ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜)
              (A.property.isHermitian.eigenprojector₀ j)
              (A.property.isHermitian.eigenprojector₀ k)).comp
            (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)))) A := by
    refine (TauCeti.hasStrictFDerivAt_congr_codomain
      (Matrix.l2OpTopologicalSpace_eq n n 𝕜).symm (Matrix.l2OpModuleReal_eq n 𝕜).symm
      fun B ↦ ?_).mp
      ((TauCeti.hasStrictFDerivAt_rankOneHermitianProjector hu_ne).comp A hv_deriv)
    simpa [u, localEigPerturb_self A.property.isHermitian hk,
      TauCeti.rankOneHermitianProjector_eq_real_smul, smul_add] using
      rankOneProjector_deriv_sum_eq A.property.isHermitian B.property.isHermitian k
  exact hcomp_l2.congr_of_eventuallyEq (eventuallyEq_eigenprojector₀_rankOne hk).symm

/-- Applied Fréchet derivative of `X ↦ X.property.isHermitian.eigenprojector₀ k` at simple `λₖ`. -/
theorem fderiv_eigenprojector₀_apply {A : selfAdjoint (Matrix n n 𝕜)} {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.property.isHermitian.eigenvalues₀ j ≠ A.property.isHermitian.eigenvalues₀ k)
    (B : selfAdjoint (Matrix n n 𝕜)) :
    fderiv ℝ (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenprojector₀ k) A B =
      ∑ j ∈ Finset.univ.erase k,
        (A.property.isHermitian.eigenvalues₀ k - A.property.isHermitian.eigenvalues₀ j)⁻¹ •
          (A.property.isHermitian.eigenprojector₀ k * (B : Matrix n n 𝕜) *
              A.property.isHermitian.eigenprojector₀ j +
            A.property.isHermitian.eigenprojector₀ j * (B : Matrix n n 𝕜) *
              A.property.isHermitian.eigenprojector₀ k) :=
  (congrFun (congrArg DFunLike.coe (hasStrictFDerivAt_eigenprojector₀ hk).hasFDerivAt.fderiv)
    B).trans (by simp)

private theorem trace_eigenprojector₀_sandwich_mul_self_of_ne {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {i j : Fin (Fintype.card n)} (hij : i ≠ j) (M : Matrix n n 𝕜) :
    (hA.eigenprojector₀ i * M * hA.eigenprojector₀ j * A).trace = 0 := by
  rw [Matrix.mul_assoc _ (hA.eigenprojector₀ j)]
  simp [trace_mul_comm (hA.eigenprojector₀ i * M), ← Matrix.mul_assoc,
    hA.eigenprojector₀_mul_of_ne hij.symm]

/-- **Hadamard's first variation of a simple sorted eigenvalue** in projector-trace strict Fréchet
form on `selfAdjoint (Matrix n n 𝕜)`. -/
theorem hasStrictFDerivAt_eigenvalues₀_selfAdjoint {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.property.isHermitian.eigenvalues₀ j ≠ A.property.isHermitian.eigenvalues₀ k) :
    HasStrictFDerivAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenvalues₀ k)
      (RCLike.reCLM.comp ((traceCLM n ℝ 𝕜).comp
        ((ContinuousLinearMap.mul ℝ (Matrix n n 𝕜) (A.property.isHermitian.eigenprojector₀ k)).comp
          (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜))))) A := by
  have hfn : (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenvalues₀ k) =
      (RCLike.reCLM.comp (traceCLM n ℝ 𝕜)) ∘ fun X : selfAdjoint (Matrix n n 𝕜) ↦
        X.property.isHermitian.eigenprojector₀ k * X.val :=
    funext fun X ↦ by
      rw [Function.comp_apply, ContinuousLinearMap.comp_apply, RCLike.reCLM_apply, traceCLM_apply,
        X.property.isHermitian.re_trace_eigenprojector₀_mul_eq_eigenvalues₀]
  rw [hfn]
  refine ((RCLike.reCLM.comp (traceCLM n ℝ 𝕜)).hasStrictFDerivAt.comp A
    ((hasStrictFDerivAt_eigenprojector₀ hk).fun_mul'
      (selfAdjoint.hasStrictFDerivAt_subtype_val ℝ))).congr_fderiv ?_
  ext B; set hA := A.property.isHermitian
  suffices ∑ j ∈ Finset.univ.erase k,
      ((hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ *
          RCLike.re (hA.eigenprojector₀ k * B.val * hA.eigenprojector₀ j * A.val).trace +
        (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ *
          RCLike.re (hA.eigenprojector₀ j * B.val * hA.eigenprojector₀ k * A.val).trace) = 0 by
    simpa [Matrix.sum_mul, add_mul, RCLike.smul_re] using this
  exact Finset.sum_eq_zero fun j hj ↦ by
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).left
    simp [trace_eigenprojector₀_sandwich_mul_self_of_ne hA hjk.symm,
      trace_eigenprojector₀_sandwich_mul_self_of_ne hA hjk]

/-- Applied Fréchet derivative of `X ↦ X.property.isHermitian.eigenvalues₀ k` at simple `λₖ`. -/
theorem fderiv_eigenvalues₀_selfAdjoint_apply {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.property.isHermitian.eigenvalues₀ j ≠ A.property.isHermitian.eigenvalues₀ k)
    (B : selfAdjoint (Matrix n n 𝕜)) :
    fderiv ℝ (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenvalues₀ k) A B =
      RCLike.re (A.property.isHermitian.eigenprojector₀ k * (B : Matrix n n 𝕜)).trace :=
  (congrFun (congrArg DFunLike.coe
    (hasStrictFDerivAt_eigenvalues₀_selfAdjoint hk).hasFDerivAt.fderiv) B).trans (by simp)

/-- **Hadamard's second variation of a simple sorted eigenvalue** on self-adjoint matrices. -/
theorem hasStrictFDerivAt_fderiv_eigenvalues₀ {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.property.isHermitian.eigenvalues₀ j ≠ A.property.isHermitian.eigenvalues₀ k)
    (C : selfAdjoint (Matrix n n 𝕜)) :
    HasStrictFDerivAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦
        fderiv ℝ (fun Y : selfAdjoint (Matrix n n 𝕜) ↦ Y.property.isHermitian.eigenvalues₀ k) X C)
      ((2 : ℝ) • ∑ j ∈ Finset.univ.erase k,
        (A.property.isHermitian.eigenvalues₀ k - A.property.isHermitian.eigenvalues₀ j)⁻¹ •
          RCLike.reCLM.comp ((traceCLM n ℝ 𝕜).comp
            (((ContinuousLinearMap.mul ℝ (Matrix n n 𝕜)).flip (C : Matrix n n 𝕜)).comp
              ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n 𝕜)
                  (A.property.isHermitian.eigenprojector₀ k)
                  (A.property.isHermitian.eigenprojector₀ j)).comp
                (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)))))) A := by
  let hlin : Matrix n n 𝕜 →L[ℝ] ℝ := RCLike.reCLM.comp
    ((traceCLM n ℝ 𝕜).comp ((ContinuousLinearMap.mul ℝ (Matrix n n 𝕜)).flip C.val))
  have hev : (fun X : selfAdjoint (Matrix n n 𝕜) ↦
      fderiv ℝ (fun Y : selfAdjoint (Matrix n n 𝕜) ↦ Y.property.isHermitian.eigenvalues₀ k) X C)
        =ᶠ[𝓝 A]
      fun X : selfAdjoint (Matrix n n 𝕜) ↦ hlin (X.property.isHermitian.eigenprojector₀ k) := by
    filter_upwards [(isOpen_setOf_forall_eigenvalues₀_ne k).mem_nhds hk] with X hX
    simp [hlin, fderiv_eigenvalues₀_selfAdjoint_apply hX C]
  refine ((hlin.hasStrictFDerivAt.comp A (hasStrictFDerivAt_eigenprojector₀ hk))
    |>.congr_of_eventuallyEq hev.symm).congr_fderiv ?_
  ext B; set hA := A.property.isHermitian
  have hsymm_tr (j : Fin (Fintype.card n)) :
      RCLike.re (hA.eigenprojector₀ j * B.val * hA.eigenprojector₀ k * C.val).trace =
        RCLike.re (hA.eigenprojector₀ k * B.val * hA.eigenprojector₀ j * C.val).trace := by
    have hconj : (hA.eigenprojector₀ j * B.val * hA.eigenprojector₀ k * C.val).trace =
        star (hA.eigenprojector₀ k * B.val * hA.eigenprojector₀ j * C.val).trace := by
      rw [← trace_conjTranspose]
      simp only [conjTranspose_mul, C.property.isHermitian.eq, B.property.isHermitian.eq,
        hA.conjTranspose_eigenprojector₀]
      rw [trace_mul_comm, Matrix.mul_assoc]
    rw [hconj, RCLike.star_def, RCLike.conj_re]
  suffices ∑ x ∈ Finset.univ.erase k,
        (RCLike.re ((hA.eigenvalues₀ k - hA.eigenvalues₀ x)⁻¹ •
            (hA.eigenprojector₀ k * B.val * hA.eigenprojector₀ x * C.val).trace) +
          RCLike.re ((hA.eigenvalues₀ k - hA.eigenvalues₀ x)⁻¹ •
            (hA.eigenprojector₀ x * B.val * hA.eigenprojector₀ k * C.val).trace)) =
      ∑ i ∈ Finset.univ.erase k, 2 * ((hA.eigenvalues₀ k - hA.eigenvalues₀ i)⁻¹ *
        RCLike.re (hA.eigenprojector₀ k * B.val * hA.eigenprojector₀ i * C.val).trace) by
    simpa [hlin, Finset.mul_sum] using this
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [RCLike.smul_re, RCLike.smul_re, hsymm_tr]
  ring

/-- Applied second Fréchet derivative of `X ↦ X.property.isHermitian.eigenvalues₀ k`. -/
theorem fderiv_fderiv_eigenvalues₀_apply {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.property.isHermitian.eigenvalues₀ j ≠ A.property.isHermitian.eigenvalues₀ k)
    (B C : selfAdjoint (Matrix n n 𝕜)) :
    fderiv ℝ (fderiv ℝ
        (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenvalues₀ k)) A B C =
      2 * ∑ j ∈ Finset.univ.erase k,
        (A.property.isHermitian.eigenvalues₀ k - A.property.isHermitian.eigenvalues₀ j)⁻¹ *
          RCLike.re (A.property.isHermitian.eigenprojector₀ k * (B : Matrix n n 𝕜) *
            A.property.isHermitian.eigenprojector₀ j * (C : Matrix n n 𝕜)).trace := by
  have h1 := ((contDiffAt_eigenvalues₀_selfAdjoint (m := 2) hk).hasFDerivAt_fderiv_apply le_rfl
    C).unique (hasStrictFDerivAt_fderiv_eigenvalues₀ hk C).hasFDerivAt
  simpa using congrFun (congrArg DFunLike.coe h1) B

namespace IsHermitian

variable {A B : Matrix n n 𝕜}

omit [Fintype n] [DecidableEq n] in
private theorem apply_isHermitian_congr {α : Type*}
    (F : ∀ {M : Matrix n n 𝕜}, M.IsHermitian → α) {M₁ M₂ : Matrix n n 𝕜}
    (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian) (h : M₁ = M₂) : F h₁ = F h₂ := by
  subst h; rfl

omit [Fintype n] [DecidableEq n] in
private theorem comp_selfAdjoint_add_smul {α : Type*}
    (F : ∀ {M : Matrix n n 𝕜}, M.IsHermitian → α) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (fun t : ℝ ↦ F (hA.add (hB.smul (IsSelfAdjoint.all t)))) =
      fun t : ℝ ↦ F ((⟨A, hA.isSelfAdjoint⟩ +
        t • (⟨B, hB.isSelfAdjoint⟩ : selfAdjoint (Matrix n n 𝕜))).property.isHermitian) :=
  funext fun _ ↦ apply_isHermitian_congr F _ _ (by simp)

/-- Directional derivative of `t ↦ (A + t • B).eigenprojector₀ k` at `t = 0` for simple `λₖ(A)`. -/
theorem hasDerivAt_eigenprojector₀_add_smul (hA : A.IsHermitian) (hB : B.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    HasDerivAt (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenprojector₀ k)
      (∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
        (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j +
          hA.eigenprojector₀ j * B * hA.eigenprojector₀ k)) 0 := by
  let A' : selfAdjoint (Matrix n n 𝕜) := ⟨A, hA.isSelfAdjoint⟩
  let B' : selfAdjoint (Matrix n n 𝕜) := ⟨B, hB.isSelfAdjoint⟩
  rw [comp_selfAdjoint_add_smul (fun h ↦ h.eigenprojector₀ k) hA hB]
  refine ((hasStrictFDerivAt_eigenprojector₀ (A := A') hk).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const B').const_add A') (by simp)).congr_deriv ?_
  dsimp only [A', B']; simp [smul_add]

/-- **Hadamard's second directional variation** (projector-trace form) at `t = 0`. -/
theorem iteratedDeriv_two_eigenvalues₀_add_smul (hA : A.IsHermitian) (hB : B.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    iteratedDeriv 2 (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k) 0 =
      2 * ∑ j ∈ Finset.univ.erase k, (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ *
        RCLike.re (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j * B).trace := by
  let A' : selfAdjoint (Matrix n n 𝕜) := ⟨A, hA.isSelfAdjoint⟩
  let B' : selfAdjoint (Matrix n n 𝕜) := ⟨B, hB.isSelfAdjoint⟩
  have hc : ContDiffAt ℝ 2
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.property.isHermitian.eigenvalues₀ k)
      (A' + (0 : ℝ) • B') := by
    simpa using contDiffAt_eigenvalues₀_selfAdjoint (A := A') (m := 2) hk
  rw [comp_selfAdjoint_add_smul (fun h ↦ h.eigenvalues₀ k) hA hB,
    iteratedDeriv_succ, iteratedDeriv_one, hc.deriv_deriv_comp_add_smul]
  simpa [A', B'] using fderiv_fderiv_eigenvalues₀_apply (A := A') hk B' B'

end IsHermitian

end SmoothAndVariation

end Matrix
