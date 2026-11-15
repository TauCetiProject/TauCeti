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
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.ImplicitContDiff
import TauCeti.Analysis.Calculus.ContDiff.Star
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous

/-!
# Smoothness and Hadamard variation of simple Hermitian eigenvalues and projectors

While the ordered eigenvalues `Matrix.IsHermitian.eigenvalues₀` are globally `1`-Lipschitz on
`selfAdjoint (Matrix n n 𝕜)`, smoothness fails at eigenvalue collisions. At any Hermitian matrix
`A` whose `k`-th sorted eigenvalue `λₖ(A)` is simple (`∀ j ≠ k, λⱼ(A) ≠ λₖ(A)`), both the
eigenvalue `X ↦ λₖ(X)` and the rank-one spectral projector `X ↦ Pₖ(X)` are real-analytic (and in
particular `C^∞`) on a neighborhood of `A` in `selfAdjoint (Matrix n n 𝕜)`, and hence on the open
Weyl chamber `{X | StrictAnti X.2.isHermitian.eigenvalues₀}` of matrices with distinct eigenvalues.

Differentiating in `selfAdjoint (Matrix n n 𝕜)` gives the **Hadamard variation formulas** (also
known in quantum mechanics as the Hellmann–Feynman and Rayleigh–Schrödinger perturbation formulas):
* **First variation of the eigenvalue:**
  `D(λₖ)(A)[B] = RCLike.re (Pₖ(A) * B).trace = RCLike.re (uₖ* B uₖ)`.
* **First variation of the spectral projector:**
  `D(Pₖ)(A)[B] = ∑ j ≠ k, (λₖ(A) - λⱼ(A))⁻¹ • (Pₖ(A) * B * Pⱼ(A) + Pⱼ(A) * B * Pₖ(A))`.
* **Second variation of the eigenvalue:**
  `D²(λₖ)(A)[B, C] = 2 * ∑ j ≠ k, (λₖ(A) - λⱼ(A))⁻¹ * RCLike.re (Pₖ(A) * B * Pⱼ(A) * C).trace`,
  and along `t ↦ A + t • B` at `t = 0`,
  `(d²/dt²)|₀ λₖ(A + t • B) = 2 * ∑ j ≠ k, (λₖ(A) - λⱼ(A))⁻¹ * ‖uⱼ* B uₖ‖²`.

The proof avoids determinants or contour integrals: for unit eigenvector `u₀` of `A` with projector
`P₀ = u₀ u₀*`, the `𝕜`-polynomial normalization equation
`G(B, w) = (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - (u₀* B (u₀ + w)) • w) + (u₀* w) • u₀ = 0`
has invertible `w`-derivative `y ↦ (A - λ₀ • 1 + P₀) *ᵥ y` at `(A, 0)`, with explicit inverse
`P₀ + ∑ j ≠ k, (λⱼ - λ₀)⁻¹ • Pⱼ`. Mathlib's `ContDiffAt.implicitFunction` supplies a local
`C^ω` eigenvector branch `u₀ + w(X)` whose rank-one Hermitian projector agrees with `Pₖ(X)` near
`A`, from which all smoothness and variation identities follow algebraically.

## Main definitions and results

* `Matrix.traceCLM`: the matrix trace as a continuous `𝕜`-linear map under the Euclidean operator
  norm.
* `Matrix.isOpen_setOf_forall_eigenvalues₀_ne` and `Matrix.isOpen_setOf_strictAnti_eigenvalues₀`:
  the simple-eigenvalue locus and the open Weyl chamber are open in `selfAdjoint (Matrix n n 𝕜)`.
* `TauCeti.contDiffAt_rankOneHermitianProjector`: `C^m` smoothness of
  `TauCeti.rankOneHermitianProjector` at any nonzero vector for every `m : ℕ∞ω`.
* `Matrix.contDiffAt_eigenprojector₀`, `Matrix.contDiffAt_eigenvalues₀`,
  `Matrix.contDiffOn_eigenprojector₀_strictAnti`, `Matrix.contDiffOn_eigenvalues₀_strictAnti`:
  `C^m` smoothness for every `m : ℕ∞ω` (including `∞` and `ω`).
* `Matrix.hasStrictFDerivAt_eigenprojector₀`, `Matrix.hasStrictFDerivAt_eigenvalues₀`, and
  `Matrix.hasStrictFDerivAt_fderiv_eigenvalues₀`: Hadamard's first and second Fréchet derivatives.
* `Matrix.IsHermitian.hasDerivAt_add_smul_eigenvalues₀`,
  `Matrix.IsHermitian.hasDerivAt_add_smul_eigenprojector₀`, and
  `Matrix.IsHermitian.iteratedDeriv_two_add_smul_eigenvalues₀_eq_sum_norm_sq`: directional first
  and second derivatives along `t ↦ A + t • B`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.1, Lemma 4.3.4.
* T. Kato, *Perturbation Theory for Linear Operators*, Classics in Mathematics, Springer (1995),
  Chapter II, §1–§2.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), Chapter V.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §1.3.4.
-/

public section

noncomputable section

open scoped ContDiff Topology Matrix.Norms.L2Operator ComplexOrder

/-- Local `ℝ`-normed algebra structure on `Matrix n n 𝕜` induced by the Euclidean operator norm. -/
local instance matrixNormedAlgebraReal {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] :
    NormedAlgebra ℝ (Matrix n n 𝕜) :=
  Matrix.l2OpNormedAlgebraReal

namespace Matrix

section Openness

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The sorted eigenvalue map `X ↦ X.2.isHermitian.eigenvalues₀` is continuous on
`selfAdjoint (Matrix n n 𝕜)`. -/
@[fun_prop]
theorem continuous_selfAdjoint_eigenvalues₀ :
    Continuous (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀) := by
  let emb : selfAdjoint (Matrix n n 𝕜) → {M : Matrix n n 𝕜 // M.IsHermitian} :=
    fun X ↦ ⟨(X : Matrix n n 𝕜), X.2.isHermitian⟩
  have hemb : Continuous emb := continuous_subtype_val.subtype_mk fun X ↦ X.2.isHermitian
  exact continuous_eigenvalues₀.comp hemb

/-- The set of self-adjoint matrices whose `k`-th sorted eigenvalue is simple is open in
`selfAdjoint (Matrix n n 𝕜)`. -/
theorem isOpen_setOf_forall_eigenvalues₀_ne (k : Fin (Fintype.card n)) :
    IsOpen {X : selfAdjoint (Matrix n n 𝕜) |
      ∀ j ≠ k, X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k} := by
  have heq : {X : selfAdjoint (Matrix n n 𝕜) |
      ∀ j ≠ k, X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k} =
      ⋂ j ∈ Finset.univ.erase k,
        {X : selfAdjoint (Matrix n n 𝕜) |
          X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k} := by
    ext X
    simp [Finset.mem_erase]
  rw [heq]
  refine isOpen_biInter_finset fun j _ ↦ isOpen_ne_fun ?_ ?_
  · exact (continuous_apply j).comp continuous_selfAdjoint_eigenvalues₀
  · exact (continuous_apply k).comp continuous_selfAdjoint_eigenvalues₀

/-- The open Weyl chamber of self-adjoint matrices with strictly decreasing sorted eigenvalues is
open in `selfAdjoint (Matrix n n 𝕜)`. -/
theorem isOpen_setOf_strictAnti_eigenvalues₀ :
    IsOpen {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.2.isHermitian.eigenvalues₀} := by
  have heq : {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.2.isHermitian.eigenvalues₀} =
      ⋂ i : Fin (Fintype.card n), ⋂ j : {j : Fin (Fintype.card n) // i < j},
        {X : selfAdjoint (Matrix n n 𝕜) |
          X.2.isHermitian.eigenvalues₀ j.1 < X.2.isHermitian.eigenvalues₀ i} := by
    ext X
    simp [StrictAnti, Subtype.forall]
  rw [heq]
  refine isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦ isOpen_lt ?_ ?_
  · exact (continuous_apply j.1).comp continuous_selfAdjoint_eigenvalues₀
  · exact (continuous_apply i).comp continuous_selfAdjoint_eigenvalues₀

end Openness

section TraceCLM

variable (𝕜 n : Type*) [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Continuous `𝕜`-linear extraction of entry `(i, j)` under the Euclidean operator norm. -/
private def entryCLM (i j : n) : Matrix n n 𝕜 →L[𝕜] 𝕜 :=
  (Matrix.entryLinearMap 𝕜 𝕜 i j).mkContinuous 1 fun M ↦ by
    simpa using M.norm_apply_le_l2_opNorm i j

@[simp]
private theorem entryCLM_apply {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
    (i j : n) (M : Matrix n n 𝕜) [DecidableEq n] : entryCLM 𝕜 n i j M = M i j :=
  rfl

/-- The matrix trace as a continuous `𝕜`-linear functional on `Matrix n n 𝕜` equipped with the
Euclidean operator norm. -/
def traceCLM : Matrix n n 𝕜 →L[𝕜] 𝕜 :=
  ∑ i : n, entryCLM 𝕜 n i i

/-- Applying `Matrix.traceCLM` evaluates `Matrix.trace`. -/
@[simp]
theorem traceCLM_apply {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (M : Matrix n n 𝕜) : traceCLM 𝕜 n M = M.trace := by
  simp [traceCLM, Matrix.trace]

end TraceCLM

end Matrix

/-! ### Smoothness and strict derivative of `rankOneHermitianProjector` -/

section RankOneProjectorCalculus

open Matrix

section NoDecidableEq

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

private def dotProductLeftCLM (w : n → 𝕜) : (n → 𝕜) →L[𝕜] 𝕜 :=
  ∑ i : n, (ContinuousLinearMap.mul 𝕜 𝕜 (w i)).comp (ContinuousLinearMap.proj (R := 𝕜) i)

@[simp]
private theorem dotProductLeftCLM_apply (w y : n → 𝕜) :
    dotProductLeftCLM w y = w ⬝ᵥ y := by
  simp [dotProductLeftCLM, dotProduct]

private def reDotProductStarCLM (u : n → 𝕜) : (n → 𝕜) →L[ℝ] ℝ :=
  RCLike.reCLM.comp ((dotProductLeftCLM (star u)).restrictScalars ℝ)

@[simp]
private theorem reDotProductStarCLM_apply (u y : n → 𝕜) :
    reDotProductStarCLM u y = RCLike.re (star u ⬝ᵥ y) := by
  simp [reDotProductStarCLM]

private theorem re_dotProduct_star_self_eq (v : n → 𝕜) :
    ((RCLike.re (star v ⬝ᵥ v) : ℝ) : 𝕜) = star v ⬝ᵥ v :=
  RCLike.conj_eq_iff_re.mp (star_dotProduct v v).symm

private theorem rankOneHermitianProjector_eq_real_smul (v : n → 𝕜) :
    TauCeti.rankOneHermitianProjector v =
      (RCLike.re (star v ⬝ᵥ v))⁻¹ • Matrix.vecMulVec v (star v) := by
  rw [TauCeti.rankOneHermitianProjector_def, RCLike.real_smul_eq_coe_smul (K := 𝕜),
    RCLike.ofReal_inv, re_dotProduct_star_self_eq]

private theorem contDiff_re_dotProduct_star_self {m : ℕ∞ω} :
    ContDiff ℝ m (fun v : n → 𝕜 ↦ RCLike.re (star v ⬝ᵥ v)) := by
  have hfn : (fun v : n → 𝕜 ↦ RCLike.re (star v ⬝ᵥ v)) =
      fun v ↦ ∑ i : n, RCLike.reCLM (star (v i) * v i) := by
    ext v
    simp [dotProduct]
  rw [hfn]
  refine ContDiff.sum fun i _ ↦ ?_
  let proj_i : (n → 𝕜) →L[ℝ] 𝕜 := ContinuousLinearMap.proj (R := ℝ) i
  have h1 : ContDiff ℝ m (fun v : n → 𝕜 ↦ star (v i)) :=
    ((starL' ℝ : 𝕜 ≃L[ℝ] 𝕜).contDiff (n := m)).comp (proj_i.contDiff (n := m))
  have h2 : ContDiff ℝ m (fun v : n → 𝕜 ↦ v i) := proj_i.contDiff (n := m)
  exact (RCLike.reCLM.contDiff (n := m)).comp (h1.mul h2)

private theorem hasStrictFDerivAt_re_dotProduct_star_self (u : n → 𝕜) :
    HasStrictFDerivAt (fun v : n → 𝕜 ↦ RCLike.re (star v ⬝ᵥ v))
      ((2 : ℝ) • reDotProductStarCLM u) u := by
  have hfn : (fun v : n → 𝕜 ↦ RCLike.re (star v ⬝ᵥ v)) =
      fun v ↦ ∑ i : n, RCLike.reCLM (star (v i) * v i) := by
    ext v
    simp [dotProduct]
  rw [hfn]
  have hsum : HasStrictFDerivAt (fun v : n → 𝕜 ↦ ∑ i : n, RCLike.reCLM (star (v i) * v i))
      (∑ i : n, RCLike.reCLM.comp
        ((((ContinuousLinearMap.mul ℝ 𝕜).flip (u i)).comp
            ((starL' ℝ : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap.comp
              (ContinuousLinearMap.proj (R := ℝ) i))) +
          ((ContinuousLinearMap.mul ℝ 𝕜 (star (u i))).comp
            (ContinuousLinearMap.proj (R := ℝ) i)))) u := by
    refine HasStrictFDerivAt.fun_sum fun i _ ↦ ?_
    let proj_i : (n → 𝕜) →L[ℝ] 𝕜 := ContinuousLinearMap.proj (R := ℝ) i
    let starProj_i : (n → 𝕜) →L[ℝ] 𝕜 :=
      (starL' ℝ : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap.comp proj_i
    have h1 := starProj_i.hasStrictFDerivAt (x := u)
    have h2 := proj_i.hasStrictFDerivAt (x := u)
    refine (RCLike.reCLM.hasStrictFDerivAt.comp u (h1.mul h2)).congr_fderiv ?_
    ext y
    simp [proj_i, starProj_i, mul_comm]
  refine hsum.congr_fderiv ?_
  ext y
  simp [reDotProductStarCLM_apply, dotProduct, Finset.mul_sum, two_mul]

end NoDecidableEq

section WithDecidableEq

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Continuous `𝕜`-linear embedding `c ↦ c • single i j 1` of a scalar into entry `(i, j)`. -/
private def singleSMulCLM (i j : n) : 𝕜 →L[𝕜] Matrix n n 𝕜 :=
  (ContinuousLinearMap.id 𝕜 𝕜).smulRight (Matrix.single i j (1 : 𝕜))

private theorem vecMulVec_eq_sum_singleSMulCLM (x y : n → 𝕜) :
    Matrix.vecMulVec x y = ∑ i : n, ∑ j : n, singleSMulCLM i j (x i * y j) := by
  ext a b
  rw [Matrix.vecMulVec_apply, Matrix.sum_apply, Finset.sum_eq_single a]
  · rw [Matrix.sum_apply, Finset.sum_eq_single b]
    · simp [singleSMulCLM]
    · intro j _ hjb
      simp [singleSMulCLM, hjb]
    · intro hb
      exact (hb (Finset.mem_univ b)).elim
  · intro i _ hia
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp [singleSMulCLM, hia]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

private def vecMulVecLeftCLM (w : n → 𝕜) : (n → 𝕜) →L[ℝ] Matrix n n 𝕜 :=
  ∑ i : n, ∑ j : n, ((singleSMulCLM i j).restrictScalars ℝ).comp
    (((ContinuousLinearMap.mul ℝ 𝕜).flip (w j)).comp (ContinuousLinearMap.proj (R := ℝ) i))

@[simp]
private theorem vecMulVecLeftCLM_apply (w y : n → 𝕜) :
    vecMulVecLeftCLM w y = Matrix.vecMulVec y w := by
  rw [vecMulVec_eq_sum_singleSMulCLM y w]
  simp [vecMulVecLeftCLM, mul_comm]

private def vecMulVecRightStarCLM (w : n → 𝕜) : (n → 𝕜) →L[ℝ] Matrix n n 𝕜 :=
  ∑ i : n, ∑ j : n, ((singleSMulCLM i j).restrictScalars ℝ).comp
    ((ContinuousLinearMap.mul ℝ 𝕜 (w i)).comp
      ((starL' ℝ : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap.comp (ContinuousLinearMap.proj (R := ℝ) j)))

@[simp]
private theorem vecMulVecRightStarCLM_apply (w y : n → 𝕜) :
    vecMulVecRightStarCLM w y = Matrix.vecMulVec w (star y) := by
  rw [vecMulVec_eq_sum_singleSMulCLM w (star y)]
  simp [vecMulVecRightStarCLM]

private theorem contDiff_vecMulVec_star {m : ℕ∞ω} :
    ContDiff ℝ m (fun v : n → 𝕜 ↦ Matrix.vecMulVec v (star v)) := by
  simp_rw [vecMulVec_eq_sum_singleSMulCLM]
  refine ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦ ?_
  let proj_i : (n → 𝕜) →L[ℝ] 𝕜 := ContinuousLinearMap.proj (R := ℝ) i
  let proj_j : (n → 𝕜) →L[ℝ] 𝕜 := ContinuousLinearMap.proj (R := ℝ) j
  have hvi : ContDiff ℝ m (fun v : n → 𝕜 ↦ v i) := proj_i.contDiff (n := m)
  have hvj : ContDiff ℝ m (fun v : n → 𝕜 ↦ star (v j)) :=
    ((starL' ℝ : 𝕜 ≃L[ℝ] 𝕜).contDiff (n := m)).comp (proj_j.contDiff (n := m))
  exact (((singleSMulCLM i j).restrictScalars ℝ).contDiff (n := m)).comp (hvi.mul hvj)

private theorem hasStrictFDerivAt_vecMulVec_star (u : n → 𝕜) :
    HasStrictFDerivAt (fun v : n → 𝕜 ↦ Matrix.vecMulVec v (star v))
      (vecMulVecLeftCLM (star u) + vecMulVecRightStarCLM u) u := by
  have hfn : (fun v : n → 𝕜 ↦ Matrix.vecMulVec v (star v)) =
      fun v ↦ ∑ i : n, ∑ j : n, singleSMulCLM i j (v i * star (v j)) := by
    ext1 v
    exact vecMulVec_eq_sum_singleSMulCLM v (star v)
  rw [hfn]
  have hsum : HasStrictFDerivAt (fun v : n → 𝕜 ↦
      ∑ i : n, ∑ j : n, singleSMulCLM i j (v i * star (v j)))
      (∑ i : n, ∑ j : n, ((singleSMulCLM i j).restrictScalars ℝ).comp
        ((((ContinuousLinearMap.mul ℝ 𝕜).flip (star (u j))).comp
            (ContinuousLinearMap.proj (R := ℝ) i)) +
          ((ContinuousLinearMap.mul ℝ 𝕜 (u i)).comp
            ((starL' ℝ : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap.comp
              (ContinuousLinearMap.proj (R := ℝ) j))))) u := by
    refine HasStrictFDerivAt.fun_sum fun i _ ↦ HasStrictFDerivAt.fun_sum fun j _ ↦ ?_
    let proj_i : (n → 𝕜) →L[ℝ] 𝕜 := ContinuousLinearMap.proj (R := ℝ) i
    let starProj_j : (n → 𝕜) →L[ℝ] 𝕜 :=
      (starL' ℝ : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap.comp (ContinuousLinearMap.proj (R := ℝ) j)
    have hvi := proj_i.hasStrictFDerivAt (x := u)
    have hvj := starProj_j.hasStrictFDerivAt (x := u)
    refine (((singleSMulCLM i j).restrictScalars ℝ).hasStrictFDerivAt.comp u
      (hvi.mul hvj)).congr_fderiv ?_
    ext y
    simp [proj_i, starProj_j, mul_comm, add_comm]
  refine hsum.congr_fderiv ?_
  ext y a b
  simp [vecMulVec_eq_sum_singleSMulCLM, singleSMulCLM, Matrix.single_apply, mul_comm,
    Finset.sum_add_distrib]

private theorem hasStrictFDerivAt_rankOneHermitianProjector_unit
    {u : n → 𝕜} (hu : star u ⬝ᵥ u = 1) :
    HasStrictFDerivAt (TauCeti.rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜)
      (vecMulVecLeftCLM (star u) + vecMulVecRightStarCLM u -
        ((2 : ℝ) • reDotProductStarCLM u).smulRight (Matrix.vecMulVec u (star u))) u := by
  have hfn : (TauCeti.rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜) =
      fun x ↦ (RCLike.re (star x ⬝ᵥ x))⁻¹ • Matrix.vecMulVec x (star x) :=
    funext rankOneHermitianProjector_eq_real_smul
  rw [hfn]
  have hre : RCLike.re (star u ⬝ᵥ u) = 1 := by simp [hu]
  have hne : RCLike.re (star u ⬝ᵥ u) ≠ 0 := by simp [hre]
  have hinv_raw := (hasStrictDerivAt_inv hne).comp_hasStrictFDerivAt u
    (hasStrictFDerivAt_re_dotProduct_star_self u)
  have hprod := hinv_raw.smul (hasStrictFDerivAt_vecMulVec_star u)
  refine hprod.congr_fderiv ?_
  ext y i j
  simp [hre, sub_eq_add_neg, add_comm]

namespace TauCeti

/-- `TauCeti.rankOneHermitianProjector` is `C^m` over `ℝ` (for every `m : ℕ∞ω`, including `∞` and
real-analytic `ω`) at every nonzero vector `v : n → 𝕜`. -/
theorem contDiffAt_rankOneHermitianProjector {v : n → 𝕜} (hv : v ≠ 0) {m : ℕ∞ω} :
    ContDiffAt ℝ m (TauCeti.rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜) v := by
  have hfn : (TauCeti.rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜) =
      fun x ↦ (RCLike.re (star x ⬝ᵥ x))⁻¹ • Matrix.vecMulVec x (star x) :=
    funext rankOneHermitianProjector_eq_real_smul
  rw [hfn]
  have hne : RCLike.re (star v ⬝ᵥ v) ≠ 0 := by
    intro h0
    apply dotProduct_star_self_eq_zero.not.mpr hv
    rw [← re_dotProduct_star_self_eq v, h0, RCLike.ofReal_zero]
  exact ((contDiff_re_dotProduct_star_self (m := m)).contDiffAt.inv hne).smul
    (contDiff_vecMulVec_star (m := m)).contDiffAt

end TauCeti

end WithDecidableEq

end RankOneProjectorCalculus

/-! ### Implicit-function eigenvector branch and local spectral identification -/

namespace Matrix

section ImplicitBranch

section MulVecCLM

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- Continuous `𝕜`-linear matrix-vector multiplication `y ↦ M *ᵥ y`. -/
private def mulVecRightCLM (M : Matrix n n 𝕜) : (n → 𝕜) →L[𝕜] (n → 𝕜) :=
  ContinuousLinearMap.pi fun i ↦
    ∑ j : n, (ContinuousLinearMap.mul 𝕜 𝕜 (M i j)).comp (ContinuousLinearMap.proj (R := 𝕜) j)

@[simp]
private theorem mulVecRightCLM_apply (M : Matrix n n 𝕜) (y : n → 𝕜) :
    mulVecRightCLM M y = M *ᵥ y := by
  ext i
  simp [mulVecRightCLM, mulVec, dotProduct]

/-- Continuous `𝕜`-linear evaluation `B ↦ B *ᵥ u` at a fixed vector `u`. -/
private def mulVecLeftCLM [DecidableEq n] (u : n → 𝕜) : Matrix n n 𝕜 →L[𝕜] (n → 𝕜) :=
  ContinuousLinearMap.pi fun i ↦
    ∑ j : n, ((ContinuousLinearMap.mul 𝕜 𝕜).flip (u j)).comp (entryCLM 𝕜 n i j)

@[simp]
private theorem mulVecLeftCLM_apply [DecidableEq n] (u : n → 𝕜) (B : Matrix n n 𝕜) :
    mulVecLeftCLM u B = B *ᵥ u := by
  ext i
  simp [mulVecLeftCLM, mulVec, dotProduct, mul_comm]

end MulVecCLM

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- `𝕜`-polynomial normalization map whose zero set near `(A, 0)` parametrizes the eigenvector
of `B` orthogonal in perturbation `w` to `u₀ = hA.eigenvectorBasis₀ k`. -/
private def eigNormMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : Fin (Fintype.card n))
    (p : Matrix n n 𝕜 × (n → 𝕜)) : n → 𝕜 :=
  let u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  let P₀ : Matrix n n 𝕜 := hA.eigenprojector₀ k
  (1 - P₀) *ᵥ (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2) +
    (star u₀ ⬝ᵥ p.2) • u₀

private theorem eigNormMap_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    eigNormMap hA k (A, 0) = 0 := by
  simp [eigNormMap, hA.mulVec_eigenvectorBasis₀_coe, sub_mulVec, mulVec_smul,
    hA.eigenprojector₀_mulVec_eigenvectorBasis₀_self]

private theorem eigNormMap_eq_zero_imp {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) {B : Matrix n n 𝕜} {w : n → 𝕜}
    (h0 : eigNormMap hA k (B, w) = 0) :
    star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ w = 0 ∧
      B *ᵥ (⇑(hA.eigenvectorBasis₀ k) + w) =
        (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (B *ᵥ (⇑(hA.eigenvectorBasis₀ k) + w))) •
          (⇑(hA.eigenvectorBasis₀ k) + w) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set P₀ : Matrix n n 𝕜 := hA.eigenprojector₀ k
  have horth : ∀ y : n → 𝕜, star u₀ ⬝ᵥ ((1 - P₀) *ᵥ y) = 0 := by
    intro y
    rw [sub_mulVec, one_mulVec, hA.eigenprojector₀_mulVec, dotProduct_sub, dotProduct_smul,
      hA.dotProduct_star_eigenvectorBasis₀_self, smul_eq_mul, mul_one, sub_self]
  have hw : star u₀ ⬝ᵥ w = 0 := by
    have hdot := congrArg (star u₀ ⬝ᵥ ·) h0
    simpa [eigNormMap, u₀, P₀, dotProduct_add, dotProduct_smul, horth,
      hA.dotProduct_star_eigenvectorBasis₀_self] using hdot
  refine ⟨hw, ?_⟩
  set α : 𝕜 := star u₀ ⬝ᵥ (B *ᵥ (u₀ + w))
  have hproj : (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) = 0 := by
    have hsub : (1 - P₀) *ᵥ u₀ = 0 := by
      rw [sub_mulVec, one_mulVec, hA.eigenprojector₀_mulVec_eigenvectorBasis₀_self, sub_self]
    have h1 : (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) =
        (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • w) := by
      rw [smul_add, add_comm (α • u₀), ← sub_sub, mulVec_sub, mulVec_smul, hsub, smul_zero,
        sub_zero]
    have h2 : (1 - P₀) *ᵥ (B *ᵥ (u₀ + w) - α • w) = 0 := by
      simpa [eigNormMap, u₀, P₀, α, hw] using h0
    exact h1.trans h2
  have hscalar : star u₀ ⬝ᵥ (B *ᵥ (u₀ + w) - α • (u₀ + w)) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_add,
      hA.dotProduct_star_eigenvectorBasis₀_self, hw, add_zero, smul_eq_mul, mul_one, sub_self]
  have hdecomp : ∀ z : n → 𝕜, z = (1 - P₀) *ᵥ z + (star u₀ ⬝ᵥ z) • u₀ := by
    intro z
    rw [sub_mulVec, one_mulVec, hA.eigenprojector₀_mulVec, sub_add_cancel]
  have hz := hdecomp (B *ᵥ (u₀ + w) - α • (u₀ + w))
  rw [hproj, hscalar, zero_smul, add_zero] at hz
  exact sub_eq_zero.mp hz

private theorem contDiff_mulVec_uncurry {m : ℕ∞ω} :
    ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ p.2) := by
  refine contDiff_pi.mpr fun i ↦ ?_
  have hfn : (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ (p.1 *ᵥ p.2) i) =
      fun p ↦ ∑ j : n, entryCLM 𝕜 n i j p.1 * p.2 j := by
    ext p
    simp [mulVec, dotProduct]
  rw [hfn]
  refine ContDiff.sum fun j _ ↦ ?_
  let proj_j : (n → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj (R := 𝕜) j
  have h1 : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ entryCLM 𝕜 n i j p.1) :=
    ((entryCLM 𝕜 n i j).contDiff (n := m)).comp contDiff_fst
  have h2 : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.2 j) :=
    (proj_j.contDiff (n := m)).comp contDiff_snd
  exact h1.mul h2

private theorem contDiff_eigNormMap {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) {m : ℕ∞ω} :
    ContDiff 𝕜 m (eigNormMap hA k) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set P₀ : Matrix n n 𝕜 := hA.eigenprojector₀ k
  have hBw : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ (u₀ + p.2)) :=
    (contDiff_mulVec_uncurry (m := m)).comp (contDiff_fst.prodMk (contDiff_const.add contDiff_snd))
  have hdot : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) := by
    simp_rw [← dotProductLeftCLM_apply]
    exact ((dotProductLeftCLM (star u₀)).contDiff (n := m)).comp hBw
  have hinner : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2) :=
    hBw.sub (hdot.smul contDiff_snd)
  have hpart1 : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      (1 - P₀) *ᵥ (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2)) := by
    have hfn : (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
        (1 - P₀) *ᵥ (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2)) =
        fun p ↦ mulVecRightCLM (1 - P₀)
          (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2) :=
      funext fun _ ↦ (mulVecRightCLM_apply _ _).symm
    rw [hfn]
    exact ((mulVecRightCLM (1 - P₀)).contDiff (n := m)).comp hinner
  have hdot2 : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ p.2) := by
    simp_rw [← dotProductLeftCLM_apply]
    exact ((dotProductLeftCLM (star u₀)).contDiff (n := m)).comp contDiff_snd
  have hpart2 : ContDiff 𝕜 m (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ (star u₀ ⬝ᵥ p.2) • u₀) :=
    hdot2.smul contDiff_const
  exact hpart1.add hpart2

omit [DecidableEq n] in
private theorem hasFDerivAt_mulVec_at_zero (A : Matrix n n 𝕜) :
    HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ p.2)
      ((mulVecRightCLM A).comp (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜))) (A, 0) := by
  classical
  have hpi : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ p.2)
      (ContinuousLinearMap.pi fun i ↦
        ∑ j : n, (ContinuousLinearMap.mul 𝕜 𝕜 (A i j)).comp
          ((ContinuousLinearMap.proj (R := 𝕜) j).comp
            (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)))) (A, 0) := by
    rw [hasFDerivAt_pi]
    intro i
    have hfn : (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ (p.1 *ᵥ p.2) i) =
        fun p ↦ ∑ j : n, entryCLM 𝕜 n i j p.1 * p.2 j := by
      ext p
      simp [mulVec, dotProduct]
    rw [hfn]
    refine HasFDerivAt.fun_sum fun j _ ↦ ?_
    let f1 : (Matrix n n 𝕜 × (n → 𝕜)) →L[𝕜] 𝕜 :=
      (entryCLM 𝕜 n i j).comp (ContinuousLinearMap.fst 𝕜 (Matrix n n 𝕜) (n → 𝕜))
    let f2 : (Matrix n n 𝕜 × (n → 𝕜)) →L[𝕜] 𝕜 :=
      (ContinuousLinearMap.proj (R := 𝕜) j).comp (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜))
    have h1 := f1.hasFDerivAt (x := (A, (0 : n → 𝕜)))
    have h2 := f2.hasFDerivAt (x := (A, (0 : n → 𝕜)))
    refine (h1.mul h2).congr_fderiv <| ContinuousLinearMap.ext fun p ↦ ?_
    simp [f1, f2]
  refine hpi.congr_fderiv <| ContinuousLinearMap.ext fun p ↦ funext fun i ↦ ?_
  simp [mulVec, dotProduct]

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
  have h1PAy : (1 - hA.eigenprojector₀ k) *ᵥ (A *ᵥ y - (hA.eigenvalues₀ k : 𝕜) • y) =
      A *ᵥ y - (hA.eigenvalues₀ k : 𝕜) • y := by
    rw [sub_mulVec, one_mulVec, hPAy, sub_zero]
  rw [add_sub_assoc, mulVec_add, h1PAy, add_assoc]
  congr 1
  rw [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, hA.eigenprojector₀_mulVec]

private theorem hasFDerivAt_eigNormMap_sub {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    HasFDerivAt
      (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
        p.1 *ᵥ (⇑(hA.eigenvectorBasis₀ k) + p.2) -
          (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (p.1 *ᵥ (⇑(hA.eigenvectorBasis₀ k) + p.2))) • p.2)
      (((mulVecLeftCLM ⇑(hA.eigenvectorBasis₀ k)).comp (ContinuousLinearMap.fst 𝕜 _ _) +
          (mulVecRightCLM A).comp (ContinuousLinearMap.snd 𝕜 _ _)) -
        (hA.eigenvalues₀ k : 𝕜) • ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)) (A, 0) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  have hBw : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ (u₀ + p.2))
      ((mulVecLeftCLM u₀).comp (ContinuousLinearMap.fst 𝕜 _ _) +
        (mulVecRightCLM A).comp (ContinuousLinearMap.snd 𝕜 _ _)) (A, 0) := by
    have hBw_eq : (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ (u₀ + p.2)) =
        fun p ↦ mulVecLeftCLM u₀ p.1 + p.1 *ᵥ p.2 := funext fun p ↦ by simp [mulVec_add]
    rw [hBw_eq]
    exact (((mulVecLeftCLM u₀).comp (ContinuousLinearMap.fst 𝕜 _ _)).hasFDerivAt).add
      (hasFDerivAt_mulVec_at_zero A)
  have hsc : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2)))
      ((dotProductLeftCLM (star u₀)).comp
        ((mulVecLeftCLM u₀).comp (ContinuousLinearMap.fst 𝕜 _ _) +
          (mulVecRightCLM A).comp (ContinuousLinearMap.snd 𝕜 _ _))) (A, 0) := by
    simp_rw [← dotProductLeftCLM_apply]
    exact (dotProductLeftCLM (star u₀)).hasFDerivAt.comp (A, 0) hBw
  have hsmul : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2)
      ((hA.eigenvalues₀ k : 𝕜) • ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)) (A, 0) := by
    refine (hsc.smul (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)).hasFDerivAt).congr_fderiv <|
      ContinuousLinearMap.ext fun p ↦ funext fun i ↦ ?_
    simp [u₀, hA.mulVec_eigenvectorBasis₀_coe, dotProduct_smul, RCLike.real_smul_eq_coe_mul]
  exact hBw.sub hsmul

private theorem fderiv_eigNormMap_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    fderiv 𝕜 (eigNormMap hA k) (A, 0) =
      ((mulVecRightCLM (1 - hA.eigenprojector₀ k)).comp
        (mulVecLeftCLM ⇑(hA.eigenvectorBasis₀ k))).comp
          (ContinuousLinearMap.fst 𝕜 (Matrix n n 𝕜) (n → 𝕜)) +
      (mulVecRightCLM (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k)).comp
        (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜)) := by
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set P₀ : Matrix n n 𝕜 := hA.eigenprojector₀ k
  have hpart1 : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
      (1 - P₀) *ᵥ (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2))
      ((mulVecRightCLM (1 - P₀)).comp
        (((mulVecLeftCLM u₀).comp (ContinuousLinearMap.fst 𝕜 _ _) +
          (mulVecRightCLM A).comp (ContinuousLinearMap.snd 𝕜 _ _)) -
          (hA.eigenvalues₀ k : 𝕜) • ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜))) (A, 0) := by
    have hfn : (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦
        (1 - P₀) *ᵥ (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2)) =
        fun p ↦ mulVecRightCLM (1 - P₀)
          (p.1 *ᵥ (u₀ + p.2) - (star u₀ ⬝ᵥ (p.1 *ᵥ (u₀ + p.2))) • p.2) :=
      funext fun _ ↦ (mulVecRightCLM_apply _ _).symm
    rw [hfn]
    exact (mulVecRightCLM (1 - P₀)).hasFDerivAt.comp (A, 0) (hasFDerivAt_eigNormMap_sub hA k)
  let L2 : (Matrix n n 𝕜 × (n → 𝕜)) →L[𝕜] (n → 𝕜) :=
    ((dotProductLeftCLM (star u₀)).comp
      (ContinuousLinearMap.snd 𝕜 (Matrix n n 𝕜) (n → 𝕜))).smulRight u₀
  have hpart2 : HasFDerivAt (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ (star u₀ ⬝ᵥ p.2) • u₀)
      L2 (A, 0) := by
    have hfn : (fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ (star u₀ ⬝ᵥ p.2) • u₀) = ⇑L2 :=
      funext fun p ↦ by simp [L2]
    rw [hfn]
    exact L2.hasFDerivAt
  refine (hpart1.add hpart2).fderiv.trans <| ContinuousLinearMap.ext fun ⟨H, y⟩ ↦ ?_
  simp only [u₀, P₀, L2, add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', mulVecRightCLM_apply, mulVecLeftCLM_apply,
    dotProductLeftCLM_apply]
  exact eigNormMap_linear_simplify hA k H y

/-- Explicit inverse of `A - λₖ • 1 + Pₖ` when `λₖ` is simple. -/
private def reducedResolventPlusProj {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) : Matrix n n 𝕜 :=
  hA.eigenprojector₀ k +
    ∑ j ∈ Finset.univ.erase k,
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
      hA.eigenprojector₀ j := by
    intro j hj
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    have hne : hA.eigenvalues₀ j - hA.eigenvalues₀ k ≠ 0 := sub_ne_zero.mpr (hk j hjk)
    rw [Matrix.mul_smul, add_mul, sub_mul, hA.mul_eigenprojector₀, Matrix.smul_mul, one_mul,
      hA.eigenprojector₀_mul_of_ne hjk.symm, add_zero, ← sub_smul, smul_smul]
    have hinv : (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) *
        ((hA.eigenvalues₀ j : 𝕜) - (hA.eigenvalues₀ k : 𝕜)) = 1 := by
      exact_mod_cast inv_mul_cancel₀ hne
    rw [hinv, one_smul]
  rw [reducedResolventPlusProj, mul_add, hterm_k, Matrix.mul_sum,
    Finset.sum_congr rfl hterm_j, Finset.add_sum_erase _ _ (Finset.mem_univ k),
    hA.sum_eigenprojector₀]

private theorem reducedResolventPlusProj_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    reducedResolventPlusProj hA k *
      (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) = 1 := by
  have hterm_k : hA.eigenprojector₀ k *
      (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) = hA.eigenprojector₀ k := by
    rw [mul_add, mul_sub, hA.eigenprojector₀_mul, Matrix.mul_smul, mul_one, sub_self, zero_add,
      hA.eigenprojector₀_mul_self]
  have hterm_j : ∀ j ∈ Finset.univ.erase k,
      ((((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j) *
        (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) =
      hA.eigenprojector₀ j := by
    intro j hj
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    have hne : hA.eigenvalues₀ j - hA.eigenvalues₀ k ≠ 0 := sub_ne_zero.mpr (hk j hjk)
    rw [Matrix.smul_mul, mul_add, mul_sub, hA.eigenprojector₀_mul, Matrix.mul_smul, mul_one,
      hA.eigenprojector₀_mul_of_ne hjk, add_zero, ← sub_smul, smul_smul]
    have hinv : (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) *
        ((hA.eigenvalues₀ j : 𝕜) - (hA.eigenvalues₀ k : 𝕜)) = 1 := by
      exact_mod_cast inv_mul_cancel₀ hne
    rw [hinv, one_smul]
  rw [reducedResolventPlusProj, add_mul, hterm_k, Matrix.sum_mul,
    Finset.sum_congr rfl hterm_j, Finset.add_sum_erase _ _ (Finset.mem_univ k),
    hA.sum_eigenprojector₀]

private theorem fderiv_eigNormMap_comp_inr {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜) =
      mulVecRightCLM (A - (hA.eigenvalues₀ k : 𝕜) • 1 + hA.eigenprojector₀ k) := by
  ext y i
  simp [fderiv_eigNormMap_self hA k]

private theorem comp_reducedResolventPlusProj_id {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    ((fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
        ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)).comp
      (mulVecRightCLM (reducedResolventPlusProj hA k)) = .id 𝕜 (n → 𝕜)) ∧
      ((mulVecRightCLM (reducedResolventPlusProj hA k)).comp
        (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
          ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)) = .id 𝕜 (n → 𝕜)) := by
  rw [fderiv_eigNormMap_comp_inr hA k]
  constructor <;>
    · ext y i
      simp only [ContinuousLinearMap.comp_apply, mulVecRightCLM_apply, mulVec_mulVec,
        mul_reducedResolventPlusProj hA hk, reducedResolventPlusProj_mul hA hk, one_mulVec,
        ContinuousLinearMap.id_apply]

private theorem isInvertible_fderiv_eigNormMap_inr {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
      ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (comp_reducedResolventPlusProj_id hA hk).1 (comp_reducedResolventPlusProj_id hA hk).2

/-- Local real-analytic perturbation `w(B)` of the `k`-th eigenvector around `A`. -/
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
  have hev := ContDiffAt.eventually_apply_implicitFunction
    ((contDiff_eigNormMap hA k (m := ω)).contDiffAt (x := (A, 0)))
    (by decide) (isInvertible_fderiv_eigNormMap_inr hA hk)
  simpa only [localEigPerturb, eigNormMap_self] using hev

private theorem hasStrictFDerivAt_localEigPerturb {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    HasStrictFDerivAt (localEigPerturb hA hk)
      (∑ j ∈ Finset.univ.erase k,
        (((hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ : ℝ) : 𝕜) •
          (mulVecRightCLM (hA.eigenprojector₀ j)).comp
            (mulVecLeftCLM ⇑(hA.eigenvectorBasis₀ k))) A := by
  have hraw : HasStrictFDerivAt (localEigPerturb hA hk) _ A :=
    ContDiffAt.hasStrictFDerivAt_implicitFunction
      ((contDiff_eigNormMap hA k (m := ω)).contDiffAt (x := (A, 0)))
      (by decide) (isInvertible_fderiv_eigNormMap_inr hA hk)
  have hinv_eq : (fderiv 𝕜 (eigNormMap hA k) (A, 0) ∘L
      ContinuousLinearMap.inr 𝕜 (Matrix n n 𝕜) (n → 𝕜)).inverse =
      mulVecRightCLM (reducedResolventPlusProj hA k) :=
    ContinuousLinearMap.inverse_eq
      (comp_reducedResolventPlusProj_id hA hk).1 (comp_reducedResolventPlusProj_id hA hk).2
  refine hraw.congr_fderiv ?_
  ext H i
  rw [hinv_eq]
  simp only [neg_apply, ContinuousLinearMap.comp_apply, sum_apply, smul_apply,
    fderiv_eigNormMap_self hA k, add_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', mulVecRightCLM_apply,
    mulVecLeftCLM_apply, mulVec_zero, add_zero]
  have hRproj : reducedResolventPlusProj hA k * (1 - hA.eigenprojector₀ k) =
      ∑ j ∈ Finset.univ.erase k,
        (((hA.eigenvalues₀ j - hA.eigenvalues₀ k)⁻¹ : ℝ) : 𝕜) • hA.eigenprojector₀ j := by
    rw [reducedResolventPlusProj, add_mul, mul_sub, mul_one, hA.eigenprojector₀_mul_self,
      sub_self, zero_add, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    rw [Matrix.smul_mul, mul_sub, mul_one, hA.eigenprojector₀_mul_of_ne hjk, sub_zero]
  have hvec : -(reducedResolventPlusProj hA k *ᵥ
      ((1 - hA.eigenprojector₀ k) *ᵥ (H *ᵥ ⇑(hA.eigenvectorBasis₀ k)))) =
      ∑ j ∈ Finset.univ.erase k,
        (((hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ : ℝ) : 𝕜) •
          (hA.eigenprojector₀ j *ᵥ (H *ᵥ ⇑(hA.eigenvectorBasis₀ k))) := by
    rw [mulVec_mulVec, hRproj, sum_mulVec, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [smul_mulVec, ← neg_smul]
    congr 1
    push_cast
    rw [← inv_neg, neg_sub]
  simpa [Finset.sum_apply] using congrFun hvec i

/-- Any nonzero vector solving `X *ᵥ v = β • v` for a Hermitian matrix `X` has `β` equal to one of
the sorted eigenvalues of `X`. -/
private theorem exists_eigenvalues₀_eq_of_mulVec {X : Matrix n n 𝕜} (hX : X.IsHermitian)
    {v : n → 𝕜} (hv_ne : v ≠ 0) {β : 𝕜} (hv : X *ᵥ v = β • v) :
    ∃ m : Fin (Fintype.card n), β = (hX.eigenvalues₀ m : 𝕜) := by
  have hsum := hX.sum_dotProduct_smul_eigenvectorBasis₀ v
  have hex : ∃ m : Fin (Fintype.card n), star ⇑(hX.eigenvectorBasis₀ m) ⬝ᵥ v ≠ 0 := by
    by_contra! hall
    apply hv_ne
    rw [← hsum]
    simp [hall]
  obtain ⟨m, hm⟩ := hex
  refine ⟨m, ?_⟩
  have h1 : (hX.eigenvalues₀ m : 𝕜) * (star ⇑(hX.eigenvectorBasis₀ m) ⬝ᵥ v) =
      β * (star ⇑(hX.eigenvectorBasis₀ m) ⬝ᵥ v) := by
    calc
      (hX.eigenvalues₀ m : 𝕜) * (star ⇑(hX.eigenvectorBasis₀ m) ⬝ᵥ v)
          = ((hX.eigenvalues₀ m : 𝕜) • star ⇑(hX.eigenvectorBasis₀ m)) ⬝ᵥ v := by
            rw [smul_dotProduct, smul_eq_mul]
      _ = (star ⇑(hX.eigenvectorBasis₀ m) ᵥ* X) ⬝ᵥ v := by
            rw [hX.star_eigenvectorBasis₀_vecMul]
      _ = star ⇑(hX.eigenvectorBasis₀ m) ⬝ᵥ (X *ᵥ v) := (dotProduct_mulVec _ _ _).symm
      _ = β * (star ⇑(hX.eigenvectorBasis₀ m) ⬝ᵥ v) := by
            rw [hv, dotProduct_smul, smul_eq_mul]
  exact mul_right_cancel₀ hm h1.symm

private theorem eventually_localEigRayleigh_ne {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k) :
    ∀ᶠ X : selfAdjoint (Matrix n n 𝕜) in 𝓝 A,
      ∀ j : Fin (Fintype.card n), j ≠ k →
        RCLike.re (star ⇑(A.2.isHermitian.eigenvectorBasis₀ k) ⬝ᵥ
          (X.1 *ᵥ (⇑(A.2.isHermitian.eigenvectorBasis₀ k) +
            localEigPerturb A.2.isHermitian hk X.1))) ≠
          X.2.isHermitian.eigenvalues₀ j := by
  set hA := A.2.isHermitian
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set v : selfAdjoint (Matrix n n 𝕜) → (n → 𝕜) := fun X ↦ u₀ + localEigPerturb hA hk X.1
  set α : selfAdjoint (Matrix n n 𝕜) → ℝ := fun X ↦ reDotProductStarCLM u₀ (X.1 *ᵥ v X)
  have hw_cont : ContinuousAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦ localEigPerturb hA hk X.1) A :=
    ((contDiffAt_localEigPerturb hA hk).continuousAt).comp continuous_subtype_val.continuousAt
  have hα_cont : ContinuousAt α A :=
    (reDotProductStarCLM u₀).continuous.continuousAt.comp
      ((contDiff_mulVec_uncurry (𝕜 := 𝕜) (n := n) (m := ω)).continuous.continuousAt.comp
        (continuous_subtype_val.continuousAt.prodMk (continuousAt_const.add hw_cont)))
  have hαA : α A = hA.eigenvalues₀ k := by
    simp [α, v, u₀, localEigPerturb_self hA hk, hA.mulVec_eigenvectorBasis₀_coe,
      dotProduct_smul, RCLike.real_smul_eq_coe_mul]
  refine Filter.eventually_all.mpr fun j ↦ ?_
  by_cases hjk : j = k
  · exact Filter.Eventually.of_forall fun _ h ↦ (h hjk).elim
  · have hj_cont : ContinuousAt
        (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ j) A :=
      ((continuous_apply j).comp continuous_selfAdjoint_eigenvalues₀).continuousAt
    have hdiff_ne : α A - hA.eigenvalues₀ j ≠ 0 := sub_ne_zero.mpr (hαA.symm ▸ (hk j hjk).symm)
    exact ((hα_cont.sub hj_cont).eventually_ne hdiff_ne).mono fun X hX _ ↦
      sub_ne_zero.mp (by simpa only [Pi.sub_apply, α, v, u₀, reDotProductStarCLM_apply] using hX)

/-- On a neighborhood of `A` in `selfAdjoint (Matrix n n 𝕜)`, the `k`-th spectral projector agrees
with `TauCeti.rankOneHermitianProjector (u₀ + localEigPerturb X)`. -/
private theorem eventuallyEq_eigenprojector₀_rankOne {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k) :
    (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k) =ᶠ[𝓝 A]
      fun X : selfAdjoint (Matrix n n 𝕜) ↦
        TauCeti.rankOneHermitianProjector
          (⇑(A.2.isHermitian.eigenvectorBasis₀ k) + localEigPerturb A.2.isHermitian hk X.1) := by
  set hA := A.2.isHermitian
  set u₀ : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  set v : selfAdjoint (Matrix n n 𝕜) → (n → 𝕜) := fun X ↦ u₀ + localEigPerturb hA hk X.1
  have hev_simple : ∀ᶠ X : selfAdjoint (Matrix n n 𝕜) in 𝓝 A,
      ∀ j ≠ k, X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k :=
    (isOpen_setOf_forall_eigenvalues₀_ne k).mem_nhds hk
  have hev_G : ∀ᶠ X : selfAdjoint (Matrix n n 𝕜) in 𝓝 A,
      eigNormMap hA k (X.1, localEigPerturb hA hk X.1) = 0 :=
    continuous_subtype_val.continuousAt.eventually (eventually_eigNormMap_localEigPerturb hA hk)
  filter_upwards [hev_G, eventually_localEigRayleigh_ne hk, hev_simple] with X hG hgap hsimple
  obtain ⟨hw_orth, heig⟩ := eigNormMap_eq_zero_imp hA k hG
  have hv_ne : v X ≠ 0 := by
    intro hv0
    have h1 : star u₀ ⬝ᵥ v X = 1 := by simp [v, u₀, dotProduct_add, hw_orth]
    simp [hv0] at h1
  obtain ⟨m, hm⟩ := exists_eigenvalues₀_eq_of_mulVec X.2.isHermitian hv_ne heig
  have hmk : m = k := by
    by_contra hmk
    exact hgap m hmk (by simpa [v, u₀] using congrArg RCLike.re hm)
  subst hmk
  rw [hm] at heig
  exact X.2.isHermitian.eigenprojector₀_eq_rankOneHermitianProjector_of_mulVec hsimple hv_ne heig

end ImplicitBranch

/-! ### Smoothness and Hadamard variation theorems -/

section SmoothAndVariation

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **Analyticity and smoothness of simple spectral projectors.** At any self-adjoint matrix `A`
whose `k`-th sorted eigenvalue is simple, `X ↦ X.2.isHermitian.eigenprojector₀ k` is `C^m` over `ℝ`
for every `m : ℕ∞ω` (including `∞` and `ω`). -/
theorem contDiffAt_eigenprojector₀ {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k)
    {m : ℕ∞ω} :
    ContDiffAt ℝ m (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k) A := by
  have hu_ne : ⇑(A.2.isHermitian.eigenvectorBasis₀ k) +
      localEigPerturb A.2.isHermitian hk A.1 ≠ 0 := by
    rw [localEigPerturb_self A.2.isHermitian hk, add_zero]
    intro h0
    have h1 := A.2.isHermitian.dotProduct_star_eigenvectorBasis₀_self k
    simp [h0] at h1
  have hw_real : ContDiffAt ℝ ω (localEigPerturb A.2.isHermitian hk) A.1 :=
    (contDiffAt_localEigPerturb A.2.isHermitian hk).restrict_scalars ℝ
  have hv_smooth : ContDiffAt ℝ ω (fun X : selfAdjoint (Matrix n n 𝕜) ↦
      ⇑(A.2.isHermitian.eigenvectorBasis₀ k) + localEigPerturb A.2.isHermitian hk X.1) A :=
    contDiffAt_const.add (hw_real.comp A (selfAdjoint.contDiff_subtype_val ℝ).contDiffAt)
  have hcomp : ContDiffAt ℝ ω (fun X : selfAdjoint (Matrix n n 𝕜) ↦
      TauCeti.rankOneHermitianProjector
        (⇑(A.2.isHermitian.eigenvectorBasis₀ k) + localEigPerturb A.2.isHermitian hk X.1)) A :=
    (TauCeti.contDiffAt_rankOneHermitianProjector hu_ne).comp A hv_smooth
  exact (hcomp.congr_of_eventuallyEq (eventuallyEq_eigenprojector₀_rankOne hk)).of_le le_top

/-- **Analyticity and smoothness of simple sorted eigenvalues.** At any self-adjoint matrix `A`
whose `k`-th sorted eigenvalue is simple, `X ↦ X.2.isHermitian.eigenvalues₀ k` is `C^m` over `ℝ`
for every `m : ℕ∞ω` (including `∞` and `ω`). -/
theorem contDiffAt_eigenvalues₀ {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k)
    {m : ℕ∞ω} :
    ContDiffAt ℝ m (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) A := by
  have hfn : (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) =
      fun X ↦ RCLike.reCLM (traceCLM 𝕜 n (X.2.isHermitian.eigenprojector₀ k * X.1)) := by
    ext X
    simp
  rw [hfn]
  have hmul : ContDiffAt ℝ m
      (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k * X.1) A :=
    (contDiffAt_eigenprojector₀ hk).mul (selfAdjoint.contDiff_subtype_val ℝ).contDiffAt
  exact ((RCLike.reCLM.comp ((traceCLM 𝕜 n).restrictScalars ℝ)).contDiff (n := m)).contDiffAt.comp
    A hmul

/-- On the open Weyl chamber of self-adjoint matrices with strictly decreasing eigenvalues, each
spectral projector `X ↦ X.2.isHermitian.eigenprojector₀ k` is `C^m` over `ℝ` for every `m : ℕ∞ω`. -/
theorem contDiffOn_eigenprojector₀_strictAnti (k : Fin (Fintype.card n)) {m : ℕ∞ω} :
    ContDiffOn ℝ m (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenprojector₀ k)
      {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.2.isHermitian.eigenvalues₀} :=
  fun _ hX ↦ (contDiffAt_eigenprojector₀ fun _ hjk ↦ hX.injective.ne hjk).contDiffWithinAt

/-- On the open Weyl chamber of self-adjoint matrices with strictly decreasing eigenvalues, each
sorted eigenvalue `X ↦ X.2.isHermitian.eigenvalues₀ k` is `C^m` over `ℝ` for every `m : ℕ∞ω`. -/
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
      ∑ j ∈ Finset.univ.erase k,
        (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
          (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j +
            hA.eigenprojector₀ j * B * hA.eigenprojector₀ k) := by
  intro u₀ dy
  have horth : star u₀ ⬝ᵥ dy = 0 := by
    rw [dotProduct_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    rw [dotProduct_smul, hA.eigenprojector₀_mulVec, dotProduct_smul,
      hA.dotProduct_star_eigenvectorBasis₀_of_ne hjk.symm, smul_zero, smul_zero]
  have hterm : ∀ j ∈ Finset.univ.erase k,
      vecMulVec (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀)) (star u₀) +
        vecMulVec u₀ (star (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀))) =
      hA.eigenprojector₀ k * B * hA.eigenprojector₀ j +
        hA.eigenprojector₀ j * B * hA.eigenprojector₀ k := by
    intro j _
    have h1 : vecMulVec (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀)) (star u₀) =
        hA.eigenprojector₀ j * B * hA.eigenprojector₀ k := by
      dsimp only [u₀]
      rw [hA.eigenprojector₀_def k, mulVec_mulVec, ← mul_vecMulVec]
    have h2 : vecMulVec u₀ (star (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀))) =
        hA.eigenprojector₀ k * B * hA.eigenprojector₀ j := by
      have hc := congrArg Matrix.conjTranspose h1
      simpa [conjTranspose_vecMulVec, star_star, conjTranspose_mul, Matrix.mul_assoc,
        hB.eq, (hA.isHermitian_eigenprojector₀ j).eq,
        (hA.isHermitian_eigenprojector₀ k).eq] using hc
    rw [h1, h2, add_comm]
  rw [horth, RCLike.zero_re, mul_zero, zero_smul, sub_zero]
  have hlhs : vecMulVec dy (star u₀) + vecMulVec u₀ (star dy) =
      ∑ j ∈ Finset.univ.erase k,
        (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
          (vecMulVec (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀)) (star u₀) +
            vecMulVec u₀ (star (hA.eigenprojector₀ j *ᵥ (B *ᵥ u₀)))) := by
    ext a b
    simp [dy, vecMulVec_apply, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
      RCLike.real_smul_eq_coe_smul (K := 𝕜), mul_assoc, mul_left_comm]
  rw [hlhs]
  exact Finset.sum_congr rfl fun j hj ↦ by rw [hterm j hj]

/-- **Hadamard's first variation of a simple spectral projector** (strict Fréchet derivative on
`selfAdjoint (Matrix n n 𝕜)`). -/
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
  have hproj_deriv := (hasStrictFDerivAt_rankOneHermitianProjector_unit hu_unit).comp A hv_deriv
  refine (hproj_deriv.congr_of_eventuallyEq (eventuallyEq_eigenprojector₀_rankOne hk).symm)
    |>.congr_fderiv ?_
  ext B : 1
  simp only [localEigPerturb_self A.2.isHermitian hk, add_zero, ContinuousLinearMap.comp_apply,
    sub_apply, add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, sum_apply,
    ContinuousLinearMap.coe_restrictScalars', selfAdjoint.subtypeL_apply, vecMulVecLeftCLM_apply,
    vecMulVecRightStarCLM_apply, reDotProductStarCLM_apply, mulVecRightCLM_apply,
    mulVecLeftCLM_apply, ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul]
  exact rankOneProjector_deriv_sum_eq A.2.isHermitian B.2.isHermitian k

/-- Applied Fréchet derivative of `X ↦ X.2.isHermitian.eigenprojector₀ k` at a simple sorted
eigenvalue. -/
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
              A.2.isHermitian.eigenprojector₀ k) := by
  have hf := (hasStrictFDerivAt_eigenprojector₀ hk).hasFDerivAt.fderiv
  exact (congrFun (congrArg DFunLike.coe hf) B).trans (by simp)

/-- **Hadamard's first variation of a simple sorted eigenvalue** (Hellmann–Feynman theorem as a
strict Fréchet derivative on `selfAdjoint (Matrix n n 𝕜)`). -/
theorem hasStrictFDerivAt_eigenvalues₀ {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k) :
    HasStrictFDerivAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k)
      (RCLike.reCLM.comp (((traceCLM 𝕜 n).restrictScalars ℝ).comp
        ((ContinuousLinearMap.mul ℝ (Matrix n n 𝕜) (A.2.isHermitian.eigenprojector₀ k)).comp
          (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜))))) A := by
  have hfn : (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) =
      fun X ↦ RCLike.reCLM (traceCLM 𝕜 n (X.2.isHermitian.eigenprojector₀ k * X.1)) := by
    ext X
    simp
  rw [hfn]
  have hP := hasStrictFDerivAt_eigenprojector₀ hk
  have hX : HasStrictFDerivAt (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.1)
      (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)) A :=
    (selfAdjoint.subtypeL ℝ (Matrix n n 𝕜)).hasStrictFDerivAt
  have hraw := (RCLike.reCLM.comp ((traceCLM 𝕜 n).restrictScalars ℝ)).hasStrictFDerivAt.comp A
    (hP.fun_mul' hX)
  refine hraw.congr_fderiv ?_
  ext B
  set hA := A.2.isHermitian
  have hdPA : ((∑ j ∈ Finset.univ.erase k,
      (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
        (hA.eigenprojector₀ k * B.1 * hA.eigenprojector₀ j +
          hA.eigenprojector₀ j * B.1 * hA.eigenprojector₀ k)) * A.1).trace = 0 := by
    rw [Matrix.sum_mul, trace_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    rw [Matrix.smul_mul, trace_smul, add_mul, trace_add, Matrix.mul_assoc _ (hA.eigenprojector₀ j),
      hA.eigenprojector₀_mul j, Matrix.mul_smul, trace_smul,
      trace_mul_comm (hA.eigenprojector₀ k * B.1), ← Matrix.mul_assoc,
      hA.eigenprojector₀_mul_of_ne hjk, zero_mul, trace_zero, smul_zero, zero_add,
      Matrix.mul_assoc _ (hA.eigenprojector₀ k), hA.eigenprojector₀_mul k, Matrix.mul_smul,
      trace_smul, trace_mul_comm (hA.eigenprojector₀ j * B.1), ← Matrix.mul_assoc,
      hA.eigenprojector₀_mul_of_ne hjk.symm, zero_mul, trace_zero, smul_zero, smul_zero]
  simp only [ContinuousLinearMap.comp_apply, add_apply, sum_apply, smul_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.mul_apply',
    selfAdjoint.subtypeL_apply, ContinuousLinearMap.coe_restrictScalars', traceCLM_apply,
    RCLike.reCLM_apply]
  -- Identify the product-rule derivative `Pₖ * B + (dPₖ[B]) * A` and kill the `(dPₖ[B]) * A` trace.
  change RCLike.re (hA.eigenprojector₀ k * B.1 + _ * A.1).trace =
    RCLike.re (hA.eigenprojector₀ k * B.1).trace
  rw [trace_add, hdPA, add_zero]

/-- Applied Fréchet derivative of `X ↦ X.2.isHermitian.eigenvalues₀ k` at a simple sorted
eigenvalue. -/
theorem fderiv_eigenvalues₀_apply {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k)
    (B : selfAdjoint (Matrix n n 𝕜)) :
    fderiv ℝ (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) A B =
      RCLike.re (A.2.isHermitian.eigenprojector₀ k * (B : Matrix n n 𝕜)).trace := by
  have hf := (hasStrictFDerivAt_eigenvalues₀ hk).hasFDerivAt.fderiv
  exact (congrFun (congrArg DFunLike.coe hf) B).trans (by simp)

/-- **Hadamard's second variation of a simple sorted eigenvalue** (strict Fréchet derivative of
`X ↦ fderiv ℝ (eigenvalues₀ k) X C` on `selfAdjoint (Matrix n n 𝕜)`). -/
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
  have hraw := (hlin.hasStrictFDerivAt.comp A (hasStrictFDerivAt_eigenprojector₀ hk))
    |>.congr_of_eventuallyEq hev.symm
  refine hraw.congr_fderiv ?_
  ext B
  set hA := A.2.isHermitian
  have hsymm_tr : ∀ j : Fin (Fintype.card n),
      RCLike.re (hA.eigenprojector₀ j * B.1 * hA.eigenprojector₀ k * C.1).trace =
        RCLike.re (hA.eigenprojector₀ k * B.1 * hA.eigenprojector₀ j * C.1).trace := by
    intro j
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

/-- Applied second Fréchet derivative of `X ↦ X.2.isHermitian.eigenvalues₀ k` at a simple sorted
eigenvalue. -/
theorem fderiv_fderiv_eigenvalues₀_apply {A : selfAdjoint (Matrix n n 𝕜)}
    {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, A.2.isHermitian.eigenvalues₀ j ≠ A.2.isHermitian.eigenvalues₀ k)
    (B C : selfAdjoint (Matrix n n 𝕜)) :
    fderiv ℝ (fun X : selfAdjoint (Matrix n n 𝕜) ↦
        fderiv ℝ (fun Y : selfAdjoint (Matrix n n 𝕜) ↦ Y.2.isHermitian.eigenvalues₀ k) X C) A B =
      2 * ∑ j ∈ Finset.univ.erase k,
        (A.2.isHermitian.eigenvalues₀ k - A.2.isHermitian.eigenvalues₀ j)⁻¹ *
          RCLike.re (A.2.isHermitian.eigenprojector₀ k * (B : Matrix n n 𝕜) *
            A.2.isHermitian.eigenprojector₀ j * (C : Matrix n n 𝕜)).trace := by
  have hf := (hasStrictFDerivAt_fderiv_eigenvalues₀ hk C).hasFDerivAt.fderiv
  exact (congrFun (congrArg DFunLike.coe hf) B).trans (by simp)

/-! ### Directional first and second derivatives along `t ↦ A + t • B` -/

namespace IsHermitian

private theorem eigenvalues₀_congr {M₁ M₂ : Matrix n n 𝕜}
    (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian) (h : M₁ = M₂) (k : Fin (Fintype.card n)) :
    h₁.eigenvalues₀ k = h₂.eigenvalues₀ k := by
  subst h; rfl

private theorem eigenprojector₀_congr {M₁ M₂ : Matrix n n 𝕜}
    (h₁ : M₁.IsHermitian) (h₂ : M₂.IsHermitian) (h : M₁ = M₂) (k : Fin (Fintype.card n)) :
    h₁.eigenprojector₀ k = h₂.eigenprojector₀ k := by
  subst h; rfl

/-- Directional derivative of `t ↦ (A + t • B).eigenprojector₀ k` at `t = 0` when `λₖ(A)` is
simple. -/
theorem hasDerivAt_add_smul_eigenprojector₀ {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    HasDerivAt (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenprojector₀ k)
      (∑ j ∈ Finset.univ.erase k,
        (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ •
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
  have hA0 : A' + (0 : ℝ) • B' = A' := by simp
  have hf := (congrArg (HasFDerivAt _ _) hA0.symm).mp
    (hasStrictFDerivAt_eigenprojector₀ (A := A') hk).hasFDerivAt
  refine (hf.comp_hasDerivAt 0 hline).congr_deriv ?_
  dsimp only [A', B']
  simp [smul_add]

/-- Directional derivative of `t ↦ (A + t • B).eigenvalues₀ k` at `t = 0` when `λₖ(A)` is
simple. -/
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
  have hA0 : A' + (0 : ℝ) • B' = A' := by simp
  have hf := (congrArg (HasFDerivAt _ _) hA0.symm).mp
    (hasStrictFDerivAt_eigenvalues₀ (A := A') hk).hasFDerivAt
  refine (hf.comp_hasDerivAt 0 hline).congr_deriv ?_
  dsimp only [A', B']
  simp

/-- **Hadamard's second directional variation** (projector-trace form) of `t ↦ λₖ(A + t • B)` at
`t = 0` when `λₖ(A)` is simple. -/
theorem iteratedDeriv_two_add_smul_eigenvalues₀ {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    iteratedDeriv 2 (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k) 0 =
      2 * ∑ j ∈ Finset.univ.erase k,
        (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ *
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
    have hγ0 : γ 0 = A' := by simp [γ]
    exact hγ_cont.continuousAt.eventually (hγ0.symm ▸
      (isOpen_setOf_forall_eigenvalues₀_ne k).mem_nhds hmem)
  have hderiv_ev : deriv ((fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀ k) ∘
      γ) =ᶠ[𝓝 0]
      fun t : ℝ ↦ fderiv ℝ (fun Y : selfAdjoint (Matrix n n 𝕜) ↦ Y.2.isHermitian.eigenvalues₀ k)
        (γ t) B' := by
    filter_upwards [hopen] with t ht
    have hline_t : HasDerivAt γ B' t := by
      simpa [γ] using ((hasDerivAt_id t).smul_const B').const_add A'
    have hf_t := (hasStrictFDerivAt_eigenvalues₀ (A := γ t) ht).hasFDerivAt
    exact (hf_t.comp_hasDerivAt t hline_t).deriv.trans (by rw [hf_t.fderiv])
  have hline0 : HasDerivAt γ B' 0 := by
    simpa [γ] using ((hasDerivAt_id (0 : ℝ)).smul_const B').const_add A'
  have hγ0 : γ 0 = A' := by simp [γ]
  have hf2 := (congrArg (HasFDerivAt _ _) hγ0.symm).mp
    (hasStrictFDerivAt_fderiv_eigenvalues₀ (A := A') hk B').hasFDerivAt
  have h2 := (hf2.comp_hasDerivAt 0 hline0).congr_of_eventuallyEq hderiv_ev
  have h2_eq : (2 : ℕ) = 1 + 1 := rfl
  rw [h2_eq, iteratedDeriv_succ (𝕜 := ℝ), iteratedDeriv_one (𝕜 := ℝ), h2.deriv]
  dsimp only [A', B']
  simp

/-- **Hadamard's second directional variation** (eigenvector matrix-element form, Anderson–Guionnet–
Zeitouni Lemma 4.3.4): at a simple sorted eigenvalue `λₖ(A)`,
`(d²/dt²)|₀ λₖ(A + t • B) = 2 * ∑ j ≠ k, (λₖ(A) - λⱼ(A))⁻¹ * ‖uⱼ* B uₖ‖²`. -/
theorem iteratedDeriv_two_add_smul_eigenvalues₀_eq_sum_norm_sq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {k : Fin (Fintype.card n)}
    (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    iteratedDeriv 2 (fun t : ℝ ↦ (hA.add (hB.smul (IsSelfAdjoint.all t))).eigenvalues₀ k) 0 =
      2 * ∑ j ∈ Finset.univ.erase k,
        (hA.eigenvalues₀ k - hA.eigenvalues₀ j)⁻¹ *
          ‖star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ k))‖ ^ 2 := by
  rw [hA.iteratedDeriv_two_add_smul_eigenvalues₀ hB hk]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
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
