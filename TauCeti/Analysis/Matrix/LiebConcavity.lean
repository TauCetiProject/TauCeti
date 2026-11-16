/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
public import TauCeti.Analysis.Matrix.Entropy
public import TauCeti.Analysis.Matrix.Exponential.Log
public import TauCeti.Analysis.Matrix.RCLike
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.Matrix.Exponential.Block
import TauCeti.Analysis.Matrix.PosDef
import TauCeti.Analysis.Matrix.StrongSubadditivity
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
import TauCeti.LinearAlgebra.Matrix.Trace.Basic
import TauCeti.Topology.Instances.Matrix

/-!
# Joint convexity of relative entropy and Lieb's concavity theorem

For a fixed Hermitian matrix `H` over `𝕜 = ℝ` or `ℂ`, **Lieb's concavity theorem** asserts that the
functional

`A ↦ re Tr exp (H + cfc Real.log A)`

is concave on the cone `{A : Matrix n n 𝕜 | A.PosDef}` of positive definite matrices. This file
proves Lieb's theorem from the monotonicity of the Umegaki relative entropy under partial traces
(`Matrix.PosDef.relativeEntropy_partialTraceRight_le`), together with the Loewner monotonicity and
operator exponential estimates needed to turn Lieb's theorem into matrix Laplace-transform bounds.

## Proof outline

1. **Spectral and exponential trace monotonicity.** Courant–Fischer monotonicity of sorted
   eigenvalues (`LinearMap.IsSymmetric.eigenvalue_mono`) gives
   `hA.eigenvalues i ≤ hB.eigenvalues i` whenever `A ≤ B` (`Matrix.IsHermitian.eigenvalues_mono`),
   hence `re Tr (cfc f A) ≤ re Tr (cfc f B)` for every monotone `f : ℝ → ℝ` and in particular
   `re Tr (exp A) ≤ re Tr (exp B)`.
2. **Joint convexity of Umegaki relative entropy.** Applying partial-trace monotonicity over `ℂ` to
   the two-block diagonal matrices `fromBlocks (a • ρ₁) 0 0 (b • ρ₂)` and
   `fromBlocks (a • σ₁) 0 0 (b • σ₂)`, reindexed along `n ⊕ n ≃ n × Fin 2`, yields
   `D(a • ρ₁ + b • ρ₂ ‖ a • σ₁ + b • σ₂) ≤ a D(ρ₁ ‖ σ₁) + b D(ρ₂ ‖ σ₂)` for positive definite
   arguments; `Matrix.toComplexStarAlgHom` transfers the inequality to any `RCLike` field.
3. **Gibbs variational principle and Lieb's theorem.** Klein's inequality applied to `X` and
   `Y = exp (H + cfc Real.log A)` gives
   `re Tr X + re Tr (X * H) - D(X ‖ A) ≤ re Tr exp (H + cfc Real.log A)`, with equality at `X = Y`.
   Evaluating at the optimizers `X₁`, `X₂` for `A₁`, `A₂` and testing the variational bound at the
   convex combination `a • X₁ + b • X₂` against joint convexity of `D` proves concavity of
   `A ↦ re Tr exp (H + cfc Real.log A)`.

We also record the operator exponential inequalities `1 + A ≤ exp A` and Bernstein's operator bound
`exp (θ • A) ≤ 1 + θ • A + (θ² / (2 (1 - θ L / 3))) • A²` for Hermitian `A` with eigenvalues at
most `L`.

## Main results

* `Matrix.IsHermitian.eigenvalues₀_mono`, `Matrix.IsHermitian.eigenvalues_mono`,
  `Matrix.IsHermitian.re_trace_cfc_mono`, `Matrix.IsHermitian.re_trace_exp_le_of_le`: Loewner
  monotonicity of eigenvalues, monotone functional-calculus traces, and exponential traces.
* `Matrix.PosDef.re_trace_mul_cfc_log_sub_cfc_log_smul_add_smul_le`,
  `Matrix.PosDef.relativeEntropy_smul_add_smul_le`: joint convexity of the Umegaki relative entropy
  on positive definite matrices.
* `Matrix.PosDef.re_trace_add_re_trace_mul_sub_le_re_trace_exp_add_cfc_log`: the Gibbs variational
  inequality.
* `Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`,
  `Matrix.IsHermitian.sum_mul_re_trace_exp_add_cfc_log_le`: Lieb's concavity theorem and its finite
  Jensen form.
* `Matrix.IsHermitian.one_add_le_exp`, `Matrix.IsHermitian.exp_smul_le_one_add_smul_add_sq`:
  first-order lower bound and Bernstein second-order upper bound for the Hermitian matrix
  exponential.

## References

* E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson conjecture*, Adv. Math. **11**
  (1973), 267–288, Theorem 6.
* D. Petz, *Quasi-entropies for finite quantum systems*, Rep. Math. Phys. **23** (1986), 57–65.
* E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, Contemporary
  Mathematics **529** (2010), §4.1.
* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. **12**
  (2012), 389–434, Theorem 3.2 and Lemma 6.2.
* J. A. Tropp, *An introduction to matrix concentration inequalities*, Found. Trends Mach. Learn.
  **8** (2015), §8.3.
-/

public section

noncomputable section

open NormedSpace Topology
open scoped ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-! ### Spectral monotonicity and operator exponential inequalities -/

/-- For a Hermitian matrix `A`, the continuous functional calculus `cfc Real.exp A` agrees with the
matrix exponential `NormedSpace.exp A`. -/
theorem IsHermitian.cfc_exp_eq_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    cfc Real.exp A = NormedSpace.exp A := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  exact CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint

/-- The trace of the exponential of a Hermitian matrix is the sum of the exponentials of its
eigenvalues. -/
theorem IsHermitian.trace_exp_eq_sum_exp_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (NormedSpace.exp A).trace = ∑ i, (Real.exp (hA.eigenvalues i) : 𝕜) := by
  rw [← hA.cfc_exp_eq_exp, hA.trace_cfc]

/-- **Loewner monotonicity of sorted eigenvalues.** If `A ≤ B` for Hermitian matrices `A` and `B`,
then `hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k` for every `k`. -/
theorem IsHermitian.eigenvalues₀_mono {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A ≤ B) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  refine (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalue_mono
    (isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace (fun x ↦ ?_) k
  have hpos := (isPositive_toEuclideanLin_iff.2 (le_iff.mp hAB)).re_inner_nonneg_left x
  rwa [map_sub, LinearMap.sub_apply, inner_sub_left, map_sub, sub_nonneg] at hpos

/-- **Loewner monotonicity of matrix-indexed eigenvalues.** If `A ≤ B` for Hermitian matrices `A`
and `B`, then `hA.eigenvalues i ≤ hB.eigenvalues i` for every `i : n`. -/
theorem IsHermitian.eigenvalues_mono {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A ≤ B) (i : n) :
    hA.eigenvalues i ≤ hB.eigenvalues i :=
  hA.eigenvalues₀_mono hB hAB _

/-- **Trace monotonicity of monotone functional calculi.** If `A ≤ B` for Hermitian `A`, `B` and
`f : ℝ → ℝ` is monotone, then `re Tr (cfc f A) ≤ re Tr (cfc f B)`. -/
theorem IsHermitian.re_trace_cfc_mono {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A ≤ B) {f : ℝ → ℝ} (hf : Monotone f) :
    RCLike.re (cfc f A).trace ≤ RCLike.re (cfc f B).trace := by
  simp only [hA.trace_cfc, hB.trace_cfc, map_sum, RCLike.ofReal_re]
  exact Finset.sum_le_sum fun i _ ↦ hf (hA.eigenvalues_mono hB hAB i)

/-- **Loewner monotonicity of the exponential trace.** If `A ≤ B` for Hermitian `A` and `B`, then
`re Tr (exp A) ≤ re Tr (exp B)`. -/
theorem IsHermitian.re_trace_exp_le_of_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A ≤ B) :
    RCLike.re (NormedSpace.exp A).trace ≤ RCLike.re (NormedSpace.exp B).trace := by
  rw [← hA.cfc_exp_eq_exp, ← hB.cfc_exp_eq_exp]
  exact hA.re_trace_cfc_mono hB hAB Real.exp_monotone

/-- Every Hermitian matrix lies below `‖A‖ • 1` in the Loewner order, where `‖A‖` is the Euclidean
operator norm. -/
theorem IsHermitian.le_l2_opNorm_smul_one {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A ≤ ‖A‖ • 1 := by
  have h1 : cfc (fun x : ℝ ↦ x) A = A := cfc_id' ℝ A hA.isSelfAdjoint
  have h2 : cfc (fun _ : ℝ ↦ ‖A‖) A = ‖A‖ • (1 : Matrix n n 𝕜) := by
    rw [cfc_const ‖A‖ A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  conv_lhs => rw [← h1]
  rw [← h2]
  refine cfc_mono (hf := A.finite_real_spectrum.continuousOn _)
    (hg := A.finite_real_spectrum.continuousOn _) fun x hx ↦ ?_
  obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  exact (le_abs_self _).trans
    ((norm_le_pi_norm hA.eigenvalues i).trans_eq hA.l2_opNorm_eq_norm_eigenvalues.symm)

/-- For any Hermitian matrix `A`, `1 + A ≤ exp A` in the Loewner order. -/
theorem IsHermitian.one_add_le_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    1 + A ≤ NormedSpace.exp A := by
  have hlin : cfc (fun x : ℝ ↦ 1 + x) A = 1 + A := by
    rw [cfc_add A _ _ (A.finite_real_spectrum.continuousOn _)
        (A.finite_real_spectrum.continuousOn _),
      cfc_const_one ℝ A hA.isSelfAdjoint, cfc_id' ℝ A hA.isSelfAdjoint]
  rw [← hlin, ← hA.cfc_exp_eq_exp]
  exact cfc_mono (hf := A.finite_real_spectrum.continuousOn _)
    (hg := A.finite_real_spectrum.continuousOn _) fun x _ ↦ by linarith [Real.add_one_le_exp x]

/-- **Bernstein's operator exponential bound.** For a Hermitian matrix `A` whose eigenvalues are at
most `L` (with `0 ≤ L`) and a parameter `0 ≤ θ` with `θ * L < 3`,
`exp (θ • A) ≤ 1 + θ • A + (θ² / (2 (1 - θ L / 3))) • A²`. -/
theorem IsHermitian.exp_smul_le_one_add_smul_add_sq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {θ L : ℝ} (hθ : 0 ≤ θ) (hL0 : 0 ≤ L) (hθL : θ * L < 3)
    (hspec : ∀ i, hA.eigenvalues i ≤ L) :
    NormedSpace.exp (θ • A) ≤ 1 + θ • A + (θ ^ 2 / (2 * (1 - θ * L / 3))) • A ^ 2 := by
  set g := θ ^ 2 / (2 * (1 - θ * L / 3))
  have hθA : (θ • A).IsHermitian := hA.smul (IsSelfAdjoint.all θ)
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  have hlhs : NormedSpace.exp (θ • A) = cfc (fun x : ℝ ↦ Real.exp (θ * x)) A := by
    rw [← hθA.cfc_exp_eq_exp, ← cfc_comp_smul θ Real.exp A
      ((A.finite_real_spectrum.image _).continuousOn _) hA.isSelfAdjoint]
    rfl
  have hrhs : 1 + θ • A + g • A ^ 2 = cfc (fun x : ℝ ↦ 1 + θ • x + g • x ^ 2) A := by
    rw [cfc_add A _ _ (hcont _) (hcont _), cfc_add A _ _ (hcont _) (hcont _),
      cfc_const_one ℝ A hA.isSelfAdjoint, cfc_smul θ (fun x : ℝ ↦ x) A (hcont _),
      cfc_smul g (fun x : ℝ ↦ x ^ 2) A (hcont _),
      cfc_id' ℝ A hA.isSelfAdjoint, cfc_pow_id A 2 hA.isSelfAdjoint]
  rw [hlhs, hrhs]
  refine cfc_mono (hf := hcont _) (hg := hcont _) fun x hx ↦ ?_
  obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  have h1 := Real.exp_le_one_add_add_sq_div_of_le
    (mul_le_mul_of_nonneg_left (hspec i) hθ) (mul_nonneg hθ hL0) hθL
  refine h1.trans_eq ?_
  simp only [g]
  ring

/-! ### Joint convexity of Umegaki relative entropy -/

/-- For a positive definite reference `σ`, `Matrix.toComplexStarAlgHom` preserves the Umegaki
relative entropy `D(ρ ‖ σ)`. -/
theorem PosDef.relativeEntropy_toComplexStarAlgHom {σ : Matrix n n 𝕜} (hσ : σ.PosDef)
    (ρ : Matrix n n 𝕜) :
    relativeEntropy (toComplexStarAlgHom n 𝕜 ρ) (toComplexStarAlgHom n 𝕜 σ) =
      relativeEntropy ρ σ := by
  have hσC : (toComplexStarAlgHom n 𝕜 σ).PosDef := posDef_toComplexStarAlgHom_iff.2 hσ
  rw [relativeEntropy_of_posDef hσC, relativeEntropy_of_posDef hσ]
  simp only [← toComplexStarAlgHom_cfc, ← map_sub, ← map_mul, RCLike.re_to_complex,
    re_trace_toComplexStarAlgHom]

/-- Equivalence `n ⊕ n ≃ n × Fin 2` identifying the two summands with the fibers over `0` and `1`.
Tracing out `Fin 2` on a reindexed block-diagonal matrix sums the two diagonal blocks. -/
private def sumEquivProdFinTwo (n : Type*) : n ⊕ n ≃ n × Fin 2 where
  toFun
    | Sum.inl i => (i, 0)
    | Sum.inr i => (i, 1)
  invFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  left_inv x := by rcases x with i | i <;> simp
  right_inv := by rintro ⟨i, k⟩; fin_cases k <;> simp

omit [Fintype n] [DecidableEq n] in
private theorem partialTraceRight_reindex_sumEquivProdFinTwo {R : Type*} [AddCommMonoid R]
    (M₁ M₂ : Matrix n n R) :
    (reindex (sumEquivProdFinTwo n) (sumEquivProdFinTwo n)
      (fromBlocks M₁ 0 0 M₂)).partialTraceRight = M₁ + M₂ := by
  ext i j
  rw [partialTraceRight_apply, Fin.sum_univ_two]
  rfl

omit [Fintype n] [DecidableEq n] in
private theorem posDef_fromBlocks_zero_complex [Finite n] {P Q : Matrix n n ℂ} (hP : P.PosDef)
    (hQ : Q.PosDef) : (fromBlocks P 0 0 Q).PosDef := by
  cases nonempty_fintype n
  classical
  have hLP : (cfc Real.log P).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log P)
  have hLQ : (cfc Real.log Q).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log Q)
  have hH : (fromBlocks (cfc Real.log P) 0 0 (cfc Real.log Q)).IsHermitian := by
    simp only [IsHermitian, fromBlocks_conjTranspose, conjTranspose_zero, hLP.eq, hLQ.eq]
  rw [← hP.exp_cfc_log, ← hQ.exp_cfc_log, ← exp_fromBlocks_diagonal]
  exact hH.posDef_exp

private theorem re_trace_reindex_fromBlocks_cfc_log_sub {ρ₁ ρ₂ σ₁ σ₂ : Matrix n n 𝕜}
    (hρ₁ : ρ₁.PosDef) (hρ₂ : ρ₂.PosDef) (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let φ := toComplexStarAlgHom n 𝕜
    let e := sumEquivProdFinTwo n
    let Bρ := fromBlocks (a • φ ρ₁) 0 0 (b • φ ρ₂)
    let Bσ := fromBlocks (a • φ σ₁) 0 0 (b • φ σ₂)
    RCLike.re (reindex e e Bρ *
        (cfc Real.log (reindex e e Bρ) - cfc Real.log (reindex e e Bσ))).trace =
      a * RCLike.re (ρ₁ * (cfc Real.log ρ₁ - cfc Real.log σ₁)).trace +
        b * RCLike.re (ρ₂ * (cfc Real.log ρ₂ - cfc Real.log σ₂)).trace := by
  intro φ e Bρ Bσ
  have hρ₁C : (φ ρ₁).PosDef := posDef_toComplexStarAlgHom_iff.2 hρ₁
  have hρ₂C : (φ ρ₂).PosDef := posDef_toComplexStarAlgHom_iff.2 hρ₂
  have hσ₁C : (φ σ₁).PosDef := posDef_toComplexStarAlgHom_iff.2 hσ₁
  have hσ₂C : (φ σ₂).PosDef := posDef_toComplexStarAlgHom_iff.2 hσ₂
  have hmul : reindex e e Bρ * (cfc Real.log (reindex e e Bρ) - cfc Real.log (reindex e e Bσ)) =
      reindex e e (Bρ * (cfc Real.log Bρ - cfc Real.log Bσ)) := by
    rw [cfc_reindex, cfc_reindex]
    change reindexAlgEquiv ℂ ℂ e Bρ *
        (reindexAlgEquiv ℂ ℂ e (cfc Real.log Bρ) - reindexAlgEquiv ℂ ℂ e (cfc Real.log Bσ)) =
      reindexAlgEquiv ℂ ℂ e (Bρ * (cfc Real.log Bρ - cfc Real.log Bσ))
    rw [← map_sub, ← map_mul]
  rw [hmul, trace_reindex_self e]
  dsimp only [Bρ, Bσ]
  have htr_fb (M₁ M₂ : Matrix n n ℂ) : (fromBlocks M₁ 0 0 M₂).trace = M₁.trace + M₂.trace := by
    simp [Matrix.trace]
  rw [(hρ₁C.smul ha).cfc_log_fromBlocks_diagonal (hρ₂C.smul hb),
    (hσ₁C.smul ha).cfc_log_fromBlocks_diagonal (hσ₂C.smul hb),
    sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, neg_zero, add_zero,
    ← sub_eq_add_neg, ← sub_eq_add_neg, fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, htr_fb,
    hρ₁C.cfc_log_smul ha, hσ₁C.cfc_log_smul ha, hρ₂C.cfc_log_smul hb, hσ₂C.cfc_log_smul hb,
    add_sub_add_left_eq_sub, Matrix.smul_mul, trace_smul]
  simp only [φ, ← toComplexStarAlgHom_cfc, ← map_sub, ← map_mul, RCLike.re_to_complex,
    Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, re_trace_toComplexStarAlgHom]

/-- **Joint convexity and subadditivity of relative entropy** on positive definite matrices (real
trace form). For positive definite `ρ₁, ρ₂, σ₁, σ₂` over `ℝ` or `ℂ` and nonnegative scalars `a, b`
(not necessarily summing to `1`),
`re Tr ((a ρ₁ + b ρ₂) (log (a ρ₁ + b ρ₂) - log (a σ₁ + b σ₂))) ≤
  a re Tr (ρ₁ (log ρ₁ - log σ₁)) + b re Tr (ρ₂ (log ρ₂ - log σ₂))`. -/
theorem PosDef.re_trace_mul_cfc_log_sub_cfc_log_smul_add_smul_le
    {ρ₁ ρ₂ σ₁ σ₂ : Matrix n n 𝕜} (hρ₁ : ρ₁.PosDef) (hρ₂ : ρ₂.PosDef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    RCLike.re ((a • ρ₁ + b • ρ₂) *
        (cfc Real.log (a • ρ₁ + b • ρ₂) - cfc Real.log (a • σ₁ + b • σ₂))).trace ≤
      a * RCLike.re (ρ₁ * (cfc Real.log ρ₁ - cfc Real.log σ₁)).trace +
        b * RCLike.re (ρ₂ * (cfc Real.log ρ₂ - cfc Real.log σ₂)).trace := by
  obtain rfl | ha := ha.eq_or_lt
  · obtain rfl | hb := hb.eq_or_lt
    · simp
    · simp only [zero_smul, zero_add, zero_mul, hρ₂.cfc_log_smul hb, hσ₂.cfc_log_smul hb,
        add_sub_add_left_eq_sub, smul_mul_assoc, trace_smul, RCLike.smul_re, le_rfl]
  obtain rfl | hb := hb.eq_or_lt
  · simp only [zero_smul, add_zero, zero_mul, hρ₁.cfc_log_smul ha, hσ₁.cfc_log_smul ha,
      add_sub_add_left_eq_sub, smul_mul_assoc, trace_smul, RCLike.smul_re, le_rfl]
  -- Push into complex matrices and apply Petz's partial-trace monotonicity to block diagonals.
  set φ := toComplexStarAlgHom n 𝕜
  have hρ₁C : (φ ρ₁).PosDef := posDef_toComplexStarAlgHom_iff.2 hρ₁
  have hρ₂C : (φ ρ₂).PosDef := posDef_toComplexStarAlgHom_iff.2 hρ₂
  have hσ₁C : (φ σ₁).PosDef := posDef_toComplexStarAlgHom_iff.2 hσ₁
  have hσ₂C : (φ σ₂).PosDef := posDef_toComplexStarAlgHom_iff.2 hσ₂
  set e := sumEquivProdFinTwo n
  set Bρ := fromBlocks (a • φ ρ₁) 0 0 (b • φ ρ₂)
  set Bσ := fromBlocks (a • φ σ₁) 0 0 (b • φ σ₂)
  have hR : (reindex e e Bρ).PosDef := by
    simpa only [reindex_apply] using
      (posDef_fromBlocks_zero_complex (hρ₁C.smul ha) (hρ₂C.smul hb)).submatrix e.symm.injective
  have hS : (reindex e e Bσ).PosDef := by
    simpa only [reindex_apply] using
      (posDef_fromBlocks_zero_complex (hσ₁C.smul ha) (hσ₂C.smul hb)).submatrix e.symm.injective
  have hmono := hR.relativeEntropy_partialTraceRight_le hS
  rw [partialTraceRight_reindex_sumEquivProdFinTwo, partialTraceRight_reindex_sumEquivProdFinTwo,
    relativeEntropy_of_posDef ((hσ₁C.smul ha).add (hσ₂C.smul hb)),
    relativeEntropy_of_posDef hS, EReal.coe_le_coe_iff] at hmono
  have hRHS := re_trace_reindex_fromBlocks_cfc_log_sub hρ₁ hρ₂ hσ₁ hσ₂ ha hb
  have hLHS : RCLike.re ((a • φ ρ₁ + b • φ ρ₂) *
        (cfc Real.log (a • φ ρ₁ + b • φ ρ₂) - cfc Real.log (a • φ σ₁ + b • φ σ₂))).trace =
      RCLike.re ((a • ρ₁ + b • ρ₂) *
        (cfc Real.log (a • ρ₁ + b • ρ₂) - cfc Real.log (a • σ₁ + b • σ₂))).trace := by
    simp only [φ, ← map_smul, ← map_add, ← toComplexStarAlgHom_cfc, ← map_sub, ← map_mul,
      RCLike.re_to_complex, re_trace_toComplexStarAlgHom]
  linarith

/-- **Joint convexity of Umegaki relative entropy** on positive definite matrices (`EReal` form). -/
theorem PosDef.relativeEntropy_smul_add_smul_le
    {ρ₁ ρ₂ σ₁ σ₂ : Matrix n n 𝕜} (hρ₁ : ρ₁.PosDef) (hρ₂ : ρ₂.PosDef)
    (hσ₁ : σ₁.PosDef) (hσ₂ : σ₂.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    relativeEntropy (a • ρ₁ + b • ρ₂) (a • σ₁ + b • σ₂) ≤
      (a : EReal) * relativeEntropy ρ₁ σ₁ + (b : EReal) * relativeEntropy ρ₂ σ₂ := by
  have hσ : (a • σ₁ + b • σ₂).PosDef := TauCeti.convex_setOfPred_posDef hσ₁ hσ₂ ha hb hab
  rw [relativeEntropy_of_posDef hσ, relativeEntropy_of_posDef hσ₁, relativeEntropy_of_posDef hσ₂,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  exact hρ₁.re_trace_mul_cfc_log_sub_cfc_log_smul_add_smul_le hρ₂ hσ₁ hσ₂ ha hb

/-! ### Gibbs variational principle and Lieb's concavity theorem -/

/-- **Gibbs variational inequality.** For Hermitian `H`, positive definite `X`, and any matrix `A`,
`re Tr X + re Tr (X * H) - re Tr (X (log X - log A)) ≤ re Tr exp (H + log A)`. Equality holds at
`X = NormedSpace.exp (H + cfc Real.log A)`. -/
theorem PosDef.re_trace_add_re_trace_mul_sub_le_re_trace_exp_add_cfc_log
    {X H : Matrix n n 𝕜} (hX : X.PosDef) (hH : H.IsHermitian) (A : Matrix n n 𝕜) :
    RCLike.re X.trace + RCLike.re (X * H).trace -
        RCLike.re (X * (cfc Real.log X - cfc Real.log A)).trace ≤
      RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace := by
  have hLA : (cfc Real.log A).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log A)
  have hHLA : (H + cfc Real.log A).IsHermitian := hH.add hLA
  set Y := NormedSpace.exp (H + cfc Real.log A)
  have hY : Y.PosDef := hHLA.posDef_exp
  have hklein := hX.posSemidef.re_trace_sub_trace_le_relativeEntropy hY.posSemidef
  rw [relativeEntropy_of_posDef hY, hHLA.cfc_log_exp, EReal.coe_le_coe_iff, map_sub] at hklein
  have hexpand : X * (cfc Real.log X - (H + cfc Real.log A)) =
      X * (cfc Real.log X - cfc Real.log A) - X * H := by
    simp only [mul_sub, mul_add]
    abel
  rw [hexpand, trace_sub, map_sub] at hklein
  linarith

/-- **Lieb's concavity theorem.** For every Hermitian matrix `H` over `ℝ` or `ℂ`, the functional
`A ↦ re Tr exp (H + cfc Real.log A)` is concave on the positive definite cone
`{A : Matrix n n 𝕜 | A.PosDef}`. -/
theorem IsHermitian.concaveOn_re_trace_exp_add_cfc_log {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef}
      (fun A ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace) := by
  refine ⟨TauCeti.convex_setOfPred_posDef, fun A₁ hA₁ A₂ hA₂ a b ha hb hab ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hA₁ hA₂
  simp only [smul_eq_mul]
  have hHLA₁ : (H + cfc Real.log A₁).IsHermitian :=
    hH.add (isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log A₁))
  have hHLA₂ : (H + cfc Real.log A₂).IsHermitian :=
    hH.add (isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log A₂))
  set X₁ := NormedSpace.exp (H + cfc Real.log A₁)
  set X₂ := NormedSpace.exp (H + cfc Real.log A₂)
  have hX₁ : X₁.PosDef := hHLA₁.posDef_exp
  have hX₂ : X₂.PosDef := hHLA₂.posDef_exp
  have hX : (a • X₁ + b • X₂).PosDef := TauCeti.convex_setOfPred_posDef hX₁ hX₂ ha hb hab
  -- At the Gibbs maximizers `Xᵢ = exp (H + log Aᵢ)`, `log Xᵢ - log Aᵢ = H`.
  have heq₁ : RCLike.re (X₁ * (cfc Real.log X₁ - cfc Real.log A₁)).trace =
      RCLike.re (X₁ * H).trace := by rw [hHLA₁.cfc_log_exp, add_sub_cancel_right]
  have heq₂ : RCLike.re (X₂ * (cfc Real.log X₂ - cfc Real.log A₂)).trace =
      RCLike.re (X₂ * H).trace := by rw [hHLA₂.cfc_log_exp, add_sub_cancel_right]
  have hconv := hX₁.re_trace_mul_cfc_log_sub_cfc_log_smul_add_smul_le hX₂ hA₁ hA₂ ha hb
  rw [heq₁, heq₂] at hconv
  have hgibbs := hX.re_trace_add_re_trace_mul_sub_le_re_trace_exp_add_cfc_log hH (a • A₁ + b • A₂)
  have hlin₁ : RCLike.re (a • X₁ + b • X₂).trace =
      a * RCLike.re X₁.trace + b * RCLike.re X₂.trace := by
    simp [trace_add, trace_smul, RCLike.smul_re]
  have hlin₂ : RCLike.re ((a • X₁ + b • X₂) * H).trace =
      a * RCLike.re (X₁ * H).trace + b * RCLike.re (X₂ * H).trace := by
    simp [add_mul, trace_add, trace_smul, RCLike.smul_re]
  linarith

/-- **Finite Jensen form of Lieb's concavity theorem.** For Hermitian `H`, positive definite `Aᵢ`,
and nonnegative weights `wᵢ` summing to `1`,
`∑ i ∈ s, w i * re Tr exp (H + log (A i)) ≤ re Tr exp (H + log (∑ i ∈ s, w i • A i))`. -/
theorem IsHermitian.sum_mul_re_trace_exp_add_cfc_log_le {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    {ι : Type*} (s : Finset ι) {w : ι → ℝ} {A : ι → Matrix n n 𝕜}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw₁ : ∑ i ∈ s, w i = 1) (hA : ∀ i ∈ s, (A i).PosDef) :
    ∑ i ∈ s, w i * RCLike.re (NormedSpace.exp (H + cfc Real.log (A i))).trace ≤
      RCLike.re (NormedSpace.exp (H + cfc Real.log (∑ i ∈ s, w i • A i))).trace :=
  hH.concaveOn_re_trace_exp_add_cfc_log.le_map_sum hw hw₁ hA

/-! ### Monotonicity, growth bound, and continuity of Lieb's functional -/

/-- Lieb's functional `A ↦ re Tr exp (H + cfc Real.log A)` is Loewner monotone on positive definite
matrices. -/
theorem PosDef.re_trace_exp_add_cfc_log_mono {A B H : Matrix n n 𝕜} (hA : A.PosDef)
    (hH : H.IsHermitian) (hAB : A ≤ B) :
    RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace ≤
      RCLike.re (NormedSpace.exp (H + cfc Real.log B)).trace := by
  have hLA : (cfc Real.log A).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log A)
  have hLB : (cfc Real.log B).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log B)
  exact IsHermitian.re_trace_exp_le_of_le (hH.add hLA) (hH.add hLB)
    (add_le_add_right (hA.cfc_log_le_cfc_log hAB) H)

/-- Lieb's functional `re Tr exp (H + cfc Real.log A)` is nonnegative for Hermitian `H`. -/
theorem IsHermitian.re_trace_exp_add_cfc_log_nonneg {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (A : Matrix n n 𝕜) :
    0 ≤ RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace := by
  have hHLA : (H + cfc Real.log A).IsHermitian :=
    hH.add (isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log A))
  rw [hHLA.posDef_exp.isHermitian.trace_eq_sum_eigenvalues]
  simp only [map_sum, RCLike.ofReal_re]
  exact Finset.sum_nonneg fun i _ ↦ (hHLA.posDef_exp.eigenvalues_pos i).le

/-- For Hermitian `H` and positive definite `A`,
`re Tr exp (H + cfc Real.log A) ≤ exp ‖H‖ * re Tr A` under the Euclidean operator norm. -/
theorem PosDef.re_trace_exp_add_cfc_log_le {A H : Matrix n n 𝕜} (hA : A.PosDef)
    (hH : H.IsHermitian) :
    RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace ≤ Real.exp ‖H‖ * RCLike.re A.trace := by
  have hLA : (cfc Real.log A).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log A)
  have hcA : (Real.exp ‖H‖ • A).PosDef := hA.smul (Real.exp_pos ‖H‖)
  have hle : H + cfc Real.log A ≤ cfc Real.log (Real.exp ‖H‖ • A) := by
    rw [hA.cfc_log_smul (Real.exp_pos ‖H‖), Real.log_exp]
    exact add_le_add_left hH.le_l2_opNorm_smul_one (cfc Real.log A)
  have hLC : (cfc Real.log (Real.exp ‖H‖ • A)).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log _)
  calc RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace
      ≤ RCLike.re (NormedSpace.exp (cfc Real.log (Real.exp ‖H‖ • A))).trace :=
        IsHermitian.re_trace_exp_le_of_le (hH.add hLA) hLC hle
    _ = Real.exp ‖H‖ * RCLike.re A.trace := by
        rw [hcA.exp_cfc_log, trace_smul, RCLike.smul_re]

/-- For any matrix `H`, the map `A ↦ re Tr exp (H + cfc Real.log A)` is continuous on
`{A : Matrix n n 𝕜 | A.PosDef}`. -/
theorem continuousOn_re_trace_exp_add_cfc_log (H : Matrix n n 𝕜) :
    ContinuousOn
      (fun A : Matrix n n 𝕜 ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace)
      {A | A.PosDef} := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := .restrictScalars ℚ ℝ _
  have hcont : Continuous fun X : Matrix n n 𝕜 ↦ RCLike.re (NormedSpace.exp (H + X)).trace :=
    RCLike.continuous_re.comp <| continuous_id.matrix_trace.comp <|
      NormedSpace.exp_continuous.comp (continuous_const.add continuous_id)
  exact hcont.comp_continuousOn (contDiffOn_cfc_log (k := 0)).continuousOn

end Matrix
