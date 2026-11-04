/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.Integration
public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.Matrix.Eigenvalues.Basic
public import TauCeti.Analysis.Matrix.Exponential.GoldenThompson
public import TauCeti.Analysis.Matrix.Exponential.Lieb
public import TauCeti.Analysis.Matrix.Exponential.Log
public import TauCeti.Analysis.Matrix.FunctionalCalculus
public import TauCeti.MeasureTheory.Integral.PosSemidef
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Lieb's expectation inequality and the matrix Laplace transform method

For an integrable, almost everywhere positive-definite random matrix `Z` on a probability space and
a deterministic Hermitian matrix `B`, Lieb's concavity theorem
(`Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log`) combined with Jensen's inequality on
shifted cones `{A | (A - ε • 1).PosSemidef}` and dominated convergence yields **Lieb's expectation
inequality**:
`E[Re Tr (exp (B + log Z))] ≤ Re Tr (exp (B + log E[Z]))`.

Iterating this inequality across a finite family of independent Hermitian random matrices yields
**Tropp's master cumulant bound** for the matrix moment generating function:
`E[Re Tr (exp (H + ∑ i ∈ s, X i))] ≤ Re Tr (exp (H + ∑ i ∈ s, log E[exp (X i)]))`.
Combined with operator monotonicity of `log`, trace monotonicity of `exp` in the Loewner order, and
Markov's inequality on the spectral trace `Re Tr (exp (θ • S))`, this gives the **matrix Laplace
transform tail bound** controlling the upper tail of the eigenvalues of `∑ i ∈ s, X i`.

## Main results

* `Matrix.PosSemidef.re_trace_mul_nonneg`, `Matrix.PosSemidef.re_trace_mul_le`: for positive
  semidefinite `P` and `Q`, `0 ≤ Re Tr (P * Q) ≤ Re Tr P * Re Tr Q`.
* `Matrix.IsHermitian.eigenvalues_mono`, `Matrix.IsHermitian.re_trace_exp_mono`: Loewner
  monotonicity of eigenvalues and of `Re Tr (exp A)` on Hermitian matrices.
* `Matrix.IsHermitian.integral_re_trace_exp_add_cfc_log_le`: Lieb's expectation inequality
  `E[Re Tr (exp (B + log Z))] ≤ Re Tr (exp (B + log E[Z]))`.
* `ProbabilityTheory.iIndepFun.integral_re_trace_exp_add_sum_le`: subadditivity of the matrix
  cumulant generating function for independent Hermitian summands.
* `ProbabilityTheory.iIndepFun.integral_re_trace_exp_smul_sum_le`: Loewner upper bounds
  `E[exp (θ • X i)] ≤ exp (M i)` imply `E[Re Tr (exp (θ • ∑ X i))] ≤ Re Tr (exp (∑ M i))`.
* `ProbabilityTheory.iIndepFun.measureReal_exists_le_eigenvalues_sum_le`: Tropp's master Laplace
  transform tail bound for eigenvalues of a sum of independent Hermitian random matrices.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12
  (2012), 389–434, Corollary 3.3, Theorem 3.6, and Proposition 3.1.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator MatrixOrder Topology

noncomputable section

namespace Matrix

section TraceOrder

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The real part of the trace of a Hermitian matrix equals the sum of its eigenvalues. -/
theorem IsHermitian.re_trace_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re A.trace = ∑ i, hA.eigenvalues i := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have h := hA.trace_cfc (id : ℝ → ℝ)
  rw [cfc_id ℝ A hA.isSelfAdjoint] at h
  simp only [h, map_sum, RCLike.ofReal_re, id_eq]

omit [DecidableEq n] in
/-- For positive semidefinite matrices `P` and `Q`, `0 ≤ Re Tr (P * Q)`. -/
theorem PosSemidef.re_trace_mul_nonneg {P Q : Matrix n n 𝕜} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ RCLike.re (P * Q).trace := by
  classical
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have h := hP.1.re_trace_cfc_mul_cfc hQ.1 (id : ℝ → ℝ) (id : ℝ → ℝ)
  rw [cfc_id ℝ P hP.1.isSelfAdjoint, cfc_id ℝ Q hQ.1.isSelfAdjoint] at h
  rw [h]
  refine Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ ?_
  exact mul_nonneg (mul_nonneg (hP.eigenvalues_nonneg i) (hQ.eigenvalues_nonneg j)) (sq_nonneg _)

omit [DecidableEq n] in
/-- For positive semidefinite matrices `P` and `Q`, `Re Tr (P * Q) ≤ Re Tr P * Re Tr Q`. -/
theorem PosSemidef.re_trace_mul_le {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    RCLike.re (P * Q).trace ≤ RCLike.re P.trace * RCLike.re Q.trace := by
  classical
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have h := hP.1.re_trace_cfc_mul_cfc hQ.1 (id : ℝ → ℝ) (id : ℝ → ℝ)
  rw [cfc_id ℝ P hP.1.isSelfAdjoint, cfc_id ℝ Q hQ.1.isSelfAdjoint] at h
  rw [h, hP.1.re_trace_eq_sum_eigenvalues, hQ.1.re_trace_eq_sum_eigenvalues, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  have hcs : ‖⟪hP.1.eigenvectorBasis i, hQ.1.eigenvectorBasis j⟫_𝕜‖ ≤ 1 := by
    calc ‖⟪hP.1.eigenvectorBasis i, hQ.1.eigenvectorBasis j⟫_𝕜‖
        ≤ ‖hP.1.eigenvectorBasis i‖ * ‖hQ.1.eigenvectorBasis j‖ := norm_inner_le_norm _ _
      _ = 1 := by simp [hP.1.eigenvectorBasis.norm_eq_one, hQ.1.eigenvectorBasis.norm_eq_one]
  have hsq : ‖⟪hP.1.eigenvectorBasis i, hQ.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg ⟪hP.1.eigenvectorBasis i, hQ.1.eigenvectorBasis j⟫_𝕜]
  have hprod : 0 ≤ hP.1.eigenvalues i * hQ.1.eigenvalues j :=
    mul_nonneg (hP.eigenvalues_nonneg i) (hQ.eigenvalues_nonneg j)
  simpa only [id_eq, mul_one] using mul_le_mul_of_nonneg_left hsq hprod

/-- **Weyl monotonicity** of sorted eigenvalues with respect to the Loewner order. -/
theorem IsHermitian.eigenvalues₀_mono {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : (B - A).PosSemidef) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  simp only [Matrix.IsHermitian.eigenvalues₀]
  refine LinearMap.IsSymmetric.eigenvalue_mono
    (isSymmetric_toEuclideanLin_iff.mpr hA) (isSymmetric_toEuclideanLin_iff.mpr hB)
    finrank_euclideanSpace (fun x ↦ ?_) k
  have hsub : 0 ≤ RCLike.re ⟪(B - A).toEuclideanLin x, x⟫_𝕜 :=
    (Matrix.isPositive_toEuclideanLin_iff.mpr hAB).2 x
  simpa only [map_sub, LinearMap.sub_apply, inner_sub_left, map_sub, sub_nonneg] using hsub

/-- **Weyl monotonicity** of matrix-indexed eigenvalues with respect to the Loewner order. -/
theorem IsHermitian.eigenvalues_mono {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : (B - A).PosSemidef) (i : n) :
    hA.eigenvalues i ≤ hB.eigenvalues i :=
  hA.eigenvalues₀_mono hB hAB ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i)

/-- Monotonicity of `Re Tr (cfc f A)` in the Loewner order for monotone `f : ℝ → ℝ`. -/
theorem IsHermitian.re_trace_cfc_mono {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : (B - A).PosSemidef) {f : ℝ → ℝ} (hf : Monotone f) :
    RCLike.re (cfc f A).trace ≤ RCLike.re (cfc f B).trace := by
  simp only [hA.trace_cfc, hB.trace_cfc, map_sum, RCLike.ofReal_re]
  exact Finset.sum_le_sum fun i _ ↦ hf (hA.eigenvalues_mono hB hAB i)

/-- Monotonicity of `Re Tr (exp A)` in the Loewner order on Hermitian matrices. -/
theorem IsHermitian.re_trace_exp_mono {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : (B - A).PosSemidef) :
    RCLike.re (NormedSpace.exp A).trace ≤ RCLike.re (NormedSpace.exp B).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint,
    ← CFC.real_exp_eq_normedSpace_exp hB.isSelfAdjoint]
  exact hA.re_trace_cfc_mono hB hAB Real.exp_monotone


private def rclikeToComplex : 𝕜 →⋆ₐ[ℝ] ℂ where
  toFun z := (RCLike.re z : ℂ) + (RCLike.im z : ℂ) * Complex.I
  map_one' := by simp
  map_mul' z w := by
    simp only [RCLike.mul_re, RCLike.mul_im, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_mul]
    ring_nf
    simp [Complex.I_sq]
    ring
  map_zero' := by simp
  map_add' z w := by
    simp only [map_add, Complex.ofReal_add]
    ring
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one, RCLike.smul_re, RCLike.smul_im]
  map_star' z := by
    simp only [RCLike.star_def, RCLike.conj_re, RCLike.conj_im, Complex.ofReal_neg, map_add,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring

@[simp]
private theorem rclikeToComplex_re (z : 𝕜) : (rclikeToComplex z).re = RCLike.re z := by
  -- Unfold `rclikeToComplex` to expose its real-part definition.
  change ((RCLike.re z : ℂ) + (RCLike.im z : ℂ) * Complex.I).re = RCLike.re z
  simp

@[simp]
private theorem rclikeToComplex_im (z : 𝕜) : (rclikeToComplex z).im = RCLike.im z := by
  -- Unfold `rclikeToComplex` to expose its imaginary-part definition.
  change ((RCLike.re z : ℂ) + (RCLike.im z : ℂ) * Complex.I).im = RCLike.im z
  simp

private theorem rclikeToComplex_injective : Function.Injective (rclikeToComplex (𝕜 := 𝕜)) := by
  intro z w h
  exact RCLike.ext (by simpa using congrArg Complex.re h) (by simpa using congrArg Complex.im h)

private def mapComplexStarAlgHom : Matrix n n 𝕜 →⋆ₐ[ℝ] Matrix n n ℂ where
  toFun M := M.map (rclikeToComplex (𝕜 := 𝕜))
  map_one' := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  map_mul' M N := by
    ext i j
    simp [Matrix.mul_apply, map_sum]
  map_zero' := by ext i j; simp
  map_add' M N := by ext i j; simp
  commutes' r := by
    ext i j
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simpa [Algebra.algebraMap_eq_smul_one, Complex.real_smul] using
        (rclikeToComplex (𝕜 := 𝕜)).commutes r
    · simp [hij]
  map_star' M := by
    ext i j
    simp only [Matrix.star_eq_conjTranspose, Matrix.map_apply, Matrix.conjTranspose_apply]
    exact map_star (rclikeToComplex (𝕜 := 𝕜)) (M j i)

@[simp]
private theorem mapComplexStarAlgHom_apply (M : Matrix n n 𝕜) (i j : n) :
    mapComplexStarAlgHom M i j = rclikeToComplex (M i j) :=
  rfl

private theorem continuous_mapComplexStarAlgHom :
    Continuous (mapComplexStarAlgHom (n := n) (𝕜 := 𝕜)) := by
  have hscalar : Continuous (rclikeToComplex (𝕜 := 𝕜)) :=
    (Complex.continuous_ofReal.comp RCLike.continuous_re).add
      ((Complex.continuous_ofReal.comp RCLike.continuous_im).mul continuous_const)
  refine continuous_matrix fun i j ↦ ?_
  exact hscalar.comp ((continuous_apply j).comp (continuous_apply i))

private theorem posSemidef_iff_mapComplexStarAlgHom {M : Matrix n n 𝕜} :
    M.PosSemidef ↔ (mapComplexStarAlgHom M).PosSemidef := by
  refine ⟨fun hM ↦ ?_, fun hφM ↦ ?_⟩
  · let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    have hsq : star (CFC.sqrt M) * CFC.sqrt M = M := by
      rw [(CFC.sqrt_nonneg M).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self M hM.nonneg]
    have hpos : 0 ≤ mapComplexStarAlgHom M := by
      rw [← hsq, map_mul, map_star]
      exact star_mul_self_nonneg _
    exact Matrix.nonneg_iff_posSemidef.mp hpos
  · have hHerm : M.IsHermitian := by
      ext i j
      apply rclikeToComplex_injective
      have hij : (mapComplexStarAlgHom M)ᴴ i j = (mapComplexStarAlgHom M) i j := hφM.1.apply i j
      simp only [Matrix.conjTranspose_apply, mapComplexStarAlgHom_apply, ← map_star] at hij
      exact hij
    refine PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun c ↦ ?_
    have hquad : rclikeToComplex (star c ⬝ᵥ (M *ᵥ c)) =
        star (rclikeToComplex ∘ c) ⬝ᵥ ((mapComplexStarAlgHom M) *ᵥ (rclikeToComplex ∘ c)) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Function.comp_apply,
        mapComplexStarAlgHom_apply, map_sum, map_mul, map_star]
    have hc_nonneg :
        0 ≤ star (rclikeToComplex ∘ c) ⬝ᵥ ((mapComplexStarAlgHom M) *ᵥ (rclikeToComplex ∘ c)) :=
      hφM.dotProduct_mulVec_nonneg _
    rw [← hquad, Complex.nonneg_iff] at hc_nonneg
    simp only [rclikeToComplex_re, rclikeToComplex_im] at hc_nonneg
    exact RCLike.nonneg_iff.mpr ⟨hc_nonneg.1, hc_nonneg.2.symm⟩

/-- **Operator monotonicity of the matrix logarithm.** If `A` is positive definite and `B - A` is
positive semidefinite, then `cfc Real.log B - cfc Real.log A` is positive semidefinite. -/
theorem PosDef.cfc_log_le_cfc_log {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hAB : (B - A).PosSemidef) : (cfc Real.log B - cfc Real.log A).PosSemidef := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hB : B.PosDef := by
    simpa [sub_add_cancel] using PosDef.posSemidef_add hAB hA
  let φ := mapComplexStarAlgHom (n := n) (𝕜 := 𝕜)
  have hφ_cont : Continuous φ := continuous_mapComplexStarAlgHom
  have hφA_pos : IsStrictlyPositive (φ A) :=
    (hA.isUnit.map φ).isStrictlyPositive
      (posSemidef_iff_mapComplexStarAlgHom.mp hA.posSemidef).nonneg
  have hφB_pos : IsStrictlyPositive (φ B) :=
    (hB.isUnit.map φ).isStrictlyPositive
      (posSemidef_iff_mapComplexStarAlgHom.mp hB.posSemidef).nonneg
  have hφAB : φ A ≤ φ B := by
    rw [Matrix.le_iff, ← map_sub]
    exact posSemidef_iff_mapComplexStarAlgHom.mp hAB
  have hlogC : CFC.log (φ A) ≤ CFC.log (φ B) := CFC.log_le_log hφAB hφA_pos
  unfold CFC.log at hlogC
  have hcontA : ContinuousOn Real.log (spectrum ℝ A) :=
    Real.continuousOn_log.mono fun x hx ↦ by
      rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact (hA.eigenvalues_pos i).ne'
  have hcontB : ContinuousOn Real.log (spectrum ℝ B) :=
    Real.continuousOn_log.mono fun x hx ↦ by
      rw [hB.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact (hB.eigenvalues_pos i).ne'
  have hmapA : φ (cfc Real.log A) = cfc Real.log (φ A) :=
    φ.map_cfc Real.log A hcontA hφ_cont hA.1.isSelfAdjoint hφA_pos.isSelfAdjoint
  have hmapB : φ (cfc Real.log B) = cfc Real.log (φ B) :=
    φ.map_cfc Real.log B hcontB hφ_cont hB.1.isSelfAdjoint hφB_pos.isSelfAdjoint
  rw [← hmapA, ← hmapB, Matrix.le_iff, ← map_sub] at hlogC
  exact posSemidef_iff_mapComplexStarAlgHom.mpr hlogC

end TraceOrder

section LiebExpectation

variable {Ω n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Fintype n] [DecidableEq n]
  [RCLike 𝕜]

private def entryCLM (i j : n) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    Matrix n n 𝕜 →L[ℝ] 𝕜 :=
  letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  { toLinearMap :=
      { toFun := fun A ↦ A i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    cont := (continuous_apply j).comp (continuous_apply i) }

private theorem integrable_entry_and_integral_eq {Z : Ω → Matrix n n 𝕜} (hZ : Integrable Z μ) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    (∀ i j, Integrable (fun ω ↦ Z ω i j) μ) ∧
      ∫ ω, Z ω ∂μ = Matrix.of fun i j ↦ ∫ ω, Z ω i j ∂μ := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  refine ⟨fun i j ↦ (entryCLM i j).integrable_comp hZ, ?_⟩
  ext i j
  rw [Matrix.of_apply]
  exact ((entryCLM (𝕜 := 𝕜) i j).integral_comp_comm hZ).symm

private def reTraceMulLeftCLM (A : Matrix n n 𝕜) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    Matrix n n 𝕜 →L[ℝ] ℝ :=
  letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  { toLinearMap :=
      { toFun := fun M ↦ RCLike.re (A * M).trace
        map_add' := fun X Y ↦ by simp [Matrix.mul_add, trace_add]
        map_smul' := fun r X ↦ by simp [trace_smul, RCLike.smul_re] }
    cont := RCLike.continuous_re.comp (continuous_const.mul continuous_id).matrix_trace }

private theorem aestronglyMeasurable_cfc_log_of_posDef {W : Ω → Matrix n n 𝕜}
    (hW : AEStronglyMeasurable W μ) (hW_pos : ∀ᵐ ω ∂μ, (W ω).PosDef) :
    AEStronglyMeasurable (fun ω ↦ cfc Real.log (W ω)) μ := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let F : ℕ → ℝ → ℝ := fun k t ↦ Real.log (max t ((k + 1 : ℝ)⁻¹))
  have hF_cont (k : ℕ) : Continuous (F k) :=
    Real.continuousOn_log.comp_continuous (continuous_id.max continuous_const) fun x ↦
      (lt_of_lt_of_le (by positivity) (le_max_right x _)).ne'
  have hF_meas (k : ℕ) : AEStronglyMeasurable (fun ω ↦ cfc (F k) (W ω)) μ :=
    ((TauCeti.measurable_matrix_cfc (hF_cont k)).comp_aemeasurable
      hW.aemeasurable).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae atTop hF_meas (hW_pos.mono fun ω hω ↦ ?_)
  by_cases hn : Nonempty n
  · let c : ℝ := Finset.univ.inf' Finset.univ_nonempty hω.1.eigenvalues
    have hc : 0 < c := (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun i _ ↦ hω.eigenvalues_pos i
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hc
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun k hk ↦ ?_
    refine cfc_congr fun t ht ↦ ?_
    rw [hω.1.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i, rfl⟩ := ht
    have hle : ((k + 1 : ℝ)⁻¹) ≤ hω.1.eigenvalues i := by
      have hkN : ((k + 1 : ℝ)⁻¹) ≤ ((N + 1 : ℝ)⁻¹) := by gcongr
      have hNc : ((N + 1 : ℝ)⁻¹) ≤ c := by simpa [one_div] using hN.le
      exact (hkN.trans hNc).trans (Finset.inf'_le _ (Finset.mem_univ i))
    exact congrArg Real.log (max_eq_left hle)
  · have : IsEmpty n := not_nonempty_iff.mp hn
    exact tendsto_atTop_of_eventually_const (i₀ := 0) fun _ _ ↦ Subsingleton.elim _ _

private theorem re_trace_exp_add_cfc_log_bounds {B P : Matrix n n 𝕜} (hB : B.IsHermitian)
    (hP : P.PosDef) :
    0 ≤ RCLike.re (NormedSpace.exp (B + cfc Real.log P)).trace ∧
      RCLike.re (NormedSpace.exp (B + cfc Real.log P)).trace ≤
        RCLike.re (NormedSpace.exp B * P).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hlogP : (cfc Real.log P).IsHermitian := isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc
  have hexp_pos : (NormedSpace.exp (B + cfc Real.log P)).PosSemidef :=
    (hB.add hlogP).posDef_exp.posSemidef
  have hnonneg : 0 ≤ RCLike.re (NormedSpace.exp (B + cfc Real.log P)).trace := by
    rw [hexp_pos.1.re_trace_eq_sum_eigenvalues]
    exact Finset.sum_nonneg fun i _ ↦ hexp_pos.eigenvalues_nonneg i
  refine ⟨hnonneg, ?_⟩
  have hgt := hB.re_trace_exp_add_le hlogP
  rwa [hP.exp_cfc_log] at hgt

private theorem integrable_re_trace_exp_add_cfc_log {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {W : Ω → Matrix n n 𝕜} (hW_int : Integrable W μ) (hW_pos : ∀ᵐ ω ∂μ, (W ω).PosDef) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (B + cfc Real.log (W ω))).trace) μ := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  have hdom : Integrable (fun ω ↦ RCLike.re (NormedSpace.exp B * W ω).trace) μ :=
    (reTraceMulLeftCLM (NormedSpace.exp B)).integrable_comp hW_int
  have hcont : Continuous (fun M : Matrix n n 𝕜 ↦ RCLike.re (NormedSpace.exp (B + M)).trace) :=
    RCLike.continuous_re.comp
      (NormedSpace.exp_continuous.comp (continuous_const.add continuous_id)).matrix_trace
  have hmeas :
      AEStronglyMeasurable
        (fun ω ↦ RCLike.re (NormedSpace.exp (B + cfc Real.log (W ω))).trace) μ :=
    hcont.comp_aestronglyMeasurable
      (aestronglyMeasurable_cfc_log_of_posDef hW_int.aestronglyMeasurable hW_pos)
  refine hdom.mono' hmeas (hW_pos.mono fun ω hω ↦ ?_)
  obtain ⟨h0, hle⟩ := re_trace_exp_add_cfc_log_bounds hB hω
  rwa [Real.norm_of_nonneg h0]

/-- **Lieb's expectation inequality.** On a probability space, for a deterministic Hermitian matrix
`B` and an integrable, a.e. positive-definite random matrix `Z`,
`E[Re Tr (exp (B + log Z))] ≤ Re Tr (exp (B + log E[Z]))`. -/
theorem IsHermitian.integral_re_trace_exp_add_cfc_log_le [IsProbabilityMeasure μ]
    {B : Matrix n n 𝕜} (hB : B.IsHermitian) {Z : Ω → Matrix n n 𝕜} (hZ_int : Integrable Z μ)
    (hZ_pos : ∀ᵐ ω ∂μ, (Z ω).PosDef) :
    ∫ ω, RCLike.re (NormedSpace.exp (B + cfc Real.log (Z ω))).trace ∂μ ≤
      RCLike.re (NormedSpace.exp
        (B + cfc Real.log (Matrix.of fun i j ↦ ∫ ω, Z ω i j ∂μ))).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  obtain ⟨hZ_entry, hZ_eq⟩ := integrable_entry_and_integral_eq hZ_int
  set EZ : Matrix n n 𝕜 := Matrix.of fun i j ↦ ∫ ω, Z ω i j ∂μ
  have hEZ_pos : EZ.PosDef := TauCeti.posDef_integral hZ_pos hZ_entry
  set φ : Matrix n n 𝕜 → ℝ := fun A ↦ RCLike.re (NormedSpace.exp (B + cfc Real.log A)).trace
  have hφ_cont : ContinuousOn φ {A : Matrix n n 𝕜 | A.PosDef} := by
    have hexp_cont :
        Continuous (fun M : Matrix n n 𝕜 ↦ RCLike.re (NormedSpace.exp (B + M)).trace) :=
      RCLike.continuous_re.comp
        (NormedSpace.exp_continuous.comp (continuous_const.add continuous_id)).matrix_trace
    exact hexp_cont.comp_continuousOn
      (Matrix.contDiffOn_cfc_log (n := n) (𝕜 := 𝕜) (k := 1)).continuousOn
  -- Step 1: Jensen's inequality on each closed shifted cone `{A | (A - ε • 1).PosSemidef}`.
  have hshift (ε : ℝ) (hε : 0 < ε) :
      ∫ ω, φ (Z ω + ε • 1) ∂μ ≤ φ (EZ + ε • 1) := by
    set sε : Set (Matrix n n 𝕜) := {A | (A - ε • 1).PosSemidef}
    have hsε_sub : sε ⊆ {A | A.PosDef} := fun A hA ↦ by
      have h1 : (ε • (1 : Matrix n n 𝕜)).PosDef := Matrix.PosDef.one.smul hε
      simpa [sub_add_cancel] using PosDef.posSemidef_add hA h1
    have hsε_closed : IsClosed sε :=
      isClosed_setOfPred_posSemidef.preimage (continuous_id.sub continuous_const)
    have hZε_int : Integrable (fun ω ↦ Z ω + ε • 1) μ := hZ_int.add (integrable_const _)
    have hZε_mem : ∀ᵐ ω ∂μ, Z ω + ε • 1 ∈ sε := hZ_pos.mono fun ω hω ↦ by
      -- Unfold membership in `sε` to the shifted positive-semidefiniteness condition.
      change ((Z ω + ε • 1) - ε • 1).PosSemidef
      simpa [add_sub_cancel_right] using hω.posSemidef
    have hφZε_int : Integrable (φ ∘ fun ω ↦ Z ω + ε • 1) μ :=
      integrable_re_trace_exp_add_cfc_log hB hZε_int (hZε_mem.mono fun _ h ↦ hsε_sub h)
    have hjensen :=
      (hB.concaveOn_re_trace_exp_add_cfc_log_posSemidef_sub_smul_one hε).le_map_integral
        (hφ_cont.mono hsε_sub) hsε_closed hZε_mem hZε_int hφZε_int
    have hint_add : ∫ ω, (Z ω + ε • 1) ∂μ = EZ + ε • 1 := by
      rw [integral_add hZ_int (integrable_const _), hZ_eq, integral_const, probReal_univ, one_smul]
    rwa [hint_add] at hjensen
  -- Step 2: Pass `ε_k = (k + 1)⁻¹ → 0` via dominated convergence on LHS and continuity on RHS.
  let ε : ℕ → ℝ := fun k ↦ ((k + 1 : ℝ)⁻¹)
  have hε_pos (k : ℕ) : 0 < ε k := by positivity
  have hε_le (k : ℕ) : ε k ≤ 1 := inv_le_one_of_one_le₀ (by norm_cast; omega)
  have hε_tendsto : Tendsto ε atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hbound_int : Integrable (fun ω ↦ RCLike.re (NormedSpace.exp B * (Z ω + 1)).trace) μ :=
    (reTraceMulLeftCLM (NormedSpace.exp B)).integrable_comp (hZ_int.add (integrable_const 1))
  have hlhs_tendsto :
      Tendsto (fun k ↦ ∫ ω, φ (Z ω + ε k • 1) ∂μ) atTop (𝓝 (∫ ω, φ (Z ω) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ω ↦ RCLike.re (NormedSpace.exp B * (Z ω + 1)).trace) ?_ hbound_int ?_ ?_
    · intro k
      refine (integrable_re_trace_exp_add_cfc_log hB
        (hZ_int.add (integrable_const _)) ?_).aestronglyMeasurable
      exact hZ_pos.mono fun ω hω ↦ hω.add (Matrix.PosDef.one.smul (hε_pos k))
    · intro k
      refine hZ_pos.mono fun ω hω ↦ ?_
      have hpos_k : (Z ω + ε k • 1).PosDef := hω.add (Matrix.PosDef.one.smul (hε_pos k))
      obtain ⟨h0, hle⟩ := re_trace_exp_add_cfc_log_bounds hB hpos_k
      rw [Real.norm_of_nonneg h0]
      have hdiff_psd : ((Z ω + 1) - (Z ω + ε k • 1)).PosSemidef := by
        have h1 : (Z ω + 1) - (Z ω + ε k • 1) = (1 - ε k) • (1 : Matrix n n 𝕜) := by
          ext i j
          simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, sub_smul, one_smul]
          abel
        rw [h1]
        exact PosDef.one.posSemidef.smul (sub_nonneg.2 (hε_le k))
      have hmono :
          0 ≤ RCLike.re (NormedSpace.exp B * ((Z ω + 1) - (Z ω + ε k • 1))).trace :=
        hB.posDef_exp.posSemidef.re_trace_mul_nonneg hdiff_psd
      rw [Matrix.mul_sub, trace_sub, map_sub, sub_nonneg] at hmono
      exact hle.trans hmono
    · refine hZ_pos.mono fun ω hω ↦ ?_
      have hshift_tendsto : Tendsto (fun k ↦ Z ω + ε k • (1 : Matrix n n 𝕜)) atTop (𝓝 (Z ω)) := by
        simpa using tendsto_const_nhds.add (hε_tendsto.smul_const (1 : Matrix n n 𝕜))
      exact (hφ_cont.continuousWithinAt hω).tendsto.comp <|
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hshift_tendsto <|
          Eventually.of_forall fun k ↦ hω.add (Matrix.PosDef.one.smul (hε_pos k))
  have hrhs_tendsto : Tendsto (fun k ↦ φ (EZ + ε k • 1)) atTop (𝓝 (φ EZ)) := by
    have hshift_EZ : Tendsto (fun k ↦ EZ + ε k • (1 : Matrix n n 𝕜)) atTop (𝓝 EZ) := by
      simpa using tendsto_const_nhds.add (hε_tendsto.smul_const (1 : Matrix n n 𝕜))
    exact (hφ_cont.continuousWithinAt hEZ_pos).tendsto.comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hshift_EZ <|
        Eventually.of_forall fun k ↦ hEZ_pos.add (Matrix.PosDef.one.smul (hε_pos k))
  exact le_of_tendsto_of_tendsto hlhs_tendsto hrhs_tendsto
    (Eventually.of_forall fun k ↦ hshift (ε k) (hε_pos k))

end LiebExpectation

end Matrix

namespace ProbabilityTheory.iIndepFun

variable {Ω ι n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Fintype n] [DecidableEq n]
  [RCLike 𝕜]

omit [Fintype n] [DecidableEq n] in
private theorem isHermitian_finset_sum {s : Finset ι} {f : ι → Matrix n n 𝕜}
    (hf : ∀ i ∈ s, (f i).IsHermitian) : (∑ i ∈ s, f i).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.isHermitian_zero]
  | insert a t hat ih =>
    rw [Finset.sum_insert hat]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- **Tropp's master cumulant bound** (both integrability and trace inequality): for mutually
independent, a.e. Hermitian random matrices `X i` (`i ∈ s`) with integrable matrix exponentials
`exp (X i)` and any deterministic Hermitian matrix `H`,
`E[Re Tr (exp (H + ∑ i ∈ s, X i))] ≤ Re Tr (exp (H + ∑ i ∈ s, log E[exp (X i)]))`. -/
theorem integrable_and_integral_re_trace_exp_add_sum_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_int : ∀ i ∈ s, Integrable (fun ω ↦ NormedSpace.exp (X i ω)) μ)
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (H + ∑ i ∈ s, X i ω)).trace) μ ∧
      ∫ ω, RCLike.re (NormedSpace.exp (H + ∑ i ∈ s, X i ω)).trace ∂μ ≤
        RCLike.re (NormedSpace.exp (H + ∑ i ∈ s,
          cfc Real.log (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (X i ω) p q ∂μ))).trace := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  let : DecidablePred (· ∈ s) := Classical.decPred _
  -- Replace `X` on `s` by genuinely measurable, everywhere-Hermitian versions `Y` preserving
  -- independence.
  let Z : ι → Ω → Matrix n n 𝕜 := fun j ↦ if hj : j ∈ s then (hX_meas j hj).mk (X j) else X j
  let g : ι → Matrix n n 𝕜 → Matrix n n 𝕜 := fun j ↦
    if j ∈ s then {M : Matrix n n 𝕜 | M.IsHermitian}.indicator id else fun _ ↦ 0
  let Y : ι → Ω → Matrix n n 𝕜 := fun j ω ↦ g j (Z j ω)
  have hXZ_ae (j : ι) : X j =ᵐ[μ] Z j := by
    by_cases hj : j ∈ s
    · simpa [Z, hj] using (hX_meas j hj).ae_eq_mk
    · simp [Z, hj]
  have hg_meas (j : ι) : Measurable (g j) := by
    by_cases hj : j ∈ s
    · simp only [g, hj, ↓reduceIte]
      exact measurable_id.indicator Matrix.isClosed_setOfPred_isHermitian.measurableSet
    · simp only [g, hj, ↓reduceIte]
      exact measurable_const
  have hY_indep : iIndepFun Y μ := (h_indep.congr hXZ_ae).comp g hg_meas
  have hY_meas (j : ι) : Measurable (Y j) := by
    by_cases hj : j ∈ s
    · have hmk : Measurable (Z j) := by simpa [Z, hj] using (hX_meas j hj).measurable_mk
      exact (hg_meas j).comp hmk
    · have hzero : Y j = fun _ ↦ 0 := by ext ω; simp [Y, g, hj]
      rw [hzero]
      exact measurable_const
  have hY_herm (j : ι) (ω : Ω) : (Y j ω).IsHermitian := by
    by_cases hj : j ∈ s
    · simp only [Y, g, hj, ↓reduceIte]
      by_cases hM : Z j ω ∈ {M : Matrix n n 𝕜 | M.IsHermitian}
      · rw [Set.indicator_of_mem hM]
        exact hM
      · rw [Set.indicator_of_notMem hM]
        exact Matrix.isHermitian_zero
    · simp only [Y, g, hj, ↓reduceIte]
      exact Matrix.isHermitian_zero
  have hXY_ae {j : ι} (hj : j ∈ s) : X j =ᵐ[μ] Y j := by
    filter_upwards [hXZ_ae j, hX_herm j hj] with ω hωZ hωH
    have hZH : Z j ω ∈ {M : Matrix n n 𝕜 | M.IsHermitian} := hωZ ▸ hωH
    simp only [Y, g, hj, ↓reduceIte, Set.indicator_of_mem hZH, id_eq, hωZ]
  have hY_int {j : ι} (hj : j ∈ s) : Integrable (fun ω ↦ NormedSpace.exp (Y j ω)) μ :=
    (hX_int j hj).congr ((hXY_ae hj).mono fun ω hω ↦ by dsimp only; rw [hω])
  let L : ι → Matrix n n 𝕜 := fun i ↦
    cfc Real.log (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (Y i ω) p q ∂μ)
  have hL_herm (i : ι) : (L i).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc
  have hL_eq {i : ι} (hi : i ∈ s) :
      L i = cfc Real.log (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (X i ω) p q ∂μ) := by
    have hmat : (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (Y i ω) p q ∂μ) =
        Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (X i ω) p q ∂μ := by
      ext p q
      simp only [Matrix.of_apply]
      exact integral_congr_ae
        ((hXY_ae hi).symm.mono fun ω hω ↦ by dsimp only; rw [hω])
    dsimp only [L]
    rw [hmat]
  -- Prove both claims on any subset `t ⊆ s` and deterministic Hermitian `B` by induction on `t`.
  have key : ∀ (t : Finset ι), t ⊆ s → ∀ {B : Matrix n n 𝕜}, B.IsHermitian →
      Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (B + ∑ i ∈ t, Y i ω)).trace) μ ∧
        ∫ ω, RCLike.re (NormedSpace.exp (B + ∑ i ∈ t, Y i ω)).trace ∂μ ≤
          RCLike.re (NormedSpace.exp (B + ∑ i ∈ t, L i)).trace := by
    intro t
    refine Finset.cons_induction ?_ ?_ t
    · intro _ B _
      simp only [Finset.sum_empty, add_zero]
      refine ⟨integrable_const _, ?_⟩
      rw [integral_const, probReal_univ, one_smul]
    · intro a t hat ih hcons B hB
      have ha : a ∈ s := hcons (Finset.mem_cons_self a t)
      have ht : t ⊆ s := fun x hx ↦ hcons (Finset.mem_cons_of_mem hx)
      let S : Ω → Matrix n n 𝕜 := ∑ i ∈ t, Y i
      have hS_apply (ω : Ω) : S ω = ∑ i ∈ t, Y i ω := Finset.sum_apply ω t Y
      have hS_eq : S = fun ω ↦ ∑ i ∈ t, Y i ω := funext hS_apply
      have hS_meas : Measurable S := by
        rw [hS_eq]
        exact Finset.measurable_sum t fun i _ ↦ hY_meas i
      have hS_herm (ω : Ω) : (S ω).IsHermitian := by
        rw [hS_apply]
        exact isHermitian_finset_sum fun i _ ↦ hY_herm i ω
      have hindep_Sa : IndepFun S (Y a) μ := hY_indep.indepFun_finsetSum_of_notMem hY_meas hat
      -- Step (a): Integrability via Golden-Thompson + `PosSemidef.re_trace_mul_le` + independence.
      let g₁ : Matrix n n 𝕜 → ℝ := fun M ↦ RCLike.re (NormedSpace.exp (B + M)).trace
      have hg₁_cont : Continuous g₁ :=
        RCLike.continuous_re.comp
          (NormedSpace.exp_continuous.comp (continuous_const.add continuous_id)).matrix_trace
      let hg₂_clm : Matrix n n 𝕜 →L[ℝ] ℝ :=
        { toLinearMap :=
            { toFun := fun M ↦ RCLike.re M.trace
              map_add' := fun X₁ X₂ ↦ by simp [Matrix.trace_add]
              map_smul' := fun r X₁ ↦ by simp [Matrix.trace_smul, RCLike.smul_re] }
          cont := RCLike.continuous_re.comp continuous_id.matrix_trace }
      have hg₁S_int : Integrable (g₁ ∘ S) μ := by
        -- Express the integrand as the composition `g₁ ∘ S`.
        change Integrable (fun ω ↦ g₁ (S ω)) μ
        simpa [g₁, hS_apply] using (ih ht hB).1
      have hg₂Ya_int : Integrable ((hg₂_clm ∘ NormedSpace.exp) ∘ Y a) μ :=
        hg₂_clm.integrable_comp (hY_int ha)
      have hindep_real : IndepFun (g₁ ∘ S) ((hg₂_clm ∘ NormedSpace.exp) ∘ Y a) μ :=
        hindep_Sa.comp hg₁_cont.measurable
          (hg₂_clm.continuous.comp NormedSpace.exp_continuous).measurable
      have hprod_int : Integrable ((g₁ ∘ S) * ((hg₂_clm ∘ NormedSpace.exp) ∘ Y a)) μ :=
        hindep_real.integrable_mul hg₁S_int hg₂Ya_int
      let Ψ : Matrix n n 𝕜 × Matrix n n 𝕜 → ℝ :=
        fun p ↦ RCLike.re (NormedSpace.exp ((B + p.1) + p.2)).trace
      have hΨ_cont : Continuous Ψ :=
        RCLike.continuous_re.comp <|
          (NormedSpace.exp_continuous.comp <|
            (continuous_const.add continuous_fst).add continuous_snd).matrix_trace
      have hF_eq_Ψ :
          (fun ω ↦ RCLike.re (NormedSpace.exp (B + ∑ i ∈ Finset.cons a t hat, Y i ω)).trace) =
            fun ω ↦ Ψ (S ω, Y a ω) := by
        ext ω
        simp only [Ψ, Finset.sum_cons, ← hS_apply]
        congr 3
        abel
      have hF_meas :
          Measurable
            (fun ω ↦ RCLike.re (NormedSpace.exp (B + ∑ i ∈ Finset.cons a t hat, Y i ω)).trace) := by
        rw [hF_eq_Ψ]
        exact hΨ_cont.measurable.comp (hS_meas.prodMk (hY_meas a))
      have hF_int :
          Integrable
            (fun ω ↦
              RCLike.re (NormedSpace.exp (B + ∑ i ∈ Finset.cons a t hat, Y i ω)).trace) μ := by
        refine hprod_int.mono' hF_meas.aestronglyMeasurable (Eventually.of_forall fun ω ↦ ?_)
        have hrew : B + ∑ i ∈ Finset.cons a t hat, Y i ω = (B + S ω) + Y a ω := by
          rw [Finset.sum_cons, ← hS_apply]
          abel
        rw [hrew]
        have hexp_psd : (NormedSpace.exp ((B + S ω) + Y a ω)).PosSemidef :=
          ((hB.add (hS_herm ω)).add (hY_herm a ω)).posDef_exp.posSemidef
        have h0 : 0 ≤ RCLike.re (NormedSpace.exp ((B + S ω) + Y a ω)).trace := by
          rw [hexp_psd.1.re_trace_eq_sum_eigenvalues]
          exact Finset.sum_nonneg fun i _ ↦ hexp_psd.eigenvalues_nonneg i
        rw [Real.norm_of_nonneg h0]
        calc RCLike.re (NormedSpace.exp ((B + S ω) + Y a ω)).trace
            ≤ RCLike.re (NormedSpace.exp (B + S ω) * NormedSpace.exp (Y a ω)).trace :=
              (hB.add (hS_herm ω)).re_trace_exp_add_le (hY_herm a ω)
          _ ≤ ((g₁ ∘ S) * ((hg₂_clm ∘ NormedSpace.exp) ∘ Y a)) ω :=
              (hB.add (hS_herm ω)).posDef_exp.posSemidef.re_trace_mul_le
                (hY_herm a ω).posDef_exp.posSemidef
      refine ⟨hF_int, ?_⟩
      -- Step (b): Fubini over the independent pair `(S, Y a)`, Lieb expectation in `Y a`, then IH.
      let μS : Measure (Matrix n n 𝕜) := μ.map S
      let μa : Measure (Matrix n n 𝕜) := μ.map (Y a)
      have hpair_eq : μ.map (fun ω ↦ (S ω, Y a ω)) = μS.prod μa :=
        hindep_Sa.map_prod_eq_prod_map_map hS_meas.aemeasurable (hY_meas a).aemeasurable
      have hΨ_int_map : Integrable Ψ (μ.map (fun ω ↦ (S ω, Y a ω))) := by
        rw [integrable_map_measure hΨ_cont.measurable.aestronglyMeasurable
          (hS_meas.prodMk (hY_meas a)).aemeasurable]
        -- Express the integrand as `Ψ` applied to the independent pair `(S, Y a)`.
        change Integrable (fun ω ↦ Ψ (S ω, Y a ω)) μ
        rwa [← hF_eq_Ψ]
      have hΨ_int_prod : Integrable Ψ (μS.prod μa) := hpair_eq ▸ hΨ_int_map
      have hfubini :
          ∫ ω, RCLike.re (NormedSpace.exp (B + ∑ i ∈ Finset.cons a t hat, Y i ω)).trace ∂μ =
            ∫ m₁, (∫ m₂, Ψ (m₁, m₂) ∂μa) ∂μS := by
        calc ∫ ω, RCLike.re (NormedSpace.exp (B + ∑ i ∈ Finset.cons a t hat, Y i ω)).trace ∂μ
            = ∫ ω, Ψ (S ω, Y a ω) ∂μ := by rw [hF_eq_Ψ]
          _ = ∫ p, Ψ p ∂(μ.map (fun ω ↦ (S ω, Y a ω))) :=
              (integral_map (hS_meas.prodMk (hY_meas a)).aemeasurable
                hΨ_cont.measurable.aestronglyMeasurable).symm
          _ = ∫ m₁, (∫ m₂, Ψ (m₁, m₂) ∂μa) ∂μS := by
              rw [hpair_eq, integral_prod Ψ hΨ_int_prod]
      have hm₁_herm : ∀ᵐ m₁ ∂μS, m₁.IsHermitian := by
        rw [ae_map_iff hS_meas.aemeasurable Matrix.isClosed_setOfPred_isHermitian.measurableSet]
        exact Eventually.of_forall hS_herm
      let rhsS : Matrix n n 𝕜 → ℝ := fun m₁ ↦ RCLike.re (NormedSpace.exp ((B + L a) + m₁)).trace
      have hrhsS_cont : Continuous rhsS :=
        RCLike.continuous_re.comp
          (NormedSpace.exp_continuous.comp (continuous_const.add continuous_id)).matrix_trace
      have hrhsS_int_μ : Integrable (fun ω ↦ rhsS (S ω)) μ := by
        simpa [rhsS, hS_apply] using (ih ht (hB.add (hL_herm a))).1
      have hrhsS_int_μS : Integrable rhsS μS :=
        (integrable_map_measure hrhsS_cont.measurable.aestronglyMeasurable
          hS_meas.aemeasurable).2 hrhsS_int_μ
      have hlieb_ae : ∀ᵐ m₁ ∂μS, ∫ m₂, Ψ (m₁, m₂) ∂μa ≤ rhsS m₁ := by
        filter_upwards [hm₁_herm] with m₁ hm₁
        have hslice_cont : Continuous (fun m₂ ↦ Ψ (m₁, m₂)) :=
          hΨ_cont.comp (continuous_const.prodMk continuous_id)
        rw [integral_map (hY_meas a).aemeasurable hslice_cont.measurable.aestronglyMeasurable]
        have hlog_eq : ∀ ω, Ψ (m₁, Y a ω) =
            RCLike.re (NormedSpace.exp ((B + m₁) + cfc Real.log (NormedSpace.exp (Y a ω)))).trace :=
          fun ω ↦ by simp [Ψ, (hY_herm a ω).cfc_log_exp]
        simp_rw [hlog_eq]
        have hlieb := (hB.add hm₁).integral_re_trace_exp_add_cfc_log_le (hY_int ha)
          (Eventually.of_forall fun ω ↦ (hY_herm a ω).posDef_exp)
        have hcomm : (B + m₁) + L a = (B + L a) + m₁ := by abel
        simpa [L, rhsS, hcomm] using hlieb
      rw [hfubini]
      calc ∫ m₁, (∫ m₂, Ψ (m₁, m₂) ∂μa) ∂μS
          ≤ ∫ m₁, rhsS m₁ ∂μS :=
            integral_mono_ae hΨ_int_prod.integral_prod_left hrhsS_int_μS hlieb_ae
        _ = ∫ ω, RCLike.re (NormedSpace.exp ((B + L a) + ∑ i ∈ t, Y i ω)).trace ∂μ := by
            rw [integral_map hS_meas.aemeasurable hrhsS_cont.measurable.aestronglyMeasurable]
            simp [rhsS, hS_apply]
        _ ≤ RCLike.re (NormedSpace.exp ((B + L a) + ∑ i ∈ t, L i)).trace :=
            (ih ht (hB.add (hL_herm a))).2
        _ = RCLike.re (NormedSpace.exp (B + ∑ i ∈ Finset.cons a t hat, L i)).trace := by
            rw [Finset.sum_cons, add_assoc]
  -- Transfer from `Y` back to `X` on `t = s`.
  obtain ⟨hY_sum_int, hY_sum_le⟩ := key s (Finset.Subset.refl s) hH
  have hsum_ae : (fun ω ↦ ∑ i ∈ s, Y i ω) =ᵐ[μ] (fun ω ↦ ∑ i ∈ s, X i ω) := by
    filter_upwards [(Filter.eventually_all_finset s).2 fun i hi ↦ (hXY_ae hi).symm] with ω hω
    exact Finset.sum_congr rfl fun i hi ↦ hω i hi
  have htrace_ae :
      (fun ω ↦ RCLike.re (NormedSpace.exp (H + ∑ i ∈ s, Y i ω)).trace) =ᵐ[μ]
        (fun ω ↦ RCLike.re (NormedSpace.exp (H + ∑ i ∈ s, X i ω)).trace) :=
    hsum_ae.mono fun ω hω ↦ by dsimp only at hω ⊢; rw [hω]
  refine ⟨hY_sum_int.congr htrace_ae, ?_⟩
  rw [← integral_congr_ae htrace_ae]
  have hL_sum : ∑ i ∈ s, L i =
      ∑ i ∈ s, cfc Real.log (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (X i ω) p q ∂μ) :=
    Finset.sum_congr rfl fun i hi ↦ hL_eq hi
  rwa [hL_sum] at hY_sum_le

/-- **Tropp's master cumulant bound** for the trace exponential of a sum of independent Hermitian
random matrices. -/
theorem integral_re_trace_exp_add_sum_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_int : ∀ i ∈ s, Integrable (fun ω ↦ NormedSpace.exp (X i ω)) μ)
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ∫ ω, RCLike.re (NormedSpace.exp (H + ∑ i ∈ s, X i ω)).trace ∂μ ≤
      RCLike.re (NormedSpace.exp (H + ∑ i ∈ s,
        cfc Real.log (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (X i ω) p q ∂μ))).trace :=
  (h_indep.integrable_and_integral_re_trace_exp_add_sum_le hX_meas hX_herm hX_int hH).2

/-- **Loewner MGF submultiplicativity.** If `X i` (`i ∈ s`) are independent and a.e. Hermitian and
each moment generating matrix `E[exp (θ • X i)]` is dominated in the Loewner order by `exp (M i)`
for deterministic Hermitian `M i`, then
`E[Re Tr (exp (θ • ∑ i ∈ s, X i))] ≤ Re Tr (exp (∑ i ∈ s, M i))`. -/
theorem integrable_and_integral_re_trace_exp_smul_sum_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} {θ : ℝ} {M : ι → Matrix n n 𝕜}
    (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_int : ∀ i ∈ s, Integrable (fun ω ↦ NormedSpace.exp (θ • X i ω)) μ)
    (hM_herm : ∀ i ∈ s, (M i).IsHermitian)
    (hM_le : ∀ i ∈ s,
      (NormedSpace.exp (M i) -
        Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • X i ω) p q ∂μ).PosSemidef) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (θ • ∑ i ∈ s, X i ω)).trace) μ ∧
      ∫ ω, RCLike.re (NormedSpace.exp (θ • ∑ i ∈ s, X i ω)).trace ∂μ ≤
        RCLike.re (NormedSpace.exp (∑ i ∈ s, M i)).trace := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hθ_indep : iIndepFun (fun i ω ↦ θ • X i ω) μ :=
    h_indep.comp (fun _ A ↦ θ • A) fun _ ↦ (continuous_const_smul θ).measurable
  have hθ_meas : ∀ i ∈ s, AEMeasurable (fun ω ↦ θ • X i ω) μ :=
    fun i hi ↦ (continuous_const_smul θ).measurable.comp_aemeasurable (hX_meas i hi)
  have hθ_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (θ • X i ω).IsHermitian :=
    fun i hi ↦ (hX_herm i hi).mono fun _ hω ↦ hω.smul (IsSelfAdjoint.all θ)
  obtain ⟨hint, hle⟩ := hθ_indep.integrable_and_integral_re_trace_exp_add_sum_le
    hθ_meas hθ_herm hX_int Matrix.isHermitian_zero
  simp only [zero_add, ← Finset.smul_sum] at hint hle
  refine ⟨hint, hle.trans ?_⟩
  let L : ι → Matrix n n 𝕜 := fun i ↦
    cfc Real.log (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • X i ω) p q ∂μ)
  have hL_herm : (∑ i ∈ s, L i).IsHermitian :=
    isHermitian_finset_sum fun _ _ ↦ Matrix.isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc
  have hM_sum_herm : (∑ i ∈ s, M i).IsHermitian := isHermitian_finset_sum hM_herm
  have hdiff_psd : ((∑ i ∈ s, M i) - ∑ i ∈ s, L i).PosSemidef := by
    rw [← Finset.sum_sub_distrib]
    classical
    have hterm : ∀ i ∈ s, (M i - L i).PosSemidef := by
      intro i hi
      set Ei : Matrix n n 𝕜 := Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • X i ω) p q ∂μ
      have hEi_entry (p q : n) : Integrable (fun ω ↦ NormedSpace.exp (θ • X i ω) p q) μ :=
        (Matrix.entryCLM p q).integrable_comp (hX_int i hi)
      have hEi_pos : Ei.PosDef := TauCeti.posDef_integral
        ((hθ_herm i hi).mono fun _ hω ↦ hω.posDef_exp) hEi_entry
      have hlog_le : (cfc Real.log (NormedSpace.exp (M i)) - cfc Real.log Ei).PosSemidef :=
        hEi_pos.cfc_log_le_cfc_log (hM_le i hi)
      rwa [(hM_herm i hi).cfc_log_exp] at hlog_le
    exact Finset.sum_induction _ Matrix.PosSemidef (fun _ _ h₁ h₂ ↦ h₁.add h₂)
      Matrix.PosSemidef.zero hterm
  exact hL_herm.re_trace_exp_mono hM_sum_herm hdiff_psd

/-- See `ProbabilityTheory.iIndepFun.integrable_and_integral_re_trace_exp_smul_sum_le` for the
paired integrability statement. -/
theorem integral_re_trace_exp_smul_sum_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} {θ : ℝ} {M : ι → Matrix n n 𝕜}
    (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_int : ∀ i ∈ s, Integrable (fun ω ↦ NormedSpace.exp (θ • X i ω)) μ)
    (hM_herm : ∀ i ∈ s, (M i).IsHermitian)
    (hM_le : ∀ i ∈ s,
      (NormedSpace.exp (M i) -
        Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • X i ω) p q ∂μ).PosSemidef) :
    ∫ ω, RCLike.re (NormedSpace.exp (θ • ∑ i ∈ s, X i ω)).trace ∂μ ≤
      RCLike.re (NormedSpace.exp (∑ i ∈ s, M i)).trace :=
  (h_indep.integrable_and_integral_re_trace_exp_smul_sum_le
    hX_meas hX_herm hX_int hM_herm hM_le).2

/-- **Matrix Laplace transform tail bound.** Under the hypotheses of
`integral_re_trace_exp_smul_sum_le`, for any `0 ≤ θ` and threshold `t : ℝ`,
`μ.real {ω | ∃ k, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k} ≤
  exp (-θ * t) * Re Tr (exp (∑ i ∈ s, M i))`. -/
theorem measureReal_exists_le_eigenvalues_sum_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} {θ t : ℝ} {M : ι → Matrix n n 𝕜}
    (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_int : ∀ i ∈ s, Integrable (fun ω ↦ NormedSpace.exp (θ • X i ω)) μ)
    (hM_herm : ∀ i ∈ s, (M i).IsHermitian)
    (hM_le : ∀ i ∈ s,
      (NormedSpace.exp (M i) -
        Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • X i ω) p q ∂μ).PosSemidef)
    (hθ : 0 ≤ θ) :
    μ.real {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k} ≤
      Real.exp (-θ * t) * RCLike.re (NormedSpace.exp (∑ i ∈ s, M i)).trace := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  obtain ⟨hint, hmgf⟩ := h_indep.integrable_and_integral_re_trace_exp_smul_sum_le
    hX_meas hX_herm hX_int hM_herm hM_le
  set f : Ω → ℝ := fun ω ↦ RCLike.re (NormedSpace.exp (θ • ∑ i ∈ s, X i ω)).trace
  have hf_nonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [(Filter.eventually_all_finset s).2 hX_herm] with ω hω
    have hS : (θ • ∑ i ∈ s, X i ω).IsHermitian :=
      (isHermitian_finset_sum hω).smul (IsSelfAdjoint.all θ)
    have hpsd : (NormedSpace.exp (θ • ∑ i ∈ s, X i ω)).PosSemidef := hS.posDef_exp.posSemidef
    rw [Pi.zero_apply, show f ω = RCLike.re (NormedSpace.exp (θ • ∑ i ∈ s, X i ω)).trace from rfl,
      hpsd.1.re_trace_eq_sum_eigenvalues]
    exact Finset.sum_nonneg fun i _ ↦ hpsd.eigenvalues_nonneg i
  have hsub : {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k} ⊆
      {ω | Real.exp (θ * t) ≤ f ω} := by
    rintro ω ⟨k, hS, htk⟩
    have hexp_cfc : NormedSpace.exp (θ • ∑ i ∈ s, X i ω) =
        cfc (fun x : ℝ ↦ Real.exp (θ * x)) (∑ i ∈ s, X i ω) := by
      have hθS : IsSelfAdjoint (θ • ∑ i ∈ s, X i ω) :=
        (hS.smul (IsSelfAdjoint.all θ)).isSelfAdjoint
      rw [← CFC.real_exp_eq_normedSpace_exp hθS,
        ← cfc_smul_id (R := ℝ) θ (∑ i ∈ s, X i ω) hS.isSelfAdjoint,
        ← cfc_comp' Real.exp (θ • ·) (∑ i ∈ s, X i ω) Real.continuous_exp.continuousOn
          (continuous_const_smul θ).continuousOn hS.isSelfAdjoint]
      rfl
    have hf_eq : f ω = ∑ j : n, Real.exp (θ * hS.eigenvalues j) := by
      simp only [f, hexp_cfc, hS.trace_cfc, map_sum, RCLike.ofReal_re]
    -- Unfold membership in `{ω | exp (θ * t) ≤ f ω}`.
    change Real.exp (θ * t) ≤ f ω
    rw [hf_eq]
    calc Real.exp (θ * t)
        ≤ Real.exp (θ * hS.eigenvalues k) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htk hθ)
      _ ≤ ∑ j : n, Real.exp (θ * hS.eigenvalues j) :=
          Finset.single_le_sum (f := fun j : n ↦ Real.exp (θ * hS.eigenvalues j))
            (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ k)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hf_nonneg hint (Real.exp (θ * t))
  calc μ.real {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k}
      ≤ μ.real {ω | Real.exp (θ * t) ≤ f ω} := measureReal_mono hsub
    _ = Real.exp (-θ * t) * (Real.exp (θ * t) * μ.real {ω | Real.exp (θ * t) ≤ f ω}) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
    _ ≤ Real.exp (-θ * t) * ∫ ω, f ω ∂μ :=
        mul_le_mul_of_nonneg_left hmarkov (Real.exp_pos _).le
    _ ≤ Real.exp (-θ * t) * RCLike.re (NormedSpace.exp (∑ i ∈ s, M i)).trace :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le

end ProbabilityTheory.iIndepFun
