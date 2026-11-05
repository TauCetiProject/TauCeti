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

Lieb's concavity theorem, Jensen's inequality on shifted cones `{A | (A - ε • 1).PosSemidef}`, and
dominated convergence yield **Lieb's expectation inequality**
`E[Re Tr (exp (B + log Z))] ≤ Re Tr (exp (B + log E[Z]))`. Iterating across independent Hermitian
summands yields **Tropp's master cumulant bound** and the **matrix Laplace transform tail bound**.

## Main results

* `Matrix.PosSemidef.re_trace_mul_nonneg`, `Matrix.PosSemidef.re_trace_mul_le`.
* `Matrix.IsHermitian.eigenvalues_mono`, `Matrix.IsHermitian.re_trace_exp_mono`.
* `Matrix.IsHermitian.integral_re_trace_exp_add_cfc_log_le`: Lieb's expectation inequality.
* `ProbabilityTheory.iIndepFun.integral_re_trace_exp_add_sum_le`: master cumulant bound.
* `ProbabilityTheory.iIndepFun.integral_re_trace_exp_smul_sum_le`: Loewner MGF submultiplicativity.
* `ProbabilityTheory.iIndepFun.measureReal_exists_le_eigenvalues_sum_le`: Laplace tail bound.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. (2012).
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator MatrixOrder Topology

noncomputable section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The real part of the trace of a Hermitian matrix equals the sum of its eigenvalues. -/
theorem IsHermitian.re_trace_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re A.trace = ∑ i, hA.eigenvalues i := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have h := hA.trace_cfc (id : ℝ → ℝ); rw [cfc_id ℝ A hA.isSelfAdjoint] at h; simp [h]

omit [DecidableEq n] in
private theorem PosSemidef.re_trace_nonneg {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    0 ≤ RCLike.re P.trace := by
  classical
  rw [hP.1.re_trace_eq_sum_eigenvalues]
  exact Finset.sum_nonneg fun i _ ↦ hP.eigenvalues_nonneg i

omit [DecidableEq n] in
/-- For positive semidefinite matrices `P` and `Q`, `0 ≤ Re Tr (P * Q)`. -/
theorem PosSemidef.re_trace_mul_nonneg {P Q : Matrix n n 𝕜} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ RCLike.re (P * Q).trace := by
  classical
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have h := hP.1.re_trace_cfc_mul_cfc hQ.1 (id : ℝ → ℝ) (id : ℝ → ℝ)
  rw [cfc_id ℝ P hP.1.isSelfAdjoint, cfc_id ℝ Q hQ.1.isSelfAdjoint] at h
  exact h.symm ▸ Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (hP.eigenvalues_nonneg i) (hQ.eigenvalues_nonneg j)) (sq_nonneg _)

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
  have hcs : ‖⟪hP.1.eigenvectorBasis i, hQ.1.eigenvectorBasis j⟫_𝕜‖ ≤ 1 :=
    (norm_inner_le_norm _ _).trans_eq <| by
      simp [hP.1.eigenvectorBasis.norm_eq_one, hQ.1.eigenvectorBasis.norm_eq_one]
  simpa only [id_eq, mul_one] using mul_le_mul_of_nonneg_left
    (by nlinarith [norm_nonneg ⟪hP.1.eigenvectorBasis i, hQ.1.eigenvectorBasis j⟫_𝕜] :
      ‖⟪hP.1.eigenvectorBasis i, hQ.1.eigenvectorBasis j⟫_𝕜‖ ^ 2 ≤ 1)
    (mul_nonneg (hP.eigenvalues_nonneg i) (hQ.eigenvalues_nonneg j))

/-- **Weyl monotonicity** of sorted eigenvalues with respect to the Loewner order. -/
theorem IsHermitian.eigenvalues₀_mono {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : (B - A).PosSemidef) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k :=
  LinearMap.IsSymmetric.eigenvalue_mono
    (isSymmetric_toEuclideanLin_iff.mpr hA) (isSymmetric_toEuclideanLin_iff.mpr hB)
    finrank_euclideanSpace (fun x ↦ by
      simpa only [map_sub, LinearMap.sub_apply, inner_sub_left, sub_nonneg] using
        (Matrix.isPositive_toEuclideanLin_iff.mpr hAB).2 x) k

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
  map_mul' _ _ := by apply Complex.ext <;> simp [RCLike.mul_re, RCLike.mul_im]
  map_zero' := by simp
  map_add' _ _ := by apply Complex.ext <;> simp
  commutes' _ := by
    apply Complex.ext <;> simp [Algebra.algebraMap_eq_smul_one, RCLike.smul_re, RCLike.smul_im]
  map_star' _ := by apply Complex.ext <;> simp [RCLike.star_def]

private theorem rclikeToComplex_injective : Function.Injective (rclikeToComplex (𝕜 := 𝕜)) :=
  fun _ _ h ↦ RCLike.ext (by simpa [rclikeToComplex] using congrArg Complex.re h)
    (by simpa [rclikeToComplex] using congrArg Complex.im h)

private def mapComplexStarAlgHom : Matrix n n 𝕜 →⋆ₐ[ℝ] Matrix n n ℂ where
  toFun M := M.map (rclikeToComplex (𝕜 := 𝕜))
  map_one' := by ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_mul' _ _ := by ext; simp [Matrix.mul_apply, map_sum]
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  commutes' r := by
    ext i j; by_cases h : i = j
    · subst h; simpa [Algebra.algebraMap_eq_smul_one, Complex.real_smul] using
        (rclikeToComplex (𝕜 := 𝕜)).commutes r
    · simp [Algebra.algebraMap_eq_smul_one, h]
  map_star' M := by ext i j; exact map_star (rclikeToComplex (𝕜 := 𝕜)) (M j i)

@[simp] private theorem mapComplexStarAlgHom_apply (M : Matrix n n 𝕜) (i j : n) :
    mapComplexStarAlgHom M i j = rclikeToComplex (M i j) := rfl

private theorem continuous_mapComplexStarAlgHom :
    Continuous (mapComplexStarAlgHom (n := n) (𝕜 := 𝕜)) :=
  continuous_matrix fun i j ↦
    ((Complex.continuous_ofReal.comp RCLike.continuous_re).add
      ((Complex.continuous_ofReal.comp RCLike.continuous_im).mul continuous_const)).comp
      ((continuous_apply j).comp (continuous_apply i))

private theorem posSemidef_iff_mapComplexStarAlgHom {M : Matrix n n 𝕜} :
    M.PosSemidef ↔ (mapComplexStarAlgHom M).PosSemidef := by
  refine ⟨fun hM ↦ ?_, fun hφM ↦ ?_⟩
  · let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    have hsq : star (CFC.sqrt M) * CFC.sqrt M = M := by
      rw [(CFC.sqrt_nonneg M).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self M hM.nonneg]
    exact Matrix.nonneg_iff_posSemidef.mp
      (by rw [← hsq, map_mul, map_star]; exact star_mul_self_nonneg _)
  · refine PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.ext fun i j ↦ rclikeToComplex_injective <| by
        simpa [Matrix.conjTranspose_apply, ← map_star] using hφM.1.apply i j) fun c ↦ ?_
    have hc := hφM.dotProduct_mulVec_nonneg (rclikeToComplex ∘ c)
    rw [← show rclikeToComplex (star c ⬝ᵥ (M *ᵥ c)) =
        star (rclikeToComplex ∘ c) ⬝ᵥ (mapComplexStarAlgHom M *ᵥ (rclikeToComplex ∘ c)) by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Function.comp_apply,
        mapComplexStarAlgHom_apply, map_sum, map_mul, map_star], Complex.nonneg_iff] at hc
    exact RCLike.nonneg_iff.mpr
      ⟨by simpa [rclikeToComplex] using hc.1, by simpa [rclikeToComplex] using hc.2.symm⟩

/-- **Operator monotonicity of the matrix logarithm.** If `A` is positive definite and `B - A` is
positive semidefinite, then `cfc Real.log B - cfc Real.log A` is positive semidefinite. -/
theorem PosDef.cfc_log_le_cfc_log {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hAB : (B - A).PosSemidef) : (cfc Real.log B - cfc Real.log A).PosSemidef := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hB : B.PosDef := by simpa [sub_add_cancel] using PosDef.posSemidef_add hAB hA
  let φ := mapComplexStarAlgHom (n := n) (𝕜 := 𝕜)
  have hφ_pos {M : Matrix n n 𝕜} (hM : M.PosDef) : IsStrictlyPositive (φ M) :=
    (hM.isUnit.map φ).isStrictlyPositive
      (posSemidef_iff_mapComplexStarAlgHom.mp hM.posSemidef).nonneg
  have hmap {M : Matrix n n 𝕜} (hM : M.PosDef) : φ (cfc Real.log M) = cfc Real.log (φ M) :=
    φ.map_cfc Real.log M (Real.continuousOn_log.mono fun x hx ↦ by
      obtain ⟨i, rfl⟩ := hM.1.spectrum_real_eq_range_eigenvalues ▸ hx
      exact (hM.eigenvalues_pos i).ne')
      continuous_mapComplexStarAlgHom hM.1.isSelfAdjoint (hφ_pos hM).isSelfAdjoint
  have hlogC : CFC.log (φ A) ≤ CFC.log (φ B) := CFC.log_le_log
    (Matrix.le_iff.mpr (by rw [← map_sub]; exact posSemidef_iff_mapComplexStarAlgHom.mp hAB))
    (hφ_pos hA)
  unfold CFC.log at hlogC
  rw [← hmap hA, ← hmap hB, Matrix.le_iff, ← map_sub] at hlogC
  exact posSemidef_iff_mapComplexStarAlgHom.mpr hlogC

section LiebExpectation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

private def entryCLM (i j : n) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    Matrix n n 𝕜 →L[ℝ] 𝕜 :=
  letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  { toLinearMap := { toFun A := A i j, map_add' _ _ := rfl, map_smul' _ _ := rfl }
    cont := (continuous_apply j).comp (continuous_apply i) }

private def reTraceMulLeftCLM (A : Matrix n n 𝕜) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    Matrix n n 𝕜 →L[ℝ] ℝ :=
  letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  { toLinearMap := { toFun M := RCLike.re (A * M).trace
                     map_add' _ _ := by simp [Matrix.mul_add, trace_add]
                     map_smul' _ _ := by simp [trace_smul, RCLike.smul_re] }
    cont := RCLike.continuous_re.comp (continuous_const.mul continuous_id).matrix_trace }

private theorem aestronglyMeasurable_cfc_log_of_posDef {W : Ω → Matrix n n 𝕜}
    (hW : AEStronglyMeasurable W μ) (hW_pos : ∀ᵐ ω ∂μ, (W ω).PosDef) :
    AEStronglyMeasurable (fun ω ↦ cfc Real.log (W ω)) μ := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hF_cont (k : ℕ) : Continuous (fun t : ℝ ↦ Real.log (max t ((k + 1 : ℝ)⁻¹))) :=
    Real.continuousOn_log.comp_continuous (continuous_id.max continuous_const) fun x ↦
      (lt_of_lt_of_le (by positivity) (le_max_right x _)).ne'
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (fun k ↦ ((TauCeti.measurable_matrix_cfc (hF_cont k)).comp_aemeasurable
      hW.aemeasurable).aestronglyMeasurable) (hW_pos.mono fun ω hω ↦ ?_)
  by_cases hn : Nonempty n
  · let c : ℝ := Finset.univ.inf' Finset.univ_nonempty hω.1.eigenvalues
    have hc : 0 < c := (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun i _ ↦ hω.eigenvalues_pos i
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hc
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun k hk ↦ cfc_congr fun t ht ↦ ?_
    obtain ⟨i, rfl⟩ := hω.1.spectrum_real_eq_range_eigenvalues ▸ ht
    exact congrArg Real.log <| max_eq_left <|
      ((by gcongr : ((k + 1 : ℝ)⁻¹) ≤ ((N + 1 : ℝ)⁻¹)).trans
        (by simpa only [one_div] using hN.le)).trans (Finset.inf'_le _ (Finset.mem_univ i))
  · have : IsEmpty n := not_nonempty_iff.mp hn
    exact tendsto_atTop_of_eventually_const (i₀ := 0) fun _ _ ↦ Subsingleton.elim _ _

private theorem re_trace_exp_add_cfc_log_bounds {B P : Matrix n n 𝕜} (hB : B.IsHermitian)
    (hP : P.PosDef) :
    0 ≤ RCLike.re (NormedSpace.exp (B + cfc Real.log P)).trace ∧
      RCLike.re (NormedSpace.exp (B + cfc Real.log P)).trace ≤
        RCLike.re (NormedSpace.exp B * P).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hlogP : (cfc Real.log P).IsHermitian := isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc
  exact ⟨(hB.add hlogP).posDef_exp.posSemidef.re_trace_nonneg,
    by simpa only [hP.exp_cfc_log] using hB.re_trace_exp_add_le hlogP⟩

private theorem integrable_re_trace_exp_add_cfc_log {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {W : Ω → Matrix n n 𝕜} (hW_int : Integrable W μ) (hW_pos : ∀ᵐ ω ∂μ, (W ω).PosDef) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (B + cfc Real.log (W ω))).trace) μ := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  have hcont : Continuous (fun M : Matrix n n 𝕜 ↦ RCLike.re (NormedSpace.exp (B + M)).trace) :=
    RCLike.continuous_re.comp
      (NormedSpace.exp_continuous.comp (continuous_const.add continuous_id)).matrix_trace
  refine ((reTraceMulLeftCLM (NormedSpace.exp B)).integrable_comp hW_int).mono'
    (hcont.comp_aestronglyMeasurable
      (aestronglyMeasurable_cfc_log_of_posDef hW_int.aestronglyMeasurable hW_pos))
    (hW_pos.mono fun ω hω ↦ ?_)
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
  set EZ : Matrix n n 𝕜 := Matrix.of fun i j ↦ ∫ ω, Z ω i j ∂μ
  have hZ_eq : ∫ ω, Z ω ∂μ = EZ :=
    Matrix.ext fun i j ↦ ((entryCLM (𝕜 := 𝕜) i j).integral_comp_comm hZ_int).symm
  have hEZ_pos : EZ.PosDef :=
    TauCeti.posDef_integral hZ_pos fun i j ↦ (entryCLM i j).integrable_comp hZ_int
  set φ : Matrix n n 𝕜 → ℝ := fun A ↦ RCLike.re (NormedSpace.exp (B + cfc Real.log A)).trace
  have hexp_cont : Continuous (fun M : Matrix n n 𝕜 ↦ RCLike.re (NormedSpace.exp (B + M)).trace) :=
    RCLike.continuous_re.comp
      (NormedSpace.exp_continuous.comp (continuous_const.add continuous_id)).matrix_trace
  have hφ_cont : ContinuousOn φ {A : Matrix n n 𝕜 | A.PosDef} :=
    hexp_cont.comp_continuousOn (Matrix.contDiffOn_cfc_log (n := n) (𝕜 := 𝕜) (k := 1)).continuousOn
  have hshift (ε : ℝ) (hε : 0 < ε) : ∫ ω, φ (Z ω + ε • 1) ∂μ ≤ φ (EZ + ε • 1) := by
    set sε : Set (Matrix n n 𝕜) := {A | (A - ε • 1).PosSemidef}
    have hsε_sub : sε ⊆ {A | A.PosDef} := fun A hA ↦ by
      simpa [sub_add_cancel] using PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hε)
    have hZε_int : Integrable (fun ω ↦ Z ω + ε • 1) μ := hZ_int.add (integrable_const _)
    have hZε_mem : ∀ᵐ ω ∂μ, Z ω + ε • 1 ∈ sε :=
      hZ_pos.mono fun ω hω ↦ by simpa [sε, add_sub_cancel_right] using hω.posSemidef
    have hjensen :=
      (hB.concaveOn_re_trace_exp_add_cfc_log_posSemidef_sub_smul_one hε).le_map_integral
        (hφ_cont.mono hsε_sub)
        (isClosed_setOfPred_posSemidef.preimage (continuous_id.sub continuous_const))
        hZε_mem hZε_int
        (integrable_re_trace_exp_add_cfc_log hB hZε_int (hZε_mem.mono fun _ h ↦ hsε_sub h))
    rwa [integral_add hZ_int (integrable_const _), hZ_eq, integral_const, probReal_univ,
      one_smul] at hjensen
  let ε : ℕ → ℝ := fun k ↦ ((k + 1 : ℝ)⁻¹)
  have hε_pos (k : ℕ) : 0 < ε k := by positivity
  have hε_tendsto : Tendsto ε atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hφ_lim {M : Matrix n n 𝕜} (hM : M.PosDef) :
      Tendsto (fun k ↦ φ (M + ε k • 1)) atTop (𝓝 (φ M)) :=
    (hφ_cont.continuousWithinAt hM).tendsto.comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using tendsto_const_nhds.add (hε_tendsto.smul_const (1 : Matrix n n 𝕜)))
        (Eventually.of_forall fun k ↦ hM.add (Matrix.PosDef.one.smul (hε_pos k)))
  have hlhs_tendsto :
      Tendsto (fun k ↦ ∫ ω, φ (Z ω + ε k • 1) ∂μ) atTop (𝓝 (∫ ω, φ (Z ω) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ω ↦ RCLike.re (NormedSpace.exp B * (Z ω + 1)).trace)
      (fun k ↦ (integrable_re_trace_exp_add_cfc_log hB (hZ_int.add (integrable_const _))
        (hZ_pos.mono fun _ hω ↦ hω.add (Matrix.PosDef.one.smul (hε_pos k)))).aestronglyMeasurable)
      ((reTraceMulLeftCLM (NormedSpace.exp B)).integrable_comp (hZ_int.add (integrable_const 1)))
      (fun k ↦ hZ_pos.mono fun ω hω ↦ ?_) (hZ_pos.mono fun _ hω ↦ hφ_lim hω)
    obtain ⟨h0, hle⟩ :=
      re_trace_exp_add_cfc_log_bounds hB (hω.add (Matrix.PosDef.one.smul (hε_pos k)))
    rw [Real.norm_of_nonneg h0]
    have hdiff_eq : (Z ω + 1) - (Z ω + ε k • 1) = (1 - ε k) • (1 : Matrix n n 𝕜) := by
      ext i j; simp [sub_smul]
    have hmono := hB.posDef_exp.posSemidef.re_trace_mul_nonneg (hdiff_eq ▸
      PosDef.one.posSemidef.smul (sub_nonneg.2 (inv_le_one_of_one_le₀ (by norm_cast; omega))))
    rw [Matrix.mul_sub, trace_sub, map_sub, sub_nonneg] at hmono
    exact hle.trans hmono
  exact le_of_tendsto_of_tendsto hlhs_tendsto (hφ_lim hEZ_pos)
    (Eventually.of_forall fun k ↦ hshift (ε k) (hε_pos k))

end LiebExpectation

end Matrix

namespace ProbabilityTheory.iIndepFun

variable {Ω ι n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Fintype n] [DecidableEq n]
  [RCLike 𝕜]

omit [Fintype n] [DecidableEq n] in
private theorem isHermitian_finset_sum {s : Finset ι} {f : ι → Matrix n n 𝕜}
    (hf : ∀ i ∈ s, (f i).IsHermitian) : (∑ i ∈ s, f i).IsHermitian :=
  Finset.sum_induction f Matrix.IsHermitian (fun _ _ h₁ h₂ ↦ h₁.add h₂)
    Matrix.isHermitian_zero hf

/-- **Tropp's master cumulant bound** (integrability and trace inequality): for independent a.e.
Hermitian `X i` (`i ∈ s`) with integrable `exp (X i)` and Hermitian `H`,
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
  let clean : Matrix n n 𝕜 → Matrix n n 𝕜 := {M | M.IsHermitian}.indicator id
  have hclean_meas : Measurable clean :=
    measurable_id.indicator Matrix.isClosed_setOfPred_isHermitian.measurableSet
  have hclean_herm (M : Matrix n n 𝕜) : (clean M).IsHermitian := by
    by_cases hM : M ∈ {M : Matrix n n 𝕜 | M.IsHermitian}
    · simpa [clean, Set.indicator_of_mem hM] using hM
    · simp [clean, Set.indicator_of_notMem hM, Matrix.isHermitian_zero]
  let Z : ι → Ω → Matrix n n 𝕜 := fun j ↦ if hj : j ∈ s then (hX_meas j hj).mk (X j) else X j
  let g : ι → Matrix n n 𝕜 → Matrix n n 𝕜 := fun j ↦ if j ∈ s then clean else fun _ ↦ 0
  let Y : ι → Ω → Matrix n n 𝕜 := fun j ω ↦ g j (Z j ω)
  have hXZ_ae (j : ι) : X j =ᵐ[μ] Z j := by
    by_cases hj : j ∈ s <;> simp [Z, hj, AEMeasurable.ae_eq_mk]
  have hg_meas (j : ι) : Measurable (g j) := by by_cases hj : j ∈ s <;> simp [g, hj, hclean_meas]
  have hY_indep : iIndepFun Y μ := (h_indep.congr hXZ_ae).comp g hg_meas
  have hY_meas (j : ι) : Measurable (Y j) := by
    by_cases hj : j ∈ s
    · exact (hg_meas j).comp (by simpa [Z, hj] using (hX_meas j hj).measurable_mk)
    · simp [Y, g, hj]
  have hY_herm (j : ι) (ω : Ω) : (Y j ω).IsHermitian := by
    by_cases hj : j ∈ s <;> simp [Y, g, hj, hclean_herm, Matrix.isHermitian_zero]
  have hXY_ae {j : ι} (hj : j ∈ s) : X j =ᵐ[μ] Y j := by
    filter_upwards [hXZ_ae j, hX_herm j hj] with ω hωZ hωH
    have hZH : Z j ω ∈ {M : Matrix n n 𝕜 | M.IsHermitian} := hωZ ▸ hωH
    simp [Y, g, clean, hj, Set.indicator_of_mem hZH, hωZ]
  have hY_int {j : ι} (hj : j ∈ s) : Integrable (fun ω ↦ NormedSpace.exp (Y j ω)) μ :=
    (hX_int j hj).congr ((hXY_ae hj).mono fun _ hω ↦ congrArg NormedSpace.exp hω)
  let L : ι → Matrix n n 𝕜 := fun i ↦
    cfc Real.log (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (Y i ω) p q ∂μ)
  have hL_herm (i : ι) : (L i).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc
  have hL_eq {i : ι} (hi : i ∈ s) :
      L i = cfc Real.log (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (X i ω) p q ∂μ) :=
    congrArg (cfc Real.log) <| Matrix.ext fun p q ↦ integral_congr_ae <|
      (hXY_ae hi).symm.mono fun _ hω ↦ by dsimp only; rw [hω]
  have key : ∀ (t : Finset ι), t ⊆ s → ∀ {B : Matrix n n 𝕜}, B.IsHermitian →
      Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (B + ∑ i ∈ t, Y i ω)).trace) μ ∧
        ∫ ω, RCLike.re (NormedSpace.exp (B + ∑ i ∈ t, Y i ω)).trace ∂μ ≤
          RCLike.re (NormedSpace.exp (B + ∑ i ∈ t, L i)).trace := fun t ↦
    Finset.cons_induction (fun _ _ _ ↦ by simp) (fun a t hat ih hcons B hB ↦ by
      have ha : a ∈ s := hcons (Finset.mem_cons_self a t)
      have ht : t ⊆ s := fun x hx ↦ hcons (Finset.mem_cons_of_mem hx)
      let S : Ω → Matrix n n 𝕜 := ∑ i ∈ t, Y i
      have hS_apply (ω : Ω) : S ω = ∑ i ∈ t, Y i ω := Finset.sum_apply ω t Y
      have hS_meas : Measurable S := by
        simpa [funext hS_apply] using Finset.measurable_sum t fun i _ ↦ hY_meas i
      have hS_herm (ω : Ω) : (S ω).IsHermitian :=
        hS_apply ω ▸ isHermitian_finset_sum fun i _ ↦ hY_herm i ω
      have hindep_Sa : IndepFun S (Y a) μ := hY_indep.indepFun_finsetSum_of_notMem hY_meas hat
      let g₁ : Matrix n n 𝕜 → ℝ := fun M ↦ RCLike.re (NormedSpace.exp (B + M)).trace
      have hg₁_cont : Continuous g₁ := RCLike.continuous_re.comp
        (NormedSpace.exp_continuous.comp (continuous_const.add continuous_id)).matrix_trace
      let trCLM : Matrix n n 𝕜 →L[ℝ] ℝ := Matrix.reTraceMulLeftCLM 1
      have hprod_int : Integrable ((g₁ ∘ S) * ((trCLM ∘ NormedSpace.exp) ∘ Y a)) μ :=
        (hindep_Sa.comp hg₁_cont.measurable
          (trCLM.continuous.comp NormedSpace.exp_continuous).measurable).integrable_mul
          (by simpa [Function.comp_def, g₁, hS_apply] using (ih ht hB).1)
          (trCLM.integrable_comp (hY_int ha))
      let Ψ : Matrix n n 𝕜 × Matrix n n 𝕜 → ℝ :=
        fun p ↦ RCLike.re (NormedSpace.exp ((B + p.1) + p.2)).trace
      have hΨ_cont : Continuous Ψ := RCLike.continuous_re.comp
        (NormedSpace.exp_continuous.comp
          ((continuous_const.add continuous_fst).add continuous_snd)).matrix_trace
      have hF_eq_Ψ :
          (fun ω ↦ RCLike.re (NormedSpace.exp (B + ∑ i ∈ Finset.cons a t hat, Y i ω)).trace) =
            fun ω ↦ Ψ (S ω, Y a ω) := by
        ext ω; simp only [Ψ, Finset.sum_cons, ← hS_apply]; congr 3; abel
      have hF_int : Integrable
          (fun ω ↦ RCLike.re (NormedSpace.exp (B + ∑ i ∈ Finset.cons a t hat, Y i ω)).trace) μ := by
        rw [hF_eq_Ψ]
        refine hprod_int.mono'
          (hΨ_cont.measurable.comp (hS_meas.prodMk (hY_meas a))).aestronglyMeasurable
          (Eventually.of_forall fun ω ↦ ?_)
        rw [Real.norm_of_nonneg
          ((hB.add (hS_herm ω)).add (hY_herm a ω)).posDef_exp.posSemidef.re_trace_nonneg]
        exact ((hB.add (hS_herm ω)).re_trace_exp_add_le (hY_herm a ω)).trans <| by
          simpa [g₁, trCLM, Matrix.reTraceMulLeftCLM] using
            (hB.add (hS_herm ω)).posDef_exp.posSemidef.re_trace_mul_le
              (hY_herm a ω).posDef_exp.posSemidef
      refine ⟨hF_int, ?_⟩
      let μS : Measure (Matrix n n 𝕜) := μ.map S
      let μa : Measure (Matrix n n 𝕜) := μ.map (Y a)
      have hpair_eq : μ.map (fun ω ↦ (S ω, Y a ω)) = μS.prod μa :=
        hindep_Sa.map_prod_eq_prod_map_map hS_meas.aemeasurable (hY_meas a).aemeasurable
      have hΨ_int_prod : Integrable Ψ (μS.prod μa) := hpair_eq ▸
        (integrable_map_measure hΨ_cont.measurable.aestronglyMeasurable
          (hS_meas.prodMk (hY_meas a)).aemeasurable).2
          (by simpa only [Function.comp_def, ← hF_eq_Ψ] using hF_int)
      let rhsS : Matrix n n 𝕜 → ℝ := fun m₁ ↦ RCLike.re (NormedSpace.exp ((B + L a) + m₁)).trace
      have hrhsS_cont : Continuous rhsS := RCLike.continuous_re.comp
        (NormedSpace.exp_continuous.comp (continuous_const.add continuous_id)).matrix_trace
      have hrhsS_int_μS : Integrable rhsS μS :=
        (integrable_map_measure hrhsS_cont.measurable.aestronglyMeasurable hS_meas.aemeasurable).2
          (by simpa only [Function.comp_def, rhsS, hS_apply] using (ih ht (hB.add (hL_herm a))).1)
      have hlieb_ae : ∀ᵐ m₁ ∂μS, ∫ m₂, Ψ (m₁, m₂) ∂μa ≤ rhsS m₁ := by
        filter_upwards [(ae_map_iff hS_meas.aemeasurable
          Matrix.isClosed_setOfPred_isHermitian.measurableSet).2 (Eventually.of_forall hS_herm)]
          with m₁ hm₁
        have hf : Continuous fun m₂ ↦ Ψ (m₁, m₂) :=
          hΨ_cont.comp (continuous_const.prodMk continuous_id)
        rw [integral_map (hY_meas a).aemeasurable hf.measurable.aestronglyMeasurable]
        simpa [Ψ, L, rhsS, fun ω ↦ (hY_herm a ω).cfc_log_exp,
          show (B + m₁) + L a = (B + L a) + m₁ by abel]
          using (hB.add hm₁).integral_re_trace_exp_add_cfc_log_le (hY_int ha)
            (Eventually.of_forall fun ω ↦ (hY_herm a ω).posDef_exp)
      calc ∫ ω, RCLike.re (NormedSpace.exp (B + ∑ i ∈ Finset.cons a t hat, Y i ω)).trace ∂μ
          = ∫ m₁, (∫ m₂, Ψ (m₁, m₂) ∂μa) ∂μS := by
            rw [hF_eq_Ψ, ← integral_map (hS_meas.prodMk (hY_meas a)).aemeasurable
              hΨ_cont.measurable.aestronglyMeasurable, hpair_eq, integral_prod Ψ hΨ_int_prod]
        _ ≤ ∫ m₁, rhsS m₁ ∂μS :=
            integral_mono_ae hΨ_int_prod.integral_prod_left hrhsS_int_μS hlieb_ae
        _ = ∫ ω, RCLike.re (NormedSpace.exp ((B + L a) + ∑ i ∈ t, Y i ω)).trace ∂μ := by
            rw [integral_map hS_meas.aemeasurable hrhsS_cont.measurable.aestronglyMeasurable]
            simp [rhsS, hS_apply]
        _ ≤ RCLike.re (NormedSpace.exp (B + ∑ i ∈ Finset.cons a t hat, L i)).trace := by
            simpa [Finset.sum_cons, add_assoc] using (ih ht (hB.add (hL_herm a))).2) t
  have htrace_ae : (fun ω ↦ RCLike.re (NormedSpace.exp (H + ∑ i ∈ s, Y i ω)).trace) =ᵐ[μ]
      fun ω ↦ RCLike.re (NormedSpace.exp (H + ∑ i ∈ s, X i ω)).trace :=
    ((Filter.eventually_all_finset s).2 fun _ hi ↦ (hXY_ae hi).symm).mono fun _ hω ↦ by
      simp only [Finset.sum_congr rfl fun i hi ↦ hω i hi]
  exact ⟨(key s Finset.Subset.rfl hH).1.congr htrace_ae, by
    simpa only [integral_congr_ae htrace_ae, Finset.sum_congr rfl fun _ hi ↦ hL_eq hi] using
      (key s Finset.Subset.rfl hH).2⟩

/-- **Tropp's master cumulant bound** for a sum of independent Hermitian random matrices. -/
theorem integral_re_trace_exp_add_sum_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_int : ∀ i ∈ s, Integrable (fun ω ↦ NormedSpace.exp (X i ω)) μ)
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ∫ ω, RCLike.re (NormedSpace.exp (H + ∑ i ∈ s, X i ω)).trace ∂μ ≤
      RCLike.re (NormedSpace.exp (H + ∑ i ∈ s,
        cfc Real.log (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (X i ω) p q ∂μ))).trace :=
  (h_indep.integrable_and_integral_re_trace_exp_add_sum_le hX_meas hX_herm hX_int hH).2

/-- **Loewner MGF submultiplicativity**: if `E[exp (θ • X i)] ≤ exp (M i)` for independent a.e.
Hermitian `X i` (`i ∈ s`), then `E[Re Tr (exp (θ • ∑ i ∈ s, X i))] ≤ Re Tr (exp (∑ i ∈ s, M i))`. -/
theorem integrable_and_integral_re_trace_exp_smul_sum_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} {θ : ℝ} {M : ι → Matrix n n 𝕜}
    (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ) (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_int : ∀ i ∈ s, Integrable (fun ω ↦ NormedSpace.exp (θ • X i ω)) μ)
    (hM_herm : ∀ i ∈ s, (M i).IsHermitian)
    (hM_le : ∀ i ∈ s, (NormedSpace.exp (M i) -
      Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • X i ω) p q ∂μ).PosSemidef) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (θ • ∑ i ∈ s, X i ω)).trace) μ ∧
      ∫ ω, RCLike.re (NormedSpace.exp (θ • ∑ i ∈ s, X i ω)).trace ∂μ ≤
        RCLike.re (NormedSpace.exp (∑ i ∈ s, M i)).trace := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hθ_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (θ • X i ω).IsHermitian :=
    fun i hi ↦ (hX_herm i hi).mono fun _ hω ↦ hω.smul (IsSelfAdjoint.all θ)
  obtain ⟨hint, hle⟩ := (h_indep.comp (fun _ A ↦ θ • A)
    fun _ ↦ (continuous_const_smul θ).measurable).integrable_and_integral_re_trace_exp_add_sum_le
    (fun i hi ↦ (continuous_const_smul θ).measurable.comp_aemeasurable (hX_meas i hi))
    hθ_herm hX_int Matrix.isHermitian_zero
  simp only [Function.comp_apply, zero_add, ← Finset.smul_sum] at hint hle
  refine ⟨hint, hle.trans <| (isHermitian_finset_sum fun _ _ ↦
    Matrix.isHermitian_iff_isSelfAdjoint.2 IsSelfAdjoint.cfc).re_trace_exp_mono
      (isHermitian_finset_sum hM_herm) ?_⟩
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ h₁ h₂ ↦ h₁.add h₂)
    Matrix.PosSemidef.zero fun i hi ↦ ?_
  have hEi_pos : (Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • X i ω) p q ∂μ).PosDef :=
    TauCeti.posDef_integral ((hθ_herm i hi).mono fun _ hω ↦ hω.posDef_exp)
      fun p q ↦ (Matrix.entryCLM p q).integrable_comp (hX_int i hi)
  simpa only [(hM_herm i hi).cfc_log_exp] using hEi_pos.cfc_log_le_cfc_log (hM_le i hi)

/-- See `ProbabilityTheory.iIndepFun.integrable_and_integral_re_trace_exp_smul_sum_le`. -/
theorem integral_re_trace_exp_smul_sum_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} {θ : ℝ} {M : ι → Matrix n n 𝕜}
    (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ) (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_int : ∀ i ∈ s, Integrable (fun ω ↦ NormedSpace.exp (θ • X i ω)) μ)
    (hM_herm : ∀ i ∈ s, (M i).IsHermitian)
    (hM_le : ∀ i ∈ s, (NormedSpace.exp (M i) -
      Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • X i ω) p q ∂μ).PosSemidef) :
    ∫ ω, RCLike.re (NormedSpace.exp (θ • ∑ i ∈ s, X i ω)).trace ∂μ ≤
      RCLike.re (NormedSpace.exp (∑ i ∈ s, M i)).trace :=
  (h_indep.integrable_and_integral_re_trace_exp_smul_sum_le
    hX_meas hX_herm hX_int hM_herm hM_le).2

/-- **Matrix Laplace transform tail bound** for `0 ≤ θ` and `t : ℝ`:
`P(∃ k, t ≤ λ_k(∑ i ∈ s, X i)) ≤ exp (-θ * t) * Re Tr (exp (∑ i ∈ s, M i))`. -/
theorem measureReal_exists_le_eigenvalues_sum_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} {θ t : ℝ} {M : ι → Matrix n n 𝕜}
    (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ) (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_int : ∀ i ∈ s, Integrable (fun ω ↦ NormedSpace.exp (θ • X i ω)) μ)
    (hM_herm : ∀ i ∈ s, (M i).IsHermitian)
    (hM_le : ∀ i ∈ s, (NormedSpace.exp (M i) -
      Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • X i ω) p q ∂μ).PosSemidef) (hθ : 0 ≤ θ) :
    μ.real {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k} ≤
      Real.exp (-θ * t) * RCLike.re (NormedSpace.exp (∑ i ∈ s, M i)).trace := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  obtain ⟨hint, hmgf⟩ := h_indep.integrable_and_integral_re_trace_exp_smul_sum_le
    hX_meas hX_herm hX_int hM_herm hM_le
  set f : Ω → ℝ := fun ω ↦ RCLike.re (NormedSpace.exp (θ • ∑ i ∈ s, X i ω)).trace
  have hf_nonneg : 0 ≤ᵐ[μ] f := ((Filter.eventually_all_finset s).2 hX_herm).mono fun _ hω ↦
    ((isHermitian_finset_sum hω).smul (IsSelfAdjoint.all θ)).posDef_exp.posSemidef.re_trace_nonneg
  have hsub : {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k} ⊆
      {ω | Real.exp (θ * t) ≤ f ω} := by
    rintro ω ⟨k, hS, htk⟩
    have hexp_cfc : NormedSpace.exp (θ • ∑ i ∈ s, X i ω) =
        cfc (fun x : ℝ ↦ Real.exp (θ * x)) (∑ i ∈ s, X i ω) := by
      rw [← CFC.real_exp_eq_normedSpace_exp (hS.smul (IsSelfAdjoint.all θ)).isSelfAdjoint,
        ← cfc_smul_id (R := ℝ) θ (∑ i ∈ s, X i ω) hS.isSelfAdjoint,
        ← cfc_comp' Real.exp (θ • ·) (∑ i ∈ s, X i ω) Real.continuous_exp.continuousOn
          (continuous_const_smul θ).continuousOn hS.isSelfAdjoint]
      rfl
    have hf_eq : f ω = ∑ j : n, Real.exp (θ * hS.eigenvalues j) := by
      simp only [f, hexp_cfc, hS.trace_cfc, map_sum, RCLike.ofReal_re]
    exact Set.mem_ofPred.mpr <| hf_eq ▸
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htk hθ)).trans
        (Finset.single_le_sum (f := fun j : n ↦ Real.exp (θ * hS.eigenvalues j))
          (fun _ _ ↦ (Real.exp_pos _).le) (Finset.mem_univ k))
  calc μ.real {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k}
      ≤ μ.real {ω | Real.exp (θ * t) ≤ f ω} := measureReal_mono hsub
    _ = Real.exp (-θ * t) * (Real.exp (θ * t) * μ.real {ω | Real.exp (θ * t) ≤ f ω}) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (-θ * t) * ∫ ω, f ω ∂μ := mul_le_mul_of_nonneg_left
        (mul_meas_ge_le_integral_of_nonneg hf_nonneg hint (Real.exp (θ * t))) (Real.exp_pos _).le
    _ ≤ Real.exp (-θ * t) * RCLike.re (NormedSpace.exp (∑ i ∈ s, M i)).trace :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le

end ProbabilityTheory.iIndepFun
