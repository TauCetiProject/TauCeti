/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.Matrix.Frobenius
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import TauCeti.Analysis.Matrix.L2OpNorm

/-!
# Bochner integration of finite matrices

Entrywise-to-Bochner bridges for finite matrices under both the entrywise `π`-norm on `m → n → E`
and the `ℓ²` operator norm (`Matrix.Norms.L2Operator`), together with entrywise integrability bounds
from operator-norm or square-integrability hypotheses and the zero-second-moment vanishing lemma.

## Main results

* `TauCeti.integrable_matrix_iff`, `TauCeti.matrix_integral_apply`, `TauCeti.integral_matrix_eq_of`:
  integrability and Bochner expectation entry-by-entry under the entrywise `π`-norm on `m → n → E`.
* `TauCeti.integrable_l2Op_matrix_iff`, `TauCeti.l2Op_matrix_integral_apply`,
  `TauCeti.integral_l2Op_matrix_eq_of`: the same under `Matrix.Norms.L2Operator`.
* `TauCeti.integrable_apply_of_ae_l2_opNorm_le`, `TauCeti.integrable_l2Op_of_ae_l2_opNorm_le`,
  `TauCeti.integrable_apply_of_integrable_l2_opNorm_sq`, `TauCeti.integrable_mul_self_apply`,
  `TauCeti.integrable_l2_opNorm_sq_of_ae_le`: entrywise and Bochner integrability under a.e.
  operator-norm or square-integrability hypotheses.
* `TauCeti.ae_eq_zero_of_sum_integral_mul_self_eq_zero`: if `∑ k ∈ s, E[X k * X k] = 0` for
  a.e. Hermitian matrices, then each `X k` vanishes almost everywhere.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory
open scoped Topology

namespace TauCeti

section EntrywisePi

variable {Ω m n E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [Fintype m] [Fintype n] [NormedAddCommGroup E]

/-- Under the entrywise `π`-norm on `m → n → E`, a matrix-valued function is integrable iff all
its entries are integrable. -/
theorem integrable_matrix_iff {F : Ω → Matrix m n E} :
    Integrable (fun ω (i : m) (j : n) ↦ F ω i j) μ ↔
      ∀ i j, Integrable (fun ω ↦ F ω i j) μ := by
  simp only [integrable_pi_iff]

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- Under the entrywise `π`-norm on `m → n → E`, entry `(i, j)` of the Bochner integral equals
the integral of entry `(i, j)`. -/
theorem matrix_integral_apply {F : Ω → Matrix m n E}
    (hF : ∀ i j, Integrable (fun ω ↦ F ω i j) μ) (i : m) (j : n) :
    (∫ ω, (fun ω (i : m) (j : n) ↦ F ω i j) ω ∂μ) i j = ∫ ω, F ω i j ∂μ := by
  rw [eval_integral (fun k ↦ Integrable.of_eval (hF k)) i, eval_integral (hF i) j]

/-- Under the entrywise `π`-norm on `m → n → E`, `Matrix.of` of the Bochner integral equals the
matrix of entrywise integrals. -/
theorem integral_matrix_eq_of {F : Ω → Matrix m n E}
    (hF : ∀ i j, Integrable (fun ω ↦ F ω i j) μ) :
    Matrix.of (∫ ω, (fun ω (i : m) (j : n) ↦ F ω i j) ω ∂μ) =
      Matrix.of fun i j ↦ ∫ ω, F ω i j ∂μ :=
  Matrix.ext (matrix_integral_apply hF)

end EntrywisePi

section L2Operator

open scoped Matrix.Norms.L2Operator

variable {Ω m n 𝕜 : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [RCLike 𝕜]

/-- `Matrix m n 𝕜` with the `ℓ²` operator norm as a normed `ℝ`-vector space, extending the native
`ℝ`-module structure so it is definitionally equal to `Matrix.l2OpNormedAlgebraReal.toNormedSpace`
when `m = n`. -/
abbrev l2OpNormedSpaceReal [Fintype m] [Fintype n] [DecidableEq n] :
    NormedSpace ℝ (Matrix m n 𝕜) where
  __ := (inferInstance : Module ℝ (Matrix m n 𝕜))
  norm_smul_le r A := by
    rw [← algebraMap_smul 𝕜 r A, norm_smul]
    simp

/-- Continuous `ℝ`-linear projection onto matrix entry `(i, j)` under `Matrix.Norms.L2Operator`. -/
private def l2OpEntryCLM [Fintype m] [Fintype n] [DecidableEq n] (i : m) (j : n) :
    letI : NormedSpace ℝ (Matrix m n 𝕜) := l2OpNormedSpaceReal
    Matrix m n 𝕜 →L[ℝ] 𝕜 :=
  letI : NormedSpace ℝ (Matrix m n 𝕜) := l2OpNormedSpaceReal
  (Matrix.entryLinearMap ℝ 𝕜 i j).mkContinuous 1 fun A ↦ by
    simpa only [one_mul, LinearMap.coe_mk, AddHom.coe_mk, Matrix.entryLinearMap_apply] using
      Matrix.norm_apply_le_l2_opNorm A i j

/-- Under `Matrix.Norms.L2Operator`, a matrix-valued function is integrable iff all its entries
are integrable. -/
theorem integrable_l2Op_matrix_iff [Fintype m] [Fintype n] [DecidableEq n]
    {F : Ω → Matrix m n 𝕜} :
    Integrable F μ ↔ ∀ i j, Integrable (fun ω ↦ F ω i j) μ := by
  classical
  let : NormedSpace ℝ (Matrix m n 𝕜) := l2OpNormedSpaceReal
  refine ⟨fun hF i j ↦ (l2OpEntryCLM i j).integrable_comp hF, fun hF ↦ ?_⟩
  have hsum : F = fun ω ↦ ∑ i : m, ∑ j : n, F ω i j • Matrix.single i j (1 : 𝕜) :=
    funext fun ω ↦ by simpa [Matrix.smul_single] using Matrix.matrix_eq_sum_single (F ω)
  rw [hsum]
  refine integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ?_
  let emb : 𝕜 →L[ℝ] Matrix m n 𝕜 :=
    { toFun := fun c ↦ c • Matrix.single i j (1 : 𝕜)
      map_add' := fun a b ↦ add_smul a b _
      map_smul' := fun r a ↦ smul_assoc r a (Matrix.single i j (1 : 𝕜))
      cont := continuous_id.smul continuous_const }
  exact emb.integrable_comp (hF i j)

/-- Under `Matrix.Norms.L2Operator`, entry `(i, j)` of the Bochner integral equals the integral of
entry `(i, j)`. -/
theorem l2Op_matrix_integral_apply [Fintype m] [Fintype n] [DecidableEq n]
    {F : Ω → Matrix m n 𝕜} (hF : Integrable F μ) (i : m) (j : n) :
    letI : NormedSpace ℝ (Matrix m n 𝕜) := l2OpNormedSpaceReal
    (∫ ω, F ω ∂μ) i j = ∫ ω, F ω i j ∂μ := by
  let : NormedSpace ℝ (Matrix m n 𝕜) := l2OpNormedSpaceReal
  exact ((l2OpEntryCLM i j).integral_comp_comm hF).symm

/-- Under `Matrix.Norms.L2Operator`, the Bochner integral of an integrable matrix-valued function
is the matrix of entrywise integrals. -/
theorem integral_l2Op_matrix_eq_of [Fintype m] [Fintype n] [DecidableEq n]
    {F : Ω → Matrix m n 𝕜} (hF : Integrable F μ) :
    letI : NormedSpace ℝ (Matrix m n 𝕜) := l2OpNormedSpaceReal
    (∫ ω, F ω ∂μ) = Matrix.of fun i j ↦ ∫ ω, F ω i j ∂μ :=
  Matrix.ext (l2Op_matrix_integral_apply hF)

/-- Entrywise integrability of an a.e. operator-norm bounded measurable random matrix. -/
theorem integrable_apply_of_ae_l2_opNorm_le [IsFiniteMeasure μ]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype m] [Fintype n] [DecidableEq n]
    {F : Ω → Matrix m n 𝕜} (hmeas : AEMeasurable F μ) {M : ℝ} (hbdd : ∀ᵐ ω ∂μ, ‖F ω‖ ≤ M)
    (i : m) (j : n) :
    Integrable (fun ω ↦ F ω i j) μ :=
  Integrable.of_bound (Matrix.measurable_apply.comp_aemeasurable hmeas).aestronglyMeasurable
    M (hbdd.mono fun ω hω ↦ (Matrix.norm_apply_le_l2_opNorm (F ω) i j).trans hω)

/-- Bochner integrability under `Matrix.Norms.L2Operator` of an a.e. operator-norm bounded
measurable random matrix. -/
theorem integrable_l2Op_of_ae_l2_opNorm_le [IsFiniteMeasure μ]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype m] [Fintype n] [DecidableEq n]
    {F : Ω → Matrix m n 𝕜} (hmeas : AEMeasurable F μ) {M : ℝ} (hbdd : ∀ᵐ ω ∂μ, ‖F ω‖ ≤ M) :
    Integrable F μ :=
  integrable_l2Op_matrix_iff.2 (integrable_apply_of_ae_l2_opNorm_le hmeas hbdd)

/-- Entrywise integrability of a square-integrable measurable random matrix on a finite measure
space. -/
theorem integrable_apply_of_integrable_l2_opNorm_sq [IsFiniteMeasure μ]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype m] [Fintype n] [DecidableEq n]
    {F : Ω → Matrix m n 𝕜} (hmeas : AEMeasurable F μ)
    (hsq : Integrable (fun ω ↦ ‖F ω‖ ^ 2) μ) (i : m) (j : n) :
    Integrable (fun ω ↦ F ω i j) μ := by
  refine ((integrable_const (1 : ℝ)).add hsq).mono
    (Matrix.measurable_apply.comp_aemeasurable hmeas).aestronglyMeasurable
    (Eventually.of_forall fun ω ↦ ?_)
  have h1 : ‖F ω i j‖ ≤ ‖F ω‖ := Matrix.norm_apply_le_l2_opNorm (F ω) i j
  have h2 : ‖F ω‖ ≤ 1 + ‖F ω‖ ^ 2 := by nlinarith [sq_nonneg (‖F ω‖ - 1 / 2)]
  simpa only [Pi.add_apply, Real.norm_of_nonneg (by positivity : 0 ≤ (1 : ℝ) + ‖F ω‖ ^ 2)] using
    h1.trans h2

/-- Entrywise integrability of `X * X` for a square-integrable measurable random square matrix. -/
theorem integrable_mul_self_apply [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]
    {X : Ω → Matrix n n 𝕜} (hmeas : AEMeasurable X μ)
    (hsq : Integrable (fun ω ↦ ‖X ω‖ ^ 2) μ) (i j : n) :
    Integrable (fun ω ↦ (X ω * X ω) i j) μ := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  refine hsq.mono
    ((Matrix.measurable_apply.comp (continuous_mul.measurable.comp
      (measurable_id.prodMk measurable_id))).comp_aemeasurable hmeas).aestronglyMeasurable
    (Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), sq]
  exact (Matrix.norm_apply_le_l2_opNorm (X ω * X ω) i j).trans (norm_mul_le (X ω) (X ω))

/-- Square-integrability of `‖F ω‖` from an a.e. operator-norm bound on a finite measure space. -/
theorem integrable_l2_opNorm_sq_of_ae_le [IsFiniteMeasure μ]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype m] [Fintype n] [DecidableEq n]
    {F : Ω → Matrix m n 𝕜} (hmeas : AEMeasurable F μ) {M : ℝ} (hbdd : ∀ᵐ ω ∂μ, ‖F ω‖ ≤ M) :
    Integrable (fun ω ↦ ‖F ω‖ ^ 2) μ :=
  Integrable.of_bound
    ((continuous_norm.pow 2).measurable.comp_aemeasurable hmeas).aestronglyMeasurable
    ((max M 0) ^ 2)
    (hbdd.mono fun ω hω ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' (by linarith [norm_nonneg (F ω), le_max_right M 0])
        (hω.trans (le_max_left M 0)))

end L2Operator

/-- If the sum of expected squares `∑ k ∈ s, E[X k * X k]` of a.e. Hermitian random matrices
with integrable squared diagonal entries vanishes, then each `X k` (`k ∈ s`) vanishes almost
everywhere. -/
theorem ae_eq_zero_of_sum_integral_mul_self_eq_zero {Ω 𝕜 n ι : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [RCLike 𝕜] [Fintype n] {s : Finset ι}
    {X : ι → Ω → Matrix n n 𝕜}
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hsq : ∀ k ∈ s, ∀ i, Integrable (fun ω ↦ (X k ω * X k ω) i i) μ)
    (hV0 : (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂μ) = 0) :
    ∀ k ∈ s, ∀ᵐ ω ∂μ, X k ω = 0 := by
  have htr_int (k : ι) (hk : k ∈ s) : Integrable (fun ω ↦ (X k ω * X k ω).trace) μ :=
    integrable_finsetSum _ fun i _ ↦ hsq k hk i
  have hre_eq (k : ι) (hk : k ∈ s) :
      ∀ᵐ ω ∂μ, RCLike.re (X k ω * X k ω).trace = ∑ i, ∑ j, ‖X k ω i j‖ ^ 2 :=
    (hherm k hk).mono fun ω hω ↦ by
      simpa only [hω.eq] using Matrix.re_trace_mul_conjTranspose_self (X k ω)
  have hre_nonneg (k : ι) (hk : k ∈ s) : 0 ≤ᵐ[μ] fun ω ↦ RCLike.re (X k ω * X k ω).trace :=
    (hre_eq k hk).mono fun _ h ↦ by
      simp only [Pi.zero_apply, h]
      exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hsum_zero : ∑ k ∈ s, ∫ ω, RCLike.re (X k ω * X k ω).trace ∂μ = 0 := by
    have h0 : RCLike.re (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂μ).trace = 0 := by
      simp [hV0]
    rw [← h0]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
    rw [Finset.sum_comm, map_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have h1 := integral_finsetSum Finset.univ fun i _ ↦ hsq k hk i
    simpa only [Matrix.trace, Matrix.diag_apply, RCLike.reCLM_apply, h1] using
      RCLike.reCLM.integral_comp_comm (htr_int k hk)
  have heach := (Finset.sum_eq_zero_iff_of_nonneg fun k hk ↦
    integral_nonneg_of_ae (hre_nonneg k hk)).1 hsum_zero
  intro k hk
  have hae0 := (integral_eq_zero_iff_of_nonneg_ae (hre_nonneg k hk)
    (RCLike.reCLM.integrable_comp (htr_int k hk))).1 (heach k hk)
  refine (hae0.and (hre_eq k hk)).mono fun ω ⟨h1, h2⟩ ↦ Matrix.ext fun i j ↦ ?_
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _).1 (h2.symm.trans h1) i (Finset.mem_univ i)
  exact norm_eq_zero.1 (sq_eq_zero_iff.1
    ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).1 hrow j (Finset.mem_univ j)))

end TauCeti
