/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Probability.Independence.Integration
public import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
public import TauCeti.Analysis.Matrix.LiebConcavity
public import TauCeti.MeasureTheory.Integral.PosSemidef
public import TauCeti.Topology.Instances.Matrix
import TauCeti.Analysis.Matrix.PosDef

/-!
# The matrix Laplace transform method and subadditivity of matrix cumulants

This file develops Joel Tropp's matrix Laplace transform method, turning Lieb's concavity theorem
from `TauCeti.Analysis.Matrix.LiebConcavity` into tail bounds for eigenvalues and operator norms of
sums of independent random Hermitian matrices over `ℝ` or `ℂ` (`[RCLike 𝕜]`).

Expectations of random matrices are written entrywise as `Matrix.of fun i j ↦ ∫ ω, A ω i j ∂P`,
matching `TauCeti.posSemidef_integral` so callers need not install a real normed-space instance on
matrices over a general `RCLike` scalar field. Under `Matrix.Norms.L2Operator`, Bochner
integrability of `A` is equivalent to entrywise integrability (`Matrix.integrable_iff`).

## Main results

* `Matrix.integrable_iff`: under the Euclidean operator norm, a random matrix is integrable if and
  only if all of its entries are integrable.
* `TauCeti.posDef_integral`: over a nonzero measure, the entrywise integral of an almost everywhere
  positive definite integrable random matrix is positive definite.
* `Matrix.IsHermitian.integral_re_trace_exp_add_cfc_log_le`: Jensen's inequality for Lieb's
  functional `A ↦ re Tr exp (H + cfc Real.log A)` on a probability space.
* `Matrix.IsHermitian.integral_re_trace_exp_add_le`: Tropp's single-step expectation bound
  `E[re Tr exp (H + X)] ≤ re Tr exp (H + log E[exp X])`.
* `ProbabilityTheory.iIndepFun.integral_re_trace_exp_sum_le`: subadditivity of matrix
  cumulant-generating functions for independent random Hermitian matrices
  `E[re Tr exp (∑ₖ Xₖ)] ≤ re Tr exp (∑ₖ log E[exp Xₖ])`.
* `Matrix.measureReal_exists_spectrum_ge_le_of_isHermitian`: the spectral exponential Markov
  inequality `P(∃ x ∈ spectrum ℝ (Y ω), t ≤ x) ≤ exp (-θ t) * E[re Tr exp (θ • Y)]`.
* `ProbabilityTheory.iIndepFun.measureReal_exists_spectrum_sum_ge_le`: Tropp's master tail bound
  from semidefinite bounds `E[exp (θ • Xₖ)] ≤ exp (Aₖ)` on each independent summand.

## References

* E. H. Lieb, *Convex trace functions and the Wigner-Yanase-Dyson conjecture*, Advances in
  Mathematics **11** (1973), 267–288.
* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Foundations of
  Computational Mathematics **12** (2012), 389–434, §3.
* J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*, Foundations and Trends in
  Machine Learning **8** (2015), §3.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology

section IntegrabilityAndOrder

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Under the Euclidean operator norm, a random matrix over `ℝ` or `ℂ` is Bochner integrable if and
only if every entry is integrable. -/
theorem Matrix.integrable_iff {m n 𝕜 : Type*} [Fintype m] [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Ω → Matrix m n 𝕜} :
    Integrable A μ ↔ ∀ i j, Integrable (fun ω ↦ A ω i j) μ := by
  constructor
  · intro hA i j
    exact hA.norm.mono'
      ((continuous_apply_apply i j).comp_aestronglyMeasurable hA.aestronglyMeasurable)
      (.of_forall fun ω ↦ (A ω).norm_apply_le_l2_opNorm i j)
  · intro h
    classical
    have hsum : A = fun ω ↦ ∑ i : m, ∑ j : n, A ω i j • Matrix.single i j (1 : 𝕜) := by
      ext ω i j
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro j' _ hj'; simp [hj']
        · intro hj; exact absurd (Finset.mem_univ j) hj
      · intro i' _ hi'; simp [hi']
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hsum]
    refine integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ?_
    refine ((h i j).norm.const_mul ‖Matrix.single i j (1 : 𝕜)‖).mono' ?_ ?_
    · exact ((continuous_id.smul continuous_const :
        Continuous fun c : 𝕜 ↦ c • Matrix.single i j (1 : 𝕜))).comp_aestronglyMeasurable
        (h i j).aestronglyMeasurable
    · exact .of_forall fun ω ↦ by rw [norm_smul, mul_comm]

/-- Over a nonzero measure, the entrywise integral of an almost everywhere positive definite
integrable random matrix is positive definite. -/
theorem TauCeti.posDef_integral {n 𝕜 : Type*} [Finite n] [RCLike 𝕜] [NeZero μ]
    {M : Ω → Matrix n n 𝕜} (hM : ∀ᵐ ω ∂μ, (M ω).PosDef)
    (hint : ∀ i j, Integrable (fun ω ↦ M ω i j) μ) :
    (Matrix.of fun i j ↦ ∫ ω, M ω i j ∂μ).PosDef := by
  have : Fintype n := Fintype.ofFinite n
  have hpsd : (Matrix.of fun i j ↦ ∫ ω, M ω i j ∂μ).PosSemidef :=
    TauCeti.posSemidef_integral (hM.mono fun _ h ↦ h.posSemidef) hint
  refine PosDef.of_dotProduct_mulVec_pos hpsd.isHermitian fun c hc ↦ ?_
  rw [RCLike.pos_iff]
  refine ⟨?_, hpsd.isHermitian.im_star_dotProduct_mulVec_self c⟩
  have hquad (ω : Ω) : RCLike.re (star c ⬝ᵥ (M ω *ᵥ c)) =
      ∑ i, ∑ j, RCLike.re (star (c i) * (M ω i j * c j)) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hint_q : Integrable (fun ω ↦ RCLike.re (star c ⬝ᵥ (M ω *ᵥ c))) μ := by
    simp_rw [hquad]
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      RCLike.reCLM.integrable_comp (((hint i j).mul_const (c j)).const_mul (star (c i)))
  have heq : RCLike.re (star c ⬝ᵥ ((Matrix.of fun i j ↦ ∫ ω, M ω i j ∂μ) *ᵥ c)) =
      ∫ ω, RCLike.re (star c ⬝ᵥ (M ω *ᵥ c)) ∂μ := by
    have h1 : star c ⬝ᵥ ((Matrix.of fun i j ↦ ∫ ω, M ω i j ∂μ) *ᵥ c) =
        ∫ ω, star c ⬝ᵥ (M ω *ᵥ c) ∂μ := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      rw [integral_finsetSum _ fun i _ ↦
        (integrable_finsetSum _ fun j _ ↦ (hint i j).mul_const (c j)).const_mul _]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ (hint i j).mul_const (c j)]
      simp only [integral_mul_const]
    have hint_c : Integrable (fun ω ↦ star c ⬝ᵥ (M ω *ᵥ c)) μ := by
      simp only [dotProduct, Matrix.mulVec]
      exact integrable_finsetSum _ fun i _ ↦
        (integrable_finsetSum _ fun j _ ↦ (hint i j).mul_const (c j)).const_mul _
    rw [h1]
    simpa using (RCLike.reCLM.integral_comp_comm hint_c).symm
  rw [heq, integral_pos_iff_support_of_nonneg_ae
    (hM.mono fun _ h ↦ (h.re_dotProduct_pos hc).le) hint_q]
  refine pos_iff_ne_zero.2 fun h0 ↦ Measure.measure_univ_ne_zero.2 (NeZero.ne μ) ?_
  have hpos : ∀ᵐ ω ∂μ, 0 < RCLike.re (star c ⬝ᵥ (M ω *ᵥ c)) :=
    hM.mono fun _ h ↦ h.re_dotProduct_pos hc
  rw [← nonpos_iff_eq_zero]
  calc μ Set.univ
      ≤ μ (Function.support fun ω ↦ RCLike.re (star c ⬝ᵥ (M ω *ᵥ c))) +
          μ (Function.support fun ω ↦ RCLike.re (star c ⬝ᵥ (M ω *ᵥ c)))ᶜ :=
        measure_univ_le_add_compl _
    _ = 0 := by
        rw [h0, zero_add]
        refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.1 hpos)
        change ¬0 < RCLike.re (star c ⬝ᵥ M ω *ᵥ c)
        rw [Function.notMem_support.1 hω]
        exact lt_irrefl 0

/-- Entrywise matrix integration is monotone with respect to the Loewner order. -/
theorem Matrix.of_integral_mono_ae {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A B : Ω → Matrix n n 𝕜} (hA : Integrable A μ) (hB : Integrable B μ)
    (hAB : ∀ᵐ ω ∂μ, A ω ≤ B ω) :
    (Matrix.of fun i j ↦ ∫ ω, A ω i j ∂μ) ≤ Matrix.of fun i j ↦ ∫ ω, B ω i j ∂μ := by
  rw [Matrix.le_iff]
  have hA' := Matrix.integrable_iff.1 hA
  have hB' := Matrix.integrable_iff.1 hB
  have hsub : (Matrix.of fun i j ↦ ∫ ω, B ω i j ∂μ) - (Matrix.of fun i j ↦ ∫ ω, A ω i j ∂μ) =
      Matrix.of fun i j ↦ ∫ ω, (B ω - A ω) i j ∂μ := by
    ext i j
    simp [integral_sub (hB' i j) (hA' i j)]
  rw [hsub]
  exact TauCeti.posSemidef_integral (hAB.mono fun _ h ↦ Matrix.le_iff.1 h)
    (Matrix.integrable_iff.1 (hB.sub hA))

end IntegrabilityAndOrder

namespace Matrix

section LiebJensen

variable {Ω n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Fintype n] [DecidableEq n]
  [RCLike 𝕜]

omit [Fintype n] [DecidableEq n] in
private theorem measurableSet_posDef_local [Finite n] :
    MeasurableSet {A : Matrix n n 𝕜 | A.PosDef} := by
  have : Fintype n := Fintype.ofFinite n
  have hset : {A : Matrix n n 𝕜 | A.PosDef} =
      {A : Matrix n n 𝕜 | A.IsHermitian} ∩
        {A : Matrix n n 𝕜 | ∀ x : n → 𝕜, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ A *ᵥ x)} := by
    ext A
    refine ⟨fun hA ↦ ⟨hA.isHermitian, fun x hx ↦ hA.re_dotProduct_pos hx⟩, ?_⟩
    rintro ⟨hAH, hpos⟩
    exact PosDef.of_dotProduct_mulVec_pos hAH fun x hx ↦
      RCLike.pos_iff.2 ⟨hpos x hx, hAH.im_star_dotProduct_mulVec_self x⟩
  rw [hset]
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet.inter
    (TauCeti.isOpen_setOfPred_re_dotProduct_pos (ι := n) (𝕜 := 𝕜)).measurableSet

omit [Fintype n] in
private theorem isClosed_Ici_smul_one [Finite n] (ε : ℝ) :
    IsClosed {M : Matrix n n 𝕜 | ε • (1 : Matrix n n 𝕜) ≤ M} := by
  have : Fintype n := Fintype.ofFinite n
  have hset : {M : Matrix n n 𝕜 | ε • (1 : Matrix n n 𝕜) ≤ M} =
      {M : Matrix n n 𝕜 | (M - ε • (1 : Matrix n n 𝕜)).IsHermitian} ∩
        ⋂ x : n → 𝕜,
          {M : Matrix n n 𝕜 | 0 ≤ RCLike.re (star x ⬝ᵥ (M - ε • (1 : Matrix n n 𝕜)) *ᵥ x)} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Matrix.le_iff]
    refine ⟨fun h ↦ ⟨h.isHermitian, h.re_dotProduct_nonneg⟩, fun ⟨hH, hq⟩ ↦ ?_⟩
    exact PosSemidef.of_dotProduct_mulVec_nonneg hH fun x ↦
      RCLike.nonneg_iff.2 ⟨hq x, hH.im_star_dotProduct_mulVec_self x⟩
  rw [hset]
  refine IsClosed.inter ?_ (isClosed_iInter fun x ↦ isClosed_le continuous_const ?_)
  · exact isClosed_eq (continuous_id.sub continuous_const).matrix_conjTranspose
      (continuous_id.sub continuous_const)
  · have hcont : Continuous
        fun M : Matrix n n 𝕜 ↦ RCLike.re (star x ⬝ᵥ (M - ε • (1 : Matrix n n 𝕜)) *ᵥ x) := by
      fun_prop
    exact hcont

/-- Lieb's functional `ω ↦ re Tr exp (H + cfc Real.log (A ω))` is integrable whenever `H` is
Hermitian and `A` is an integrable almost everywhere positive definite random matrix. -/
theorem IsHermitian.integrable_re_trace_exp_add_cfc_log {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    {A : Ω → Matrix n n 𝕜} (hA : Integrable A P) (hA_pos : ∀ᵐ ω ∂P, (A ω).PosDef) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log (A ω))).trace) P := by
  set g : Matrix n n 𝕜 → ℝ := fun M ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log M)).trace
  have hA_meas : AEMeasurable A P := hA.aestronglyMeasurable.aemeasurable
  have hmap_ae : ∀ᵐ M ∂P.map A, M ∈ {M : Matrix n n 𝕜 | M.PosDef} :=
    (ae_map_iff hA_meas measurableSet_posDef_local).2 hA_pos
  have hg_map : AEMeasurable g (P.map A) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hmap_ae]
    exact (continuousOn_re_trace_exp_add_cfc_log H).aemeasurable measurableSet_posDef_local
  have hg_aesm : AEStronglyMeasurable (fun ω ↦ g (A ω)) P :=
    (hg_map.comp_aemeasurable hA_meas).aestronglyMeasurable
  refine (hA.norm.const_mul (Real.exp ‖H‖ * Fintype.card n)).mono' hg_aesm ?_
  filter_upwards [hA_pos] with ω hω
  rw [Real.norm_of_nonneg (hH.re_trace_exp_add_cfc_log_nonneg (A ω))]
  calc g (A ω)
      ≤ Real.exp ‖H‖ * RCLike.re (A ω).trace := hω.re_trace_exp_add_cfc_log_le hH
    _ ≤ Real.exp ‖H‖ * ‖(A ω).trace‖ := by
        gcongr
        exact RCLike.re_le_norm _
    _ ≤ Real.exp ‖H‖ * (Fintype.card n * ‖A ω‖) := by
        gcongr
        exact norm_trace_le_card_mul_l2_opNorm (A ω)
    _ = Real.exp ‖H‖ * Fintype.card n * ‖A ω‖ := by ring

private theorem integral_re_trace_exp_add_cfc_log_le_shift [IsProbabilityMeasure P]
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) {A : Ω → Matrix n n 𝕜} (hA : Integrable A P)
    (hA_pos : ∀ᵐ ω ∂P, (A ω).PosDef) {ε : ℝ} (hε : 0 < ε) :
    let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    ∫ ω, RCLike.re (NormedSpace.exp (H + cfc Real.log (A ω))).trace ∂P ≤
      RCLike.re (NormedSpace.exp
        (H + cfc Real.log ((∫ ω, A ω ∂P) + ε • (1 : Matrix n n 𝕜)))).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  set g : Matrix n n 𝕜 → ℝ := fun M ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log M)).trace
  set S := {M : Matrix n n 𝕜 | ε • (1 : Matrix n n 𝕜) ≤ M}
  have hS_sub : S ⊆ {M : Matrix n n 𝕜 | M.PosDef} := fun M hM ↦ by
    have hsub : M = ε • 1 + (M - ε • 1) := by abel
    exact hsub ▸ (PosDef.one.smul hε).add_posSemidef (Matrix.le_iff.1 hM)
  have hS_conv : Convex ℝ S := fun M₁ h₁ M₂ h₂ a b ha hb hab ↦ by
    change ε • 1 ≤ a • M₁ + b • M₂
    have h1 : ε • (1 : Matrix n n 𝕜) = a • (ε • 1) + b • (ε • 1) := by
      rw [← add_smul, hab, one_smul]
    exact h1 ▸ add_le_add (smul_le_smul_of_nonneg_left h₁ ha) (smul_le_smul_of_nonneg_left h₂ hb)
  have hAε_int : Integrable (fun ω ↦ A ω + ε • 1) P := hA.add (integrable_const _)
  have hAε_mem : ∀ᵐ ω ∂P, A ω + ε • 1 ∈ S := hA_pos.mono fun ω hω ↦ by
    change ε • 1 ≤ A ω + ε • 1
    simpa using add_le_add_left hω.posSemidef.nonneg (ε • 1)
  have hAε_pos : ∀ᵐ ω ∂P, (A ω + ε • 1).PosDef := hAε_mem.mono fun _ h ↦ hS_sub h
  have hjensen := (hH.concaveOn_re_trace_exp_add_cfc_log.subset hS_sub hS_conv).le_map_integral
    ((continuousOn_re_trace_exp_add_cfc_log H).mono hS_sub) (isClosed_Ici_smul_one ε) hAε_mem
    hAε_int (hH.integrable_re_trace_exp_add_cfc_log hAε_int hAε_pos)
  have hint_shift : ∫ ω, (A ω + ε • 1) ∂P = (∫ ω, A ω ∂P) + ε • 1 := by
    rw [integral_add hA (integrable_const _), integral_const, probReal_univ, one_smul]
  calc ∫ ω, g (A ω) ∂P
      ≤ ∫ ω, g (A ω + ε • 1) ∂P := by
        refine integral_mono_ae (hH.integrable_re_trace_exp_add_cfc_log hA hA_pos)
          (hH.integrable_re_trace_exp_add_cfc_log hAε_int hAε_pos) ?_
        filter_upwards [hA_pos] with ω hω
        exact hω.re_trace_exp_add_cfc_log_mono hH
          (le_add_of_nonneg_right (PosDef.one.smul hε).posSemidef.nonneg)
    _ ≤ g ((∫ ω, A ω ∂P) + ε • 1) := hint_shift ▸ hjensen

/-- **Expectation form of Lieb's concavity theorem** (Tropp 2012, Lemma 3.3). For a deterministic
Hermitian matrix `H` and an integrable almost everywhere positive definite random matrix `A` on a
probability space,
`E[re Tr exp (H + log A)] ≤ re Tr exp (H + log E[A])`. -/
theorem IsHermitian.integral_re_trace_exp_add_cfc_log_le [IsProbabilityMeasure P]
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) {A : Ω → Matrix n n 𝕜} (hA : Integrable A P)
    (hA_pos : ∀ᵐ ω ∂P, (A ω).PosDef) :
    ∫ ω, RCLike.re (NormedSpace.exp (H + cfc Real.log (A ω))).trace ∂P ≤
      RCLike.re (NormedSpace.exp
        (H + cfc Real.log (Matrix.of fun i j ↦ ∫ ω, A ω i j ∂P))).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  set g : Matrix n n 𝕜 → ℝ := fun M ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log M)).trace
  have hEA_eq : ∫ ω, A ω ∂P = Matrix.of fun i j ↦ ∫ ω, A ω i j ∂P := by
    ext i j
    let proj : Matrix n n 𝕜 →L[ℝ] 𝕜 :=
      ⟨{ toFun := fun M ↦ M i j, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl },
        continuous_apply_apply i j⟩
    exact (proj.integral_comp_comm hA).symm
  set EA := ∫ ω, A ω ∂P
  have hEA_pos : EA.PosDef := hEA_eq ▸ TauCeti.posDef_integral hA_pos (Matrix.integrable_iff.1 hA)
  rw [← hEA_eq]
  have hcont_at : ContinuousWithinAt g {M : Matrix n n 𝕜 | M.PosDef} EA :=
    continuousOn_re_trace_exp_add_cfc_log H EA hEA_pos
  have htend_shift : Tendsto (fun ε : ℝ ↦ EA + ε • (1 : Matrix n n 𝕜)) (𝓝[>] 0)
      (𝓝[{M : Matrix n n 𝕜 | M.PosDef}] EA) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ε hε ↦
      hEA_pos.add (PosDef.one.smul hε)⟩
    have h0 : Tendsto (fun ε : ℝ ↦ EA + ε • (1 : Matrix n n 𝕜)) (𝓝 0) (𝓝 (EA + (0 : ℝ) • 1)) :=
      continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    simpa using h0.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto (hcont_at.tendsto.comp htend_shift)
    (eventually_nhdsWithin_of_forall fun _ hε ↦
      integral_re_trace_exp_add_cfc_log_le_shift hH hA hA_pos hε)

/-- **Tropp's single-step expectation bound** (Tropp 2012, Corollary 3.3). For deterministic
Hermitian `H` and an almost everywhere Hermitian random matrix `X` with integrable matrix
exponential on a probability space,
`E[re Tr exp (H + X)] ≤ re Tr exp (H + log E[exp X])`. -/
theorem IsHermitian.integral_re_trace_exp_add_le [IsProbabilityMeasure P]
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) {X : Ω → Matrix n n 𝕜}
    (hX_herm : ∀ᵐ ω ∂P, (X ω).IsHermitian)
    (hX_int : Integrable (fun ω ↦ NormedSpace.exp (X ω)) P) :
    ∫ ω, RCLike.re (NormedSpace.exp (H + X ω)).trace ∂P ≤
      RCLike.re (NormedSpace.exp
        (H + cfc Real.log (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (X ω) i j ∂P))).trace := by
  have hpos : ∀ᵐ ω ∂P, (NormedSpace.exp (X ω)).PosDef := hX_herm.mono fun _ h ↦ h.posDef_exp
  have hcongr : (fun ω ↦ RCLike.re (NormedSpace.exp (H + X ω)).trace) =ᵐ[P]
      fun ω ↦ RCLike.re (NormedSpace.exp (H + cfc Real.log (NormedSpace.exp (X ω)))).trace :=
    hX_herm.mono fun ω hω ↦ by dsimp only; rw [hω.cfc_log_exp]
  rw [integral_congr_ae hcongr]
  exact hH.integral_re_trace_exp_add_cfc_log_le hX_int hpos

end LiebJensen

/-! ### Deterministic exponential domination for sums of Hermitian matrices -/

section ExpDomination

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

omit [Fintype n] [DecidableEq n] in
private theorem isHermitian_smul_real {M : Matrix n n 𝕜} (hM : M.IsHermitian) (c : ℝ) :
    (c • M).IsHermitian := by
  simp [Matrix.IsHermitian, conjTranspose_smul, hM.eq]

omit [Fintype n] [DecidableEq n] in
private theorem isHermitian_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Matrix n n 𝕜}
    (hf : ∀ k ∈ s, (f k).IsHermitian) : (∑ k ∈ s, f k).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_sum]
  exact Finset.sum_congr rfl fun k hk ↦ (hf k hk).eq

private theorem cfc_log_one_eq_zero : cfc Real.log (1 : Matrix n n 𝕜) = 0 := by
  simp

private theorem exp_smul_one_eq (c : ℝ) :
    NormedSpace.exp (c • (1 : Matrix n n 𝕜)) = Real.exp c • (1 : Matrix n n 𝕜) := by
  have hc : (Real.exp c • (1 : Matrix n n 𝕜)).PosDef := PosDef.one.smul (Real.exp_pos c)
  have hlog : cfc Real.log (Real.exp c • (1 : Matrix n n 𝕜)) = c • (1 : Matrix n n 𝕜) := by
    rw [PosDef.one.cfc_log_smul (Real.exp_pos c), Real.log_exp, cfc_log_one_eq_zero, add_zero]
  rw [← hlog, hc.exp_cfc_log]

private theorem re_trace_exp_smul_one (c : ℝ) :
    RCLike.re (NormedSpace.exp (c • (1 : Matrix n n 𝕜))).trace =
      Fintype.card n * Real.exp c := by
  rw [exp_smul_one_eq, trace_smul, trace_one, RCLike.smul_re, RCLike.natCast_re, mul_comm]

private theorem re_trace_exp_add_add_le {H A B : Matrix n n 𝕜} (hH : H.IsHermitian)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (NormedSpace.exp (H + (A + B))).trace ≤
      Fintype.card n * Real.exp ‖H‖ * ‖NormedSpace.exp A‖ * ‖NormedSpace.exp B‖ := by
  by_cases hn : Nonempty n
  · have hpos_n : ∀ {M : Matrix n n 𝕜}, M.PosDef → 0 < ‖M‖ := fun {M} hM ↦ by
      obtain ⟨i⟩ := hn
      let v : n → 𝕜 := fun j ↦ if j = i then 1 else 0
      have hne : v ≠ 0 := fun h ↦ (one_ne_zero : (1 : 𝕜) ≠ 0) (by simpa [v] using congr_fun h i)
      have h1 : 0 < RCLike.re (M i i) := by
        simpa [v, Matrix.mulVec, dotProduct] using hM.re_dotProduct_pos hne
      exact h1.trans_le ((RCLike.re_le_norm _).trans (M.norm_apply_le_l2_opNorm i i))
    have hlog_le : ∀ {M : Matrix n n 𝕜}, M.IsHermitian →
        M ≤ Real.log ‖NormedSpace.exp M‖ • (1 : Matrix n n 𝕜) := fun {M} hM ↦ by
      have hexp := hM.posDef_exp
      have hle := hexp.cfc_log_le_cfc_log hexp.isHermitian.le_l2_opNorm_smul_one
      rwa [hM.cfc_log_exp, PosDef.one.cfc_log_smul (hpos_n hexp), cfc_log_one_eq_zero,
        add_zero] at hle
    set c := ‖H‖ + (Real.log ‖NormedSpace.exp A‖ + Real.log ‖NormedSpace.exp B‖)
    have hsum_le : H + (A + B) ≤ c • (1 : Matrix n n 𝕜) := by
      rw [add_smul, add_smul]
      exact add_le_add hH.le_l2_opNorm_smul_one (add_le_add (hlog_le hA) (hlog_le hB))
    calc RCLike.re (NormedSpace.exp (H + (A + B))).trace
        ≤ RCLike.re (NormedSpace.exp (c • (1 : Matrix n n 𝕜))).trace :=
          IsHermitian.re_trace_exp_le_of_le (hH.add (hA.add hB))
            (isHermitian_smul_real isHermitian_one c) hsum_le
      _ = Fintype.card n * Real.exp c := re_trace_exp_smul_one c
      _ = Fintype.card n * Real.exp ‖H‖ * ‖NormedSpace.exp A‖ * ‖NormedSpace.exp B‖ := by
          simp only [c, Real.exp_add, Real.exp_log (hpos_n hA.posDef_exp),
            Real.exp_log (hpos_n hB.posDef_exp)]
          ring
  · have : IsEmpty n := not_nonempty_iff.1 hn
    simp

private theorem norm_exp_add_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖NormedSpace.exp (A + B)‖ ≤
      Fintype.card n * ‖NormedSpace.exp A‖ * ‖NormedSpace.exp B‖ := by
  have hexp := (hA.add hB).posDef_exp
  have hnorm : ‖NormedSpace.exp (A + B)‖ ≤ RCLike.re (NormedSpace.exp (A + B)).trace := by
    rw [hexp.isHermitian.l2_opNorm_eq_norm_eigenvalues, hexp.isHermitian.trace_eq_sum_eigenvalues]
    simp only [map_sum, RCLike.ofReal_re]
    refine (pi_norm_le_iff_of_nonneg
      (Finset.sum_nonneg fun i _ ↦ (hexp.eigenvalues_pos i).le)).2 fun i ↦ ?_
    rw [Real.norm_of_nonneg (hexp.eigenvalues_pos i).le]
    exact Finset.single_le_sum (fun j _ ↦ (hexp.eigenvalues_pos j).le) (Finset.mem_univ i)
  have h := re_trace_exp_add_add_le (isHermitian_zero : (0 : Matrix n n 𝕜).IsHermitian) hA hB
  rw [zero_add, norm_zero, Real.exp_zero, mul_one] at h
  exact hnorm.trans h

end ExpDomination

/-! ### Spectral exponential Markov inequality -/

section SpectralMarkov

variable {Ω n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Fintype n] [DecidableEq n]
  [RCLike 𝕜]

private theorem exp_mul_le_re_trace_exp_smul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {θ t x : ℝ} (hθ : 0 ≤ θ) (hx : x ∈ spectrum ℝ A) (htx : t ≤ x) :
    Real.exp (θ * t) ≤ RCLike.re (NormedSpace.exp (θ • A)).trace := by
  have hθA : (θ • A).IsHermitian := isHermitian_smul_real hA θ
  have hx_smul : θ * x ∈ spectrum ℝ (θ • A) := by
    have : IsSelfAdjoint A := isHermitian_iff_isSelfAdjoint.1 hA
    have hcfc : cfc (fun u : ℝ ↦ θ * u) A = θ • A := by
      rw [show (fun u : ℝ ↦ θ * u) = fun u : ℝ ↦ θ • id u from rfl,
        cfc_smul θ (id : ℝ → ℝ) A, cfc_id ℝ A]
    rw [← hcfc, cfc_map_spectrum (fun u : ℝ ↦ θ * u) A]
    exact ⟨x, hx, rfl⟩
  rw [hθA.spectrum_real_eq_range_eigenvalues] at hx_smul
  obtain ⟨i, hi⟩ := hx_smul
  rw [hθA.trace_exp_eq_sum_exp_eigenvalues, map_sum]
  simp only [RCLike.ofReal_re]
  calc Real.exp (θ * t)
      ≤ Real.exp (θ * x) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htx hθ)
    _ = Real.exp (hθA.eigenvalues i) := by rw [hi]
    _ ≤ ∑ j, Real.exp (hθA.eigenvalues j) :=
        Finset.single_le_sum (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i)

/-- **Spectral exponential Markov inequality** (Tropp 2012, Proposition 3.1). For an almost
everywhere Hermitian random matrix `Y` on a finite measure space, any `θ ≥ 0`, and any threshold
`t : ℝ`,
`P(∃ x ∈ spectrum ℝ (Y ω), t ≤ x) ≤ exp (-θ * t) * E[re Tr exp (θ • Y)]`. -/
theorem measureReal_exists_spectrum_ge_le_of_isHermitian [IsFiniteMeasure P]
    {Y : Ω → Matrix n n 𝕜} (hY_herm : ∀ᵐ ω ∂P, (Y ω).IsHermitian)
    {θ : ℝ} (hθ : 0 ≤ θ) (t : ℝ)
    (hint : Integrable (fun ω ↦ NormedSpace.exp (θ • Y ω)) P) :
    P.real {ω | ∃ x ∈ spectrum ℝ (Y ω), t ≤ x} ≤
      Real.exp (-θ * t) * ∫ ω, RCLike.re (NormedSpace.exp (θ • Y ω)).trace ∂P := by
  set Z : Ω → ℝ := fun ω ↦ RCLike.re (NormedSpace.exp (θ • Y ω)).trace
  have hZ_int : Integrable Z P := by
    refine (hint.norm.const_mul (Fintype.card n : ℝ)).mono'
      ((RCLike.continuous_re.comp continuous_id.matrix_trace).comp_aestronglyMeasurable
        hint.aestronglyMeasurable)
      (.of_forall fun ω ↦ ?_)
    exact (RCLike.norm_re_le_norm _).trans (norm_trace_le_card_mul_l2_opNorm _)
  have hZ_nonneg : 0 ≤ᵐ[P] Z := hY_herm.mono fun ω hω ↦ by
    have hpos := (isHermitian_smul_real hω θ).posDef_exp
    change 0 ≤ RCLike.re (NormedSpace.exp (θ • Y ω)).trace
    rw [hpos.isHermitian.trace_eq_sum_eigenvalues]
    simp only [map_sum, RCLike.ofReal_re]
    exact Finset.sum_nonneg fun i _ ↦ (hpos.eigenvalues_pos i).le
  have hsub : P.real {ω | ∃ x ∈ spectrum ℝ (Y ω), t ≤ x} ≤
      P.real {ω | Real.exp (θ * t) ≤ Z ω} := by
    have hincl : {ω | ∃ x ∈ spectrum ℝ (Y ω), t ≤ x} ⊆
        {ω | Real.exp (θ * t) ≤ Z ω} ∪ {ω | ¬(Y ω).IsHermitian} := by
      rintro ω ⟨x, hx, htx⟩
      by_cases hYω : (Y ω).IsHermitian
      · exact Or.inl (exp_mul_le_re_trace_exp_smul hYω hθ hx htx)
      · exact Or.inr hYω
    have hnull : P.real {ω | ¬(Y ω).IsHermitian} = 0 := by
      simp [measureReal_def, ae_iff.1 hY_herm]
    calc P.real {ω | ∃ x ∈ spectrum ℝ (Y ω), t ≤ x}
        ≤ P.real ({ω | Real.exp (θ * t) ≤ Z ω} ∪ {ω | ¬(Y ω).IsHermitian}) :=
          measureReal_mono hincl
      _ ≤ P.real {ω | Real.exp (θ * t) ≤ Z ω} + P.real {ω | ¬(Y ω).IsHermitian} :=
          measureReal_union_le _ _
      _ = P.real {ω | Real.exp (θ * t) ≤ Z ω} := by rw [hnull, add_zero]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hZ_nonneg hZ_int (Real.exp (θ * t))
  calc P.real {ω | ∃ x ∈ spectrum ℝ (Y ω), t ≤ x}
      ≤ P.real {ω | Real.exp (θ * t) ≤ Z ω} := hsub
    _ = Real.exp (-θ * t) * (Real.exp (θ * t) * P.real {ω | Real.exp (θ * t) ≤ Z ω}) := by
        rw [← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-θ * t) * ∫ ω, Z ω ∂P :=
        mul_le_mul_of_nonneg_left hmarkov (Real.exp_pos _).le

end SpectralMarkov

end Matrix

/-! ### Subadditivity of matrix cumulants and Tropp's master tail bound -/

namespace ProbabilityTheory.iIndepFun

variable {Ω ι n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Fintype n] [DecidableEq n]
  [RCLike 𝕜]

private theorem continuous_exp_matrix :
    Continuous (NormedSpace.exp : Matrix n n 𝕜 → Matrix n n 𝕜) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := .restrictScalars ℚ ℝ _
  exact NormedSpace.exp_continuous

private theorem indepFun_integrable_exp_and_trace {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    {U V : Ω → Matrix n n 𝕜} (hUV : U ⟂ᵢ[P] V) (hU_meas : AEMeasurable U P)
    (hV_meas : AEMeasurable V P) (hU_herm : ∀ᵐ ω ∂P, (U ω).IsHermitian)
    (hV_herm : ∀ᵐ ω ∂P, (V ω).IsHermitian)
    (hU_int : Integrable (fun ω ↦ NormedSpace.exp (U ω)) P)
    (hV_int : Integrable (fun ω ↦ NormedSpace.exp (V ω)) P) :
    Integrable (fun ω ↦ NormedSpace.exp (U ω + V ω)) P ∧
      Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (H + (U ω + V ω))).trace) P := by
  have hexp_cont : Continuous (NormedSpace.exp : Matrix n n 𝕜 → Matrix n n 𝕜) :=
    continuous_exp_matrix
  have hnorm_indep : (fun ω ↦ ‖NormedSpace.exp (U ω)‖) ⟂ᵢ[P] (fun ω ↦ ‖NormedSpace.exp (V ω)‖) :=
    hUV.comp₀ hU_meas hV_meas (continuous_norm.comp hexp_cont).measurable.aemeasurable
      (continuous_norm.comp hexp_cont).measurable.aemeasurable
  have hprod_int : Integrable (fun ω ↦ ‖NormedSpace.exp (U ω)‖ * ‖NormedSpace.exp (V ω)‖) P :=
    hnorm_indep.integrable_mul hU_int.norm hV_int.norm
  have hsum_asm : AEStronglyMeasurable (fun ω ↦ U ω + V ω) P :=
    hU_meas.aestronglyMeasurable.add hV_meas.aestronglyMeasurable
  refine ⟨(hprod_int.const_mul (Fintype.card n : ℝ)).mono'
    (hexp_cont.comp_aestronglyMeasurable hsum_asm) ?_, ?_⟩
  · filter_upwards [hU_herm, hV_herm] with ω hUω hVω
    simpa [mul_assoc] using Matrix.norm_exp_add_le hUω hVω
  · have hcont : Continuous
        (fun M : Matrix n n 𝕜 ↦ RCLike.re (NormedSpace.exp (H + M)).trace) :=
      RCLike.continuous_re.comp <| continuous_id.matrix_trace.comp <|
        hexp_cont.comp (continuous_const.add continuous_id)
    refine (hprod_int.const_mul (Fintype.card n * Real.exp ‖H‖)).mono'
      (hcont.comp_aestronglyMeasurable hsum_asm) ?_
    filter_upwards [hU_herm, hV_herm] with ω hUω hVω
    have hpos := (hH.add (hUω.add hVω)).posDef_exp
    have hnn : 0 ≤ RCLike.re (NormedSpace.exp (H + (U ω + V ω))).trace := by
      rw [hpos.isHermitian.trace_eq_sum_eigenvalues]
      simp only [map_sum, RCLike.ofReal_re]
      exact Finset.sum_nonneg fun i _ ↦ (hpos.eigenvalues_pos i).le
    rw [Real.norm_of_nonneg hnn]
    simpa [mul_assoc] using Matrix.re_trace_exp_add_add_le hH hUω hVω

private theorem indepFun_step [IsProbabilityMeasure P] {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    {U V : Ω → Matrix n n 𝕜} (hUV : U ⟂ᵢ[P] V) (hU_meas : AEMeasurable U P)
    (hV_meas : AEMeasurable V P) (hU_herm : ∀ᵐ ω ∂P, (U ω).IsHermitian)
    (hV_herm : ∀ᵐ ω ∂P, (V ω).IsHermitian)
    (hU_int : Integrable (fun ω ↦ NormedSpace.exp (U ω)) P)
    (hV_int : Integrable (fun ω ↦ NormedSpace.exp (V ω)) P) :
    Integrable (fun ω ↦ NormedSpace.exp (U ω + V ω)) P ∧
      ∫ ω, RCLike.re (NormedSpace.exp (H + (U ω + V ω))).trace ∂P ≤
        ∫ ω, RCLike.re (NormedSpace.exp
          ((H + cfc Real.log (Matrix.of fun i j ↦ ∫ ω', NormedSpace.exp (U ω') i j ∂P)) +
            V ω)).trace ∂P := by
  obtain ⟨hUV_exp_int, hΦ_comp_int⟩ :=
    indepFun_integrable_exp_and_trace hH hUV hU_meas hV_meas hU_herm hV_herm hU_int hV_int
  refine ⟨hUV_exp_int, ?_⟩
  set Φ : Matrix n n 𝕜 × Matrix n n 𝕜 → ℝ :=
    fun p ↦ RCLike.re (NormedSpace.exp (H + (p.1 + p.2))).trace
  have hΦ_cont : Continuous Φ :=
    RCLike.continuous_re.comp <| continuous_id.matrix_trace.comp <|
      continuous_exp_matrix.comp (continuous_const.add (continuous_fst.add continuous_snd))
  have hmap_prod : P.map (fun ω ↦ (U ω, V ω)) = (P.map U).prod (P.map V) :=
    hUV.map_prod_eq_prod_map_map hU_meas hV_meas
  have hΦ_prod_int : Integrable Φ ((P.map U).prod (P.map V)) := by
    rw [← hmap_prod]
    exact (integrable_map_measure hΦ_cont.aestronglyMeasurable (hU_meas.prodMk hV_meas)).2
      hΦ_comp_int
  have : IsProbabilityMeasure (P.map U) := (Measure.isProbabilityMeasure_map_iff hU_meas).2 ‹_›
  have : IsProbabilityMeasure (P.map V) := (Measure.isProbabilityMeasure_map_iff hV_meas).2 ‹_›
  have hslice_eq (ω : Ω) :
      ∫ ω', RCLike.re (NormedSpace.exp ((H + V ω) + U ω')).trace ∂P =
        ∫ u, Φ (u, V ω) ∂P.map U := by
    have hcont_slice : Continuous (fun u : Matrix n n 𝕜 ↦ Φ (u, V ω)) :=
      hΦ_cont.comp (continuous_id.prodMk continuous_const)
    rw [integral_map hU_meas hcont_slice.aestronglyMeasurable]
    congr 1 with ω'
    dsimp only [Φ]
    rw [add_comm (U ω') (V ω), add_assoc]
  have hfubini : ∫ ω, Φ (U ω, V ω) ∂P =
      ∫ ω, (∫ ω', RCLike.re (NormedSpace.exp ((H + V ω) + U ω')).trace ∂P) ∂P := by
    rw [← integral_map (hU_meas.prodMk hV_meas) hΦ_cont.aestronglyMeasurable, hmap_prod,
      integral_prod_symm Φ hΦ_prod_int,
      integral_map hV_meas hΦ_prod_int.integral_prod_right.aestronglyMeasurable]
    exact integral_congr_ae (.of_forall fun ω ↦ (hslice_eq ω).symm)
  rw [hfubini]
  set LU := cfc Real.log (Matrix.of fun i j ↦ ∫ ω', NormedSpace.exp (U ω') i j ∂P)
  have hHLU : (H + LU).IsHermitian :=
    hH.add (isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log _))
  have hinner_int : Integrable
      (fun ω ↦ ∫ ω', RCLike.re (NormedSpace.exp ((H + V ω) + U ω')).trace ∂P) P :=
    (funext hslice_eq : _ = (fun v ↦ ∫ u, Φ (u, v) ∂P.map U) ∘ V) ▸
      hΦ_prod_int.integral_prod_right.comp_aemeasurable hV_meas
  have hrhs_int : Integrable
      (fun ω ↦ RCLike.re (NormedSpace.exp ((H + LU) + V ω)).trace) P :=
    (hHLU.integrable_re_trace_exp_add_cfc_log hV_int
      (hV_herm.mono fun _ h ↦ h.posDef_exp)).congr
      (hV_herm.mono fun ω hω ↦
        congrArg (fun M ↦ RCLike.re (NormedSpace.exp ((H + LU) + M)).trace) hω.cfc_log_exp)
  refine integral_mono_ae hinner_int hrhs_int ?_
  filter_upwards [hV_herm] with ω hVω
  simpa only [LU, add_assoc, add_right_comm H _ (V ω)] using
    (hH.add hVω).integral_re_trace_exp_add_le hU_herm hU_int

/-- For independent almost everywhere Hermitian random matrices `Xₖ` (`k ∈ s`) with integrable
matrix exponentials and deterministic Hermitian `H`, the sum `∑ k ∈ s, Xₖ` has integrable matrix
exponential and satisfies
`E[re Tr exp (H + ∑ k ∈ s, Xₖ)] ≤ re Tr exp (H + ∑ k ∈ s, log E[exp Xₖ])`. -/
theorem integral_re_trace_exp_add_sum_le {X : ι → Ω → Matrix n n 𝕜} (hindep : iIndepFun X P)
    {s : Finset ι} {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (hX_meas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hX_herm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hX_int : ∀ k ∈ s, Integrable (fun ω ↦ NormedSpace.exp (X k ω)) P) :
    Integrable (fun ω ↦ NormedSpace.exp (∑ k ∈ s, X k ω)) P ∧
      ∫ ω, RCLike.re (NormedSpace.exp (H + ∑ k ∈ s, X k ω)).trace ∂P ≤
        RCLike.re (NormedSpace.exp (H + ∑ k ∈ s,
          cfc Real.log (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (X k ω) i j ∂P))).trace := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let : MeasurableAdd₂ (Matrix n n 𝕜) :=
    ⟨Measurable.of_eval_matrix _ fun i j ↦
      measurable_fst.eval_matrix.add measurable_snd.eval_matrix⟩
  -- Restrict the index type to `s` so every coordinate is a.e. measurable.
  let Y : s → Ω → Matrix n n 𝕜 := fun k ↦ X k.1
  have hindep_s : iIndepFun Y P := hindep.precomp Subtype.val_injective
  have hY_meas : ∀ k : s, AEMeasurable (Y k) P := fun k ↦ hX_meas k.1 k.2
  suffices ∀ (t : Finset s) {H₀ : Matrix n n 𝕜}, H₀.IsHermitian →
      Integrable (fun ω ↦ NormedSpace.exp (∑ k ∈ t, Y k ω)) P ∧
        ∫ ω, RCLike.re (NormedSpace.exp (H₀ + ∑ k ∈ t, Y k ω)).trace ∂P ≤
          RCLike.re (NormedSpace.exp (H₀ + ∑ k ∈ t,
            cfc Real.log (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (Y k ω) i j ∂P))).trace by
    obtain ⟨hint, hle⟩ := this Finset.univ hH
    have hsum_Y : ∀ ω, ∑ k : s, Y k ω = ∑ k ∈ s, X k ω := fun ω ↦
      Finset.sum_coe_sort s fun k ↦ X k ω
    have hlog_Y : (∑ k : s,
        cfc Real.log (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (Y k ω) i j ∂P)) =
          ∑ k ∈ s, cfc Real.log (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (X k ω) i j ∂P) :=
      Finset.sum_coe_sort s
        (fun k ↦ cfc Real.log (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (X k ω) i j ∂P))
    simp_rw [hsum_Y, hlog_Y] at hint hle
    exact ⟨hint, hle⟩
  intro t
  induction t using Finset.cons_induction with
  | empty =>
    intro H₀ _
    simp only [Finset.sum_empty, add_zero, NormedSpace.exp_zero, integrable_const, true_and]
    rw [integral_const, probReal_univ, one_smul]
  | cons k t hkt ih =>
    intro H₀ hH₀
    have hsum_fn : (∑ j ∈ t, Y j) = fun ω ↦ ∑ j ∈ t, Y j ω := by ext ω; simp
    have hind_kt : Y k ⟂ᵢ[P] (fun ω ↦ ∑ j ∈ t, Y j ω) :=
      hsum_fn ▸ (hindep_s.indepFun_finsetSum_of_notMem₀ hY_meas hkt).symm
    have hH₀' : (H₀ + cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (Y k ω) i j ∂P)).IsHermitian :=
      hH₀.add (isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log _))
    obtain ⟨ht_int, ht_le⟩ := ih hH₀'
    have hVt_herm : ∀ᵐ ω ∂P, (∑ j ∈ t, Y j ω).IsHermitian := by
      filter_upwards [(Filter.eventually_all_finset t).2 fun j _ ↦ hX_herm j.1 j.2] with ω hω
      exact Matrix.isHermitian_finsetSum t hω
    have hVt_meas : AEMeasurable (fun ω ↦ ∑ j ∈ t, Y j ω) P :=
      Finset.aemeasurable_fun_sum t fun j _ ↦ hY_meas j
    obtain ⟨hcons_int, hstep⟩ := indepFun_step hH₀ hind_kt (hY_meas k) hVt_meas
      (hX_herm k.1 k.2) hVt_herm (hX_int k.1 k.2) ht_int
    simp only [Finset.sum_cons]
    exact ⟨hcons_int, hstep.trans (by simpa only [add_assoc] using ht_le)⟩

/-- **Subadditivity of matrix cumulant-generating functions** (Tropp 2012, Lemma 3.4). For
independent almost everywhere Hermitian random matrices `Xₖ` (`k ∈ s`) with integrable matrix
exponentials,
`E[re Tr exp (∑ k ∈ s, Xₖ)] ≤ re Tr exp (∑ k ∈ s, log E[exp Xₖ])`. -/
theorem integral_re_trace_exp_sum_le {X : ι → Ω → Matrix n n 𝕜} (hindep : iIndepFun X P)
    {s : Finset ι} (hX_meas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hX_herm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hX_int : ∀ k ∈ s, Integrable (fun ω ↦ NormedSpace.exp (X k ω)) P) :
    ∫ ω, RCLike.re (NormedSpace.exp (∑ k ∈ s, X k ω)).trace ∂P ≤
      RCLike.re (NormedSpace.exp (∑ k ∈ s,
        cfc Real.log (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (X k ω) i j ∂P))).trace := by
  simpa only [zero_add] using
    (hindep.integral_re_trace_exp_add_sum_le (isHermitian_zero : (0 : Matrix n n 𝕜).IsHermitian)
      hX_meas hX_herm hX_int).2

/-- **Tropp's master tail bound** (Tropp 2012, Theorem 3.6). If `Xₖ` (`k ∈ s`) are independent
almost everywhere Hermitian random matrices satisfying `E[exp (θ • Xₖ)] ≤ exp (Aₖ)` for
deterministic Hermitian matrices `Aₖ` and `θ ≥ 0`, then for every `t : ℝ`,
`P(∃ x ∈ spectrum ℝ (∑ k ∈ s, Xₖ ω), t ≤ x) ≤ card n * exp (-θ * t + ‖∑ k ∈ s, Aₖ‖)`. -/
theorem measureReal_exists_spectrum_sum_ge_le {X : ι → Ω → Matrix n n 𝕜} (hindep : iIndepFun X P)
    {s : Finset ι} (hX_meas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hX_herm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    {θ : ℝ} (hθ : 0 ≤ θ) {A : ι → Matrix n n 𝕜} (hA : ∀ k ∈ s, (A k).IsHermitian)
    (hX_int : ∀ k ∈ s, Integrable (fun ω ↦ NormedSpace.exp (θ • X k ω)) P)
    (hmgf : ∀ k ∈ s,
      (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (θ • X k ω) i j ∂P) ≤ NormedSpace.exp (A k))
    (t : ℝ) :
    P.real {ω | ∃ x ∈ spectrum ℝ (∑ k ∈ s, X k ω), t ≤ x} ≤
      Fintype.card n * Real.exp (-θ * t + ‖∑ k ∈ s, A k‖) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hindep_θ : iIndepFun (fun k ω ↦ θ • X k ω) P :=
    hindep.comp (fun _ M ↦ θ • M) fun _ ↦ (continuous_const_smul θ).measurable
  have hmeas_θ : ∀ k ∈ s, AEMeasurable (fun ω ↦ θ • X k ω) P := fun k hk ↦
    (continuous_const_smul θ).measurable.comp_aemeasurable (hX_meas k hk)
  have hherm_θ : ∀ k ∈ s, ∀ᵐ ω ∂P, (θ • X k ω).IsHermitian := fun k hk ↦
    (hX_herm k hk).mono fun _ h ↦ Matrix.isHermitian_smul_real h θ
  obtain ⟨hsum_int, hcumulant⟩ := hindep_θ.integral_re_trace_exp_add_sum_le
    (isHermitian_zero : (0 : Matrix n n 𝕜).IsHermitian) hmeas_θ hherm_θ hX_int
  simp only [zero_add, ← Finset.smul_sum] at hsum_int hcumulant
  have hsum_herm : ∀ᵐ ω ∂P, (∑ k ∈ s, X k ω).IsHermitian := by
    filter_upwards [(Filter.eventually_all_finset s).2 hX_herm] with ω hω
    exact Matrix.isHermitian_finsetSum s hω
  -- Bound each `log E[exp (θ • Xₖ)] ≤ Aₖ` by operator monotonicity of `log`.
  have hlog_sum : (∑ k ∈ s,
      cfc Real.log (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (θ • X k ω) i j ∂P)) ≤
        ‖∑ k ∈ s, A k‖ • (1 : Matrix n n 𝕜) := by
    refine (Finset.sum_le_sum fun k hk ↦ ?_).trans
      (Matrix.isHermitian_finsetSum s hA).le_l2_opNorm_smul_one
    have hpos_k : (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (θ • X k ω) i j ∂P).PosDef :=
      TauCeti.posDef_integral ((hherm_θ k hk).mono fun _ h ↦ h.posDef_exp)
        (Matrix.integrable_iff.1 (hX_int k hk))
    simpa only [(hA k hk).cfc_log_exp] using hpos_k.cfc_log_le_cfc_log (hmgf k hk)
  have hHS : (∑ k ∈ s,
      cfc Real.log (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (θ • X k ω) i j ∂P)).IsHermitian :=
    Matrix.isHermitian_finsetSum s fun k _ ↦
      isHermitian_iff_isSelfAdjoint.2 (cfc_predicate Real.log _)
  have htr_bound : RCLike.re (NormedSpace.exp (∑ k ∈ s,
      cfc Real.log (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (θ • X k ω) i j ∂P))).trace ≤
        Fintype.card n * Real.exp ‖∑ k ∈ s, A k‖ :=
    (IsHermitian.re_trace_exp_le_of_le hHS
      (Matrix.isHermitian_smul_real isHermitian_one ‖∑ k ∈ s, A k‖) hlog_sum).trans_eq
      (Matrix.re_trace_exp_smul_one ‖∑ k ∈ s, A k‖)
  calc P.real {ω | ∃ x ∈ spectrum ℝ (∑ k ∈ s, X k ω), t ≤ x}
      ≤ Real.exp (-θ * t) * ∫ ω, RCLike.re (NormedSpace.exp (θ • ∑ k ∈ s, X k ω)).trace ∂P :=
        measureReal_exists_spectrum_ge_le_of_isHermitian hsum_herm hθ t hsum_int
    _ ≤ Real.exp (-θ * t) * (Fintype.card n * Real.exp ‖∑ k ∈ s, A k‖) :=
        mul_le_mul_of_nonneg_left (hcumulant.trans htr_bound) (Real.exp_pos _).le
    _ = Fintype.card n * Real.exp (-θ * t + ‖∑ k ∈ s, A k‖) := by
        rw [Real.exp_add]
        ring

end ProbabilityTheory.iIndepFun
