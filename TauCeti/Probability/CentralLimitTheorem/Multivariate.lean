/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Moments.Covariance
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.Instances.Matrix
import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation
import TauCeti.MeasureTheory.Function.TendstoInDistribution
import TauCeti.Probability.CentralLimitTheorem.Lindeberg
import TauCeti.Probability.CramerWold
import TauCeti.Probability.Distributions.Gaussian.Transforms
import TauCeti.Probability.Independence.InfinitePi

/-!
# Multivariate Lindeberg–Feller and central limit theorems

This file establishes central limit theorems for random vectors taking values in a
finite-dimensional Euclidean space `EuclideanSpace ℝ κ`, allowing singular limiting covariance
matrices throughout and imposing no global measurability hypotheses beyond square-integrability.

## Main results

* `TauCeti.tendstoInDistribution_sum_of_lindeberg`: the **multivariate Lindeberg–Feller central
  limit theorem** for triangular arrays of row-wise independent, centred, square-integrable random
  vectors whose row covariance matrices converge to `S` and whose norms satisfy the Lindeberg
  condition `∑ i, ∫_{ε < ‖Y n i‖} ‖Y n i‖² → 0`. Positive semidefiniteness of `S` is derived
  automatically as a closed-cone limit of the row covariance matrices.
* `TauCeti.tendstoInDistribution_sum_smul_of_tendsto_vecMulVec`: multivariate central limit theorem
  for weighted sums `∑ i, ξ n i • w n i` of row-wise independent centred scalar shocks sharing a
  square-integrable law `ν` with deterministic vector weights whose Gram matrices
  `∑ i, vecMulVec (w n i) (w n i)` converge to `Q` and whose maximum norm tends to `0`.
* `TauCeti.tendstoInDistribution_inv_sqrt_smul_sum_sub_euclidean`: the **multivariate central limit
  theorem** for an i.i.d. sequence in `EuclideanSpace ℝ κ` with finite second moment, converging in
  distribution to `multivariateGaussian 0 (covMatrix (μ.map (X 0)))`.
* `TauCeti.tendstoInDistribution_inv_sqrt_smul_sum_sub_pi`: the sample-space form of the
  multivariate central limit theorem on `(Fin n → α, Measure.pi (fun _ ↦ P))` for a
  square-integrable statistic `s : α → EuclideanSpace ℝ κ`.

## Implementation notes

Via the varying-space Cramér–Wold theorem
`TauCeti.tendstoInDistribution_iff_tendstoInDistribution_inner_dep`, both main theorems reduce to
one dimension along every projection `z ↦ ⟪z, t⟫`. In each direction `t`, Cauchy–Schwarz transfers
the Euclidean Lindeberg condition to the scalar Lindeberg condition at threshold `δ` via radius
`δ / (2 ‖t‖)`, `TauCeti.variance_inner_eq_inner_covMatrix_map` identifies the projected variance as
`⟪t, (covMatrix …).toEuclideanLin t⟫`, and `ProbabilityTheory.HasLaw.inner_multivariateGaussian`
identifies the projected Gaussian limit even when `S` is singular (`⟪t, S.toEuclideanLin t⟫ = 0`).

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Sections 27 and 29.
* H. Cramér and H. Wold, “Some theorems on distribution functions,” *Journal of the London
  Mathematical Society* 11 (1936), 290–294.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Propositions 2.17
  and 2.27.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Real RealInnerProductSpace Topology NNReal

namespace TauCeti

section Lindeberg

variable {κ : Type*} [Fintype κ]

/-- Cauchy–Schwarz transfers the vector Lindeberg condition `∑ i, ∫_{ε < ‖Y n i‖} ‖Y n i‖² → 0`
to the scalar Lindeberg condition along every inner-product direction `t`. -/
private theorem tendsto_sum_indicator_inner_sq_of_lindeberg
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : (n : ℕ) → Measure (Ω n)}
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {Y : (n : ℕ) → ι n → Ω n → EuclideanSpace ℝ κ}
    (hL2 : ∀ n i, MemLp (Y n i) 2 (μ n))
    (hlind : ∀ ε > 0, Tendsto
      (fun n ↦ ∑ i, ∫ ω in {ω | ε < ‖Y n i ω‖}, ‖Y n i ω‖ ^ 2 ∂(μ n)) atTop (𝓝 0))
    (t : EuclideanSpace ℝ κ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n ↦ ∑ i, (μ n)[{ω | δ ≤ |⟪Y n i ω, t⟫|}.indicator fun ω ↦ ⟪Y n i ω, t⟫ ^ 2])
      atTop (𝓝 0) := by
  by_cases ht : t = 0
  · subst ht
    simp [not_le.mpr hδ]
  have ht_pos : 0 < ‖t‖ := norm_pos_iff.mpr ht
  set ε : ℝ := δ / (2 * ‖t‖)
  have hε : 0 < ε := by positivity
  refine squeeze_zero (fun n ↦ Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _) (fun n ↦ ?_)
      (by simpa only [mul_zero] using (hlind ε hε).const_mul (‖t‖ ^ 2))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hY_sq : Integrable (fun ω ↦ ‖Y n i ω‖ ^ 2) (μ n) :=
    (memLp_two_iff_integrable_sq_norm (hL2 n i).aestronglyMeasurable).mp (hL2 n i)
  have hs : NullMeasurableSet {ω | ε < ‖Y n i ω‖} (μ n) :=
    nullMeasurableSet_lt aemeasurable_const (hL2 n i).aestronglyMeasurable.norm.aemeasurable
  rw [← integral_indicator₀ hs, ← integral_const_mul]
  refine integral_mono (((hL2 n i).inner_const t).integrable_indicator_sq δ)
    ((hY_sq.indicator₀ hs).const_mul _) fun ω ↦ ?_
  by_cases hω : δ ≤ |⟪Y n i ω, t⟫|
  · have hcs : |⟪Y n i ω, t⟫| ≤ ‖Y n i ω‖ * ‖t‖ := abs_real_inner_le_norm (Y n i ω) t
    have hεlt : ε < ‖Y n i ω‖ := by
      have hdiv : δ / ‖t‖ ≤ ‖Y n i ω‖ := (div_le_iff₀ ht_pos).mpr (hω.trans hcs)
      have hhalf : ε < δ / ‖t‖ := by
        rw [div_lt_div_iff₀ (by positivity) ht_pos]; nlinarith
      exact hhalf.trans_le hdiv
    rw [Set.indicator_of_mem (s := {ω | δ ≤ |⟪Y n i ω, t⟫|}) hω,
      Set.indicator_of_mem (s := {ω | ε < ‖Y n i ω‖}) hεlt, ← sq_abs ⟪Y n i ω, t⟫]
    nlinarith [mul_self_le_mul_self (abs_nonneg _) hcs]
  · rw [Set.indicator_of_notMem (s := {ω | δ ≤ |⟪Y n i ω, t⟫|}) hω]
    exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)

/-- **Multivariate Lindeberg–Feller central limit theorem.** Let `Y n i`, `i : ι n`, be a
triangular array of row-wise independent, centred, square-integrable random vectors in
`EuclideanSpace ℝ κ` on probability spaces `(Ω n, μ n)`. If the row covariance matrices
`∑ i, covMatrix ((μ n).map (Y n i))` converge to `S` and the Lindeberg condition
`∑ i, ∫_{ε < ‖Y n i‖} ‖Y n i‖² ∂(μ n) → 0` holds for every `ε > 0`, then the row sums
`∑ i, Y n i` converge in distribution to any random vector `Z` with law
`multivariateGaussian 0 S` (allowing singular `S`). -/
theorem tendstoInDistribution_sum_of_lindeberg [DecidableEq κ]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {Y : (n : ℕ) → ι n → Ω n → EuclideanSpace ℝ κ}
    {S : Matrix κ κ ℝ}
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → EuclideanSpace ℝ κ}
    (hindep : ∀ n, iIndepFun (Y n) (μ n))
    (hL2 : ∀ n i, MemLp (Y n i) 2 (μ n))
    (hmean : ∀ n i, ∫ ω, Y n i ω ∂(μ n) = 0)
    (hcov : Tendsto (fun n ↦ ∑ i, covMatrix ((μ n).map (Y n i))) atTop (𝓝 S))
    (hlind : ∀ ε > 0, Tendsto
      (fun n ↦ ∑ i, ∫ ω in {ω | ε < ‖Y n i ω‖}, ‖Y n i ω‖ ^ 2 ∂(μ n)) atTop (𝓝 0))
    (hZ : HasLaw Z (multivariateGaussian 0 S) μ') :
    TendstoInDistribution (fun n ω ↦ ∑ i, Y n i ω) atTop Z μ μ' := by
  have hS : S.PosSemidef :=
    isClosed_setOfPred_posSemidef.mem_of_tendsto hcov (.of_forall fun n ↦
      (Matrix.PosSemidef.addSubmonoid κ ℝ).sum_mem fun i _ ↦ posSemidef_covMatrix_map (hL2 n i))
  refine tendstoInDistribution_iff_tendstoInDistribution_inner_dep.mpr fun t ↦ ?_
  simp_rw [sum_inner]
  have hZt : HasLaw (fun ω' ↦ ⟪Z ω', t⟫)
      (gaussianReal 0 (⟪t, S.toEuclideanLin t⟫).toNNReal) μ' := by
    simpa only [real_inner_comm t, inner_zero_right] using hZ.inner_multivariateGaussian hS t
  refine hZt.tendstoInDistribution_sum_of_lindeberg
    (fun n ↦ (hindep n).comp (fun _ z ↦ ⟪z, t⟫)
      fun _ ↦ (continuous_id.inner continuous_const).measurable)
    (fun n i ↦ (hL2 n i).inner_const t)
    (fun n i ↦ by
      simp_rw [real_inner_comm t]
      rw [integral_inner (𝕜 := ℝ) ((hL2 n i).integrable one_le_two) t, hmean n i,
        inner_zero_right])
    ?_ (fun δ hδ ↦ tendsto_sum_indicator_inner_sq_of_lindeberg hL2 hlind t hδ)
  have hSt_nn : 0 ≤ ⟪t, S.toEuclideanLin t⟫ := by
    simpa only [RCLike.re_to_real, real_inner_comm] using
      (Matrix.isPositive_toEuclideanLin_iff.mpr hS).right t
  rw [Real.coe_toNNReal _ hSt_nn]
  have hquad_cont : Continuous (fun A : Matrix κ κ ℝ ↦ ⟪t, A.toEuclideanLin t⟫) := by
    simp_rw [Matrix.toLpLin_apply]
    exact continuous_const.inner
      ((PiLp.continuous_toLp 2 _).comp (continuous_id.matrix_mulVec continuous_const))
  refine (hquad_cont.tendsto S |>.comp hcov).congr' (.of_forall fun n ↦ ?_)
  dsimp only [Function.comp_def]
  rw [map_sum, LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simpa only [real_inner_comm t] using (variance_inner_eq_inner_covMatrix_map (hL2 n i) t).symm

/-- Single-summand upper-tail bound for a weighted scalar shock `ξ • w` when `‖w‖ ≤ ε / R`. -/
private theorem setIntegral_norm_smul_sq_le
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {μ₀ : Measure Ω₀}
    {ξ₀ : Ω₀ → ℝ} {w₀ : EuclideanSpace ℝ κ} {ν : Measure ℝ}
    (hlaw : HasLaw ξ₀ ν μ₀) (hL2 : MemLp id 2 ν)
    {ε : ℝ} {R : ℝ≥0} (hε : 0 < ε) (hRpos : 0 < (R : ℝ)) (hw : ‖w₀‖ ≤ ε / (R : ℝ)) :
    ∫ ω in {ω | ε < ‖ξ₀ ω • w₀‖}, ‖ξ₀ ω • w₀‖ ^ 2 ∂μ₀ ≤
      ‖w₀‖ ^ 2 * ∫ u, {u | (R : ℝ) < ‖u‖}.indicator (fun u ↦ ‖u‖ ^ 2) u ∂ν := by
  have hξm : AEMeasurable ξ₀ μ₀ := hlaw.aemeasurable
  have hξ2 : Integrable (fun ω ↦ ‖ξ₀ ω‖ ^ 2) μ₀ :=
    (hlaw.memLp hL2).integrable_norm_pow two_ne_zero
  have hs : NullMeasurableSet {ω | ε < ‖ξ₀ ω • w₀‖} μ₀ :=
    nullMeasurableSet_lt aemeasurable_const (by fun_prop)
  have hmap_ind : ∫ u, {u | (R : ℝ) < ‖u‖}.indicator (fun u ↦ ‖u‖ ^ 2) u ∂ν =
      ∫ ω, {ω | (R : ℝ) < ‖ξ₀ ω‖}.indicator (fun ω ↦ ‖ξ₀ ω‖ ^ 2) ω ∂μ₀ := by
    rw [← hlaw.map_eq]
    exact integral_map hξm
      ((by fun_prop : Measurable fun u : ℝ ↦ ‖u‖ ^ 2).aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const (by fun_prop : Measurable fun u : ℝ ↦ ‖u‖)))
  rw [← integral_indicator₀ hs, hmap_ind, ← integral_const_mul]
  refine integral_mono
    (((hξ2.mul_const (‖w₀‖ ^ 2)).congr (.of_forall fun ω ↦ ?_)).indicator₀ hs)
    ((hξ2.indicator₀ (nullMeasurableSet_lt aemeasurable_const hξm.norm)).const_mul _) fun ω ↦ ?_
  · simp [norm_smul, mul_pow]
  · by_cases hω : ε < ‖ξ₀ ω • w₀‖
    · have hω' : ε < ‖ξ₀ ω‖ * ‖w₀‖ := by rwa [norm_smul] at hω
      have hw_pos : 0 < ‖w₀‖ := pos_of_mul_pos_right (hε.trans hω') (norm_nonneg _)
      have hRlt : (R : ℝ) < ‖ξ₀ ω‖ :=
        lt_of_mul_lt_mul_right (((le_div_iff₀' hRpos).mp hw).trans_lt hω') hw_pos.le
      rw [Set.indicator_of_mem (s := {ω | ε < ‖ξ₀ ω • w₀‖}) hω,
        Set.indicator_of_mem (s := {ω | (R : ℝ) < ‖ξ₀ ω‖}) hRlt,
        norm_smul, mul_pow, mul_comm]
    · rw [Set.indicator_of_notMem (s := {ω | ε < ‖ξ₀ ω • w₀‖}) hω]
      exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)

/-- Tail truncation transfers uniform asymptotic negligibility of deterministic weights `w n i` and
convergence of their Gram matrices to the vector Lindeberg condition for `ξ n i • w n i`. -/
private theorem tendsto_sum_setIntegral_norm_smul_sq
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : (n : ℕ) → Measure (Ω n)}
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {ξ : (n : ℕ) → ι n → Ω n → ℝ} {w : (n : ℕ) → ι n → EuclideanSpace ℝ κ}
    {ν : Measure ℝ} {Q : Matrix κ κ ℝ}
    (hlaw : ∀ n i, HasLaw (ξ n i) ν (μ n)) (hL2 : MemLp id 2 ν)
    (hgram : Tendsto (fun n ↦ ∑ i, Matrix.vecMulVec (w n i) (w n i)) atTop (𝓝 Q))
    (hmax : ∀ δ > 0, ∀ᶠ n in atTop, ∀ i, ‖w n i‖ ≤ δ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ ∑ i, ∫ ω in {ω | ε < ‖ξ n i ω • w n i‖}, ‖ξ n i ω • w n i‖ ^ 2 ∂(μ n))
      atTop (𝓝 0) := by
  have htail := hL2.tendsto_integral_indicator_norm_sq
  have htrace : Tendsto (fun n ↦ ∑ i, ‖w n i‖ ^ 2) atTop (𝓝 Q.trace) := by
    have hcont : Continuous (fun A : Matrix κ κ ℝ ↦ A.trace) := continuous_id.matrix_trace
    refine ((hcont.tendsto Q).comp hgram).congr fun n ↦ ?_
    simp only [Function.comp_def, Matrix.trace_sum, Matrix.trace_vecMulVec]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [Metric.tendsto_nhds]
  intro η hη
  set M : ℝ := |Q.trace| + 1
  have hM : 0 < M := by positivity
  obtain ⟨R, hRpos, hRtail⟩ : ∃ R : ℝ≥0, 0 < R ∧
      ∫ u, {u | (R : ℝ) < ‖u‖}.indicator (fun u ↦ ‖u‖ ^ 2) u ∂ν < η / (2 * M) :=
    ((eventually_gt_atTop (0 : ℝ≥0)).and
      (htail (Iio_mem_nhds (div_pos hη (mul_pos two_pos hM))))).exists
  have hRpos' : 0 < (R : ℝ) := R.coe_pos.mpr hRpos
  filter_upwards [hmax (ε / (R : ℝ)) (div_pos hε hRpos'),
    htrace (Iio_mem_nhds (by linarith [le_abs_self Q.trace] : Q.trace < M))] with n hwn hsum
  have hsum_lt : ∑ i, ‖w n i‖ ^ 2 < M := hsum
  have htail0 : 0 ≤ ∫ u, {u | (R : ℝ) < ‖u‖}.indicator (fun u ↦ ‖u‖ ^ 2) u ∂ν :=
    integral_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
  have hnonneg : 0 ≤ ∑ i, ∫ ω in {ω | ε < ‖ξ n i ω • w n i‖}, ‖ξ n i ω • w n i‖ ^ 2 ∂(μ n) :=
    Finset.sum_nonneg fun i _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  refine (le_trans (b := (∑ i, ‖w n i‖ ^ 2) *
    ∫ u, {u | (R : ℝ) < ‖u‖}.indicator (fun u ↦ ‖u‖ ^ 2) u ∂ν) ?_ ?_).trans_lt (half_lt_self hη)
  · rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦
      setIntegral_norm_smul_sq_le (hlaw n i) hL2 hε hRpos' (hwn i)
  · calc (∑ i, ‖w n i‖ ^ 2) * ∫ u, {u | (R : ℝ) < ‖u‖}.indicator (fun u ↦ ‖u‖ ^ 2) u ∂ν
        ≤ M * (η / (2 * M)) := mul_le_mul hsum_lt.le hRtail.le htail0 hM.le
      _ = η / 2 := by field_simp [hM.ne']

/-- **Multivariate central limit theorem for weighted scalar shocks.** Let `ξ n i` be row-wise
independent real random variables with common centred square-integrable law `ν`, and let
`w n i : EuclideanSpace ℝ κ` be deterministic weights whose Gram matrices
`∑ i, vecMulVec (w n i) (w n i)` converge to `Q` and whose maximum norm tends to `0`
(`∀ δ > 0, ∀ᶠ n, ∀ i, ‖w n i‖ ≤ δ`). Then `∑ i, ξ n i • w n i` converges in distribution to
`multivariateGaussian 0 (Var[id; ν] • Q)`. -/
theorem tendstoInDistribution_sum_smul_of_tendsto_vecMulVec [DecidableEq κ]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {ξ : (n : ℕ) → ι n → Ω n → ℝ} {w : (n : ℕ) → ι n → EuclideanSpace ℝ κ}
    {ν : Measure ℝ} {Q : Matrix κ κ ℝ}
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → EuclideanSpace ℝ κ}
    (hindep : ∀ n, iIndepFun (ξ n) (μ n))
    (hlaw : ∀ n i, HasLaw (ξ n i) ν (μ n))
    (hL2 : MemLp id 2 ν)
    (hmean : ∫ u, u ∂ν = 0)
    (hgram : Tendsto (fun n ↦ ∑ i, Matrix.vecMulVec (w n i) (w n i)) atTop (𝓝 Q))
    (hmax : ∀ δ > 0, ∀ᶠ n in atTop, ∀ i, ‖w n i‖ ≤ δ)
    (hZ : HasLaw Z (multivariateGaussian 0 (Var[id; ν] • Q)) μ') :
    TendstoInDistribution (fun n ω ↦ ∑ i, ξ n i ω • w n i) atTop Z μ μ' := by
  have hξL2 (n : ℕ) (i : ι n) : MemLp (ξ n i) 2 (μ n) := (hlaw n i).memLp hL2
  refine tendstoInDistribution_sum_of_lindeberg
    (Y := fun n i ω ↦ ξ n i ω • w n i)
    (fun n ↦ (hindep n).comp (fun i u ↦ u • w n i)
      fun i ↦ (continuous_id.smul continuous_const).measurable)
    (fun n i ↦ by
      simpa only [Function.comp_def, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply] using
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (w n i)).comp_memLp' (hξL2 n i))
    (fun n i ↦ by
      rw [integral_smul_const]
      have h0 : ∫ ω, ξ n i ω ∂(μ n) = 0 := by
        rw [← hmean, ← (hlaw n i).map_eq]
        exact (integral_map (hlaw n i).aemeasurable aestronglyMeasurable_id).symm
      rw [h0, zero_smul])
    ?_ (fun ε hε ↦ tendsto_sum_setIntegral_norm_smul_sq hlaw hL2 hgram hmax hε) hZ
  refine (hgram.const_smul Var[id; ν]).congr fun n ↦ ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hmap : (μ n).map (fun ω ↦ ξ n i ω • w n i) = ν.map (fun u : ℝ ↦ u • w n i) := by
    rw [← (hlaw n i).map_eq,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hlaw n i).aemeasurable,
      Function.comp_def]
  rw [hmap, covMatrix_map_smul_const]

end Lindeberg

section CentralLimitTheorem

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Multivariate central limit theorem.** For an independent, identically distributed sequence of
square-integrable random vectors `X : ℕ → Ω → EuclideanSpace ℝ κ` on a probability space `(Ω, μ)`,
the normalized centred partial sums `(√n)⁻¹ • ∑ i ∈ Finset.range n, (X i - E[X 0])` converge in
distribution to any random vector `Z` with law
`multivariateGaussian 0 (covMatrix (μ.map (X 0)))` (allowing singular covariance matrices). -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_sub_euclidean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → EuclideanSpace ℝ κ}
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → EuclideanSpace ℝ κ}
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hindep : iIndepFun X μ)
    (hL2 : MemLp (X 0) 2 μ)
    (hZ : HasLaw Z (multivariateGaussian 0 (covMatrix (μ.map (X 0)))) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, (X i ω - ∫ ω', X 0 ω' ∂μ))
      atTop Z (fun _ ↦ μ) μ' := by
  have hS : (covMatrix (μ.map (X 0))).PosSemidef := posSemidef_covMatrix_map hL2
  refine tendstoInDistribution_iff_tendstoInDistribution_inner_dep.mpr fun t ↦ ?_
  set U : ℕ → Ω → ℝ := fun i ω ↦ ⟪t, X i ω⟫
  have hU_var : Var[U 0; μ] = ⟪t, (covMatrix (μ.map (X 0))).toEuclideanLin t⟫ :=
    variance_inner_eq_inner_covMatrix_map hL2 t
  have hZt : HasLaw (fun ω' ↦ ⟪Z ω', t⟫) (gaussianReal 0 Var[U 0; μ].toNNReal) μ' := by
    simpa only [real_inner_comm t, inner_zero_right, hU_var] using
      hZ.inner_multivariateGaussian hS t
  have hclt := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub hZt
    (hL2.const_inner t)
    (hindep.comp (fun _ z ↦ ⟪t, z⟫) fun _ ↦ (continuous_const.inner continuous_id).measurable)
    fun i ↦ (hident i).comp (continuous_const.inner continuous_id).measurable
  have hmean : ∫ ω', U 0 ω' ∂μ = ⟪t, ∫ ω', X 0 ω' ∂μ⟫ :=
    integral_inner (𝕜 := ℝ) (hL2.integrable one_le_two) t
  refine hclt.congr' (fun n ↦ ?_) (.of_forall fun n ↦ .of_forall fun ω ↦ ?_)
    Filter.EventuallyEq.rfl
  · have hm : ∀ i, AEMeasurable (X i) μ := fun i ↦ (hident i).aemeasurable_fst
    fun_prop
  · dsimp only
    rw [hmean, real_inner_smul_left, sum_inner]
    simp only [U, inner_sub_left, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    simp_rw [real_inner_comm t]

/-- **Sample-space multivariate central limit theorem on product measures.** For a square-integrable
statistic `s : α → EuclideanSpace ℝ κ` on a probability space `(α, P)`, the normalized centred
sample sums `(√n)⁻¹ • ∑ i : Fin n, (s (x i) - ∫ a, s a ∂P)` under `Measure.pi (fun _ : Fin n ↦ P)`
converge in distribution to any random vector `Z` with law
`multivariateGaussian 0 (covMatrix (P.map s))`. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_sub_pi
    {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    (s : α → EuclideanSpace ℝ κ) (hs : MemLp s 2 P)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → EuclideanSpace ℝ κ}
    (hZ : HasLaw Z (multivariateGaussian 0 (covMatrix (P.map s))) μ') :
    TendstoInDistribution
      (fun (n : ℕ) (x : Fin n → α) ↦ (√(n : ℝ))⁻¹ • ∑ i : Fin n, (s (x i) - ∫ a, s a ∂P))
      atTop Z (fun n ↦ Measure.pi fun _ : Fin n ↦ P) μ' := by
  let Q : Measure (ℕ → α) := Measure.infinitePi fun _ : ℕ ↦ P
  -- Realize `s (ω i)` as an i.i.d. sequence on the countable product `(ℕ → α, Q)`.
  have heval (i : ℕ) : MeasurePreserving (fun ω : ℕ → α ↦ ω i) Q P :=
    measurePreserving_eval_infinitePi (fun _ : ℕ ↦ P) i
  have hsm (i : ℕ) : AEMeasurable s (Q.map fun ω : ℕ → α ↦ ω i) := by
    rw [(heval i).map_eq]; exact hs.aestronglyMeasurable.aemeasurable
  have hindep : iIndepFun (fun i (ω : ℕ → α) ↦ s (ω i)) Q :=
    (TauCeti.Probability.iIndepFun_eval_infinitePi _).comp₀ (fun _ ↦ s)
      (fun i ↦ (measurable_pi_apply i).aemeasurable) hsm
  have hident (i : ℕ) : IdentDistrib (fun ω : ℕ → α ↦ s (ω i)) (fun ω ↦ s (ω 0)) Q Q :=
    (P.identDistrib_eval_infinitePi i 0).comp_of_aemeasurable (hsm i)
  have hX0_map : Q.map (fun ω : ℕ → α ↦ s (ω 0)) = P.map s := by
    rw [← (heval 0).map_eq,
      AEMeasurable.map_map_of_aemeasurable (hsm 0) (measurable_pi_apply 0).aemeasurable,
      Function.comp_def]
  have hseq := tendstoInDistribution_inv_sqrt_smul_sum_sub_euclidean hident hindep
    (hs.comp_measurePreserving (heval 0)) (hX0_map ▸ hZ)
  -- Transfer convergence in distribution from `(ℕ → α, Q)` to `(Fin n → α, Measure.pi …)`.
  have hmean : ∫ ω', s (ω' 0) ∂Q = ∫ a, s a ∂P := by
    rw [← (heval 0).map_eq, integral_map (measurable_pi_apply 0).aemeasurable
      (by rw [(heval 0).map_eq]; exact hs.aestronglyMeasurable)]
  have hT (n : ℕ) : AEMeasurable
      (fun x : Fin n → α ↦ (√(n : ℝ))⁻¹ • ∑ i : Fin n, (s (x i) - ∫ a, s a ∂P))
      (Measure.pi fun _ : Fin n ↦ P) := by
    have hsum := Finset.aemeasurable_fun_sum Finset.univ fun i : Fin n ↦ fun _ ↦
      (hs.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ P) i)).sub_const (∫ a, s a ∂P)
    fun_prop
  refine hseq.congr_map hT hseq.aemeasurable_limit (.of_forall fun n ↦ ?_) rfl
  let f : (ℕ → α) → (Fin n → α) := fun ω i ↦ ω i
  have hf : AEMeasurable f Q :=
    (Measurable.of_eval fun i : Fin n ↦ measurable_pi_apply (i : ℕ)).aemeasurable
  have hproj : Q.map f = Measure.pi fun _ : Fin n ↦ P := by
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  rw [← hproj, AEMeasurable.map_map_of_aemeasurable (by rw [hproj]; exact hT n) hf]
  exact Measure.map_congr (.of_forall fun ω ↦ by
    rw [hmean, Function.comp_apply, Fin.sum_univ_eq_sum_range (fun k ↦ s (ω k) - ∫ a, s a ∂P)])

end CentralLimitTheorem

end TauCeti
