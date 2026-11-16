/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.Instances.Matrix
import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation
import TauCeti.MeasureTheory.Function.TendstoInDistribution
import TauCeti.Probability.CentralLimitTheorem.Lindeberg
import TauCeti.Probability.CramerWold
import TauCeti.Probability.Distributions.Gaussian.Transforms

/-!
# Multivariate Lindeberg–Feller and central limit theorems

This file establishes central limit theorems for random vectors taking values in a
finite-dimensional Euclidean space `EuclideanSpace ℝ κ`, allowing singular limiting covariance
matrices throughout and imposing no global measurability hypotheses beyond square-integrability
(or almost-everywhere measurability when moments are deduced from asymptotic bounds).

## Main results

* `TauCeti.tendstoInDistribution_sum_of_lindeberg`: the **multivariate Lindeberg–Feller central
  limit theorem** for triangular arrays of row-wise independent, centred, square-integrable random
  vectors whose row covariance matrices converge to `S` and whose norms satisfy the Lindeberg
  condition `∑ i, ∫_{ε < ‖Y n i‖} ‖Y n i‖² → 0`. Positive semidefiniteness of `S` is derived
  automatically as a closed-cone limit of the row covariance matrices.
* `TauCeti.tendstoInDistribution_sum_of_norm_le_eventually`: multivariate Lindeberg–Feller under
  asymptotic uniform norm negligibility (`∀ δ > 0, ∀ᶠ n, ∀ i, ‖Y n i‖ ≤ δ` a.e.), deriving
  eventual square-integrability from almost-everywhere measurability and the norm bound.
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
`TauCeti.tendstoInDistribution_iff_tendstoInDistribution_inner`, both main theorems reduce to one
dimension along every projection `z ↦ ⟪z, t⟫`. In each direction `t`, Cauchy–Schwarz transfers the
Euclidean Lindeberg condition to the scalar Lindeberg condition at threshold `δ` via radius
`δ / (2 ‖t‖)`, `TauCeti.variance_inner_eq_inner_covMatrix_map` identifies the projected variance as
`⟪t, (covMatrix …).toEuclideanLin t⟫`, and `TauCeti.Probability.map_inner_multivariateGaussian`
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
  have hproj_L2 : MemLp (fun ω ↦ ⟪Y n i ω, t⟫) 2 (μ n) := by
    simpa only [Function.comp_def, real_inner_comm t, coe_innerSL_apply] using
      (innerSL ℝ t).comp_memLp' (hL2 n i)
  have hY_sq : Integrable (fun ω ↦ ‖Y n i ω‖ ^ 2) (μ n) :=
    (memLp_two_iff_integrable_sq_norm (hL2 n i).aestronglyMeasurable).1 (hL2 n i)
  have hs : NullMeasurableSet {ω | ε < ‖Y n i ω‖} (μ n) :=
    nullMeasurableSet_lt aemeasurable_const (hL2 n i).aestronglyMeasurable.norm.aemeasurable
  rw [← integral_indicator₀ hs, ← integral_const_mul]
  refine integral_mono (hproj_L2.integrable_indicator_sq δ) ((hY_sq.indicator₀ hs).const_mul _)
    fun ω ↦ ?_
  by_cases hω : δ ≤ |⟪Y n i ω, t⟫|
  · have hcs : |⟪Y n i ω, t⟫| ≤ ‖Y n i ω‖ * ‖t‖ := abs_real_inner_le_norm (Y n i ω) t
    have hεlt : ε < ‖Y n i ω‖ := by
      have hdiv : δ / ‖t‖ ≤ ‖Y n i ω‖ := (div_le_iff₀ ht_pos).2 (hω.trans hcs)
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
  have hS : S.PosSemidef := by
    refine isClosed_setOfPred_posSemidef.mem_of_tendsto hcov (.of_forall fun n ↦ ?_)
    refine (Matrix.PosSemidef.addSubmonoid κ ℝ).sum_mem fun i _ ↦ ?_
    have hm : AEMeasurable (Y n i) (μ n) := (hL2 n i).aestronglyMeasurable.aemeasurable
    exact posSemidef_covMatrix _ ((memLp_map_measure_iff aestronglyMeasurable_id hm).2 (hL2 n i))
  refine tendstoInDistribution_iff_tendstoInDistribution_inner.2 fun t ↦ ?_
  simp_rw [sum_inner]
  have hZt : HasLaw (fun ω' ↦ ⟪Z ω', t⟫)
      (gaussianReal 0 (⟪t, S.toEuclideanLin t⟫).toNNReal) μ' := by
    have hZ_meas : AEMeasurable Z μ' := hZ.aemeasurable
    refine ⟨by fun_prop, ?_⟩
    have hcomp : (fun ω' ↦ ⟪Z ω', t⟫) = (fun z ↦ ⟪t, z⟫) ∘ Z :=
      funext fun ω' ↦ real_inner_comm t (Z ω')
    rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop : Measurable _).aemeasurable
      hZ_meas, hZ.map_eq, TauCeti.Probability.map_inner_multivariateGaussian 0 t hS,
      inner_zero_right]
  refine hZt.tendstoInDistribution_sum_of_lindeberg
    (fun n ↦ (hindep n).comp (fun _ z ↦ ⟪z, t⟫)
      fun _ ↦ (continuous_id.inner continuous_const).measurable)
    (fun n i ↦ by
      simpa only [Function.comp_def, real_inner_comm t, coe_innerSL_apply] using
        (innerSL ℝ t).comp_memLp' (hL2 n i))
    (fun n i ↦ by
      simp_rw [real_inner_comm t]
      rw [integral_inner (𝕜 := ℝ) ((hL2 n i).integrable one_le_two) t, hmean n i,
        inner_zero_right])
    ?_ (fun δ hδ ↦ tendsto_sum_indicator_inner_sq_of_lindeberg hL2 hlind t hδ)
  have hSt_nn : 0 ≤ ⟪t, S.toEuclideanLin t⟫ := by
    simpa only [RCLike.re_to_real, real_inner_comm] using
      (Matrix.isPositive_toEuclideanLin_iff.mpr hS).2 t
  rw [Real.coe_toNNReal _ hSt_nn]
  have hquad_cont : Continuous (fun A : Matrix κ κ ℝ ↦ ⟪t, A.toEuclideanLin t⟫) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct]
    fun_prop
  refine (hquad_cont.tendsto S |>.comp hcov).congr' (.of_forall fun n ↦ ?_)
  dsimp only [Function.comp_def]
  rw [map_sum, LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simpa only [real_inner_comm t] using (variance_inner_eq_inner_covMatrix_map (hL2 n i) t).symm

/-- **Multivariate Lindeberg–Feller theorem under asymptotic uniform norm negligibility.** If
row-wise independent, centred, almost-everywhere measurable random vectors `Y n i` satisfy
`∀ δ > 0, ∀ᶠ n in atTop, ∀ i, ∀ᵐ ω ∂(μ n), ‖Y n i ω‖ ≤ δ` and their row covariance matrices
converge to `S`, then `∑ i, Y n i` converges in distribution to `multivariateGaussian 0 S`. -/
theorem tendstoInDistribution_sum_of_norm_le_eventually [DecidableEq κ]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {Y : (n : ℕ) → ι n → Ω n → EuclideanSpace ℝ κ}
    {S : Matrix κ κ ℝ}
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → EuclideanSpace ℝ κ}
    (hindep : ∀ n, iIndepFun (Y n) (μ n))
    (hm : ∀ n i, AEMeasurable (Y n i) (μ n))
    (hmean : ∀ n i, ∫ ω, Y n i ω ∂(μ n) = 0)
    (hcov : Tendsto (fun n ↦ ∑ i, covMatrix ((μ n).map (Y n i))) atTop (𝓝 S))
    (hbound : ∀ δ > 0, ∀ᶠ n in atTop, ∀ i, ∀ᵐ ω ∂(μ n), ‖Y n i ω‖ ≤ δ)
    (hZ : HasLaw Z (multivariateGaussian 0 S) μ') :
    TendstoInDistribution (fun n ω ↦ ∑ i, Y n i ω) atTop Z μ μ' := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hbound 1 one_pos)
  let Y' : (n : ℕ) → ι n → Ω n → EuclideanSpace ℝ κ :=
    fun n i ↦ if N ≤ n then Y n i else 0
  have hY'_indep (n : ℕ) : iIndepFun (Y' n) (μ n) := by
    dsimp only [Y']; split_ifs
    · exact hindep n
    · exact (hindep n).comp (fun _ _ ↦ 0) fun _ ↦ measurable_const
  have hY'_L2 (n : ℕ) (i : ι n) : MemLp (Y' n i) 2 (μ n) := by
    dsimp only [Y']; split_ifs with hn
    · exact MemLp.of_bound (hm n i).aestronglyMeasurable 1 (hN n hn i)
    · exact MemLp.zero
  have hY'_mean (n : ℕ) (i : ι n) : ∫ ω, Y' n i ω ∂(μ n) = 0 := by
    dsimp only [Y']; split_ifs
    · exact hmean n i
    · exact integral_zero _ _
  have hY'_cov : Tendsto (fun n ↦ ∑ i, covMatrix ((μ n).map (Y' n i))) atTop (𝓝 S) := by
    refine hcov.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [Y', hn]
  have hY'_lind (ε : ℝ) (hε : 0 < ε) : Tendsto
      (fun n ↦ ∑ i, ∫ ω in {ω | ε < ‖Y' n i ω‖}, ‖Y' n i ω‖ ^ 2 ∂(μ n)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hbound ε hε, eventually_ge_atTop N] with n hεn hn
    symm
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hs : NullMeasurableSet {ω | ε < ‖Y' n i ω‖} (μ n) :=
      nullMeasurableSet_lt aemeasurable_const (hY'_L2 n i).aestronglyMeasurable.norm.aemeasurable
    rw [← integral_indicator₀ hs]
    refine integral_eq_zero_of_ae ((hεn i).mono fun ω hω ↦ ?_)
    simp only [Y', hn, ↓reduceIte]
    exact Set.indicator_of_notMem (not_lt.mpr hω) _
  have hclt := tendstoInDistribution_sum_of_lindeberg hY'_indep hY'_L2 hY'_mean hY'_cov hY'_lind hZ
  refine hclt.congr' (fun n ↦ Finset.aemeasurable_fun_sum _ fun i _ ↦ hm n i) ?_
    Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop N] with n hn
  exact .of_forall fun ω ↦ by simp [Y', hn]

/-- Dominated convergence sends the upper-tail second moment `∫_{|u| > R} u² ∂ν` to `0` as
`R → ∞`. -/
private theorem tendsto_integral_indicator_sq_atTop {ν : Measure ℝ}
    (hu2 : Integrable (fun u : ℝ ↦ u ^ 2) ν) :
    Tendsto (fun R : ℝ ↦ ∫ u, ({u | R < |u|}.indicator fun u ↦ u ^ 2) u ∂ν) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (F := fun (R : ℝ) (u : ℝ) ↦ ({u | R < |u|}.indicator fun u ↦ u ^ 2) u)
    (f := fun _ ↦ 0) (fun u : ℝ ↦ u ^ 2)
    (.of_forall fun R ↦ hu2.aestronglyMeasurable.indicator
      (measurableSet_lt measurable_const measurable_norm))
    (.of_forall fun R ↦ .of_forall fun u ↦ by
      by_cases h : R < |u|
      · rw [Set.indicator_of_mem (s := {u | R < |u|}) h, Real.norm_of_nonneg (sq_nonneg u)]
      · rw [Set.indicator_of_notMem (s := {u | R < |u|}) h, norm_zero]
        exact sq_nonneg u)
    hu2 (.of_forall fun u ↦ tendsto_const_nhds.congr' <| by
      filter_upwards [eventually_ge_atTop |u|] with R hR
      exact (Set.indicator_of_notMem (not_lt.mpr hR) _).symm)
  rwa [integral_zero] at h

/-- Single-summand upper-tail bound for a weighted scalar shock `ξ • w` when `‖w‖ ≤ ε / R`. -/
private theorem setIntegral_norm_smul_sq_le
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {μ₀ : Measure Ω₀}
    {ξ₀ : Ω₀ → ℝ} {w₀ : EuclideanSpace ℝ κ} {ν : Measure ℝ}
    (hlaw : HasLaw ξ₀ ν μ₀) (hL2 : MemLp id 2 ν)
    {ε R : ℝ} (hε : 0 < ε) (hRpos : 0 < R) (hw : ‖w₀‖ ≤ ε / R) :
    ∫ ω in {ω | ε < ‖ξ₀ ω • w₀‖}, ‖ξ₀ ω • w₀‖ ^ 2 ∂μ₀ ≤
      ‖w₀‖ ^ 2 * ∫ u, ({u | R < |u|}.indicator fun u ↦ u ^ 2) u ∂ν := by
  have hξm : AEMeasurable ξ₀ μ₀ := hlaw.aemeasurable
  have hξ2 : Integrable (fun ω ↦ ξ₀ ω ^ 2) μ₀ :=
    ((memLp_map_measure_iff aestronglyMeasurable_id hξm).1
      (by rwa [hlaw.map_eq])).integrable_sq
  have hs : NullMeasurableSet {ω | ε < ‖ξ₀ ω • w₀‖} μ₀ :=
    nullMeasurableSet_lt aemeasurable_const (by fun_prop)
  have hmap_ind : ∫ u, ({u | R < |u|}.indicator fun u ↦ u ^ 2) u ∂ν =
      ∫ ω, ({ω | R < |ξ₀ ω|}.indicator fun ω ↦ ξ₀ ω ^ 2) ω ∂μ₀ := by
    rw [← hlaw.map_eq]
    exact integral_map hξm
      ((by fun_prop : Measurable fun u : ℝ ↦ u ^ 2).aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const (by fun_prop : Measurable fun u : ℝ ↦ |u|)))
  rw [← integral_indicator₀ hs, hmap_ind, ← integral_const_mul]
  refine integral_mono
    (((hξ2.mul_const (‖w₀‖ ^ 2)).congr (.of_forall fun ω ↦ ?_)).indicator₀ hs)
    ((hξ2.indicator₀ (nullMeasurableSet_lt aemeasurable_const hξm.norm)).const_mul _) fun ω ↦ ?_
  · simp [norm_smul, mul_pow]
  · by_cases hω : ε < ‖ξ₀ ω • w₀‖
    · have hω' : ε < |ξ₀ ω| * ‖w₀‖ := by rwa [norm_smul, Real.norm_eq_abs] at hω
      have hw_pos : 0 < ‖w₀‖ := pos_of_mul_pos_right (hε.trans hω') (abs_nonneg _)
      have hRlt : R < |ξ₀ ω| :=
        lt_of_mul_lt_mul_right (((le_div_iff₀' hRpos).1 hw).trans_lt hω') hw_pos.le
      rw [Set.indicator_of_mem (s := {ω | ε < ‖ξ₀ ω • w₀‖}) hω,
        Set.indicator_of_mem (s := {ω | R < |ξ₀ ω|}) hRlt,
        norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_comm]
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
  have htail := tendsto_integral_indicator_sq_atTop hL2.integrable_sq
  have htrace : Tendsto (fun n ↦ ∑ i, ‖w n i‖ ^ 2) atTop (𝓝 Q.trace) := by
    have hcont : Continuous (fun A : Matrix κ κ ℝ ↦ A.trace) := by
      simp only [Matrix.trace, Matrix.diag_apply]; fun_prop
    refine (hcont.tendsto Q |>.comp hgram).congr fun n ↦ ?_
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Function.comp_def, Matrix.trace, Matrix.diag_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, sq]
    exact Finset.sum_comm
  rw [Metric.tendsto_nhds]
  intro η hη
  set M : ℝ := |Q.trace| + 1
  have hM : 0 < M := by positivity
  obtain ⟨R, hRpos, hRtail⟩ : ∃ R > 0,
      ∫ u, ({u | R < |u|}.indicator fun u ↦ u ^ 2) u ∂ν < η / (2 * M) :=
    ((eventually_gt_atTop (0 : ℝ)).and
      (htail (Iio_mem_nhds (div_pos hη (mul_pos two_pos hM))))).exists
  filter_upwards [hmax (ε / R) (div_pos hε hRpos),
    htrace (Iio_mem_nhds (by linarith [le_abs_self Q.trace] : Q.trace < M))] with n hwn hsum
  have hsum_lt : ∑ i, ‖w n i‖ ^ 2 < M := hsum
  have htail0 : 0 ≤ ∫ u, ({u | R < |u|}.indicator fun u ↦ u ^ 2) u ∂ν :=
    integral_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
  have hnonneg : 0 ≤ ∑ i, ∫ ω in {ω | ε < ‖ξ n i ω • w n i‖}, ‖ξ n i ω • w n i‖ ^ 2 ∂(μ n) :=
    Finset.sum_nonneg fun i _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  refine (le_trans (b := (∑ i, ‖w n i‖ ^ 2) *
    ∫ u, ({u | R < |u|}.indicator fun u ↦ u ^ 2) u ∂ν) ?_ ?_).trans_lt (half_lt_self hη)
  · rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦
      setIntegral_norm_smul_sq_le (hlaw n i) hL2 hε hRpos (hwn i)
  · calc (∑ i, ‖w n i‖ ^ 2) * ∫ u, ({u | R < |u|}.indicator fun u ↦ u ^ 2) u ∂ν
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
  have hξL2 (n : ℕ) (i : ι n) : MemLp (ξ n i) 2 (μ n) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (hlaw n i).aemeasurable).1
      (by rwa [(hlaw n i).map_eq])
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
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hlaw n i).aemeasurable]
    rfl
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
  have hX0m : AEMeasurable (X 0) μ := hL2.aestronglyMeasurable.aemeasurable
  have hS : (covMatrix (μ.map (X 0))).PosSemidef :=
    posSemidef_covMatrix _ ((memLp_map_measure_iff aestronglyMeasurable_id hX0m).2 hL2)
  refine tendstoInDistribution_iff_tendstoInDistribution_inner.2 fun t ↦ ?_
  set U : ℕ → Ω → ℝ := fun i ω ↦ ⟪t, X i ω⟫
  have hU_var : Var[U 0; μ] = ⟪t, (covMatrix (μ.map (X 0))).toEuclideanLin t⟫ :=
    variance_inner_eq_inner_covMatrix_map hL2 t
  have hZt : HasLaw (fun ω' ↦ ⟪Z ω', t⟫) (gaussianReal 0 Var[U 0; μ].toNNReal) μ' := by
    have hZm : AEMeasurable Z μ' := hZ.aemeasurable
    refine ⟨by fun_prop, ?_⟩
    have hcomp : (fun ω' ↦ ⟪Z ω', t⟫) = (fun z ↦ ⟪t, z⟫) ∘ Z :=
      funext fun ω' ↦ real_inner_comm t (Z ω')
    rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop : Measurable _).aemeasurable
      hZm, hZ.map_eq, TauCeti.Probability.map_inner_multivariateGaussian 0 t hS, inner_zero_right,
      hU_var]
  have hclt := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub hZt
    ((innerSL ℝ t).comp_memLp' hL2)
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
  let s' : α → EuclideanSpace ℝ κ := hs.aestronglyMeasurable.mk s
  have hs'_meas : Measurable s' := hs.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hs_ae : s =ᵐ[P] s' := hs.aestronglyMeasurable.ae_eq_mk
  have hQ_eval (i : ℕ) : Q.map (fun ω : ℕ → α ↦ ω i) = P := Measure.infinitePi_map_eval _ i
  have hX_ae (i : ℕ) : (fun ω : ℕ → α ↦ s' (ω i)) =ᵐ[Q] (fun ω ↦ s (ω i)) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ P) i).quasiMeasurePreserving.ae_eq_comp
      hs_ae.symm
  have hindep : iIndepFun (fun i (ω : ℕ → α) ↦ s (ω i)) Q :=
    (iIndepFun_infinitePi (P := fun _ : ℕ ↦ P) fun _ ↦ hs'_meas).congr hX_ae
  have hX_meas (i : ℕ) : AEMeasurable (fun ω : ℕ → α ↦ s (ω i)) Q :=
    (hs'_meas.comp (measurable_pi_apply i)).aemeasurable.congr (hX_ae i)
  have hX_map (i : ℕ) : Q.map (fun ω : ℕ → α ↦ s (ω i)) = P.map s := by
    rw [← hQ_eval i, AEMeasurable.map_map_of_aemeasurable
      (by rw [hQ_eval i]; exact hs.aestronglyMeasurable.aemeasurable)
      (by fun_prop : Measurable _).aemeasurable]
    rfl
  have hident (i : ℕ) : IdentDistrib (fun ω : ℕ → α ↦ s (ω i)) (fun ω ↦ s (ω 0)) Q Q :=
    ⟨hX_meas i, hX_meas 0, by rw [hX_map i, hX_map 0]⟩
  have hX0_L2 : MemLp (fun ω : ℕ → α ↦ s (ω 0)) 2 Q :=
    (memLp_map_measure_iff (by rw [hQ_eval 0]; exact hs.aestronglyMeasurable)
      (by fun_prop : Measurable _).aemeasurable).1 (by rwa [hQ_eval 0])
  have hZ' : HasLaw Z (multivariateGaussian 0 (covMatrix (Q.map fun ω ↦ s (ω 0)))) μ' := by
    rwa [hX_map 0]
  have hseq := tendstoInDistribution_inv_sqrt_smul_sum_sub_euclidean hident hindep hX0_L2 hZ'
  have hmean : ∫ ω', s (ω' 0) ∂Q = ∫ a, s a ∂P := by
    rw [← hQ_eval 0, integral_map (by fun_prop : Measurable _).aemeasurable
      (by rw [hQ_eval 0]; exact hs.aestronglyMeasurable)]
  have hTn_meas (n : ℕ) : AEMeasurable
      (fun x : Fin n → α ↦ (√(n : ℝ))⁻¹ • ∑ i : Fin n, (s (x i) - ∫ a, s a ∂P))
      (Measure.pi fun _ : Fin n ↦ P) := by
    have hcoord (i : Fin n) : AEMeasurable (fun x : Fin n → α ↦ s (x i))
        (Measure.pi fun _ : Fin n ↦ P) :=
      hs.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ P) i)
    have hsum := Finset.aemeasurable_fun_sum Finset.univ
      fun i _ ↦ (hcoord i).sub_const (∫ a, s a ∂P)
    fun_prop
  refine ⟨hTn_meas, hZ.aemeasurable,
    hseq.tendsto.congr fun n ↦ ProbabilityMeasure.toMeasure_injective ?_⟩
  simp only [ProbabilityMeasure.coe_mk]
  have hr : Q.map (fun (ω : ℕ → α) (i : Fin n) ↦ ω i) = Measure.pi fun _ : Fin n ↦ P := by
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  rw [← hr, AEMeasurable.map_map_of_aemeasurable (by rw [hr]; exact hTn_meas n)
    (by fun_prop : Measurable _).aemeasurable]
  congr 1; ext ω
  simp only [Function.comp_def, hmean, ← Fin.sum_univ_eq_sum_range]

end CentralLimitTheorem

end TauCeti
