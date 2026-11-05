/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import TauCeti.MeasureTheory.Function.PolynomialMemLp
public import TauCeti.MeasureTheory.Measure.Prokhorov
public import TauCeti.MeasureTheory.Measure.Tight.Basic
import TauCeti.Algebra.Order.Group.MinMax

/-!
# The method of moments

If probability measures `μₙ` on `ℝ` have moments that are eventually integrable and the moments
converge to those of a probability measure `μ`, and `μ` is determined by its moments among
probability measures with all moments, then `μₙ → μ` weakly (the method of moments).

The proof is the standard one: bounded moments give tightness, Prokhorov's theorem gives compactness
of the sequence, and uniform integrability of the monomials (from the bounds on the higher moments)
identifies the moments of every weak limit point with those of `μ`.

## Main results

* `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow_of_determined_moments`: weak
  convergence when the limit is determined by its moments.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley (1995), Theorem 30.2.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.MethodOfMoments

/-- The truncation of the real line to `[-R, R]`. -/
private def clamp (R : ℝ) (x : ℝ) : ℝ := max (-R) (min R x)

private theorem continuous_clamp (R : ℝ) : Continuous (clamp R) := by
  unfold clamp; fun_prop

private theorem clamp_eq_self {R x : ℝ} (h : |x| ≤ R) : clamp R x = x := by
  rw [abs_le] at h
  simp [clamp, h.1, h.2]

/-- The `k`th power of the truncation of `x` to `[-R, R]`, as a bounded continuous function. -/
private noncomputable def clampPow (R : ℝ≥0) (k : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => clamp R x ^ k)
    ((continuous_clamp R).pow k) ((R : ℝ) ^ k) fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (by simpa [clamp, abs_of_nonneg R.2] using
          TauCeti.abs_max_min_le (R : ℝ) x) k

private theorem clampPow_apply (R : ℝ≥0) (k : ℕ) (x : ℝ) :
    clampPow R k x = clamp R x ^ k := rfl

private theorem abs_pow_sub_clamp_pow_le {R : ℝ} (hR : 0 < R) {k : ℕ} (x : ℝ) :
    |x ^ k - clamp R x ^ k| ≤ 2 * (x ^ (2 * k) / R ^ k) := by
  have hx2 : x ^ (2 * k) = |x| ^ k * |x| ^ k := by
    rw [← pow_add, ← two_mul, pow_mul, pow_mul, sq_abs]
  by_cases h : |x| ≤ R
  · rw [clamp_eq_self h, sub_self, abs_zero, hx2]
    positivity
  · push Not at h
    have hRk : R ^ k ≤ |x| ^ k := pow_le_pow_left₀ hR.le h.le k
    have hRk0 : 0 < R ^ k := by positivity
    have h1 : |x ^ k - clamp R x ^ k| ≤ 2 * |x| ^ k := by
      calc |x ^ k - clamp R x ^ k| ≤ |x ^ k| + |clamp R x ^ k| := abs_sub _ _
        _ ≤ |x| ^ k + |x| ^ k := by
          rw [abs_pow, abs_pow]
          exact add_le_add_right (pow_le_pow_left₀ (abs_nonneg _)
            (TauCeti.abs_max_min_le_abs hR.le x) k) _
        _ = 2 * |x| ^ k := by ring
    refine h1.trans ?_
    rw [hx2, mul_div_assoc]
    gcongr
    exact le_mul_of_one_le_right (pow_nonneg (abs_nonneg x) k) ((one_le_div hRk0).2 hRk)

private theorem abs_integral_pow_sub_integral_clampPow_le
    (ν : Measure ℝ) [IsFiniteMeasure ν] {R : ℝ≥0} (hR : 0 < R)
    {k : ℕ} (h1 : Integrable (fun x : ℝ => x ^ k) ν)
    (h2 : Integrable (fun x : ℝ => x ^ (2 * k)) ν) :
    |∫ x, x ^ k ∂ν - ∫ x, clampPow R k x ∂ν| ≤ 2 * ((∫ x, x ^ (2 * k) ∂ν) / (R : ℝ) ^ k) := by
  have hg : Integrable (clampPow R k) ν := (clampPow R k).integrable ν
  rw [← integral_sub h1 hg, ← Real.norm_eq_abs]
  calc ‖∫ x, (x ^ k - clampPow R k x) ∂ν‖
      ≤ ∫ x, 2 * (x ^ (2 * k) / (R : ℝ) ^ k) ∂ν :=
        norm_integral_le_of_norm_le ((h2.div_const _).const_mul 2) (ae_of_all _ fun x => by
          simpa [clampPow_apply] using abs_pow_sub_clamp_pow_le (R := (R : ℝ))
            (by exact_mod_cast hR) (k := k) x)
    _ = _ := by rw [integral_const_mul, integral_div]

private theorem eventually_clampPow_eq (k : ℕ) (x : ℝ) :
    ∀ᶠ N : ℕ in atTop, clampPow (N : ℝ≥0) k x = x ^ k :=
  (eventually_ge_atTop ⌈|x|⌉₊).mono fun N hN => by
    rw [clampPow_apply, clamp_eq_self]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hN)

private theorem tendsto_clampPow (k : ℕ) (x : ℝ) :
    Tendsto (fun N : ℕ => clampPow (N : ℝ≥0) k x) atTop (𝓝 (x ^ k)) :=
  tendsto_const_nhds.congr' ((eventually_clampPow_eq k x).mono fun _ h => h.symm)

private theorem clampPow_two_mul_le (R : ℝ≥0) (k : ℕ) (x : ℝ) :
    clampPow R (2 * k) x ≤ x ^ (2 * k) := by
  rw [clampPow_apply, ← (even_two_mul k).pow_abs x, ← (even_two_mul k).pow_abs (clamp R x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (TauCeti.abs_max_min_le_abs R.2 x) _

private theorem integrable_pow_two_mul_of_clampPow_integral_le
    {ν : ProbabilityMeasure ℝ} {B : ℕ → ℝ}
    (htrunc : ∀ k (R : ℝ≥0), ∫ x, clampPow R (2 * k) x ∂(ν : Measure ℝ) ≤ B k) :
    ∀ k, Integrable (fun x : ℝ => x ^ (2 * k)) (ν : Measure ℝ) := by
  intro k
  have hc : Continuous fun x : ℝ => x ^ (2 * k) := by fun_prop
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => (even_two_mul k).pow_nonneg x)]
  calc ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(ν : Measure ℝ)
      = ∫⁻ x, liminf (fun N : ℕ => ENNReal.ofReal (clampPow (N : ℝ≥0) (2 * k) x)) atTop
          ∂(ν : Measure ℝ) := by
        congr 1; ext x
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (tendsto_clampPow _ x)).liminf_eq.symm
    _ ≤ liminf (fun N : ℕ => ∫⁻ x, ENNReal.ofReal (clampPow (N : ℝ≥0) (2 * k) x)
          ∂(ν : Measure ℝ)) atTop :=
        lintegral_liminf_le fun N =>
          (clampPow (N : ℝ≥0) (2 * k)).continuous.measurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal (B k) := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun N => ?_)
        rw [← ofReal_integral_eq_lintegral_ofReal (BoundedContinuousFunction.integrable _ _)
          (ae_of_all _ fun x => (even_two_mul k).pow_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (htrunc k N)
    _ < ⊤ := ENNReal.ofReal_lt_top

private theorem tendsto_integral_clampPow (ν : Measure ℝ) (k : ℕ)
    (hint : Integrable (fun x : ℝ => x ^ k) ν) :
    Tendsto (fun N : ℕ => ∫ x, clampPow (N : ℝ≥0) k x ∂ν) atTop
      (𝓝 (∫ x, x ^ k ∂ν)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖x ^ k‖)
    (fun N => (clampPow (N : ℝ≥0) k).continuous.aestronglyMeasurable) hint.norm
    (fun N => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => tendsto_clampPow k x)
  rw [clampPow_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (TauCeti.abs_max_min_le_abs (NNReal.coe_nonneg _) x) k

/-- A weak cluster point of a sequence of probability measures with converging moments has
finite moments, equal to the limits. -/
private theorem integrable_pow_and_integral_pow_eq_of_mapClusterPt
    {μn : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {m : ℕ → ℝ} (hint : ∀ k, ∀ᶠ n in atTop,
      Integrable (fun x : ℝ => x ^ k) (μn n : Measure ℝ))
    (hlim : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μn n : Measure ℝ)) atTop (𝓝 (m k)))
    (hν : MapClusterPt ν atTop μn) :
    (∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ)) ∧
      ∀ k, ∫ x, x ^ k ∂(ν : Measure ℝ) = m k := by
  -- The convergent even moments give uniform bounds along the sequence.
  choose B hB using fun k => (hlim (2 * k)).bddAbove_range
  have hB' : ∀ k n, ∫ x, x ^ (2 * k) ∂(μn n : Measure ℝ) ≤ B k :=
    fun k n => hB k ⟨n, rfl⟩
  -- Bounded truncations transfer these bounds to the cluster point; Fatou then gives its even
  -- moments, and domination by `1 + x^(2k)` gives all remaining moments.
  have htrunc : ∀ k (R : ℝ≥0), ∫ x, clampPow R (2 * k) x ∂(ν : Measure ℝ) ≤ B k := by
    intro k R
    refine MeasureTheory.ProbabilityMeasure.integral_mem_of_mapClusterPt hν
      (clampPow R (2 * k) : ℝ →ᵇ ℝ) (isClosed_Iic (a := B k) ) ?_
    filter_upwards [hint (2 * k)] with n hn
    exact (integral_mono (BoundedContinuousFunction.integrable _ _) hn
      (clampPow_two_mul_le R k)).trans (hB' k n)
  have hint2 := integrable_pow_two_mul_of_clampPow_integral_le htrunc
  have hint1 : ∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) := by
    intro k
    have hk : k ≤ 2 * k := by omega
    have hnorm2 : Integrable (fun x : ℝ => ‖x‖ ^ (2 * k)) (ν : Measure ℝ) := by
      simpa only [norm_pow] using (hint2 k).norm
    have hnormk := integrable_norm_pow_of_le
      (μ := (ν : Measure ℝ)) (f := id) (by fun_prop) hk hnorm2
    change Integrable (fun x : ℝ => ‖x‖ ^ k) (ν : Measure ℝ) at hnormk
    have hnormpow : Integrable (fun x : ℝ => ‖x ^ k‖) (ν : Measure ℝ) := by
      simpa only [norm_pow] using hnormk
    exact (integrable_norm_iff (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => x ^ k) (ν : Measure ℝ))).mp hnormpow
  refine ⟨hint1, fun k => ?_⟩
  rcases k.eq_zero_or_pos with rfl | hk
  · have h0 := hlim 0
    simp only [pow_zero, integral_const, probReal_univ, one_smul] at h0 ⊢
    exact (tendsto_nhds_unique h0 tendsto_const_nhds).symm
  -- A fixed truncation is continuous under weak convergence; its error is controlled by the
  -- higher moment bounds, so these truncated moments converge to the target moment.
  have hA : ∀ N : ℕ, 0 < N →
      |∫ x, clampPow (N : ℝ≥0) k x ∂(ν : Measure ℝ) - m k| ≤ 2 * (B k / (N : ℝ) ^ k) := by
    intro N hN
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hmem := MeasureTheory.ProbabilityMeasure.integral_mem_of_mapClusterPt hν
      (clampPow (N : ℝ≥0) k)
      (Metric.isClosed_closedBall (x := m k) (ε := 2 * (B k / (N : ℝ) ^ k) + δ))
      (by
        filter_upwards [hint k, hint (2 * k),
          Metric.tendsto_nhds.1 (hlim k) δ hδ] with n hk h2k hn
        rw [Metric.mem_closedBall, Real.dist_eq]
        have h1 := abs_integral_pow_sub_integral_clampPow_le (μn n : Measure ℝ)
          (R := (N : ℝ≥0)) (by exact_mod_cast hN) hk h2k
        have h2 : (∫ x, x ^ (2 * k) ∂(μn n : Measure ℝ)) / (N : ℝ) ^ k ≤
            B k / (N : ℝ) ^ k :=
          div_le_div_of_nonneg_right (hB' k n) (by positivity)
        rw [Real.dist_eq] at hn
        rw [abs_sub_comm] at h1
        rw [NNReal.coe_natCast] at h1
        have h1' : |∫ x, clampPow (N : ℝ≥0) k x ∂(μn n : Measure ℝ) -
            ∫ x, x ^ k ∂(μn n : Measure ℝ)| ≤ 2 * (B k / (N : ℝ) ^ k) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
        calc
          |∫ x, clampPow (N : ℝ≥0) k x ∂(μn n : Measure ℝ) - m k| ≤
              |∫ x, clampPow (N : ℝ≥0) k x ∂(μn n : Measure ℝ) -
                  ∫ x, x ^ k ∂(μn n : Measure ℝ)| +
                |∫ x, x ^ k ∂(μn n : Measure ℝ) - m k| := abs_sub_le _ _ _
          _ ≤ 2 * (B k / (N : ℝ) ^ k) + δ := add_le_add h1' hn.le)
    · rw [Metric.mem_closedBall, Real.dist_eq] at hmem
      linarith
  -- Dominated convergence removes the truncation on the cluster point.
  have hdc := tendsto_integral_clampPow (ν : Measure ℝ) k (hint1 k)
  have hsq : Tendsto (fun N : ℕ => ∫ x, clampPow (N : ℝ≥0) k x ∂(ν : Measure ℝ)) atTop
      (𝓝 (m k)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hz : Tendsto (fun N : ℕ => 2 * (B k / (N : ℝ) ^ k)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := B k)).div_atTop
        ((tendsto_pow_atTop hk.ne').comp tendsto_natCast_atTop_atTop)
      simpa using this.const_mul 2
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_gt_atTop 0).mono fun N hN => ?_) hz
    simpa [Real.norm_eq_abs] using hA N hN
  exact tendsto_nhds_unique hdc hsq

end MethodOfMoments

end TauCeti

namespace MeasureTheory.ProbabilityMeasure

open TauCeti.MethodOfMoments

/-- **The method of moments.** Let `μn` be probability measures on `ℝ` whose moments are
eventually finite and converge to those of `μ`. If `μ` is determined by its moments among
probability measures with finite moments, then `μn` converges weakly to `μ`. -/
theorem tendsto_of_tendsto_integral_pow_of_determined_moments
    {μn : ℕ → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ}
    (hint : ∀ k, ∀ᶠ n in atTop, Integrable (fun x : ℝ => x ^ k) (μn n : Measure ℝ))
    (hlim : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μn n : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ k ∂(μ : Measure ℝ))))
    (hdet : ∀ ν : ProbabilityMeasure ℝ, (∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ)) →
      (∀ k, ∫ x, x ^ k ∂(ν : Measure ℝ) = ∫ x, x ^ k ∂(μ : Measure ℝ)) → ν = μ) :
    Tendsto μn atTop (𝓝 μ) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hint 2)
  let μtail : ℕ → ProbabilityMeasure ℝ := fun n => μn (n + N)
  have hint_tail : ∀ k, ∀ᶠ n in atTop,
      Integrable (fun x : ℝ => x ^ k) (μtail n : Measure ℝ) := by
    intro k
    obtain ⟨Nk, hNk⟩ := Filter.eventually_atTop.1 (hint k)
    filter_upwards [eventually_ge_atTop Nk] with n hn
    exact hNk (n + N) (by omega)
  have hint2_tail : ∀ n, Integrable (fun x : ℝ => x ^ 2) (μtail n : Measure ℝ) := by
    intro n
    exact hN (n + N) (by omega)
  have hlim_tail : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μtail n : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ k ∂(μ : Measure ℝ))) := by
    intro k
    change Tendsto
      (fun n => (fun j => ∫ x, x ^ k ∂(μn j : Measure ℝ)) (n + N)) atTop _
    exact (hlim k).comp (tendsto_add_atTop_nat N)
  obtain ⟨B, hB⟩ := (hlim 2).bddAbove_range
  have htight : IsTightMeasureSet
      ((fun p : ProbabilityMeasure ℝ => (p : Measure ℝ)) '' Set.range μtail) := by
    refine TauCeti.isTightProbabilityMeasureSet_of_integral_sq_le (B := B) ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨hint2_tail n, hB ⟨n + N, rfl⟩⟩
  have htail : Tendsto μtail atTop (𝓝 μ) := by
    refine (isCompact_closure_of_isTightMeasureSet htight).tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun n => subset_closure ⟨n, rfl⟩) fun ν _ hν => ?_
    obtain ⟨h1, h2⟩ := integrable_pow_and_integral_pow_eq_of_mapClusterPt
      hint_tail hlim_tail hν
    exact hdet ν h1 h2
  exact (tendsto_add_atTop_iff_nat N).mp (by simpa [μtail] using htail)

end MeasureTheory.ProbabilityMeasure
