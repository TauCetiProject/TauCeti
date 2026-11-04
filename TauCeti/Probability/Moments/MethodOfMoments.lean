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

/-!
# The method of moments

If probability measures `μₙ` on `ℝ` have all moments, the moments converge to those of a
probability measure `μ`, and `μ` is determined by its moments among probability measures with
all moments, then `μₙ → μ` weakly (the method of moments).

The proof is the standard one: bounded moments give tightness, Prokhorov's theorem gives compactness
of the sequence, and uniform integrability of the monomials (from the bounds on the higher moments)
identifies the moments of every weak limit point with those of `μ`.

## Main results

* `TauCeti.tendsto_probabilityMeasure_of_tendsto_integral_pow`: weak convergence from convergence
  of moments.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.MethodOfMoments

/-- The truncation of the real line to `[-R, R]`. -/
def clamp (R : ℝ) (x : ℝ) : ℝ := max (-R) (min x R)

theorem continuous_clamp (R : ℝ) : Continuous (clamp R) := by
  unfold clamp; fun_prop

theorem clamp_eq_self {R x : ℝ} (h : |x| ≤ R) : clamp R x = x := by
  rw [abs_le] at h
  simp [clamp, h.1, h.2]

theorem abs_clamp_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clamp R x| ≤ R := by
  rw [abs_le]
  unfold clamp
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem abs_clamp_le_abs {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clamp R x| ≤ |x| := by
  by_cases h : |x| ≤ R
  · rw [clamp_eq_self h]
  · have := abs_clamp_le hR x
    linarith [not_le.mp h]

/-- The `k`th power of the truncation of `x` to `[-R, R]`, as a bounded continuous function. -/
noncomputable def clampPow (R : ℝ≥0) (k : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => clamp R x ^ k)
    ((continuous_clamp R).pow k) ((R : ℝ) ^ k) fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_clamp_le R.2 x) k

theorem clampPow_apply (R : ℝ≥0) (k : ℕ) (x : ℝ) : clampPow R k x = clamp R x ^ k := rfl

theorem abs_pow_sub_clamp_pow_le {R : ℝ} (hR : 0 < R) {k : ℕ} (x : ℝ) :
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
          exact add_le_add_right (pow_le_pow_left₀ (abs_nonneg _) (abs_clamp_le_abs hR.le x) k) _
        _ = 2 * |x| ^ k := by ring
    refine h1.trans ?_
    rw [hx2, mul_div_assoc]
    gcongr
    exact le_mul_of_one_le_right (pow_nonneg (abs_nonneg x) k) ((one_le_div hRk0).2 hRk)

theorem abs_integral_sub_clampPow_le (ν : Measure ℝ) [IsFiniteMeasure ν] {R : ℝ≥0} (hR : 0 < R)
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

/-- A weak cluster point of a family with bounded `∫ g` belongs to every closed set that
eventually contains the integrals of `g`. -/
theorem integral_mem_of_mapClusterPt {μn : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : MapClusterPt ν atTop μn) (g : ℝ →ᵇ ℝ) {C : Set ℝ} (hC : IsClosed C)
    (h : ∀ᶠ n in atTop, ∫ x, g x ∂(μn n : Measure ℝ) ∈ C) : ∫ x, g x ∂(ν : Measure ℝ) ∈ C := by
  by_contra hmem
  have hc : Continuous fun p : ProbabilityMeasure ℝ => ∫ x, g x ∂(p : Measure ℝ) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction g
  have := (mapClusterPt_iff_frequently.1 (hν.continuousAt_comp hc.continuousAt)) Cᶜ
    (hC.isOpen_compl.mem_nhds hmem)
  exact this (h.mono fun n hn hn' => hn' hn)

/-- A set of finite measures on `ℝ` with uniformly bounded second moment is tight. -/
theorem isTightMeasureSet_of_integral_sq_le {S : Set (Measure ℝ)} {B : ℝ}
    (hS : ∀ ρ ∈ S, IsFiniteMeasure ρ ∧ Integrable (fun x : ℝ => x ^ 2) ρ ∧
      ∫ x, x ^ 2 ∂ρ ≤ B) : IsTightMeasureSet S := by
  refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε hε => ?_
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have hlim : Tendsto (fun R : ℝ => B / R ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  obtain ⟨R, hR1, hR0⟩ := ((hlim.eventually (gt_mem_nhds hε')).and (eventually_gt_atTop 0)).exists
  refine ⟨Icc (-R) R, isCompact_Icc, fun ρ hρ => ?_⟩
  obtain ⟨hfin, hint, hB⟩ := hS ρ hρ
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := ρ) (f := fun x : ℝ => x ^ 2)
    (ae_of_all _ fun x => sq_nonneg x) hint (R ^ 2)
  have hsub : (Icc (-R) R)ᶜ ⊆ {x : ℝ | R ^ 2 ≤ x ^ 2} := fun x hx => by
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    simp only [mem_ofPred_eq]
    rcases hx with hx | hx <;> nlinarith
  have hreal : ρ.real (Icc (-R) R)ᶜ ≤ B / R ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [measureReal_mono (μ := ρ) hsub, measureReal_nonneg (μ := ρ) (s := (Icc (-R) R)ᶜ),
      sq_nonneg R]
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε'.le).2 ?_ |>.trans_eq
    (ENNReal.ofReal_toReal hεtop)
  exact hreal.trans hR1.le

theorem eventually_clampPow_eq (k : ℕ) (x : ℝ) :
    ∀ᶠ N : ℕ in atTop, clampPow (N : ℝ≥0) k x = x ^ k :=
  (eventually_ge_atTop ⌈|x|⌉₊).mono fun N hN => by
    rw [clampPow_apply, clamp_eq_self]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hN)

theorem tendsto_clampPow (k : ℕ) (x : ℝ) :
    Tendsto (fun N : ℕ => clampPow (N : ℝ≥0) k x) atTop (𝓝 (x ^ k)) :=
  tendsto_const_nhds.congr' ((eventually_clampPow_eq k x).mono fun _ h => h.symm)

theorem clampPow_two_mul_le (R : ℝ≥0) (k : ℕ) (x : ℝ) : clampPow R (2 * k) x ≤ x ^ (2 * k) := by
  rw [clampPow_apply, ← (even_two_mul k).pow_abs x, ← (even_two_mul k).pow_abs (clamp R x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_clamp_le_abs R.2 x) _

/-- A weak cluster point of a sequence of probability measures with converging moments has
finite moments, equal to the limits. -/
theorem moments_of_mapClusterPt {μn : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {m : ℕ → ℝ} (hint : ∀ n k, Integrable (fun x : ℝ => x ^ k) (μn n : Measure ℝ))
    (hlim : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μn n : Measure ℝ)) atTop (𝓝 (m k)))
    (hν : MapClusterPt ν atTop μn) :
    (∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ)) ∧
      ∀ k, ∫ x, x ^ k ∂(ν : Measure ℝ) = m k := by
  choose B hB using fun k => (hlim (2 * k)).bddAbove_range
  have hB' : ∀ k n, ∫ x, x ^ (2 * k) ∂(μn n : Measure ℝ) ≤ B k := fun k n => hB k ⟨n, rfl⟩
  have htrunc : ∀ k (R : ℝ≥0), ∫ x, clampPow R (2 * k) x ∂(ν : Measure ℝ) ≤ B k := by
    intro k R
    refine integral_mem_of_mapClusterPt hν (clampPow R (2 * k)) (isClosed_Iic (a := B k))
      (Eventually.of_forall fun n => ?_)
    exact (integral_mono (BoundedContinuousFunction.integrable _ _) (hint n _)
      (clampPow_two_mul_le R k)).trans (hB' k n)
  have hint2 : ∀ k, Integrable (fun x : ℝ => x ^ (2 * k)) (ν : Measure ℝ) := by
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
  have hint1 : ∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) := by
    intro k
    refine Integrable.mono' ((integrable_const 1).add (hint2 k))
      (by fun_prop : Continuous fun x : ℝ => x ^ k).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have : x ^ (2 * k) = (|x| ^ k) ^ 2 := by rw [← abs_pow, sq_abs, ← pow_mul, mul_comm]
    rw [Real.norm_eq_abs, abs_pow]
    simp only [Pi.add_apply, this]
    nlinarith [sq_nonneg (|x| ^ k - 1)]
  refine ⟨hint1, fun k => ?_⟩
  rcases k.eq_zero_or_pos with rfl | hk
  · have h0 := hlim 0
    simp only [pow_zero, integral_const, probReal_univ, one_smul] at h0 ⊢
    exact (tendsto_nhds_unique h0 tendsto_const_nhds).symm
  have hA : ∀ N : ℕ, 0 < N →
      |∫ x, clampPow (N : ℝ≥0) k x ∂(ν : Measure ℝ) - m k| ≤ 2 * (B k / (N : ℝ) ^ k) := by
    intro N hN
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hmem := integral_mem_of_mapClusterPt hν (clampPow (N : ℝ≥0) k)
      (Metric.isClosed_closedBall (x := m k) (ε := 2 * (B k / (N : ℝ) ^ k) + δ))
      (((Metric.tendsto_nhds.1 (hlim k) δ hδ).mono fun n hn => ?_))
    · rw [Metric.mem_closedBall, Real.dist_eq] at hmem
      linarith
    · rw [Metric.mem_closedBall, Real.dist_eq]
      have h1 := abs_integral_sub_clampPow_le (μn n : Measure ℝ) (R := (N : ℝ≥0))
        (by exact_mod_cast hN) (hint n k) (hint n (2 * k))
      have h2 : (∫ x, x ^ (2 * k) ∂(μn n : Measure ℝ)) / (N : ℝ) ^ k ≤ B k / (N : ℝ) ^ k :=
        div_le_div_of_nonneg_right (hB' k n) (by positivity)
      rw [Real.dist_eq] at hn
      have e : ∫ x, clampPow (N : ℝ≥0) k x ∂(μn n : Measure ℝ) - m k =
          (∫ x, clampPow (N : ℝ≥0) k x ∂(μn n : Measure ℝ) - ∫ x, x ^ k ∂(μn n : Measure ℝ)) +
            (∫ x, x ^ k ∂(μn n : Measure ℝ) - m k) := by ring
      rw [abs_sub_comm] at h1
      rw [NNReal.coe_natCast] at h1
      rw [e]
      linarith [abs_add_le (∫ x, clampPow (N : ℝ≥0) k x ∂(μn n : Measure ℝ) -
        ∫ x, x ^ k ∂(μn n : Measure ℝ)) (∫ x, x ^ k ∂(μn n : Measure ℝ) - m k)]
  have hdc : Tendsto (fun N : ℕ => ∫ x, clampPow (N : ℝ≥0) k x ∂(ν : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ k ∂(ν : Measure ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖x ^ k‖)
      (fun N => (clampPow (N : ℝ≥0) k).continuous.aestronglyMeasurable) (hint1 k).norm
      (fun N => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => tendsto_clampPow k x)
    rw [clampPow_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_clamp_le_abs (NNReal.coe_nonneg _) x) k
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

open MethodOfMoments in
/-- **The method of moments.** Let `μn` be probability measures on `ℝ` with finite moments of all
orders, whose moments converge to those of `μ`. If `μ` is determined by its moments among
probability measures with finite moments, then `μn` converges weakly to `μ`. -/
theorem tendsto_probabilityMeasure_of_tendsto_integral_pow {μn : ℕ → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ}
    (hint : ∀ n k, Integrable (fun x : ℝ => x ^ k) (μn n : Measure ℝ))
    (hlim : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μn n : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ k ∂(μ : Measure ℝ))))
    (hdet : ∀ ν : ProbabilityMeasure ℝ, (∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ)) →
      (∀ k, ∫ x, x ^ k ∂(ν : Measure ℝ) = ∫ x, x ^ k ∂(μ : Measure ℝ)) → ν = μ) :
    Tendsto μn atTop (𝓝 μ) := by
  obtain ⟨B, hB⟩ := (hlim 2).bddAbove_range
  have htight : IsTightMeasureSet
      {((p : ProbabilityMeasure ℝ) : Measure ℝ) | p ∈ Set.range μn} := by
    refine isTightMeasureSet_of_integral_sq_le (B := B) ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨inferInstance, hint n 2, hB ⟨n, rfl⟩⟩
  refine (isCompact_closure_of_isTightMeasureSet htight).tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n => subset_closure ⟨n, rfl⟩) fun ν _ hν => ?_
  obtain ⟨h1, h2⟩ := moments_of_mapClusterPt hint hlim hν
  exact hdet ν h1 h2

end TauCeti
