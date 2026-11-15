/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Topology.MetricSpace.ModulusOfContinuity

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.Probability.BrownianMotion.NormalizedIncrements
import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Probability.Moments.SubGaussian

/-!
# Lévy's exact uniform modulus of continuity for Brownian motion

For a standard one-dimensional Brownian motion `B` (`ProbabilityTheory.IsBrownianReal B P`) and
every positive finite horizon `T > 0`, almost surely
`modulusOfContinuityOn (B · ω) (Set.Iic T) h / √(2 * h * Real.log (1 / h)) → 1` as `h → 0⁺`.
Moreover, monotonicity of the modulus in `T` together with countable rational-scale squeezing
yields a single common full-measure event on which this limit holds simultaneously for every
`T > 0`.

## Proof outline

* **Deterministic comparison (`HolderOnWith`, `LipschitzOnWith`)**: Any Hölder path of exponent
  `r > 1 / 2` (in particular any Lipschitz or affine path) has Lévy-normalized modulus ratio
  tending to `0` as `h → 0⁺`.
* **Unit-horizon upper bound**: For `q ≥ 2` and `ε = 1 / q`, at dyadic level `n` we bound all
  increments `|B ((i + k) / 2 ^ n) - B (i / 2 ^ n)|` over step counts `1 ≤ k ≤ 2 ^ (n / (3 * q))`
  using the sub-Gaussian Chernoff tail of centered Gaussian increments. The union over at most
  `2 * 2 ^ (n + n / (3 * q))` pairs has probability `O(2 ^ (-ε * n))`, which is summable in `n`.
  Outside the Borel–Cantelli exceptional event, `TauCeti.modulusOfContinuityOn_Iic_one_le_of_dyadic`
  applied at level `n = m + m / (3 * q)` for `h ∈ (2 ^ (-(m + 1)), 2 ^ (-m)]` bounds the coarse
  dyadic jump by `(1 + ε) ^ 2 * √(2 * h * log (1 / h))` and the binary-refinement tail by
  `o(√(2 * h * log (1 / h)))`.
* **Unit-horizon lower bound**: For `q ≥ 2`, `ε = 1 / q`, and `b = 1 + 1 / q > 1`, at mesh
  `δ_n = (b ^ (n + 1))⁻¹` the `⌊b ^ (n + 1)⌋₊` standardized increments in `[0, 1]` are independent
  standard Gaussians (`IsPreBrownianReal.hasLaw_normalizedBrownianIncrements`). Using the Gaussian
  tail lower bound `gaussianPDFReal_add_one_le_measureReal_map_abs_Ioi`, the probability that all
  `⌊b ^ (n + 1)⌋₊` increments stay below `(1 - ε) * √(2 * log (1 / δ_n))` is summable in `n`.
  Comparing `h ∈ (δ_n, b * δ_n]` with `δ_n` yields asymptotic lower bound `(1 - ε) / √b`.
* **General horizon and scaling**: Brownian scaling `IsBrownianReal.smul` moves `[0, 1]` to
  `[0, T]` for `T > 0`, and `TauCeti.modulusOfContinuityOn_smul` scales the limit by `|c|` for
  `c • B`.

## References

* P. Lévy, *Théorie de l'addition des variables aléatoires*, Gauthier-Villars, 1937.
* P. Mörters, Y. Peres, *Brownian Motion*, Cambridge University Press, 2010, Theorem 1.14,
  Remark 1.18, and Exercise 1.7.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991,
  Theorem 2.9.25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

section DeterministicChecks

/-- Any `(C, r)`-Hölder map with exponent `r > 1 / 2` has Lévy-normalized uniform modulus tending
to `0` as `h → 0⁺`. -/
theorem HolderOnWith.tendsto_modulusOfContinuityOn_div_sqrt_mul_log_zero
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {C r : ℝ≥0} {f : X → Y} {S : Set X}
    (hf : HolderOnWith C r f S) (hr : (1 / 2 : ℝ) < r) :
    Tendsto (fun h : ℝ ↦ TauCeti.modulusOfContinuityOn f S h / √(2 * h * Real.log (1 / h)))
      (𝓝[>] 0) (𝓝 0) := by
  have : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hden_pos : 0 < √(2 * Real.log 2) := Real.sqrt_pos.2 (by positivity)
  have h_id : Tendsto (fun h : ℝ ↦ h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hpow : Tendsto (fun h : ℝ ↦ (C : ℝ) / √(2 * Real.log 2) * h ^ ((r : ℝ) - 1 / 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using
      (h_id.rpow_const_nhds_zero (sub_pos.2 hr)).const_mul ((C : ℝ) / √(2 * Real.log 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with h _
    exact div_nonneg (TauCeti.modulusOfContinuityOn_nonneg f S h) (Real.sqrt_nonneg _)
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with h hh
    have h1h : 2 ≤ 1 / h := by rw [le_div_iff₀ hh.1]; linarith [hh.2]
    have hlog_ge : Real.log 2 ≤ Real.log (1 / h) := Real.log_le_log zero_lt_two h1h
    have hsqrt_ge : √(2 * Real.log 2) * h ^ (1 / 2 : ℝ) ≤ √(2 * h * Real.log (1 / h)) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith [hh.1])
    calc TauCeti.modulusOfContinuityOn f S h / √(2 * h * Real.log (1 / h))
        ≤ (C : ℝ) * h ^ (r : ℝ) / (√(2 * Real.log 2) * h ^ (1 / 2 : ℝ)) :=
          div_le_div₀ (mul_nonneg C.coe_nonneg (Real.rpow_nonneg hh.1.le _))
            (hf.modulusOfContinuityOn_le hh.1.le)
            (mul_pos hden_pos (Real.rpow_pos_of_pos hh.1 _)) hsqrt_ge
      _ = (C : ℝ) / √(2 * Real.log 2) * (h ^ (r : ℝ) / h ^ (1 / 2 : ℝ)) := by ring
      _ = (C : ℝ) / √(2 * Real.log 2) * h ^ ((r : ℝ) - 1 / 2) := by
          rw [← Real.rpow_sub hh.1]

/-- Any Lipschitz map has Lévy-normalized uniform modulus tending to `0` as `h → 0⁺`. -/
theorem LipschitzOnWith.tendsto_modulusOfContinuityOn_div_sqrt_mul_log_zero
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {K : ℝ≥0} {f : X → Y} {S : Set X}
    (hf : LipschitzOnWith K f S) :
    Tendsto (fun h : ℝ ↦ TauCeti.modulusOfContinuityOn f S h / √(2 * h * Real.log (1 / h)))
      (𝓝[>] 0) (𝓝 0) :=
  hf.holderOnWith.tendsto_modulusOfContinuityOn_div_sqrt_mul_log_zero (by norm_num)

namespace TauCeti

/-- A deterministic affine path `t ↦ a * t + b` on `S : Set ℝ≥0` has Lévy-normalized uniform
modulus ratio tending to `0` as `h → 0⁺`. -/
theorem tendsto_modulusOfContinuityOn_affine_div_sqrt_mul_log_zero
    (a b : ℝ) (S : Set ℝ≥0) :
    Tendsto (fun h : ℝ ↦
      modulusOfContinuityOn (fun t : ℝ≥0 ↦ a * (t : ℝ) + b) S h / √(2 * h * Real.log (1 / h)))
      (𝓝[>] 0) (𝓝 0) := by
  have hlip : LipschitzOnWith ‖a‖₊ (fun t : ℝ≥0 ↦ a * (t : ℝ) + b) S :=
    LipschitzOnWith.of_dist_le_mul fun s _ t _ ↦ by
      simp only [Real.dist_eq, NNReal.dist_eq, coe_nnNorm, Real.norm_eq_abs]
      exact le_of_eq (by rw [← abs_mul]; congr 1; ring)
  exact hlip.tendsto_modulusOfContinuityOn_div_sqrt_mul_log_zero

end TauCeti

end DeterministicChecks

namespace ProbabilityTheory.IsBrownianReal

section UpperBoundHelpers

/-- `u ↦ u * log (1 / u)` is nondecreasing on `(0, exp (-1)]`. -/
private lemma mul_log_one_div_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hv : v ≤ Real.exp (-1)) :
    u * Real.log (1 / u) ≤ v * Real.log (1 / v) := by
  have hv_pos : 0 < v := hu.trans_le huv
  have htan := Real.mul_log_sub_mul_log_ge hv_pos hu.le
  have hlogv : Real.log v ≤ -1 := by simpa only [Real.log_exp] using Real.log_le_log hv_pos hv
  have hprod : 0 ≤ (u - v) * (Real.log v + 1) :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 huv) (by linarith)
  rw [one_div, Real.log_inv, one_div, Real.log_inv]
  linarith

private lemma nat_add_le_pow_mul {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    ((n + 1 + k : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (36 / 25 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hnk : (3 : ℝ) ≤ ((n + 1 + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ n + 1 + k)
    calc ((n + 1 + (k + 1) : ℕ) : ℝ) = ((n + 1 + k : ℕ) : ℝ) + 1 := by push_cast; ring
      _ ≤ (36 / 25 : ℝ) * ((n + 1 + k : ℕ) : ℝ) := by linarith
      _ ≤ (36 / 25 : ℝ) * (((n + 1 : ℕ) : ℝ) * (36 / 25 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = ((n + 1 : ℕ) : ℝ) * (36 / 25 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

private lemma sqrt_div_two_pow_step_le {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    √(((n + 1 + k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1 + k)) ≤
      √(((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) * (6 / 7 : ℝ) ^ k := by
  have hpow : (49 / 25 : ℝ) ^ k ≤ (2 : ℝ) ^ k :=
    pow_le_pow_left₀ (by positivity) (by norm_num) k
  have hfrac : ((n + 1 + k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1 + k) ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) * ((6 / 7 : ℝ) ^ k) ^ 2 := by
    have hsq : ((6 / 7 : ℝ) ^ k) ^ 2 = (36 / 25 : ℝ) ^ k / (49 / 25 : ℝ) ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul, ← div_pow]
      congr 1; norm_num
    rw [pow_add, ← div_div, hsq]
    calc ((n + 1 + k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) / (2 : ℝ) ^ k
        ≤ ((n + 1 : ℕ) : ℝ) * (36 / 25 : ℝ) ^ k / (2 : ℝ) ^ (n + 1) / (49 / 25 : ℝ) ^ k := by
          refine div_le_div₀ (by positivity) ?_ (by positivity) hpow
          exact div_le_div_of_nonneg_right (nat_add_le_pow_mul hn k) (by positivity)
      _ = ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) * ((36 / 25 : ℝ) ^ k / (49 / 25 : ℝ) ^ k) := by
          ring
  calc √(((n + 1 + k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1 + k))
      ≤ √(((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) * ((6 / 7 : ℝ) ^ k) ^ 2) :=
        Real.sqrt_le_sqrt hfrac
    _ = √(((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) * (6 / 7 : ℝ) ^ k := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

private lemma summable_const_mul_sqrt_div_two_pow (c : ℝ) :
    Summable (fun r : ℕ ↦ c * √((r : ℝ) / (2 : ℝ) ^ r)) := by
  refine Summable.mul_left c ((summable_nat_add_iff 3).1 ?_)
  refine Summable.of_nonneg_of_le (fun _ ↦ Real.sqrt_nonneg _)
    (fun k ↦ by simpa only [Nat.add_comm k 3] using sqrt_div_two_pow_step_le (n := 2) le_rfl k) ?_
  exact (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left _

private lemma tsum_sqrt_div_two_pow_le {n : ℕ} (hn : 2 ≤ n) :
    (∑' k : ℕ, √(((n + 1 + k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1 + k))) ≤
      7 * √(((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  have hgeom : Summable (fun k : ℕ ↦ (6 / 7 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hsum : Summable (fun k : ℕ ↦ √(((n + 1 + k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1 + k))) :=
    Summable.of_nonneg_of_le (fun _ ↦ Real.sqrt_nonneg _) (sqrt_div_two_pow_step_le hn)
      (hgeom.mul_left _)
  calc (∑' k : ℕ, √(((n + 1 + k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1 + k)))
      ≤ ∑' k : ℕ, √(((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) * (6 / 7 : ℝ) ^ k :=
        hsum.tsum_le_tsum (sqrt_div_two_pow_step_le hn) (hgeom.mul_left _)
    _ = √(((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) * (1 - 6 / 7 : ℝ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by norm_num)]
    _ = 7 * √(((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) := by ring

/-- Two-sided sub-Gaussian Chernoff bound for a pre-Brownian increment. -/
private lemma measure_abs_sub_gt_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | u < |B s ω - B t ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * dist (s : ℝ) t))) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hsub : HasSubgaussianMGF (B s - B t) (nndist s.1 t.1) P :=
    (hB.hasLaw_sub s t).hasSubgaussianMGF
  have hset : {ω | u < |B s ω - B t ω|} ⊆
      {ω | u ≤ (B s - B t) ω} ∪ {ω | u ≤ -(B s - B t) ω} := fun _ hω ↦
    by simpa only [mem_union, mem_ofPred_eq, Pi.sub_apply] using le_abs.1 hω.le
  refine (measure_mono hset).trans ((measure_union_le _ _).trans ?_)
  rw [← ofReal_measureReal (μ := P) (s := {ω | u ≤ (B s - B t) ω}),
    ← ofReal_measureReal (μ := P) (s := {ω | u ≤ -(B s - B t) ω}),
    ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := hsub.measure_ge_le hu
  have h2 := hsub.neg.measure_ge_le hu
  rw [coe_nndist] at h1 h2
  exact (add_le_add h1 h2).trans_eq (two_mul _).symm

private def dyadicBadEvent {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (p n : ℕ) : Set Ω :=
  ⋃ i ∈ Finset.range (2 ^ n + 1), ⋃ k ∈ Finset.Icc 1 (2 ^ (n / p)),
    {ω | i + k ≤ 2 ^ n ∧
      (1 + ε) * √(2 * ((k : ℝ) / (2 : ℝ) ^ n) * Real.log ((2 : ℝ) ^ n / k)) <
        |B (((i + k : ℕ) : ℝ≥0) / 2 ^ n) ω - B ((i : ℝ≥0) / 2 ^ n) ω|}

private lemma dist_le_of_notMem_dyadicBadEvent {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ε : ℝ}
    {p n i k : ℕ} {ω : Ω} (hnot : ω ∉ dyadicBadEvent B ε p n)
    (hk1 : 1 ≤ k) (hk_le : k ≤ 2 ^ (n / p)) (hik : i + k ≤ 2 ^ n) :
    dist (B (((i + k : ℕ) : ℝ≥0) / 2 ^ n) ω) (B ((i : ℝ≥0) / 2 ^ n) ω) ≤
      (1 + ε) * √(2 * ((k : ℝ) / (2 : ℝ) ^ n) * Real.log ((2 : ℝ) ^ n / k)) := by
  rw [Real.dist_eq]
  by_contra! hlt
  exact hnot (mem_biUnion (Finset.mem_range.2 (by omega))
    (mem_biUnion (Finset.mem_Icc.2 ⟨hk1, hk_le⟩) ⟨hik, hlt⟩))

private lemma measure_dyadicBadEvent_pair_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {q n i k : ℕ}
    (hk1 : 1 ≤ k) (hk_le : k ≤ 2 ^ (n / (3 * q))) (hik : i + k ≤ 2 ^ n) :
    P {ω | i + k ≤ 2 ^ n ∧
        (1 + 1 / (q : ℝ)) * √(2 * ((k : ℝ) / (2 : ℝ) ^ n) * Real.log ((2 : ℝ) ^ n / k)) <
          |B (((i + k : ℕ) : ℝ≥0) / 2 ^ n) ω - B ((i : ℝ≥0) / 2 ^ n) ω|} ≤
      ENNReal.ofReal (2 * ((2 : ℝ) ^ (-((1 + 1 / (q : ℝ)) ^ 2))) ^ (n - n / (3 * q))) := by
  set ε : ℝ := 1 / (q : ℝ)
  set p : ℕ := 3 * q
  set Δ : ℝ := (k : ℝ) / (2 : ℝ) ^ n
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hΔ_pos : 0 < Δ := div_pos hk_pos (by positivity)
  have hΔ_le : Δ ≤ (2 : ℝ) ^ (-((n - n / p : ℕ) : ℝ)) := by
    have hk_r : (k : ℝ) ≤ (2 : ℝ) ^ (n / p) := by exact_mod_cast hk_le
    refine (div_le_div_of_nonneg_right hk_r (by positivity)).trans_eq ?_
    rw [Real.rpow_neg zero_le_two, Real.rpow_natCast, inv_eq_one_div,
      div_eq_div_iff (by positivity) (by positivity), one_mul, mul_comm, ← pow_add,
      Nat.sub_add_cancel (Nat.div_le_self n p)]
  have hlog_nn : 0 ≤ Real.log ((2 : ℝ) ^ n / k) :=
    Real.log_nonneg ((one_le_div hk_pos).2 (by exact_mod_cast (by omega : k ≤ 2 ^ n)))
  set u : ℝ := (1 + ε) * √(2 * Δ * Real.log ((2 : ℝ) ^ n / k))
  have hu_nn : 0 ≤ u := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hdist : dist ((((i + k : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)
      ((((i : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) = Δ := by
    rw [Real.dist_eq, NNReal.coe_div, NNReal.coe_div]; push_cast
    rw [show ((i : ℝ) + k) / (2 : ℝ) ^ n - (i : ℝ) / (2 : ℝ) ^ n = Δ by dsimp [Δ]; ring]
    exact abs_of_pos hΔ_pos
  have hexp_eq : Real.exp (-u ^ 2 / (2 * Δ)) ≤ ((2 : ℝ) ^ (-((1 + ε) ^ 2))) ^ (n - n / p) := by
    have hu_sq : -u ^ 2 / (2 * Δ) = Real.log Δ * (1 + ε) ^ 2 := by
      have hsq := Real.sq_sqrt (show 0 ≤ 2 * Δ * Real.log ((2 : ℝ) ^ n / k) by positivity)
      dsimp only [u]; rw [mul_pow, hsq, show (2 : ℝ) ^ n / (k : ℝ) = Δ⁻¹ by simp [Δ], Real.log_inv]
      field_simp
    rw [hu_sq, Real.exp_mul, Real.exp_log hΔ_pos]
    refine (Real.rpow_le_rpow hΔ_pos.le hΔ_le (by positivity)).trans_eq ?_
    rw [← Real.rpow_mul zero_le_two, ← Real.rpow_natCast _ (n - n / p), ← Real.rpow_mul zero_le_two]
    congr 1; ring
  refine le_trans (measure_mono fun _ hω ↦ hω.2)
    ((measure_abs_sub_gt_le hB _ _ hu_nn).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hdist]; exact mul_le_mul_of_nonneg_left hexp_eq zero_le_two

private lemma dyadic_union_exponent_le {q n : ℕ} (hq : 2 ≤ q) :
    (n : ℝ) + (n / (3 * q) : ℕ) -
      (1 + 1 / (q : ℝ)) ^ 2 * ((n - n / (3 * q) : ℕ) : ℝ) ≤ -(1 / (q : ℝ)) * n := by
  set ε : ℝ := 1 / (q : ℝ)
  set p : ℕ := 3 * q
  have hε_le : ε ≤ 1 / 2 := one_div_le_one_div_of_le zero_lt_two (by exact_mod_cast hq)
  have hdiv3 : 3 * ((n / p : ℕ) : ℝ) ≤ ε * n := by
    have h1 : ((n / p : ℕ) : ℝ) * (3 * (q : ℝ)) ≤ n := by exact_mod_cast Nat.div_mul_le_self n p
    have hεq : ε * q = 1 := one_div_mul_cancel (by positivity)
    calc 3 * ((n / p : ℕ) : ℝ) = ε * (((n / p : ℕ) : ℝ) * (3 * (q : ℝ))) := by
          rw [← mul_one (3 * _), ← hεq]; ring
      _ ≤ ε * n := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hsub : ((n - n / p : ℕ) : ℝ) = (n : ℝ) - (n / p : ℕ) := Nat.cast_sub (Nat.div_le_self n p)
  have hsub_nn : 0 ≤ (n : ℝ) - (n / p : ℕ) := by rw [← hsub]; positivity
  have hsq_ge : (1 + 2 * ε) * ((n : ℝ) - (n / p : ℕ)) ≤ (1 + ε) ^ 2 * ((n : ℝ) - (n / p : ℕ)) :=
    mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ε]) hsub_nn
  have h2ε : (2 + 2 * ε) * ((n / p : ℕ) : ℝ) ≤ 3 * ((n / p : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  rw [hsub]; linarith

private lemma measure_dyadicBadEvent_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {q n : ℕ} (hq : 2 ≤ q) :
    P (dyadicBadEvent B (1 / (q : ℝ)) (3 * q) n) ≤
      ENNReal.ofReal (4 * ((2 : ℝ) ^ (-(1 / (q : ℝ)))) ^ n) := by
  set ε : ℝ := 1 / (q : ℝ)
  set p : ℕ := 3 * q
  refine (measure_biUnion_finset_le _ _).trans
    ((Finset.sum_le_sum fun _ _ ↦ measure_biUnion_finset_le _ _).trans ?_)
  have hterm (i k : ℕ) (hk : k ∈ Finset.Icc 1 (2 ^ (n / p))) :
      P {ω | i + k ≤ 2 ^ n ∧
          (1 + ε) * √(2 * ((k : ℝ) / (2 : ℝ) ^ n) * Real.log ((2 : ℝ) ^ n / k)) <
            |B (((i + k : ℕ) : ℝ≥0) / 2 ^ n) ω - B ((i : ℝ≥0) / 2 ^ n) ω|} ≤
        ENNReal.ofReal (2 * ((2 : ℝ) ^ (-((1 + ε) ^ 2))) ^ (n - n / p)) := by
    by_cases hik : i + k ≤ 2 ^ n
    · exact measure_dyadicBadEvent_pair_le hB (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2 hik
    · simp [hik]
  refine (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun k hk ↦ hterm i k hk).trans ?_
  simp only [Finset.sum_const, Finset.card_range, Nat.card_Icc, add_tsub_cancel_right,
    nsmul_eq_mul, ← mul_assoc]
  rw [← ENNReal.ofReal_natCast (2 ^ n + 1), ← ENNReal.ofReal_natCast (2 ^ (n / p)),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard1 : ((2 ^ n + 1 : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ n := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ one_le_two
    push_cast; linarith
  have hexp_le := dyadic_union_exponent_le (n := n) hq
  calc ((2 ^ n + 1 : ℕ) : ℝ) * ((2 ^ (n / p) : ℕ) : ℝ) *
        (2 * ((2 : ℝ) ^ (-((1 + ε) ^ 2))) ^ (n - n / p))
      ≤ 2 * (2 : ℝ) ^ n * (2 : ℝ) ^ (n / p) *
          (2 * ((2 : ℝ) ^ (-((1 + ε) ^ 2))) ^ (n - n / p)) := by gcongr; exact_mod_cast le_rfl
    _ = 4 * (2 : ℝ) ^ ((n : ℝ) + (n / p : ℕ) - (1 + ε) ^ 2 * ((n - n / p : ℕ) : ℝ)) := by
        have hrpow : (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ ((n / p : ℕ) : ℝ) *
            (2 : ℝ) ^ (-((1 + ε) ^ 2) * ((n - n / p : ℕ) : ℝ)) =
              (2 : ℝ) ^ ((n : ℝ) + (n / p : ℕ) - (1 + ε) ^ 2 * ((n - n / p : ℕ) : ℝ)) := by
          rw [← Real.rpow_add zero_lt_two, ← Real.rpow_add zero_lt_two]; ring_nf
        rw [← Real.rpow_natCast 2 n, ← Real.rpow_natCast 2 (n / p),
          ← Real.rpow_natCast _ (n - n / p), ← Real.rpow_mul zero_le_two, ← hrpow]
        ring
    _ ≤ 4 * (2 : ℝ) ^ (-ε * n) := by gcongr; exact one_le_two
    _ = 4 * ((2 : ℝ) ^ (-ε)) ^ n := by rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]

private lemma ae_eventually_notMem_dyadicBadEvent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {q : ℕ} (hq : 2 ≤ q) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ dyadicBadEvent B (1 / (q : ℝ)) (3 * q) n := by
  have hε_pos : (0 : ℝ) < 1 / (q : ℝ) := by positivity
  have hr_lt : (2 : ℝ) ^ (-(1 / (q : ℝ))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hsum_geom : Summable (fun n : ℕ ↦ 4 * ((2 : ℝ) ^ (-(1 / (q : ℝ)))) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hr_lt).mul_left 4
  exact ae_eventually_notMem (ne_top_of_le_ne_top hsum_geom.tsum_ofReal_ne_top
    (tsum_le_tsum fun _ ↦ measure_dyadicBadEvent_le hB hq))

private lemma sqrt_dyadic_tail_div_le {p m : ℕ} (hm : p + 2 ≤ m) :
    √(((m + m / p + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (m + m / p + 1)) /
      √(1 / (2 : ℝ) ^ m * ((m : ℝ) * Real.log 2)) ≤
        (1 / √(Real.log 2)) * √2 * (1 / √2) ^ (m / p) := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hnum_le : ((m + m / p + 1 : ℕ) : ℝ) ≤ 3 * (m : ℝ) := by
    have : m / p ≤ m := Nat.div_le_self m p
    exact_mod_cast (by omega : m + m / p + 1 ≤ 3 * m)
  rw [← Real.sqrt_div (by positivity)]
  have hinside : ((m + m / p + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (m + m / p + 1) /
      (1 / (2 : ℝ) ^ m * ((m : ℝ) * Real.log 2)) ≤ 2 / Real.log 2 * (1 / 2 : ℝ) ^ (m / p) := by
    have h32 : ((m + m / p + 1 : ℕ) : ℝ) / (2 : ℝ) ≤ 2 * (m : ℝ) := by linarith
    rw [pow_add, pow_add, pow_one]
    calc ((m + m / p + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ m * (2 : ℝ) ^ (m / p) * 2) /
          (1 / (2 : ℝ) ^ m * ((m : ℝ) * Real.log 2))
        = (((m + m / p + 1 : ℕ) : ℝ) / 2 / (m : ℝ)) / Real.log 2 * (1 / (2 : ℝ) ^ (m / p)) := by
            field_simp
      _ ≤ 2 / Real.log 2 * (1 / 2 : ℝ) ^ (m / p) := by
            rw [one_div_pow]; gcongr; rwa [div_le_iff₀ hm_pos]
  have hsqrt_pow : √((1 / 2 : ℝ) ^ (m / p)) = (1 / √2) ^ (m / p) := by
    rw [← Real.sqrt_sq (show 0 ≤ (1 / √2 : ℝ) ^ (m / p) by positivity)]
    congr 1; rw [← pow_mul, mul_comm _ 2, pow_mul]; congr 1
    rw [div_pow, Real.sq_sqrt zero_le_two, one_pow]
  refine (Real.sqrt_le_sqrt hinside).trans_eq ?_
  rw [Real.sqrt_mul (by positivity), Real.sqrt_div zero_le_two, hsqrt_pow]; ring

private lemma tail_div_sqrt_tendsto_zero (p : ℕ) (hp : 1 ≤ p) (c : ℝ) :
    Tendsto (fun m : ℕ ↦
      c * √(((m + m / p + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (m + m / p + 1)) /
        √(2 * (1 / (2 : ℝ) ^ (m + 1)) * ((m : ℝ) * Real.log 2))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun m : ℕ ↦
      (|c| / √(Real.log 2)) * √2 * ((1 / √2) ^ (m / p))) atTop (𝓝 0) := by
    have hr : (1 / √2 : ℝ) < 1 := (div_lt_one (Real.sqrt_pos.2 zero_lt_two)).2 Real.one_lt_sqrt_two
    have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).comp
      (Nat.tendsto_div_const_atTop (by omega : p ≠ 0))
    simpa [Function.comp_def] using hpow.const_mul ((|c| / √(Real.log 2)) * √2)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ici_mem_atTop (p + 2)] with m (hm : p + 2 ≤ m)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _),
    show (2 : ℝ) * (1 / (2 : ℝ) ^ (m + 1)) = 1 / (2 : ℝ) ^ m by rw [pow_succ]; field_simp,
    mul_div_assoc]
  exact (mul_le_mul_of_nonneg_left (sqrt_dyadic_tail_div_le hm) (abs_nonneg c)).trans_eq (by ring)

private lemma dyadic_mesh_bounds {m₀ : ℕ} {h : ℝ} (hh_pos : 0 < h)
    (hh_lt : h < (1 / 2 : ℝ) ^ m₀) :
    let m := ⌊Real.log (1 / h) / Real.log 2⌋₊
    m₀ ≤ m ∧ h ≤ 1 / (2 : ℝ) ^ m ∧ 1 / (2 : ℝ) ^ (m + 1) < h ∧
      (m : ℝ) * Real.log 2 ≤ Real.log (1 / h) := by
  intro m
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hh_lt1 : h < 1 := hh_lt.trans_le (pow_le_one₀ (by positivity) (by norm_num))
  have hm_ge : m₀ ≤ m := by
    refine Nat.le_floor ((le_div_iff₀ hlog2).2 ?_)
    have h2m₀ : (2 : ℝ) ^ m₀ ≤ 1 / h := by
      rw [one_div_pow, lt_div_iff₀ (by positivity)] at hh_lt
      rw [le_div_iff₀ hh_pos, mul_comm]; exact hh_lt.le
    exact (Real.log_pow 2 m₀).symm.trans_le (Real.log_le_log (by positivity) h2m₀)
  have hm_log : (m : ℝ) * Real.log 2 ≤ Real.log (1 / h) :=
    (le_div_iff₀ hlog2).1 (Nat.floor_le (div_nonneg
      (Real.log_nonneg ((one_le_div hh_pos).2 hh_lt1.le)) hlog2.le))
  have hh_le_2m : h ≤ 1 / (2 : ℝ) ^ m := by
    have h1 : (2 : ℝ) ^ m ≤ 1 / h :=
      (Real.log_le_log_iff (by positivity) (by positivity)).1 (by rwa [Real.log_pow])
    rwa [le_div_iff₀ hh_pos, mul_comm, ← le_div_iff₀ (by positivity)] at h1
  have hh_gt_2m1 : 1 / (2 : ℝ) ^ (m + 1) < h := by
    have h1 : 1 / h < (2 : ℝ) ^ (m + 1) := by
      refine (Real.log_lt_log_iff (by positivity) (by positivity)).1 ?_
      rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
      exact (div_lt_iff₀ hlog2).1 (Nat.lt_floor_add_one _)
    rwa [div_lt_iff₀ hh_pos, mul_comm, ← div_lt_iff₀ (by positivity)] at h1
  exact ⟨hm_ge, hh_le_2m, hh_gt_2m1, hm_log⟩

private lemma coarse_dyadic_dist_le {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω} {ε h : ℝ}
    {p m i j : ℕ} (hε_pos : 0 < ε) (hh_pos : 0 < h)
    (hh_le_2m : h ≤ 1 / (2 : ℝ) ^ m) (hh_gt_2m1 : 1 / (2 : ℝ) ^ (m + 1) < h)
    (h1εh : (1 + ε) * h ≤ Real.exp (-1)) (hpow_lt : (1 / 2 : ℝ) ^ (m / p) < ε / 2)
    (hnot : ω ∉ dyadicBadEvent B ε p (m + m / p))
    (hij : i < j) (hj : j ≤ 2 ^ (m + m / p))
    (hlen : ((j - i : ℕ) : ℝ) / (2 : ℝ) ^ (m + m / p) < h + 1 / (2 : ℝ) ^ (m + m / p)) :
    dist (B ((j : ℝ≥0) / 2 ^ (m + m / p)) ω) (B ((i : ℝ≥0) / 2 ^ (m + m / p)) ω) ≤
      (1 + ε) ^ 2 * √(2 * h * Real.log (1 / h)) := by
  set n : ℕ := m + m / p
  set k : ℕ := j - i
  have hk1 : 1 ≤ k := by omega
  have hk_le : k ≤ 2 ^ (n / p) := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hmul : (k : ℝ) < h * (2 : ℝ) ^ n + 1 := by
      have := mul_lt_mul_of_pos_right hlen h2
      rwa [div_mul_cancel₀ _ h2.ne', add_mul, one_div_mul_cancel h2.ne'] at this
    have hh2n : h * (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (m / p) :=
      (mul_le_mul_of_nonneg_right hh_le_2m h2.le).trans_eq (by dsimp [n]; rw [pow_add]; field_simp)
    have hk_r : (k : ℝ) < ((2 ^ (m / p) + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact (Nat.lt_succ_iff.1 (Nat.cast_lt.1 hk_r)).trans (Nat.pow_le_pow_right (by omega)
      (Nat.div_le_div_right (Nat.le_add_right m (m / p))))
  have hik : i + k = j := Nat.add_sub_of_le hij.le
  have h1 := dist_le_of_notMem_dyadicBadEvent hnot hk1 hk_le (hik ▸ hj)
  rw [hik] at h1; refine h1.trans ?_
  have h2n_lt : 1 / (2 : ℝ) ^ n < ε * h := by
    calc 1 / (2 : ℝ) ^ n = 2 * (1 / (2 : ℝ) ^ (m + 1)) * (1 / 2 : ℝ) ^ (m / p) := by
          rw [one_div_pow]; dsimp [n]; rw [pow_add, pow_add, pow_one]; field_simp
      _ < 2 * h * (ε / 2) := mul_lt_mul'' (mul_lt_mul_of_pos_left hh_gt_2m1 zero_lt_two) hpow_lt
          (by positivity) (by positivity)
      _ = ε * h := by ring
  set Δ : ℝ := (k : ℝ) / (2 : ℝ) ^ n
  have hΔ_pos : 0 < Δ := div_pos (by exact_mod_cast hk1) (by positivity)
  have hmono := mul_log_one_div_mono hΔ_pos (by linarith [hlen, h2n_lt]) h1εh
  have hlog_le : Real.log (1 / ((1 + ε) * h)) ≤ Real.log (1 / h) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hh_pos (by nlinarith))
  have hlog1h_nn : 0 ≤ Real.log (1 / h) :=
    Real.log_nonneg ((one_le_div hh_pos).2 (hh_le_2m.trans
      ((div_le_one (by positivity)).2 (one_le_pow₀ one_le_two))))
  have hprod_le : 2 * Δ * Real.log ((2 : ℝ) ^ n / k) ≤
      (1 + ε) ^ 2 * (2 * h * Real.log (1 / h)) := by
    rw [show (2 : ℝ) ^ n / (k : ℝ) = 1 / Δ by simp [Δ]]
    calc 2 * Δ * Real.log (1 / Δ) ≤ 2 * ((1 + ε) * h * Real.log (1 / ((1 + ε) * h))) := by linarith
      _ ≤ 2 * ((1 + ε) * h * Real.log (1 / h)) := by gcongr
      _ ≤ (1 + ε) ^ 2 * (2 * h * Real.log (1 / h)) := by
          nlinarith [mul_nonneg (sq_nonneg ε) (mul_nonneg hh_pos.le hlog1h_nn)]
  refine (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprod_le) (by positivity)).trans_eq ?_
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]; ring

private lemma dyadic_tail_tsum_div_sqrt_le {ε h : ℝ} {p m : ℕ}
    (hε_pos : 0 < ε) (hh_pos : 0 < h) (hm2 : 2 ≤ m)
    (hh_gt_2m1 : 1 / (2 : ℝ) ^ (m + 1) < h) (hm_log : (m : ℝ) * Real.log 2 ≤ Real.log (1 / h))
    (h_tail_lt : dist (2 * ((1 + ε) * √(2 * Real.log 2) * 7) *
      √(((m + m / p + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (m + m / p + 1)) /
        √(2 * (1 / (2 : ℝ) ^ (m + 1)) * ((m : ℝ) * Real.log 2))) 0 < ε) :
    (2 * ∑' k : ℕ, (1 + ε) * √(2 * Real.log 2) *
      √(((m + m / p + 1 + k : ℕ) : ℝ) / (2 : ℝ) ^ (m + m / p + 1 + k))) /
        √(2 * h * Real.log (1 / h)) ≤ ε ∧ 0 < √(2 * h * Real.log (1 / h)) := by
  let c_tail : ℝ := 2 * ((1 + ε) * √(2 * Real.log 2) * 7)
  have hc_tail : 0 ≤ c_tail := by dsimp only [c_tail]; positivity
  have : m ≤ m + m / p := Nat.le_add_right m (m / p)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have htail_bound : 2 * ∑' k : ℕ, (1 + ε) * √(2 * Real.log 2) *
      √(((m + m / p + 1 + k : ℕ) : ℝ) / (2 : ℝ) ^ (m + m / p + 1 + k)) ≤
        c_tail * √(((m + m / p + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (m + m / p + 1)) := by
    rw [tsum_mul_left]
    refine (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (tsum_sqrt_div_two_pow_le (n := m + m / p) (by omega))
        (by positivity)) zero_le_two).trans_eq ?_
    dsimp only [c_tail]; ring
  have hden_pos : 0 < √(2 * (1 / (2 : ℝ) ^ (m + 1)) * ((m : ℝ) * Real.log 2)) :=
    Real.sqrt_pos.2 (mul_pos (by positivity) (mul_pos (by exact_mod_cast (by omega : 0 < m)) hlog2))
  have hden_ge : √(2 * (1 / (2 : ℝ) ^ (m + 1)) * ((m : ℝ) * Real.log 2)) ≤
      √(2 * h * Real.log (1 / h)) :=
    Real.sqrt_le_sqrt (mul_le_mul (mul_le_mul_of_nonneg_left hh_gt_2m1.le zero_le_two) hm_log
      (mul_nonneg (Nat.cast_nonneg m) hlog2.le) (mul_nonneg zero_le_two hh_pos.le))
  refine ⟨(div_le_div₀ (mul_nonneg hc_tail (Real.sqrt_nonneg _)) htail_bound hden_pos
    hden_ge).trans ?_, hden_pos.trans_le hden_ge⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (mul_nonneg hc_tail (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))]
    at h_tail_lt
  exact h_tail_lt.le

private lemma ae_eventually_modulus_div_sqrt_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {q : ℕ} (hq : 2 ≤ q) :
    ∀ᵐ ω ∂P, ∀ᶠ h in 𝓝[>] 0,
      TauCeti.modulusOfContinuityOn (B · ω) (Iic 1) h / √(2 * h * Real.log (1 / h)) ≤
        (1 + 1 / (q : ℝ)) ^ 2 + 1 / (q : ℝ) := by
  set ε : ℝ := 1 / (q : ℝ)
  set p : ℕ := 3 * q
  have hε_pos : 0 < ε := by positivity
  have hp_pos : 1 ≤ p := by omega
  obtain ⟨M_tail, hM_tail⟩ := Metric.tendsto_atTop.1
    (tail_div_sqrt_tendsto_zero p hp_pos (2 * ((1 + ε) * √(2 * Real.log 2) * 7))) ε hε_pos
  obtain ⟨M_pow, hM_pow⟩ :=
    exists_pow_lt_of_lt_one (half_pos hε_pos) (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [hB.cont, ae_eventually_notMem_dyadicBadEvent hB.toIsPreBrownianReal hq]
    with ω hcont hgood
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hgood
  let m₀ : ℕ := N₀ + M_tail + (M_pow + 1) * p + 2
  filter_upwards [Ioo_mem_nhdsGT (show 0 < min ((1 / 2 : ℝ) ^ m₀) (Real.exp (-1) / (1 + ε))
    by positivity)] with h hh
  have hbounds := dyadic_mesh_bounds hh.1 (hh.2.trans_le (min_le_left _ _))
  dsimp only at hbounds
  generalize ⌊Real.log (1 / h) / Real.log 2⌋₊ = m at hbounds
  obtain ⟨hm_ge, hh_le_2m, hh_gt_2m1, hm_log⟩ := hbounds
  have hm_all : N₀ + M_tail + (M_pow + 1) * p + 2 ≤ m := hm_ge
  have : m ≤ m + m / p := Nat.le_add_right m (m / p)
  have hstep (r : ℕ) (hr : m + m / p + 1 ≤ r) (i : ℕ) (hi : i < 2 ^ r) :
      dist (B (((i + 1 : ℕ) : ℝ≥0) / 2 ^ r) ω) (B ((i : ℝ≥0) / 2 ^ r) ω) ≤
        (1 + ε) * √(2 * Real.log 2) * √((r : ℝ) / (2 : ℝ) ^ r) := by
    refine (dist_le_of_notMem_dyadicBadEvent (hN₀ r (by omega)) le_rfl Nat.one_le_two_pow
      (by omega)).trans_eq ?_
    simp only [Nat.cast_one, div_one, Real.log_pow]; dsimp only [ε]
    rw [mul_assoc (1 + 1 / (q : ℝ)), ← Real.sqrt_mul (by positivity)]; congr 2; ring
  have h1εh : (1 + ε) * h ≤ Real.exp (-1) :=
    (mul_lt_mul_of_pos_left (hh.2.trans_le (min_le_right _ _)) (by positivity)).le.trans_eq
      (mul_div_cancel₀ _ (by positivity))
  have hpow_lt : (1 / 2 : ℝ) ^ (m / p) < ε / 2 :=
    (pow_le_pow_of_le_one (by positivity) (by norm_num)
      ((Nat.le_div_iff_mul_le hp_pos).2 (by nlinarith [hm_all]))).trans_lt hM_pow
  have hchaining := TauCeti.modulusOfContinuityOn_Iic_one_le_of_dyadic hcont.continuousOn
    (m + m / p) hh.1.le (by positivity) (fun i j hij hj hlen ↦
      coarse_dyadic_dist_le hε_pos hh.1 hh_le_2m hh_gt_2m1 h1εh hpow_lt
        (hN₀ (m + m / p) (by omega)) hij hj hlen)
    (summable_const_mul_sqrt_div_two_pow ((1 + ε) * √(2 * Real.log 2))) hstep
  obtain ⟨htail_ratio, hden_h_pos⟩ := dyadic_tail_tsum_div_sqrt_le hε_pos hh.1 (by omega)
    hh_gt_2m1 hm_log (hM_tail m (by omega))
  have hdiv := div_le_div_of_nonneg_right hchaining hden_h_pos.le
  rw [add_div, mul_div_cancel_right₀ _ hden_h_pos.ne'] at hdiv
  linarith

end UpperBoundHelpers

section LowerBoundHelpers

private def lowerGrid (b : ℝ≥0) (n : ℕ) (i : Fin (⌊((b : ℝ) ^ (n + 1))⌋₊ + 1)) : ℝ≥0 :=
  (i : ℝ≥0) * (b ^ (n + 1))⁻¹

private lemma strictMono_lowerGrid {b : ℝ≥0} (hb : 0 < b) (n : ℕ) :
    StrictMono (lowerGrid b n) := fun _ _ hij ↦
  mul_lt_mul_of_pos_right (by exact_mod_cast hij) (inv_pos.2 (pow_pos hb _))

private lemma lowerGrid_le_one {b : ℝ≥0} (hb : 0 < b) (n : ℕ)
    (i : Fin (⌊((b : ℝ) ^ (n + 1))⌋₊ + 1)) :
    lowerGrid b n i ≤ 1 := by
  rw [← NNReal.coe_le_coe, lowerGrid, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_natCast, NNReal.coe_one]
  have hi : (i : ℕ) ≤ ⌊(b : ℝ) ^ (n + 1)⌋₊ := Nat.lt_succ_iff.1 i.isLt
  calc ((i : ℕ) : ℝ) * ((b : ℝ) ^ (n + 1))⁻¹
      ≤ (b : ℝ) ^ (n + 1) * ((b : ℝ) ^ (n + 1))⁻¹ := by
        gcongr
        exact (Nat.cast_le.2 hi).trans (Nat.floor_le (by positivity))
    _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hb.ne'))

private lemma measure_forall_abs_normalized_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {b : ℝ≥0} (hb : 0 < b) (n : ℕ)
    {s : ℝ} (hs : 0 ≤ s) :
    P {ω | ∀ j : Fin ⌊(b : ℝ) ^ (n + 1)⌋₊,
        |TauCeti.normalizedBrownianIncrements B (lowerGrid b n) ω j| ≤ s} ≤
      ENNReal.ofReal (Real.exp (-(⌊(b : ℝ) ^ (n + 1)⌋₊ : ℝ) * gaussianPDFReal 0 1 (s + 1))) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  set N : ℕ := ⌊(b : ℝ) ^ (n + 1)⌋₊
  have hlaw := hB.hasLaw_normalizedBrownianIncrements (strictMono_lowerGrid hb n)
  let box : Set (Fin N → ℝ) := Set.pi univ fun _ ↦ Icc (-s) s
  have hbox_meas : MeasurableSet box := MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hpre : {ω | ∀ j : Fin N,
      |TauCeti.normalizedBrownianIncrements B (lowerGrid b n) ω j| ≤ s} =
        TauCeti.normalizedBrownianIncrements B (lowerGrid b n) ⁻¹' box := by
    ext ω; simp only [box, mem_ofPred_eq, mem_preimage, mem_univ_pi, mem_Icc, abs_le]
  have hprob : P (TauCeti.normalizedBrownianIncrements B (lowerGrid b n) ⁻¹' box) =
      (gaussianReal 0 1 (Icc (-s) s)) ^ N := by
    rw [← Measure.map_apply_of_aemeasurable hlaw.aemeasurable hbox_meas, hlaw.map_eq, Measure.pi_pi]
    simp [N]
  have hIcc_le : (gaussianReal 0 1).real (Icc (-s) s) ≤ 1 - gaussianPDFReal 0 1 (s + 1) := by
    have htail := TauCeti.Probability.gaussianPDFReal_add_one_le_measureReal_map_abs_Ioi hs
    rw [map_measureReal_apply continuous_abs.measurable measurableSet_Ioi] at htail
    have hcompl : (Icc (-s) s : Set ℝ) = (abs ⁻¹' Ioi s)ᶜ := by ext x; simp [abs_le, not_lt]
    rw [hcompl, probReal_compl_eq_one_sub (measurableSet_Ioi.preimage continuous_abs.measurable)]
    linarith
  have hexp_step : (gaussianReal 0 1).real (Icc (-s) s) ≤
      Real.exp (-gaussianPDFReal 0 1 (s + 1)) :=
    hIcc_le.trans (by simpa [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-gaussianPDFReal 0 1 (s + 1)))
  rw [hpre, hprob, ← ofReal_measureReal, ← ENNReal.ofReal_pow measureReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  exact (pow_le_pow_left₀ measureReal_nonneg hexp_step N).trans_eq
    (by rw [← Real.exp_nat_mul]; dsimp only [N]; congr 1; ring)

private lemma exp_neg_floor_mul_gaussianPDFReal_le {b ε : ℝ} (hb_gt1 : 1 < b)
    (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / 2) {n : ℕ}
    (hn : 1 / ((ε / 2) ^ 2 * (2 * Real.log b)) < ((n + 1 : ℕ) : ℝ)) :
    Real.exp (-(⌊b ^ (n + 1)⌋₊ : ℝ) *
      gaussianPDFReal 0 1 ((1 - ε) * √(2 * Real.log (b ^ (n + 1))) + 1)) ≤
        Real.exp (-(1 / (2 * √(2 * Real.pi))) * (b ^ (ε / 2) - 1) * ((n + 1 : ℕ) : ℝ)) := by
  have hlogb : 0 < Real.log b := Real.log_pos hb_gt1
  set L : ℝ := ((n + 1 : ℕ) : ℝ) * Real.log b
  have hL_gt : 1 < (ε / 2) ^ 2 * (2 * L) :=
    ((div_lt_iff₀ (by positivity)).1 hn).trans_eq (by dsimp [L]; ring)
  have h1_le : 1 ≤ (ε / 2) * √(2 * L) := by
    rw [← Real.sqrt_one]; exact (Real.sqrt_le_sqrt hL_gt.le).trans_eq
      (by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)])
  have hs_le : (1 - ε) * √(2 * L) + 1 ≤ (1 - ε / 2) * √(2 * L) := by linarith
  have hsq_le : ((1 - ε) * √(2 * L) + 1) ^ 2 / 2 ≤ (1 - ε / 2) * L := by
    have : 0 ≤ 1 - ε := by linarith
    have h1 := pow_le_pow_left₀ (by positivity) hs_le 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at h1
    nlinarith [show (1 - ε / 2) ^ 2 ≤ 1 - ε / 2 by nlinarith, show 0 ≤ L by positivity]
  have hpdf_ge : (√(2 * Real.pi))⁻¹ * (b ^ (n + 1)) ^ (-(1 - ε / 2)) ≤
      gaussianPDFReal 0 1 ((1 - ε) * √(2 * L) + 1) := by
    rw [TauCeti.Probability.gaussianPDFReal_zero_one]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Real.rpow_natCast b (n + 1), ← Real.rpow_mul (by positivity),
      Real.rpow_def_of_pos (by positivity),
      show Real.log b * ((n + 1 : ℕ) * -(1 - ε / 2)) = -(1 - ε / 2) * L by dsimp [L]; ring]
    exact Real.exp_le_exp.2 (by linarith)
  have hfloor_ge : b ^ (n + 1) / 2 ≤ (⌊b ^ (n + 1)⌋₊ : ℝ) := by
    have hfl1 : (1 : ℝ) ≤ (⌊b ^ (n + 1)⌋₊ : ℝ) := by
      exact_mod_cast Nat.le_floor (by exact_mod_cast one_le_pow₀ hb_gt1.le : ((1 : ℕ) : ℝ) ≤ _)
    linarith [Nat.lt_floor_add_one (b ^ (n + 1))]
  set r : ℝ := b ^ (ε / 2)
  have hr_gt1 : 1 < r := Real.one_lt_rpow hb_gt1 (by positivity)
  have hr_bern : ((n + 1 : ℕ) : ℝ) * (r - 1) ≤ r ^ (n + 1) := by
    linarith [one_add_mul_sub_le_pow (by linarith : -1 ≤ r) (n + 1)]
  have hr_pow : b ^ (n + 1) * (b ^ (n + 1)) ^ (-(1 - ε / 2)) = r ^ (n + 1) := by
    rw [← Real.rpow_natCast b (n + 1), ← Real.rpow_one_add' (by positivity) (by linarith),
      show (1 : ℝ) + -(1 - ε / 2) = ε / 2 by ring, ← Real.rpow_mul (by positivity),
      mul_comm _ (ε / 2), Real.rpow_mul (by positivity), Real.rpow_natCast]
  have hprod_ge : (1 / (2 * √(2 * Real.pi))) * (r - 1) * ((n + 1 : ℕ) : ℝ) ≤
      (⌊b ^ (n + 1)⌋₊ : ℝ) * gaussianPDFReal 0 1 ((1 - ε) * √(2 * L) + 1) := by
    calc (1 / (2 * √(2 * Real.pi))) * (r - 1) * ((n + 1 : ℕ) : ℝ)
        ≤ (1 / (2 * √(2 * Real.pi))) * r ^ (n + 1) := by
          nlinarith [hr_bern, show 0 < 1 / (2 * √(2 * Real.pi)) by positivity]
      _ = (b ^ (n + 1) / 2) * ((√(2 * Real.pi))⁻¹ * (b ^ (n + 1)) ^ (-(1 - ε / 2))) := by
          rw [← hr_pow]; ring
      _ ≤ (⌊b ^ (n + 1)⌋₊ : ℝ) * gaussianPDFReal 0 1 ((1 - ε) * √(2 * L) + 1) :=
          mul_le_mul hfloor_ge hpdf_ge (by positivity) (by positivity)
  rw [Real.log_pow]; exact Real.exp_le_exp.2 (by linarith)

private lemma summable_exp_neg_floor_mul_gaussianPDFReal {q : ℕ} (hq : 2 ≤ q) :
    let b : ℝ := 1 + 1 / (q : ℝ)
    let ε : ℝ := 1 / (q : ℝ)
    Summable fun n : ℕ ↦
      Real.exp (-(⌊b ^ (n + 1)⌋₊ : ℝ) *
        gaussianPDFReal 0 1 ((1 - ε) * √(2 * Real.log (b ^ (n + 1))) + 1)) := by
  intro b ε
  have hε_pos : 0 < ε := by positivity
  have hε_le : ε ≤ 1 / 2 := one_div_le_one_div_of_le zero_lt_two (by exact_mod_cast hq)
  have hb_gt1 : 1 < b := lt_add_of_pos_right 1 hε_pos
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / ((ε / 2) ^ 2 * (2 * Real.log b)))
  refine (summable_nat_add_iff N₁).1 ?_
  refine Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le)
    (fun k ↦ exp_neg_floor_mul_gaussianPDFReal_le hb_gt1 hε_pos hε_le
      (hN₁.trans_le (by exact_mod_cast (by omega : N₁ ≤ k + N₁ + 1)))) ?_
  have hr_gt1 : 1 < b ^ (ε / 2) := Real.one_lt_rpow hb_gt1 (by positivity)
  have hα : Real.exp (-(1 / (2 * √(2 * Real.pi))) * (b ^ (ε / 2) - 1)) < 1 :=
    Real.exp_lt_one_iff.2 (mul_neg_of_neg_of_pos
      (neg_neg_of_pos (by positivity)) (sub_pos.2 hr_gt1))
  refine ((summable_geometric_of_lt_one (Real.exp_pos _).le hα).comp_injective
    (add_left_injective (N₁ + 1))).congr fun k ↦ ?_
  dsimp only [Function.comp_apply]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

private lemma geometric_mesh_bounds {b h : ℝ} {n : ℕ} (hb_gt1 : 1 < b) (hh_pos : 0 < h)
    (h1h_gt : b < 1 / h) (hn_eq : n = ⌊Real.log (1 / h) / Real.log b⌋₊) :
    1 / h < b ^ (n + 1) ∧ 1 / b ^ (n + 1) < h ∧ h ≤ b * (1 / b ^ (n + 1)) := by
  have : 0 < b := zero_lt_one.trans hb_gt1
  have hlogb : 0 < Real.log b := Real.log_pos hb_gt1
  have h1h_lt_bn1 : 1 / h < b ^ (n + 1) := by
    refine (Real.log_lt_log_iff (by positivity) (by positivity)).1 ?_
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one, hn_eq]
    exact (div_lt_iff₀ hlogb).1 (Nat.lt_floor_add_one _)
  have hδ_lt_h : 1 / b ^ (n + 1) < h := by
    rwa [div_lt_iff₀ (by positivity), mul_comm, ← div_lt_iff₀ hh_pos]
  have hbn_le : b ^ n ≤ 1 / h := by
    refine (Real.log_le_log_iff (by positivity) (by positivity)).1 ?_
    rw [Real.log_pow, hn_eq]
    exact (le_div_iff₀ hlogb).1 (Nat.floor_le
      (div_nonneg (Real.log_nonneg (hb_gt1.le.trans h1h_gt.le)) hlogb.le))
  refine ⟨h1h_lt_bn1, hδ_lt_h, ?_⟩
  rw [show b * (1 / b ^ (n + 1)) = 1 / b ^ n by rw [pow_succ']; field_simp,
    le_div_iff₀ (by positivity), mul_comm]
  exact (le_div_iff₀ hh_pos).1 hbn_le

private lemma le_modulus_div_sqrt_of_exists_gt {g : ℝ≥0 → ℝ}
    (hbdd : Bornology.IsBounded (g '' Iic 1)) {b_nn : ℝ≥0} {ε h : ℝ} {n : ℕ}
    (hb_gt1 : 1 < (b_nn : ℝ)) (hh_pos : 0 < h)
    (h1h_gt : (b_nn : ℝ) < 1 / h) (hn_eq : n = ⌊Real.log (1 / h) / Real.log b_nn⌋₊)
    {j : Fin ⌊(b_nn : ℝ) ^ (n + 1)⌋₊}
    (hj : (1 - ε) * √(2 * Real.log ((b_nn : ℝ) ^ (n + 1))) <
      |g (lowerGrid b_nn n j.succ) - g (lowerGrid b_nn n j.castSucc)| /
        √((lowerGrid b_nn n j.succ : ℝ) - lowerGrid b_nn n j.castSucc)) :
    (1 - ε) / √(b_nn : ℝ) ≤
      TauCeti.modulusOfContinuityOn g (Iic 1) h / √(2 * h * Real.log (1 / h)) := by
  let b : ℝ := (b_nn : ℝ)
  have : 0 < b := zero_lt_one.trans hb_gt1
  have hb_pos : 0 < b_nn := zero_lt_one.trans hb_gt1
  set δ : ℝ := (((b_nn ^ (n + 1))⁻¹ : ℝ≥0) : ℝ)
  have hδ_eq : δ = 1 / b ^ (n + 1) := by simp [δ, b, one_div]
  have hδ_pos : 0 < δ := by rw [hδ_eq]; positivity
  obtain ⟨h1h_lt_bn1, hδ_lt_h, hh_le_bδ⟩ := geometric_mesh_bounds hb_gt1 hh_pos h1h_gt hn_eq
  rw [← hδ_eq] at hδ_lt_h hh_le_bδ
  have hstep_eq : ((lowerGrid b_nn n j.succ : ℝ) - lowerGrid b_nn n j.castSucc) = δ := by
    simp only [lowerGrid, NNReal.coe_mul, Fin.val_succ, Fin.val_castSucc, NNReal.coe_natCast,
      Nat.cast_add, Nat.cast_one]
    change (((j : ℕ) : ℝ) + 1) * δ - ((j : ℕ) : ℝ) * δ = δ; ring
  rw [hstep_eq, lt_div_iff₀ (Real.sqrt_pos.2 hδ_pos)] at hj
  have hdist_grid : dist (lowerGrid b_nn n j.succ) (lowerGrid b_nn n j.castSucc) ≤ h := by
    rw [NNReal.dist_eq, hstep_eq, abs_of_pos hδ_pos]; exact hδ_lt_h.le
  have hmod_ge : (1 - ε) * √(2 * δ * Real.log (b ^ (n + 1))) ≤
      TauCeti.modulusOfContinuityOn g (Iic 1) h := by
    have hmul : (1 - ε) * √(2 * Real.log ((b_nn : ℝ) ^ (n + 1))) * √δ =
        (1 - ε) * √(2 * δ * Real.log (b ^ (n + 1))) := by
      rw [mul_assoc, ← Real.sqrt_mul
        (mul_nonneg zero_le_two (Real.log_nonneg (one_le_pow₀ hb_gt1.le)))]
      dsimp only [b]; congr 2; ring
    exact (hmul ▸ hj.le).trans (TauCeti.dist_le_modulusOfContinuityOn hbdd
      (lowerGrid_le_one hb_pos n j.succ) (lowerGrid_le_one hb_pos n j.castSucc) hdist_grid)
  have hlog_pos : 0 < Real.log (1 / h) := Real.log_pos (hb_gt1.trans h1h_gt)
  have hden_le : √(2 * h * Real.log (1 / h)) ≤ √b * √(2 * δ * Real.log (b ^ (n + 1))) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have := Real.log_le_log (by positivity) h1h_lt_bn1.le
    calc 2 * h * Real.log (1 / h) ≤ 2 * (b * δ) * Real.log (1 / h) := by gcongr
      _ ≤ 2 * (b * δ) * Real.log (b ^ (n + 1)) := by gcongr
      _ = b * (2 * δ * Real.log (b ^ (n + 1))) := by ring
  have hsqrt_pos : 0 < √(2 * δ * Real.log (b ^ (n + 1))) :=
    Real.sqrt_pos.2 (mul_pos (by positivity) (Real.log_pos (one_lt_pow₀ hb_gt1 (by omega))))
  exact (mul_div_mul_right (1 - ε) √b hsqrt_pos.ne').symm.trans_le
    (div_le_div₀ (TauCeti.modulusOfContinuityOn_nonneg g (Iic 1) h) hmod_ge
      (Real.sqrt_pos.2 (mul_pos (by positivity) hlog_pos)) hden_le)

private lemma ae_eventually_le_modulus_div_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {q : ℕ} (hq : 2 ≤ q) :
    ∀ᵐ ω ∂P, ∀ᶠ h in 𝓝[>] 0,
      (1 - 1 / (q : ℝ)) / √(1 + 1 / (q : ℝ)) ≤
        TauCeti.modulusOfContinuityOn (B · ω) (Iic 1) h / √(2 * h * Real.log (1 / h)) := by
  set b_nn : ℝ≥0 := 1 + 1 / (q : ℝ≥0)
  set b : ℝ := (b_nn : ℝ)
  set ε : ℝ := 1 / (q : ℝ)
  have hb_eq : b = 1 + 1 / (q : ℝ) := by simp [b, b_nn]
  have hb_pos : 0 < b_nn := by positivity
  have hb_gt1 : 1 < b := by rw [hb_eq]; exact lt_add_of_pos_right 1 (by positivity)
  have : 0 < 1 - ε := by
    have : ε ≤ 1 / 2 := one_div_le_one_div_of_le zero_lt_two (by exact_mod_cast hq)
    linarith
  let F : ℕ → Set Ω := fun n ↦ {ω | ∀ j : Fin ⌊b ^ (n + 1)⌋₊,
    |TauCeti.normalizedBrownianIncrements B (lowerGrid b_nn n) ω j| ≤
      (1 - ε) * √(2 * Real.log (b ^ (n + 1)))}
  have hF_ne : (∑' n : ℕ, P (F n)) ≠ ∞ := by
    have hsum := summable_exp_neg_floor_mul_gaussianPDFReal hq
    rw [← hb_eq] at hsum
    exact ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (tsum_le_tsum fun n ↦
      measure_forall_abs_normalized_le hB.toIsPreBrownianReal hb_pos n (by positivity))
  filter_upwards [hB.cont, ae_eventually_notMem hF_ne] with ω hcont hgood
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hgood
  filter_upwards [Ioo_mem_nhdsGT (show 0 < 1 / b ^ (N₀ + 1) by positivity)] with h hh
  have h1h_gt_pow : b ^ (N₀ + 1) < 1 / h :=
    (lt_div_iff₀ hh.1).2 (by rw [mul_comm]; exact (lt_div_iff₀ (by positivity)).1 hh.2)
  set n : ℕ := ⌊Real.log (1 / h) / Real.log b⌋₊
  have hn_ge : N₀ + 1 ≤ n := Nat.le_floor ((le_div_iff₀ (Real.log_pos hb_gt1)).2
    ((Real.log_pow b (N₀ + 1)).symm ▸ Real.log_le_log (by positivity) h1h_gt_pow.le))
  have hnot : ω ∉ F n := hN₀ n (by omega)
  simp only [F, mem_ofPred_eq, not_forall, not_le] at hnot
  obtain ⟨j, hj⟩ := hnot
  rw [TauCeti.normalizedBrownianIncrements_apply, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hj
  have hbdd : Bornology.IsBounded ((B · ω) '' Iic 1) :=
    ((isCompact_Icc (a := (0 : ℝ≥0)) (b := 1)).image hcont).isBounded.subset
      (image_mono fun _ hx ↦ ⟨zero_le, hx⟩)
  have h1h_gt : b < 1 / h := (le_self_pow₀ hb_gt1.le (by omega : N₀ + 1 ≠ 0)).trans_lt h1h_gt_pow
  rw [← hb_eq]; exact le_modulus_div_sqrt_of_exists_gt hbdd hb_gt1 hh.1 h1h_gt rfl hj

end LowerBoundHelpers

section MainTheorems

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Lévy's exact uniform modulus of continuity on `[0, 1]`**: for a standard Brownian motion
`B`, almost surely `modulusOfContinuityOn (B · ω) (Set.Iic 1) h / √(2 * h * log (1 / h)) → 1`
as `h → 0⁺`. -/
theorem tendsto_modulusOfContinuityOn_Iic_one_div_sqrt (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun h : ℝ ↦ TauCeti.modulusOfContinuityOn (B · ω) (Iic 1) h / √(2 * h * Real.log (1 / h)))
      (𝓝[>] 0) (𝓝 1) := by
  have hall_up : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ h in 𝓝[>] 0,
      TauCeti.modulusOfContinuityOn (B · ω) (Iic 1) h / √(2 * h * Real.log (1 / h)) ≤
        (1 + 1 / ((k + 2 : ℕ) : ℝ)) ^ 2 + 1 / ((k + 2 : ℕ) : ℝ) :=
    ae_all_iff.2 fun k ↦ ae_eventually_modulus_div_sqrt_le hB (by omega : 2 ≤ k + 2)
  have hall_low : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ h in 𝓝[>] 0,
      (1 - 1 / ((k + 2 : ℕ) : ℝ)) / √(1 + 1 / ((k + 2 : ℕ) : ℝ)) ≤
        TauCeti.modulusOfContinuityOn (B · ω) (Iic 1) h / √(2 * h * Real.log (1 / h)) :=
    ae_all_iff.2 fun k ↦ ae_eventually_le_modulus_div_sqrt hB (by omega : 2 ≤ k + 2)
  have h0 : Tendsto (fun k : ℕ ↦ 1 / ((k + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr fun k ↦ by
      dsimp only [Function.comp_apply]; push_cast; ring
  have hlim_up : Tendsto (fun k : ℕ ↦
      (1 + 1 / ((k + 2 : ℕ) : ℝ)) ^ 2 + 1 / ((k + 2 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow 2).add h0
  have hlim_low : Tendsto (fun k : ℕ ↦
      (1 - 1 / ((k + 2 : ℕ) : ℝ)) / √(1 + 1 / ((k + 2 : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa [Pi.div_def] using Filter.Tendsto.div ((tendsto_const_nhds (x := (1 : ℝ))).sub h0)
      (((tendsto_const_nhds (x := (1 : ℝ))).add h0).sqrt) (by simp)
  filter_upwards [hall_up, hall_low] with ω hup hlow
  rw [Metric.tendsto_nhds]; intro ε hε
  obtain ⟨K₁, hK₁⟩ := ((tendsto_order.1 hlim_up).2 (1 + ε) (by linarith)).exists
  obtain ⟨K₂, hK₂⟩ := ((tendsto_order.1 hlim_low).1 (1 - ε) (by linarith)).exists
  filter_upwards [hup K₁, hlow K₂] with h hh_up hh_low
  rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩

private lemma tendsto_sqrt_log_div_log {T : ℝ} (hT_pos : 0 < T) :
    Tendsto (fun h : ℝ ↦ √(Real.log (T / h) / Real.log (1 / h))) (𝓝[>] 0) (𝓝 1) := by
  have hlog_atTop : Tendsto (fun h : ℝ ↦ Real.log (1 / h)) (𝓝[>] 0) atTop := by
    simpa [Function.comp_def, one_div] using Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hinv_zero : Tendsto (fun h : ℝ ↦ Real.log T * (Real.log (1 / h))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp hlog_atTop).const_mul (Real.log T)
  have h1 : Tendsto (fun h : ℝ ↦ √(1 + Real.log T * (Real.log (1 / h))⁻¹)) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hinv_zero).sqrt
  refine h1.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with h hh
  have hlog_ne : Real.log (1 / h) ≠ 0 := (Real.log_pos ((one_lt_div hh.1).2 hh.2)).ne'
  congr 1
  rw [show T / h = T * (1 / h) by ring, Real.log_mul hT_pos.ne' (one_div_pos.2 hh.1).ne',
    add_div, div_self hlog_ne]
  ring

/-- **Lévy's exact uniform modulus of continuity on `[0, T]`**: for a standard Brownian motion
`B` and every positive finite horizon `T > 0`, almost surely
`modulusOfContinuityOn (B · ω) (Set.Iic T) h / √(2 * h * log (1 / h)) → 1` as `h → 0⁺`. -/
theorem tendsto_modulusOfContinuityOn_Iic_div_sqrt (hB : IsBrownianReal B P)
    {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun h : ℝ ↦ TauCeti.modulusOfContinuityOn (B · ω) (Iic T) h / √(2 * h * Real.log (1 / h)))
      (𝓝[>] 0) (𝓝 1) := by
  have hT_pos : (0 : ℝ) < T := hT
  have hW : IsBrownianReal (fun u ω ↦ (√(T : ℝ))⁻¹ * B (T * u) ω) P := hB.smul hT.ne'
  have hscale : Tendsto (fun h : ℝ ↦ h / (T : ℝ)) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using
      ((continuous_id.div_const (T : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds,
      by filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h); exact div_pos hh hT_pos⟩
  filter_upwards [hW.tendsto_modulusOfContinuityOn_Iic_one_div_sqrt] with ω hω
  have hcomp := (hω.comp hscale).mul (tendsto_sqrt_log_div_log hT_pos)
  rw [mul_one] at hcomp; refine hcomp.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one hT_pos)] with h hh
  have hh_pos : 0 < h := hh.1
  have hlog_u : 0 < Real.log ((T : ℝ) / h) :=
    Real.log_pos ((one_lt_div hh_pos).2 (hh.2.trans_le (min_le_right _ _)))
  have hlog_h : 0 < Real.log (1 / h) :=
    Real.log_pos ((one_lt_div hh_pos).2 (hh.2.trans_le (min_le_left _ _)))
  have hmod : TauCeti.modulusOfContinuityOn (fun u ↦ (√(T : ℝ))⁻¹ * B (T * u) ω) (Iic 1)
      (h / (T : ℝ)) = (√(T : ℝ))⁻¹ * TauCeti.modulusOfContinuityOn (B · ω) (Iic T) h := by
    have h1 := TauCeti.modulusOfContinuityOn_fun_smul (√(T : ℝ))⁻¹
      (fun u : ℝ≥0 ↦ B (T * u) ω) (Iic 1) (h / (T : ℝ))
    simpa only [smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.2 hT_pos),
      TauCeti.modulusOfContinuityOn_Iic_nnreal_mul (B · ω) hT, mul_div_cancel₀ _ hT_pos.ne']
      using h1
  dsimp only [Function.comp_apply]; rw [hmod, one_div_div]
  have hsqrt_u : √(2 * (h / (T : ℝ)) * Real.log ((T : ℝ) / h)) =
      (√(T : ℝ))⁻¹ * √(2 * h * Real.log ((T : ℝ) / h)) := by
    rw [show 2 * (h / (T : ℝ)) * Real.log ((T : ℝ) / h) =
      ((T : ℝ))⁻¹ * (2 * h * Real.log ((T : ℝ) / h)) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_inv]
  have hsqrt_ratio : √(Real.log ((T : ℝ) / h) / Real.log (1 / h)) =
      √(2 * h * Real.log ((T : ℝ) / h)) / √(2 * h * Real.log (1 / h)) := by
    rw [← Real.sqrt_div (by positivity), mul_div_mul_left _ _ (mul_pos two_pos hh_pos).ne']
  rw [hsqrt_u, hsqrt_ratio]
  have : √(T : ℝ) ≠ 0 := (Real.sqrt_pos.2 hT_pos).ne'
  have : √(2 * h * Real.log ((T : ℝ) / h)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have : √(2 * h * Real.log (1 / h)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp

/-- **Simultaneous Lévy uniform modulus across all positive horizons**: outside a single common
null set, `modulusOfContinuityOn (B · ω) (Set.Iic T) h / √(2 * h * log (1 / h)) → 1` as `h → 0⁺`
for every `T > 0`. -/
theorem ae_forall_tendsto_modulusOfContinuityOn_Iic_div_sqrt (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → Tendsto (fun h : ℝ ↦
      TauCeti.modulusOfContinuityOn (B · ω) (Iic T) h / √(2 * h * Real.log (1 / h)))
      (𝓝[>] 0) (𝓝 1) := by
  have hnat : ∀ᵐ ω ∂P, ∀ m : ℕ, Tendsto (fun h : ℝ ↦
      TauCeti.modulusOfContinuityOn (B · ω) (Iic ((m + 1 : ℕ) : ℝ≥0)) h /
        √(2 * h * Real.log (1 / h))) (𝓝[>] 0) (𝓝 1) :=
    ae_all_iff.2 fun _ ↦ hB.tendsto_modulusOfContinuityOn_Iic_div_sqrt (by positivity)
  have hinv : ∀ᵐ ω ∂P, ∀ n : ℕ, Tendsto (fun h : ℝ ↦
      TauCeti.modulusOfContinuityOn (B · ω) (Iic (((n + 1 : ℕ) : ℝ≥0)⁻¹)) h /
        √(2 * h * Real.log (1 / h))) (𝓝[>] 0) (𝓝 1) :=
    ae_all_iff.2 fun _ ↦ hB.tendsto_modulusOfContinuityOn_Iic_div_sqrt (by positivity)
  filter_upwards [hB.cont, hnat, hinv] with ω hcont hω_nat hω_inv T hT
  have hT_pos : (0 : ℝ) < T := hT
  set m : ℕ := ⌊(T : ℝ)⌋₊
  set n : ℕ := ⌊1 / (T : ℝ)⌋₊
  have hT_le : T ≤ ((m + 1 : ℕ) : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one]
    exact (Nat.lt_floor_add_one (T : ℝ)).le
  have hinv_le : ((n + 1 : ℕ) : ℝ≥0)⁻¹ ≤ T := by
    rw [← NNReal.coe_le_coe, NNReal.coe_inv, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one,
      inv_eq_one_div, div_le_iff₀' (by positivity)]
    exact ((div_lt_iff₀ hT_pos).1 (Nat.lt_floor_add_one (1 / (T : ℝ)))).le
  have hbdd_top : Bornology.IsBounded ((B · ω) '' Iic ((m + 1 : ℕ) : ℝ≥0)) :=
    ((isCompact_Icc (a := (0 : ℝ≥0)) (b := ((m + 1 : ℕ) : ℝ≥0))).image hcont).isBounded.subset
      (image_mono fun _ hx ↦ ⟨zero_le, hx⟩)
  have hbdd_T : Bornology.IsBounded ((B · ω) '' Iic T) :=
    hbdd_top.subset (image_mono (Iic_subset_Iic.2 hT_le))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hω_inv n) (hω_nat m) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h _
    exact div_le_div_of_nonneg_right
      (TauCeti.modulusOfContinuityOn_mono_set (Iic_subset_Iic.2 hinv_le) hbdd_T h)
      (Real.sqrt_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with h _
    exact div_le_div_of_nonneg_right
      (TauCeti.modulusOfContinuityOn_mono_set (Iic_subset_Iic.2 hT_le) hbdd_top h)
      (Real.sqrt_nonneg _)

/-- **Lévy's exact uniform modulus of continuity** in explicit `sSup` form on `[0, T]` for `T > 0`
(Mörters–Peres, Theorem 1.14, Remark 1.18, and Exercise 1.7). -/
theorem tendsto_sSup_abs_sub_div_sqrt (hB : IsBrownianReal B P) {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun h : ℝ ↦ sSup {a : ℝ | ∃ s t : ℝ≥0,
        s ≤ T ∧ t ≤ T ∧ dist s t ≤ h ∧ a = |B t ω - B s ω|} / √(2 * h * Real.log (1 / h)))
      (𝓝[>] 0) (𝓝 1) := by
  simpa only [← TauCeti.modulusOfContinuityOn_Iic_real_eq] using
    hB.tendsto_modulusOfContinuityOn_Iic_div_sqrt hT

/-- Scaling a standard Brownian motion by `c : ℝ` scales its Lévy uniform-modulus limit on `[0, T]`
(`T > 0`) to `|c|`. -/
theorem tendsto_modulusOfContinuityOn_Iic_const_mul_div_sqrt (hB : IsBrownianReal B P)
    (c : ℝ) {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun h : ℝ ↦ TauCeti.modulusOfContinuityOn (fun t ↦ c * B t ω) (Iic T) h /
        √(2 * h * Real.log (1 / h))) (𝓝[>] 0) (𝓝 |c|) := by
  filter_upwards [hB.tendsto_modulusOfContinuityOn_Iic_div_sqrt hT] with ω hω
  have hmul : Tendsto
      (fun h : ℝ ↦ |c| *
        (TauCeti.modulusOfContinuityOn (B · ω) (Iic T) h / √(2 * h * Real.log (1 / h))))
      (𝓝[>] 0) (𝓝 |c|) := by simpa only [mul_one] using hω.const_mul |c|
  refine hmul.congr fun h ↦ ?_
  have h1 := TauCeti.modulusOfContinuityOn_fun_smul c (B · ω) (Iic T) h
  simp only [smul_eq_mul, Real.norm_eq_abs] at h1
  rw [h1, mul_div_assoc]

end MainTheorems

end ProbabilityTheory.IsBrownianReal
