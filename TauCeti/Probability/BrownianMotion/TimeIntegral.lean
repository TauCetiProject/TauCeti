/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mean-square time integration of Brownian motion

Brownian motion is a continuous curve in native real `L²`. Its ordinary Bochner time integral
therefore exists without choosing jointly measurable representatives. This file computes the
exact squared `L²` error of left-rectangle quadrature: it is one third of the sum of the cubes
of the interval lengths. In particular it tends to zero along vanishing-mesh partitions.

These are ordinary time integrals, not stochastic integrals. Only the pre-Brownian
finite-dimensional laws are required; no filtration or path-continuity hypothesis is imposed.
No identification with time integrals of arbitrary raw sample paths is asserted.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.3, for the polynomial Itô approximation in which this time-integral error occurs.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal InnerProductSpace

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- Brownian evaluation as a native real `L²` class. -/
def toL2 (hB : IsPreBrownianReal B P) (t : ℝ≥0) : Lp ℝ 2 P :=
  ((hB.hasLaw_eval t).memLp (memLp_id_gaussianReal 2)).toLp (B t)

omit [IsProbabilityMeasure P] in
/-- The `L²` evaluation class represents the original evaluation almost surely. -/
theorem coeFn_toL2 (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ⇑(hB.toL2 t) =ᵐ[P] B t :=
  MemLp.coeFn_toLp _

/-- The inner product of two Brownian evaluation classes is their covariance `min s t`. -/
@[simp]
theorem inner_toL2 (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    ⟪hB.toL2 s, hB.toL2 t⟫_ℝ = (min s t : ℝ≥0) := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  trans ∫ ω, B t ω * B s ω ∂P
  · apply integral_congr_ae
    filter_upwards [hB.coeFn_toL2 t, hB.coeFn_toL2 s] with ω ht hs
    rw [ht, hs]
  have hcov := covariance_eq_sub ((hB.hasLaw_eval t).memLp (memLp_id_gaussianReal 2))
    ((hB.hasLaw_eval s).memLp (memLp_id_gaussianReal 2))
  simpa [hB.integral_eval, hB.covariance_eval, min_comm] using hcov.symm

/-- Squared mean-square distance of Brownian evaluations equals elapsed time. -/
theorem norm_toL2_sub_sq (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    ‖hB.toL2 s - hB.toL2 t‖ ^ 2 = |(s : ℝ) - t| := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_toL2, min_self, NNReal.coe_min]
  rcases le_total (s : ℝ) t with h | h
  · rw [min_eq_left h, min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Brownian evaluation is continuous in mean square, even for a raw pre-Brownian version. -/
theorem continuous_toL2 (hB : IsPreBrownianReal B P) : Continuous hB.toL2 := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  have hc : Continuous (fun s : ℝ≥0 => Real.sqrt |(s : ℝ) - t|) := by fun_prop
  have h : Tendsto (fun s : ℝ≥0 => Real.sqrt |(s : ℝ) - t|) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self, abs_zero, Real.sqrt_zero] using hc.tendsto t
  convert h using 1
  ext s
  rw [← hB.norm_toL2_sub_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The left-rectangle error on one interval, as an ordinary time integral in `L²`.
Real time is mapped to nonnegative time; only intervals with nonnegative endpoints are used. -/
def timeIntegralError (hB : IsPreBrownianReal B P) (a b : ℝ≥0) : Lp ℝ 2 P :=
  ∫ u in (a : ℝ)..b, hB.toL2 a - hB.toL2 u.toNNReal

omit [IsProbabilityMeasure P] in
/-- A zero-length cell has zero quadrature error. -/
@[simp]
theorem timeIntegralError_self (hB : IsPreBrownianReal B P) (a : ℝ≥0) :
    hB.timeIntegralError a a = 0 := by
  simp [timeIntegralError]

/-- The error is the left rectangle minus the mean-square time integral. -/
theorem timeIntegralError_eq (hB : IsPreBrownianReal B P) (a b : ℝ≥0) :
    hB.timeIntegralError a b = ((b : ℝ) - a) • hB.toL2 a -
      ∫ u in (a : ℝ)..b, hB.toL2 u.toNNReal := by
  have hc : Continuous (fun u : ℝ => hB.toL2 u.toNNReal) :=
    hB.continuous_toL2.comp continuous_real_toNNReal
  rw [timeIntegralError, intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const]

private theorem inner_sub_toL2 (hB : IsPreBrownianReal B P) (a : ℝ≥0)
    {u v : ℝ} (hu : (a : ℝ) ≤ u) (hv : (a : ℝ) ≤ v) :
    ⟪hB.toL2 a - hB.toL2 u.toNNReal, hB.toL2 a - hB.toL2 v.toNNReal⟫_ℝ =
      min u v - a := by
  simp only [inner_sub_left, inner_sub_right, inner_toL2, min_self, NNReal.coe_min,
    Real.coe_toNNReal _ (le_trans a.coe_nonneg hu),
    Real.coe_toNNReal _ (le_trans a.coe_nonneg hv), min_eq_right hu, min_eq_left hv]
  ring

private theorem integral_inner_sub_toL2 (hB : IsPreBrownianReal B P)
    {a b : ℝ≥0} (hab : a ≤ b) (u : ℝ) (hu : u ∈ Icc (a : ℝ) b) :
    (∫ v in (a : ℝ)..b,
      ⟪hB.toL2 a - hB.toL2 u.toNNReal, hB.toL2 a - hB.toL2 v.toNNReal⟫_ℝ) =
        (u ^ 2 - (a : ℝ) ^ 2) / 2 + (b - u) * u - (b - a) * a := by
  have hcont : Continuous (fun v : ℝ => min u v - a) := by fun_prop
  rw [intervalIntegral.integral_congr (fun v hv =>
    hB.inner_sub_toL2 a hu.1 (by
      have hv' : v ∈ Icc (a : ℝ) b := by
        simpa only [uIcc_of_le (show (a : ℝ) ≤ b from hab)] using hv
      exact hv'.1))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (a : ℝ) u) (hcont.intervalIntegrable u b)]
  have hleft : (∫ v in (a : ℝ)..u, min u v - a) = ∫ v in (a : ℝ)..u, v - a := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc (a : ℝ) u := by simpa only [uIcc_of_le hu.1] using hv
    simp only [min_eq_right hv'.2]
  have hright : (∫ v in u..(b : ℝ), min u v - a) = (b - u) * (u - a) := by
    trans ∫ _ in u..(b : ℝ), u - a
    · apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Icc u (b : ℝ) := by simpa only [uIcc_of_le hu.2] using hv
      simp only [min_eq_left hv'.1]
    · simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [hleft, hright, intervalIntegral.integral_sub (f := fun v : ℝ => v)
    (continuous_id.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Squared mean-square error of one Brownian left rectangle. -/
theorem norm_timeIntegralError_sq (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    ‖hB.timeIntegralError a b‖ ^ 2 = ((b : ℝ) - a) ^ 3 / 3 := by
  let X : ℝ → Lp ℝ 2 P := fun u => hB.toL2 a - hB.toL2 u.toNNReal
  have hX : Continuous X := continuous_const.sub
    (hB.continuous_toL2.comp continuous_real_toNNReal)
  have hint (y : Lp ℝ 2 P) :
      ⟪y, ∫ u in (a : ℝ)..b, X u⟫_ℝ = ∫ u in (a : ℝ)..b, ⟪y, X u⟫_ℝ := by
    simpa only [innerSL_apply_apply] using
      ((innerSL ℝ y).intervalIntegral_comp_comm (hX.intervalIntegrable _ _)).symm
  have hexpand : ‖hB.timeIntegralError a b‖ ^ 2 =
      ∫ u in (a : ℝ)..b, ∫ v in (a : ℝ)..b, ⟪X u, X v⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, timeIntegralError, hint]
    congr 1
    ext u
    rw [real_inner_comm, hint]
  rw [hexpand]
  rw [intervalIntegral.integral_congr (fun u hu =>
    hB.integral_inner_sub_toL2 hab u
      (by simpa only [uIcc_of_le (show (a : ℝ) ≤ b from hab)] using hu))]
  have hpoly : (∫ u in (a : ℝ)..b,
      (u ^ 2 - (a : ℝ) ^ 2) / 2 + (b - u) * u - (b - a) * a) =
      (- (b : ℝ) ^ 3 / 6 + b * b ^ 2 / 2 + (a ^ 2 / 2 - b * a) * b) -
      (- (a : ℝ) ^ 3 / 6 + b * a ^ 2 / 2 + (a ^ 2 / 2 - b * a) * a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => -u ^ 3 / 6 + b * u ^ 2 / 2 + (a ^ 2 / 2 - b * a) * u)
    · intro u _
      convert (((((hasDerivAt_pow 3 u).neg.div_const 6).add
        (((hasDerivAt_pow 2 u).const_mul (b : ℝ)).div_const 2)).add
        ((hasDerivAt_id u).const_mul ((a : ℝ) ^ 2 / 2 - (b : ℝ) * a)))) using 1
      · ext x
        simp only [Pi.add_apply, Pi.neg_apply, id_eq]
      · ring
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hpoly]
  ring

/-- Brownian left-rectangle errors on disjoint intervals are orthogonal in `L²`. -/
theorem inner_timeIntegralError_eq_zero (hB : IsPreBrownianReal B P)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ⟪hB.timeIntegralError a b, hB.timeIntegralError c d⟫_ℝ = 0 := by
  have hc : Continuous (fun u : ℝ => hB.toL2 u.toNNReal) :=
    hB.continuous_toL2.comp continuous_real_toNNReal
  have hcont (s : ℝ≥0) : Continuous (fun u : ℝ => hB.toL2 s - hB.toL2 u.toNNReal) :=
    continuous_const.sub hc
  have hint (y : Lp ℝ 2 P) (s t : ℝ≥0) :
      ⟪y, hB.timeIntegralError s t⟫_ℝ =
        ∫ u in (s : ℝ)..t, ⟪y, hB.toL2 s - hB.toL2 u.toNNReal⟫_ℝ := by
    simpa only [timeIntegralError, innerSL_apply_apply] using
      ((innerSL ℝ y).intervalIntegral_comp_comm
        ((hcont s).intervalIntegrable (s : ℝ) t)).symm
  rw [real_inner_comm, hint]
  trans ∫ _ in (a : ℝ)..b, (0 : ℝ)
  · apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (a : ℝ) b := by
      simpa only [uIcc_of_le (show (a : ℝ) ≤ b from hab)] using hu
    dsimp only
    rw [real_inner_comm, hint]
    trans ∫ _ in (c : ℝ)..d, (0 : ℝ)
    · apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Icc (c : ℝ) d := by
        simpa only [uIcc_of_le (show (c : ℝ) ≤ d from hcd)] using hv
      have huv : u ≤ v := hu'.2.trans ((show (b : ℝ) ≤ c from hbc).trans hv'.1)
      simp only [inner_sub_left, inner_sub_right, inner_toL2, NNReal.coe_min,
        Real.coe_toNNReal _ (a.coe_nonneg.trans hu'.1),
        Real.coe_toNNReal _ (c.coe_nonneg.trans hv'.1),
        min_eq_left (show (a : ℝ) ≤ c from hab.trans hbc),
        min_eq_left (hu'.1.trans huv),
        min_eq_left (hu'.2.trans (show (b : ℝ) ≤ c from hbc)), min_eq_left huv]
      ring
    · simp
  · simp

/-- Summed local errors equal the left quadrature sum minus the time integral on the full grid.
No ordering assumption is needed for this telescoping identity. -/
theorem sum_timeIntegralError_eq (hB : IsPreBrownianReal B P) (t : ℕ → ℝ≥0) (n : ℕ) :
    ∑ i ∈ Finset.range n, hB.timeIntegralError (t i) (t (i + 1)) =
      (∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) • hB.toL2 (t i)) -
        ∫ u in (t 0 : ℝ)..t n, hB.toL2 u.toNNReal := by
  simp_rw [timeIntegralError_eq]
  rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals]
  intro i _
  exact (hB.continuous_toL2.comp continuous_real_toNNReal).intervalIntegrable _ _

/-- The exact squared `L²` error of Brownian left-rectangle quadrature on a nondecreasing grid.
Repeated dates and the empty grid are allowed. -/
theorem norm_sum_timeIntegralError_sq (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, hB.timeIntegralError (t i) (t (i + 1))‖ ^ 2 =
      (∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) ^ 3) / 3 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq, hB.norm_timeIntegralError_sq (ht (Nat.le_succ i))]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hij | hij
    · rw [real_inner_comm]
      exact hB.inner_timeIntegralError_eq_zero (ht (Nat.le_succ j))
        (ht (by omega)) (ht (Nat.le_succ i))
    · exact hB.inner_timeIntegralError_eq_zero (ht (Nat.le_succ i))
        (ht (by omega)) (ht (Nat.le_succ j))
  · exact fun h => (h hi).elim

/-- The squared quadrature error is bounded by elapsed time times mesh squared, divided by three. -/
theorem norm_sum_timeIntegralError_sq_le (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) {δ : ℝ}
    (hδ : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ) :
    ‖∑ i ∈ Finset.range n, hB.timeIntegralError (t i) (t (i + 1))‖ ^ 2 ≤
      ((t n : ℝ) - t 0) * δ ^ 2 / 3 := by
  rw [hB.norm_sum_timeIntegralError_sq t ht n]
  gcongr
  calc
    ∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) ^ 3 ≤
        ∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) * δ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi0 : 0 ≤ (t (i + 1) : ℝ) - t i := sub_nonneg.mpr (ht (Nat.le_succ i))
      have hiδ := hδ i (Finset.mem_range.mp hi)
      calc
        ((t (i + 1) : ℝ) - t i) ^ 3 =
            ((t (i + 1) : ℝ) - t i) * (((t (i + 1) : ℝ) - t i) ^ 2) := by ring
        _ ≤ ((t (i + 1) : ℝ) - t i) * δ ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hi0 hiδ 2) hi0
    _ = ((t n : ℝ) - t 0) * δ ^ 2 := by
      rw [← Finset.sum_mul, Finset.sum_range_sub (fun i => (t i : ℝ))]

/-- On the equal grid with `n > 0` cells, the exact squared quadrature error is `T³/(3n²)`. -/
theorem norm_sum_timeIntegralError_sq_equidistant (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ‖∑ i ∈ Finset.range n, hB.timeIntegralError ((i : ℝ≥0) * T / n)
      (((i + 1 : ℕ) : ℝ≥0) * T / n)‖ ^ 2 = (T : ℝ) ^ 3 / (3 * (n : ℝ) ^ 2) := by
  have ht : Monotone (fun i : ℕ => (i : ℝ≥0) * T / n) := by
    intro i j hij
    dsimp only
    gcongr
  rw [hB.norm_sum_timeIntegralError_sq _ ht n]
  have hstep (i : ℕ) :
      ((((i + 1 : ℕ) : ℝ≥0) * T / n : ℝ≥0) : ℝ) -
        (((i : ℝ≥0) * T / n : ℝ≥0) : ℝ) = (T : ℝ) / n := by
    simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add,
      Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
    ring
  simp_rw [hstep]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- Brownian left-rectangle quadrature converges in native `L²` along every bounded-horizon
vanishing-mesh family, without nestedness or a fixed number of cells. -/
theorem tendsto_sum_timeIntegralError_zero (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {t : ι → ℕ → ℝ≥0} {n : ι → ℕ} {δ : ι → ℝ}
    (ht : ∀ k, Monotone (t k)) {T : ℝ≥0} (hT : ∀ k, t k (n k) ≤ T)
    (hδ : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (n k),
      hB.timeIntegralError (t k i) (t k (i + 1))) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hbound k :
      ‖∑ i ∈ Finset.range (n k), hB.timeIntegralError (t k i) (t k (i + 1))‖ ^ 2 ≤
        (T : ℝ) * (δ k) ^ 2 / 3 := by
    have hspan : (t k (n k) : ℝ) - t k 0 ≤ T :=
      (sub_le_self _ (t k 0).coe_nonneg).trans (hT k)
    exact (hB.norm_sum_timeIntegralError_sq_le (t k) (ht k) (n k) (hδ k)).trans
      (by gcongr)
  have hs : Tendsto (fun k =>
      ‖∑ i ∈ Finset.range (n k), hB.timeIntegralError (t k i) (t k (i + 1))‖ ^ 2)
      l (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hbound (by
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, div_mul_eq_mul_div] using
        (hlim.pow 2).const_mul ((T : ℝ) / 3))
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

end ProbabilityTheory.IsPreBrownianReal
