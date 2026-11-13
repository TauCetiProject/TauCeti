/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import TauCeti.MeasureTheory.Function.Lp.Basic

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

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- Brownian evaluation as a native real `L²` class. -/
def toL2 (hB : IsPreBrownianReal B P) (t : ℝ≥0) : Lp ℝ 2 P :=
  ((hB.hasLaw_eval t).memLp (memLp_id_gaussianReal 2)).toLp (B t)

/-- The `L²` evaluation class represents the original evaluation almost surely. -/
theorem coeFn_toL2 (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ⇑(hB.toL2 t) =ᵐ[P] B t :=
  MemLp.coeFn_toLp _

/-- The `L²` class of a finite weighted sum of Brownian evaluations is the corresponding
sum of evaluation classes, for any square-integrability witness on the sum. -/
theorem toLp_sum_smul_eval (hB : IsPreBrownianReal B P) {ι : Type*}
    (s : Finset ι) (t : ι → ℝ≥0) (w : ι → ℝ)
    (hsum : MemLp (fun ω ↦ ∑ i ∈ s, w i * B (t i) ω) 2 P) :
    hsum.toLp _ = ∑ i ∈ s, w i • hB.toL2 (t i) := by
  let hf i : MemLp (B (t i)) 2 P :=
    (hB.hasLaw_eval (t i)).memLp (memLp_id_gaussianReal 2)
  exact (hsum.toLp_finsetSum (fun i ↦ (hf i).const_smul (w i))).trans
    (Finset.sum_congr rfl fun i _ ↦ by
      simpa only [toL2, Pi.smul_def, smul_eq_mul] using
        MemLp.toLp_const_smul (w i) (hf i))

/-- The inner product of two Brownian evaluation classes is their covariance `min s t`. -/
@[simp]
theorem inner_toL2 (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    ⟪hB.toL2 s, hB.toL2 t⟫_ℝ = (min s t : ℝ≥0) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
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

/-- Brownian evaluation extended to real time by truncation at zero is continuous in `L²`. -/
theorem continuous_toL2_toNNReal (hB : IsPreBrownianReal B P) :
    Continuous (fun u : ℝ => hB.toL2 u.toNNReal) :=
  hB.continuous_toL2.comp continuous_real_toNNReal

/-- The left-rectangle error on one interval, as an ordinary time integral in `L²`.
Real time is mapped to nonnegative time; only intervals with nonnegative endpoints are used. -/
def leftRiemannError (hB : IsPreBrownianReal B P) (a b : ℝ≥0) : Lp ℝ 2 P :=
  ∫ u in (a : ℝ)..b, hB.toL2 a - hB.toL2 u.toNNReal

/-- A zero-length cell has zero quadrature error. -/
@[simp]
theorem leftRiemannError_self (hB : IsPreBrownianReal B P) (a : ℝ≥0) :
    hB.leftRiemannError a a = 0 := by
  simp [leftRiemannError]

/-- The error is the left rectangle minus the mean-square time integral. -/
theorem leftRiemannError_eq (hB : IsPreBrownianReal B P) (a b : ℝ≥0) :
    hB.leftRiemannError a b = ((b : ℝ) - a) • hB.toL2 a -
      ∫ u in (a : ℝ)..b, hB.toL2 u.toNNReal := by
  rw [leftRiemannError, intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable _ _) (hB.continuous_toL2_toNNReal.intervalIntegrable _ _),
    intervalIntegral.integral_const]

/-- Taking an inner product commutes with the mean-square left-rectangle error integral. -/
theorem inner_leftRiemannError_right (hB : IsPreBrownianReal B P)
    (y : Lp ℝ 2 P) (a b : ℝ≥0) :
    ⟪y, hB.leftRiemannError a b⟫_ℝ =
      ∫ u in (a : ℝ)..b, ⟪y, hB.toL2 a - hB.toL2 u.toNNReal⟫_ℝ := by
  simpa only [leftRiemannError, innerSL_apply_apply, Pi.sub_apply] using
    ((innerSL ℝ y).intervalIntegral_comp_comm
      ((continuous_const.sub hB.continuous_toL2_toNNReal).intervalIntegrable _ _)).symm

private theorem inner_sub_toL2 (hB : IsPreBrownianReal B P) (a : ℝ≥0)
    {u v : ℝ} (hu : (a : ℝ) ≤ u) (hv : (a : ℝ) ≤ v) :
    ⟪hB.toL2 a - hB.toL2 u.toNNReal, hB.toL2 a - hB.toL2 v.toNNReal⟫_ℝ =
      min u v - a := by
  simp only [inner_sub_left, inner_sub_right, inner_toL2, min_self, NNReal.coe_min,
    Real.coe_toNNReal _ (le_trans a.coe_nonneg hu),
    Real.coe_toNNReal _ (le_trans a.coe_nonneg hv), min_eq_right hu, min_eq_left hv]
  ring

private theorem inner_sub_toL2_eq_zero (hB : IsPreBrownianReal B P)
    {a c : ℝ≥0} {u v : ℝ} (hau : (a : ℝ) ≤ u) (huc : u ≤ c) (hcv : (c : ℝ) ≤ v) :
    ⟪hB.toL2 a - hB.toL2 u.toNNReal, hB.toL2 c - hB.toL2 v.toNNReal⟫_ℝ = 0 := by
  have hac := hau.trans huc
  have huv := huc.trans hcv
  simp only [inner_sub_left, inner_sub_right, inner_toL2, NNReal.coe_min,
    Real.coe_toNNReal _ (a.coe_nonneg.trans hau),
    Real.coe_toNNReal _ (c.coe_nonneg.trans hcv),
    min_eq_left hac, min_eq_left (hau.trans huv), min_eq_left huc, min_eq_left huv]
  ring

private theorem integral_inner_sub_toL2 (hB : IsPreBrownianReal B P)
    {a b : ℝ≥0} (hab : a ≤ b) (u : ℝ) (hu : u ∈ Icc (a : ℝ) b) :
    (∫ v in (a : ℝ)..b,
      ⟪hB.toL2 a - hB.toL2 u.toNNReal, hB.toL2 a - hB.toL2 v.toNNReal⟫_ℝ) =
        (u ^ 2 - (a : ℝ) ^ 2) / 2 + (b - u) * u - (b - a) * a := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hcont : Continuous (fun v : ℝ => min u v - a) := by fun_prop
  rw [intervalIntegral.integral_congr (fun v hv =>
    hB.inner_sub_toL2 a hu.1 (by
      have hv' : v ∈ Icc (a : ℝ) b := by
        simpa only [uIcc_of_le hab'] using hv
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
theorem norm_leftRiemannError_sq (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    ‖hB.leftRiemannError a b‖ ^ 2 = ((b : ℝ) - a) ^ 3 / 3 := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hexpand : ‖hB.leftRiemannError a b‖ ^ 2 =
      ∫ u in (a : ℝ)..b, ∫ v in (a : ℝ)..b,
        ⟪hB.toL2 a - hB.toL2 u.toNNReal, hB.toL2 a - hB.toL2 v.toNNReal⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, hB.inner_leftRiemannError_right]
    congr 1
    ext u
    rw [real_inner_comm, hB.inner_leftRiemannError_right]
  rw [hexpand]
  rw [intervalIntegral.integral_congr (fun u hu =>
    hB.integral_inner_sub_toL2 hab u
      (by simpa only [uIcc_of_le hab'] using hu))]
  have hpoly : (∫ u in (a : ℝ)..b,
      (u ^ 2 - (a : ℝ) ^ 2) / 2 + (b - u) * u - (b - a) * a) =
      (- (b : ℝ) ^ 3 / 6 + b * b ^ 2 / 2 + (a ^ 2 / 2 - b * a) * b) -
      (- (a : ℝ) ^ 3 / 6 + b * a ^ 2 / 2 + (a ^ 2 / 2 - b * a) * a) := by
    trans ∫ u in (a : ℝ)..b, -(u ^ 2) / 2 + b * u + (a ^ 2 / 2 - b * a)
    · apply intervalIntegral.integral_congr
      intro u _
      ring
    rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_div, intervalIntegral.integral_neg,
      integral_pow, intervalIntegral.integral_const_mul,
      integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hpoly]
  ring

/-- Brownian left-rectangle errors on disjoint intervals are orthogonal in `L²`. -/
theorem inner_leftRiemannError_eq_zero (hB : IsPreBrownianReal B P)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ⟪hB.leftRiemannError a b, hB.leftRiemannError c d⟫_ℝ = 0 := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc
  have hcd' : (c : ℝ) ≤ d := by exact_mod_cast hcd
  rw [real_inner_comm, hB.inner_leftRiemannError_right]
  trans ∫ _ in (a : ℝ)..b, (0 : ℝ)
  · apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (a : ℝ) b := by
      simpa only [uIcc_of_le hab'] using hu
    dsimp only
    rw [real_inner_comm, hB.inner_leftRiemannError_right]
    trans ∫ _ in (c : ℝ)..d, (0 : ℝ)
    · apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Icc (c : ℝ) d := by
        simpa only [uIcc_of_le hcd'] using hv
      exact hB.inner_sub_toL2_eq_zero hu'.1 (hu'.2.trans hbc') hv'.1
    · simp
  · simp

/-- Summed local errors equal the left quadrature sum minus the time integral on the full grid.
No ordering assumption is needed for this telescoping identity. -/
theorem sum_leftRiemannError_eq (hB : IsPreBrownianReal B P) (t : ℕ → ℝ≥0) (n : ℕ) :
    ∑ i ∈ Finset.range n, hB.leftRiemannError (t i) (t (i + 1)) =
      (∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) • hB.toL2 (t i)) -
        ∫ u in (t 0 : ℝ)..t n, hB.toL2 u.toNNReal := by
  simp_rw [leftRiemannError_eq]
  rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals]
  intro i _
  exact hB.continuous_toL2_toNNReal.intervalIntegrable _ _

/-- The exact squared `L²` error of Brownian left-rectangle quadrature on a nondecreasing grid.
Repeated dates and the empty grid are allowed. -/
theorem norm_sum_leftRiemannError_sq (hB : IsPreBrownianReal B P)
    {t : ℕ → ℝ≥0} {n : ℕ} (ht : MonotoneOn t (Set.Iic n)) :
    ‖∑ i ∈ Finset.range n, hB.leftRiemannError (t i) (t (i + 1))‖ ^ 2 =
      (∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) ^ 3) / 3 := by
  have hstep (i : ℕ) (hi : i < n) : t i ≤ t (i + 1) :=
    ht hi.le hi (Nat.le_succ i)
  have horth : (Finset.range n : Set ℕ).Pairwise fun i j =>
      ⟪hB.leftRiemannError (t i) (t (i + 1)),
        hB.leftRiemannError (t j) (t (j + 1))⟫_ℝ = 0 := by
    intro i hi j hj hij
    have hi := Finset.mem_range.mp hi
    have hj := Finset.mem_range.mp hj
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact hB.inner_leftRiemannError_eq_zero (hstep i hi)
        (ht hi hj.le hij) (hstep j hj)
    · rw [real_inner_comm]
      exact hB.inner_leftRiemannError_eq_zero (hstep j hj)
        (ht hj hi.le hij) (hstep i hi)
  rw [TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero horth, Finset.sum_div]
  exact Finset.sum_congr rfl fun i hi ↦
    hB.norm_leftRiemannError_sq (hstep i (Finset.mem_range.mp hi))

/-- The squared quadrature error is bounded by elapsed time times mesh squared, divided by three. -/
theorem norm_sum_leftRiemannError_sq_le (hB : IsPreBrownianReal B P)
    {t : ℕ → ℝ≥0} {n : ℕ} (ht : MonotoneOn t (Set.Iic n)) {δ : ℝ}
    (hδ : ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ) :
    ‖∑ i ∈ Finset.range n, hB.leftRiemannError (t i) (t (i + 1))‖ ^ 2 ≤
      ((t n : ℝ) - t 0) * δ ^ 2 / 3 := by
  rw [hB.norm_sum_leftRiemannError_sq ht]
  gcongr
  calc
    ∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) ^ 3 ≤
        ∑ i ∈ Finset.range n, ((t (i + 1) : ℝ) - t i) * δ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi := Finset.mem_range.mp hi
      have hi0 : 0 ≤ (t (i + 1) : ℝ) - t i :=
        sub_nonneg.mpr (ht hi.le hi (Nat.le_succ i))
      have hiδ := hδ i hi
      calc
        ((t (i + 1) : ℝ) - t i) ^ 3 =
            ((t (i + 1) : ℝ) - t i) * (((t (i + 1) : ℝ) - t i) ^ 2) := by ring
        _ ≤ ((t (i + 1) : ℝ) - t i) * δ ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hi0 hiδ 2) hi0
    _ = ((t n : ℝ) - t 0) * δ ^ 2 := by
      rw [← Finset.sum_mul, Finset.sum_range_sub (fun i => (t i : ℝ))]

/-- On the equal grid with `n` cells, the exact squared quadrature error is `T³/(3n²)`.
For `n = 0` both sides are zero, using division by zero in the formula. -/
theorem norm_sum_leftRiemannError_sq_equidistant (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, hB.leftRiemannError ((i : ℝ≥0) * T / n)
      (((i + 1 : ℕ) : ℝ≥0) * T / n)‖ ^ 2 = (T : ℝ) ^ 3 / (3 * (n : ℝ) ^ 2) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have ht : Monotone (fun i : ℕ => (i : ℝ≥0) * T / n) := by
    intro i j hij
    dsimp only
    gcongr
  rw [hB.norm_sum_leftRiemannError_sq (ht.monotoneOn _)]
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
theorem tendsto_sum_leftRiemannError_zero (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {t : ι → ℕ → ℝ≥0} {n : ι → ℕ} {δ : ι → ℝ}
    (ht : ∀ k, MonotoneOn (t k) (Set.Iic (n k))) {T : ℝ≥0} (hT : ∀ k, t k (n k) ≤ T)
    (hδ : ∀ k i, i < n k → (t k (i + 1) : ℝ) - t k i ≤ δ k)
    (hlim : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (n k),
      hB.leftRiemannError (t k i) (t k (i + 1))) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hbound k :
      ‖∑ i ∈ Finset.range (n k), hB.leftRiemannError (t k i) (t k (i + 1))‖ ^ 2 ≤
        (T : ℝ) * (δ k) ^ 2 / 3 := by
    have hspan : (t k (n k) : ℝ) - t k 0 ≤ T :=
      (sub_le_self _ (t k 0).coe_nonneg).trans (hT k)
    exact (hB.norm_sum_leftRiemannError_sq_le (ht k) (hδ k)).trans
      (by gcongr)
  have hs : Tendsto (fun k =>
      ‖∑ i ∈ Finset.range (n k), hB.leftRiemannError (t k i) (t k (i + 1))‖ ^ 2)
      l (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hbound (by
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, div_mul_eq_mul_div] using
        (hlim.pow 2).const_mul ((T : ℝ) / 3))
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

end ProbabilityTheory.IsPreBrownianReal
