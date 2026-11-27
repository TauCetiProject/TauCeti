/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Weighted power means

The weighted power mean uses the geometric mean at exponent zero and the usual root of
weighted powers otherwise. For positive entries and nonnegative weights of total mass one,
it is monotone in its real exponent, including negative and zero exponents.
The comparison is strict exactly when two positive-weight entries differ. The mean is
continuous in its exponent; the derivative of the logarithm of the moment sum supplies
the limit at zero.

## Main results

* `TauCeti.powerMean_le_powerMean`: the comparison for all real exponents.
* `TauCeti.powerMean_lt_powerMean_iff`: the strictness criterion on the support of the weights.
* `TauCeti.continuous_powerMean`: continuity across the geometric-mean case.

## References

Hardy, Littlewood and Pólya, *Inequalities*, Theorem 16.
-/

public section

open Finset

namespace TauCeti

variable {ι : Type*} [Fintype ι]

open Classical in
/-- The weighted power mean, with the geometric mean at exponent zero. -/
noncomputable def powerMean (w x : ι → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then ∏ i, x i ^ w i else (∑ i, w i * x i ^ r) ^ r⁻¹

/-- The power mean at exponent zero is the weighted geometric mean. -/
@[simp] theorem powerMean_zero (w x : ι → ℝ) : powerMean w x 0 = ∏ i, x i ^ w i := by
  simp [powerMean]

/-- Formula for the power mean at a nonzero exponent. -/
theorem powerMean_of_ne_zero (w x : ι → ℝ) {r : ℝ} (hr : r ≠ 0) :
    powerMean w x r = (∑ i, w i * x i ^ r) ^ r⁻¹ := by
  simp [powerMean, hr]

/-- The power mean at exponent one is the weighted arithmetic mean. -/
@[simp] theorem powerMean_one (w x : ι → ℝ) : powerMean w x 1 = ∑ i, w i * x i := by
  simp [powerMean]

/-- The power mean at exponent minus one is the weighted harmonic mean. -/
@[simp] theorem powerMean_neg_one (w x : ι → ℝ) :
    powerMean w x (-1) = (∑ i, w i / x i)⁻¹ := by
  simp [powerMean, Real.rpow_neg_one, div_eq_mul_inv]

private theorem weighted_rpow_sum_pos {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hwpos : 0 < ∑ i, w i) (hx : ∀ i, 0 < x i) (r : ℝ) : 0 < ∑ i, w i * x i ^ r := by
  obtain ⟨i, hi, hwi⟩ := (sum_pos_iff_of_nonneg (fun i _ ↦ hw i)).mp
    hwpos
  exact sum_pos' (fun j _ ↦ mul_nonneg (hw j) (Real.rpow_pos_of_pos (hx j) r).le)
    ⟨i, hi, mul_pos hwi (Real.rpow_pos_of_pos (hx i) r)⟩

/-- A power mean of positive entries with nonnegative weights of positive total mass is positive. -/
theorem powerMean_pos {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hwpos : 0 < ∑ i, w i)
    (hx : ∀ i, 0 < x i) (r : ℝ) : 0 < powerMean w x r := by
  by_cases hr : r = 0
  · subst r
    rw [powerMean_zero]
    exact prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hx i) _
  · rw [powerMean_of_ne_zero w x hr]
    exact Real.rpow_pos_of_pos (weighted_rpow_sum_pos hw hwpos hx r) _

/-- Negating the exponent is equivalent to inverting both entries and the resulting mean. -/
theorem powerMean_neg {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (r : ℝ) :
    powerMean w x (-r) = (powerMean w (fun i ↦ (x i)⁻¹) r)⁻¹ := by
  by_cases hr : r = 0
  · subst r
    simp [Real.inv_rpow, hx, prod_inv_distrib]
  · rw [powerMean_of_ne_zero w x (neg_ne_zero.mpr hr),
      powerMean_of_ne_zero _ _ hr, inv_neg]
    simp_rw [Real.rpow_neg_eq_inv_rpow]
    exact Real.inv_rpow (sum_nonneg fun i _ ↦ mul_nonneg (hw i)
      (Real.rpow_nonneg (inv_nonneg.mpr (hx i)) r)) _

/-- The geometric mean commutes with taking a common real power of nonnegative entries. -/
theorem powerMean_zero_rpow (w : ι → ℝ) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (s : ℝ) :
    powerMean w x 0 ^ s = powerMean w (fun i ↦ x i ^ s) 0 := by
  simp only [powerMean_zero]
  rw [← Real.finsetProd_rpow univ _ (fun i _ ↦ Real.rpow_nonneg (hx i) (w i))]
  apply prod_congr rfl
  intro i _
  rw [← Real.rpow_mul (hx i), ← Real.rpow_mul (hx i), mul_comm]


/-- Taking the defining power recovers the weighted sum of powers. -/
theorem powerMean_rpow {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i)
    {r : ℝ} (hr : r ≠ 0) : powerMean w x r ^ r = ∑ i, w i * x i ^ r := by
  rw [powerMean_of_ne_zero w x hr,
    ← Real.rpow_mul (sum_nonneg fun i _ ↦ mul_nonneg (hw i) (Real.rpow_nonneg (hx i) r)),
    inv_mul_cancel₀ hr, Real.rpow_one]


private theorem powerMean_lt_of_pos {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hne : ∃ i j, 0 < w i ∧ 0 < w j ∧ x i ≠ x j) : powerMean w x r < powerMean w x s := by
  have hmass : 0 < ∑ i, w i := by rw [hw1]; exact zero_lt_one
  have hs := hr.trans hrs
  have hconv := strictConvexOn_rpow ((lt_div_iff₀ hr).mpr (by simpa using hrs))
  have hstrict := hconv.map_sum_lt_iff_of_nonneg (t := univ) (p := fun i ↦ x i ^ r)
      (fun i _ ↦ hw i) hw1 (fun i _ ↦ (Real.rpow_pos_of_pos (hx i) r).le)
  obtain ⟨i, j, hi, hj, hij⟩ := hne
  have h := hstrict.mpr ⟨i, mem_univ i, j, mem_univ j, hi.ne', hj.ne',
    fun heq ↦ hij ((Real.rpow_left_inj (hx i).le (hx j).le hr.ne').mp heq)⟩
  simp only [smul_eq_mul] at h
  apply (Real.rpow_lt_rpow_iff (powerMean_pos hw hmass hx r).le
    (powerMean_pos hw hmass hx s).le hs).mp
  rw [powerMean_rpow hw (fun i ↦ (hx i).le) hs.ne']
  have hexp : r * (s / r) = s := by field_simp
  have heq : powerMean w x r ^ s = (∑ i, w i * x i ^ r) ^ (s / r) := by
    rw [← powerMean_rpow hw (fun i ↦ (hx i).le) hr.ne',
      ← Real.rpow_mul (powerMean_pos hw hmass hx r).le, hexp]
  rw [heq]
  convert h using 1
  apply sum_congr rfl
  intro i _
  rw [← Real.rpow_mul (hx i).le, hexp]

private theorem powerMean_zero_lt_of_pos {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) {s : ℝ} (hs : 0 < s)
    (hne : ∃ i j, 0 < w i ∧ 0 < w j ∧ x i ≠ x j) : powerMean w x 0 < powerMean w x s := by
  have hmass : 0 < ∑ i, w i := by rw [hw1]; exact zero_lt_one
  apply (Real.rpow_lt_rpow_iff (powerMean_pos hw hmass hx 0).le
    (powerMean_pos hw hmass hx s).le hs).mp
  rw [powerMean_zero_rpow w (fun i ↦ (hx i).le), powerMean_zero,
    powerMean_rpow hw (fun i ↦ (hx i).le) hs.ne']
  apply (Real.geom_mean_lt_arith_mean_weighted_iff_of_nonneg univ w (fun i ↦ x i ^ s)
    (fun i _ ↦ hw i) hw1 (fun i _ ↦ (Real.rpow_pos_of_pos (hx i) s).le)).mpr
  obtain ⟨i, j, hi, hj, hij⟩ := hne
  exact ⟨i, mem_univ i, j, mem_univ j, hi.ne', hj.ne',
    fun heq ↦ hij ((Real.rpow_left_inj (hx i).le (hx j).le hs.ne').mp heq)⟩

private theorem powerMean_lt_of_nonconstant {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) {r s : ℝ} (hrs : r < s)
    (hne : ∃ i j, 0 < w i ∧ 0 < w j ∧ x i ≠ x j) : powerMean w x r < powerMean w x s := by
  have hmass : 0 < ∑ i, w i := by rw [hw1]; exact zero_lt_one
  have hnonneg {y : ι → ℝ} (hy : ∀ i, 0 < y i)
      (hne : ∃ i j, 0 < w i ∧ 0 < w j ∧ y i ≠ y j)
      {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : powerMean w y a < powerMean w y b := by
    rcases ha.eq_or_lt with rfl | ha
    · exact powerMean_zero_lt_of_pos hw hw1 hy hab hne
    · exact powerMean_lt_of_pos hw hw1 hy ha hab hne
  have hnonpos {a b : ℝ} (hab : a < b) (hb : b ≤ 0) :
      powerMean w x a < powerMean w x b := by
    have hxinv : ∀ i, 0 < (x i)⁻¹ := fun i ↦ inv_pos.mpr (hx i)
    have hneinv : ∃ i j, 0 < w i ∧ 0 < w j ∧ (x i)⁻¹ ≠ (x j)⁻¹ := by
      obtain ⟨i, j, hi, hj, hij⟩ := hne
      exact ⟨i, j, hi, hj, fun heq ↦ hij (inv_inj.mp heq)⟩
    have h := hnonneg hxinv hneinv (neg_nonneg.mpr hb) (neg_lt_neg hab)
    have hinv := (inv_lt_inv₀ (powerMean_pos hw hmass hxinv (-a))
      (powerMean_pos hw hmass hxinv (-b))).mpr h
    simpa only [← powerMean_neg hw (fun i ↦ (hx i).le), neg_neg] using hinv
  by_cases hr : 0 ≤ r
  · exact hnonneg hx hne hr hrs
  · by_cases hs : s ≤ 0
    · exact hnonpos hrs hs
    · exact (hnonpos (lt_of_not_ge hr) le_rfl).trans
        (hnonneg hx hne le_rfl (lt_of_not_ge hs))

/-- For weights of total mass one, if every nonzero-weight entry equals a nonnegative
constant, the power mean equals that constant. -/
theorem powerMean_eq_of_eq_on_support {w x : ι → ℝ} (hw1 : ∑ i, w i = 1) {c : ℝ}
    (hc : 0 ≤ c) (hx : ∀ i, w i ≠ 0 → x i = c) (r : ℝ) : powerMean w x r = c := by
  have hterm (i : ι) : x i ^ w i = c ^ w i := by
    by_cases hi : w i = 0
    · simp [hi]
    · rw [hx i hi]
  by_cases hr : r = 0
  · subst r
    rw [powerMean_zero]
    simp only [hterm]
    rcases hc.eq_or_lt with rfl | hc
    · have hex : ∃ i, w i ≠ 0 := by
        by_contra! hz
        have : ∑ i, w i = 0 := by simp [hz]
        linarith
      obtain ⟨i, hi⟩ := hex
      exact prod_eq_zero (mem_univ i) (Real.zero_rpow hi)
    · rw [← Real.rpow_sum_of_pos hc, hw1, Real.rpow_one]
  · rw [powerMean_of_ne_zero w x hr]
    have hsum : (∑ i, w i * x i ^ r) = c ^ r :=
      Real.arith_mean_weighted_of_constant univ w (fun i ↦ x i ^ r) (c ^ r) hw1
        (fun i _ hi ↦ by rw [hx i hi])
    rw [hsum, ← Real.rpow_mul hc, mul_inv_cancel₀ hr, Real.rpow_one]

private theorem powerMean_eq_of_not_nonconstant {w x : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i)
    (hconst : ¬ ∃ i j, 0 < w i ∧ 0 < w j ∧ x i ≠ x j) (r s : ℝ) :
    powerMean w x r = powerMean w x s := by
  push Not at hconst
  obtain ⟨j, _, hj⟩ := (sum_pos_iff_of_nonneg (fun i _ ↦ hw i)).mp
    (show 0 < ∑ i, w i by rw [hw1]; exact zero_lt_one)
  have hc (i : ι) (hi : w i ≠ 0) : x i = x j :=
    hconst i j (lt_of_le_of_ne (hw i) hi.symm) hj
  rw [powerMean_eq_of_eq_on_support hw1 (hx j).le hc r,
    powerMean_eq_of_eq_on_support hw1 (hx j).le hc s]

/-- The power-mean inequality is strict exactly when two positive-weight entries differ. -/
theorem powerMean_lt_powerMean_iff {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) {r s : ℝ} (hrs : r < s) :
    powerMean w x r < powerMean w x s ↔ ∃ i j, 0 < w i ∧ 0 < w j ∧ x i ≠ x j := by
  refine ⟨?_, powerMean_lt_of_nonconstant hw hw1 hx hrs⟩
  intro hlt
  by_contra hconst
  exact hlt.ne (powerMean_eq_of_not_nonconstant hw hw1 hx hconst r s)

/-- **The power-mean inequality**, for arbitrary ordered real exponents. -/
theorem powerMean_le_powerMean {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hx : ∀ i, 0 < x i) {r s : ℝ} (hrs : r ≤ s) : powerMean w x r ≤ powerMean w x s := by
  rcases hrs.eq_or_lt with rfl | hrs
  · exact le_rfl
  by_cases hne : ∃ i j, 0 < w i ∧ 0 < w j ∧ x i ≠ x j
  · exact (powerMean_lt_of_nonconstant hw hw1 hx hrs hne).le
  · exact (powerMean_eq_of_not_nonconstant hw hw1 hx hne r s).le

/-- The weighted geometric mean as the exponential of the weighted logarithms. -/
theorem powerMean_zero_eq_exp (w : ι → ℝ) {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    powerMean w x 0 = Real.exp (∑ i, w i * Real.log (x i)) := by
  rw [powerMean_zero, Real.exp_sum]
  apply prod_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (hx i), mul_comm]

/-- For positive entries and weights of total mass one, the power mean is continuous
at exponent zero. Signed weights are allowed. -/
theorem continuousAt_powerMean_zero {w x : ι → ℝ} (hw1 : ∑ i, w i = 1)
    (hx : ∀ i, 0 < x i) : ContinuousAt (powerMean w x) 0 := by
  have hsum : HasDerivAt (fun r : ℝ ↦ ∑ i, w i * x i ^ r)
      (∑ i, w i * Real.log (x i)) 0 := by
    simpa [Finset.sum_apply] using HasDerivAt.fun_sum (u := univ) (fun i _ ↦
      ((hasDerivAt_id (0 : ℝ)).const_rpow (hx i)).const_mul (w i))
  have hlog : HasDerivAt (fun r : ℝ ↦ Real.log (∑ i, w i * x i ^ r))
      (∑ i, w i * Real.log (x i)) 0 := by
    simpa [hw1] using hsum.log (by simp [hw1])
  have hlim : Filter.Tendsto (fun r : ℝ ↦ r⁻¹ * Real.log (∑ i, w i * x i ^ r))
      (nhdsWithin 0 {0}ᶜ) (nhds (∑ i, w i * Real.log (x i))) := by
    simpa [smul_eq_mul, hw1] using hlog.tendsto_slope_zero
  have hpos : ∀ᶠ r in nhds (0 : ℝ), 0 < ∑ i, w i * x i ^ r :=
    hsum.continuousAt.tendsto.eventually (eventually_gt_nhds (by simp [hw1]))
  rw [continuousAt_iff_punctured_nhds, powerMean_zero_eq_exp w hx]
  apply (Real.continuous_exp.continuousAt.tendsto.comp hlim).congr'
  filter_upwards [self_mem_nhdsWithin, hpos.filter_mono nhdsWithin_le_nhds] with r hr hpr
  have hr0 : r ≠ 0 := Set.mem_compl_singleton_iff.mp hr
  rw [powerMean_of_ne_zero w x hr0, Real.rpow_def_of_pos hpr]
  simp only [Function.comp_apply, mul_comm]

/-- The weighted power mean is continuous in its exponent, including at zero. -/
theorem continuous_powerMean {w x : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hx : ∀ i, 0 < x i) : Continuous (powerMean w x) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    exact continuousAt_powerMean_zero hw1 hx
  · have hsum : ContinuousAt (fun t : ℝ ↦ ∑ i, w i * x i ^ t) r := by
      apply tendsto_finsetSum
      intro i _
      exact (continuousAt_const.rpow continuousAt_id (Or.inl (hx i).ne')).const_mul (w i)
    have hcont := hsum.rpow (continuousAt_inv₀ hr)
      (Or.inl (weighted_rpow_sum_pos hw (by rw [hw1]; exact zero_lt_one) hx r).ne')
    apply hcont.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hr] with t ht
    exact powerMean_of_ne_zero w x ht

end TauCeti
