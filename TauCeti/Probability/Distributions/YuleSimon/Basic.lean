/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.Distributions.Beta
public import TauCeti.Probability.Cdf
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The Yule–Simon distribution

For a shape `ρ > 0`, the Yule–Simon law is the probability measure on `ℕ` with mass
`ρ B(k, ρ + 1)` at every positive integer `k` and no mass at zero, where `B` is Euler's beta
function `ProbabilityTheory.beta`. Every nonpositive shape gives the zero measure.

The masses telescope: since `B(k + 1, ρ + 1) = k / (k + ρ + 1) B(k, ρ + 1)`, the mass at `k + 1` is
the difference of consecutive values of `k B(k, ρ + 1)`, and these values tend to zero by Euler's
limit formula for `Γ`. This gives both the normalization and the closed upper tail
`P(X > k) = k B(k, ρ + 1)` for `k ≥ 1`.

## Main results

* `isProbabilityMeasure_yuleSimonMeasure` proves normalization;
* `yuleSimonMeasure_singleton` and `yuleSimonMeasure_real_singleton` compute the native masses,
  and `yuleSimonMeasure_singleton_ne_zero_iff` identifies the support as the positive integers;
* `yuleSimonMeasure_real_Ioi` gives the upper tail `P(X > k) = k B(k, ρ + 1)` for `k ≥ 1`, and
  `yuleSimonMeasure_real_Iic` the corresponding cumulative mass;
* `cdf_map_cast_yuleSimonMeasure` computes the cdf of the real cast law;
* `measurable_yuleSimonMeasure` proves parameter measurability of the totalized family.

## References

* H. A. Simon, *On a class of skew distribution functions*, Biometrika 42 (1955), 425–440.
* N. L. Johnson, A. W. Kemp, and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Section 6.10.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Nat Topology

namespace TauCeti

namespace Probability

variable {ρ : ℝ}

/-- The real Yule–Simon mass `ρ B(k, ρ + 1)` at `k`.

At `k = 0` it vanishes because `Γ 0 = 0` in Mathlib's convention; see
`yuleSimonWeightReal_zero`. -/
def yuleSimonWeightReal (ρ : ℝ) (k : ℕ) : ℝ :=
  ρ * beta k (ρ + 1)

/-- The `ℝ≥0∞`-valued Yule–Simon mass at `k`. -/
def yuleSimonWeight (ρ : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (yuleSimonWeightReal ρ k)

/-- The defining formula of the real Yule–Simon mass. -/
theorem yuleSimonWeightReal_def (ρ : ℝ) (k : ℕ) :
    yuleSimonWeightReal ρ k = ρ * beta k (ρ + 1) := (rfl)

/-- The `ℝ≥0∞`-valued Yule–Simon mass is the `ENNReal.ofReal` of the real mass. -/
theorem yuleSimonWeight_def (ρ : ℝ) (k : ℕ) :
    yuleSimonWeight ρ k = ENNReal.ofReal (yuleSimonWeightReal ρ k) := (rfl)

/-- Every Yule–Simon mass is finite. -/
@[simp]
theorem yuleSimonWeight_ne_top (ρ : ℝ) (k : ℕ) : yuleSimonWeight ρ k ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- The Yule–Simon law with shape `ρ`.

For `0 < ρ` this is the weighted Dirac sum with masses `ρ B(k, ρ + 1)`, which are supported on
the positive integers; every other shape gives the zero measure. -/
def yuleSimonMeasure (ρ : ℝ) : Measure ℕ :=
  if 0 < ρ then Measure.sum (fun k => yuleSimonWeight ρ k • Measure.dirac k) else 0

/-- For positive shape, the measure is its weighted Dirac sum. -/
theorem yuleSimonMeasure_eq_sum_dirac (hρ : 0 < ρ) :
    yuleSimonMeasure ρ = Measure.sum (fun k => yuleSimonWeight ρ k • Measure.dirac k) := by
  simp [yuleSimonMeasure, hρ]

/-- For nonpositive shape, the measure is explicitly totalized to zero. -/
@[simp]
theorem yuleSimonMeasure_of_nonpos (hρ : ρ ≤ 0) : yuleSimonMeasure ρ = 0 := by
  simp [yuleSimonMeasure, hρ.not_gt]

/-! ### Masses -/

/-- The Yule–Simon law puts no mass at zero. -/
@[simp]
theorem yuleSimonWeightReal_zero (ρ : ℝ) : yuleSimonWeightReal ρ 0 = 0 := by
  simp [yuleSimonWeightReal, beta]

/-- The mass at one is `ρ / (ρ + 1)`. -/
theorem yuleSimonWeightReal_one (hρ : 0 < ρ) : yuleSimonWeightReal ρ 1 = ρ / (ρ + 1) := by
  rw [yuleSimonWeightReal, Nat.cast_one, beta_comm, beta_one_right (by positivity)]
  ring

/-- The masses satisfy the recursion `p (k + 1) = k / (k + ρ + 1) * p k` at positive `k`. -/
theorem yuleSimonWeightReal_add_one (hρ : 0 < ρ) {k : ℕ} (hk : k ≠ 0) :
    yuleSimonWeightReal ρ (k + 1) = k / (k + ρ + 1) * yuleSimonWeightReal ρ k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [yuleSimonWeightReal, yuleSimonWeightReal, Nat.cast_succ,
    beta_add_one_left hk'.ne' (by positivity), ← add_assoc]
  ring

/-- For positive shape, the real mass is positive exactly at the positive integers. -/
theorem yuleSimonWeightReal_pos_iff (hρ : 0 < ρ) (k : ℕ) :
    0 < yuleSimonWeightReal ρ k ↔ k ≠ 0 := by
  refine ⟨fun h hk => by simp [hk] at h, fun hk => ?_⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  exact mul_pos hρ (beta_pos hk' (by positivity))

/-- For nonnegative shape, every real mass is nonnegative. -/
theorem yuleSimonWeightReal_nonneg (hρ : 0 ≤ ρ) (k : ℕ) : 0 ≤ yuleSimonWeightReal ρ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    exact mul_nonneg hρ (beta_pos hk' (by positivity)).le

/-- The real-valued mass agrees with the `toReal` of the nonnegative mass. -/
theorem yuleSimonWeight_toReal (hρ : 0 ≤ ρ) (k : ℕ) :
    (yuleSimonWeight ρ k).toReal = yuleSimonWeightReal ρ k := by
  rw [yuleSimonWeight, ENNReal.toReal_ofReal (yuleSimonWeightReal_nonneg hρ k)]

/-! ### Telescoping and normalization -/

/-- The mass at `k + 1` is the decrement of `k B(k, ρ + 1)`, for positive `k`. -/
private theorem sub_mul_beta_add_one_eq_yuleSimonWeightReal (hρ : 0 < ρ) {k : ℕ} (hk : k ≠ 0) :
    k * beta k (ρ + 1) - ((k + 1 : ℕ) : ℝ) * beta (k + 1 : ℕ) (ρ + 1) =
      yuleSimonWeightReal ρ (k + 1) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [yuleSimonWeightReal_add_one hρ hk, yuleSimonWeightReal, Nat.cast_succ,
    beta_add_one_left hk'.ne' (by positivity)]
  field_simp
  ring

/-- The partial sums of the masses through a positive `n` are `1 - n B(n, ρ + 1)`. -/
private theorem sum_range_yuleSimonWeightReal (hρ : 0 < ρ) {n : ℕ} (hn : n ≠ 0) :
    ∑ j ∈ Finset.range (n + 1), yuleSimonWeightReal ρ j = 1 - n * beta n (ρ + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  induction m with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_one, yuleSimonWeightReal_zero,
      yuleSimonWeightReal_one hρ, Nat.cast_one, one_mul, beta_comm,
      beta_one_right (by positivity)]
    field_simp
    ring
  | succ m ih =>
    rw [Finset.sum_range_succ, ih m.succ_ne_zero,
      ← sub_mul_beta_add_one_eq_yuleSimonWeightReal hρ m.succ_ne_zero]
    ring

/-- For positive shape, the real masses sum to one. -/
theorem hasSum_yuleSimonWeightReal (hρ : 0 < ρ) : HasSum (yuleSimonWeightReal ρ) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (yuleSimonWeightReal_nonneg hρ.le),
    ← tendsto_add_atTop_iff_nat 1]
  have hlim := (tendsto_natCast_mul_beta_atTop (by linarith : 1 < ρ + 1)).const_sub 1
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (sum_range_yuleSimonWeightReal hρ hn).symm

/-- The Yule–Simon measure is a probability measure for positive shape. -/
theorem isProbabilityMeasure_yuleSimonMeasure (hρ : 0 < ρ) :
    IsProbabilityMeasure (yuleSimonMeasure ρ) := by
  rw [yuleSimonMeasure_eq_sum_dirac hρ]
  exact (hasSum_yuleSimonWeightReal hρ).isProbabilityMeasure_sum_dirac
    (yuleSimonWeightReal_nonneg hρ.le)

/-- The singleton mass of the Yule–Simon law for positive shape. -/
@[simp]
theorem yuleSimonMeasure_singleton (hρ : 0 < ρ) (k : ℕ) :
    yuleSimonMeasure ρ {k} = yuleSimonWeight ρ k := by
  rw [yuleSimonMeasure_eq_sum_dirac hρ]
  exact Measure.sum_smul_dirac_singleton

/-- The real singleton mass of the Yule–Simon law for positive shape. -/
theorem yuleSimonMeasure_real_singleton (hρ : 0 < ρ) (k : ℕ) :
    (yuleSimonMeasure ρ).real {k} = yuleSimonWeightReal ρ k := by
  rw [measureReal_def, yuleSimonMeasure_singleton hρ, yuleSimonWeight_toReal hρ.le]

/-! ### Support -/

/-- Every Yule–Simon measure, including the totalized zero measure, vanishes at zero. -/
@[simp]
theorem yuleSimonMeasure_singleton_zero (ρ : ℝ) : yuleSimonMeasure ρ {0} = 0 := by
  rcases lt_or_ge 0 ρ with hρ | hρ
  · simp [yuleSimonMeasure_singleton hρ, yuleSimonWeight]
  · simp [hρ]

/-- For positive shape, the singleton mass is nonzero exactly at the positive integers. -/
theorem yuleSimonMeasure_singleton_ne_zero_iff (hρ : 0 < ρ) (k : ℕ) :
    yuleSimonMeasure ρ {k} ≠ 0 ↔ k ≠ 0 := by
  rw [yuleSimonMeasure_singleton hρ, yuleSimonWeight, ENNReal.ofReal_ne_zero_iff,
    yuleSimonWeightReal_pos_iff hρ]

/-- A Yule–Simon variable is almost surely positive. -/
theorem ae_pos_yuleSimonMeasure (ρ : ℝ) : ∀ᵐ k ∂yuleSimonMeasure ρ, 0 < k := by
  rw [ae_iff]
  simp

/-! ### Cumulative masses and tails -/

/-- The cumulative mass through a positive integer `k` is `1 - k B(k, ρ + 1)`. -/
theorem yuleSimonMeasure_real_Iic (hρ : 0 < ρ) {k : ℕ} (hk : k ≠ 0) :
    (yuleSimonMeasure ρ).real (Iic k) = 1 - k * beta k (ρ + 1) := by
  have := isProbabilityMeasure_yuleSimonMeasure hρ
  have hIic : (Iic k : Set ℕ) = ↑(Finset.range (k + 1)) := by
    ext j
    simp
  rw [← sum_range_yuleSimonWeightReal hρ hk, hIic, ← sum_measureReal_singleton]
  exact Finset.sum_congr rfl fun j _ => yuleSimonMeasure_real_singleton hρ j

/-- The upper tail beyond a positive integer `k` is `P(X > k) = k B(k, ρ + 1)`. -/
theorem yuleSimonMeasure_real_Ioi (hρ : 0 < ρ) {k : ℕ} (hk : k ≠ 0) :
    (yuleSimonMeasure ρ).real (Ioi k) = k * beta k (ρ + 1) := by
  have := isProbabilityMeasure_yuleSimonMeasure hρ
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, yuleSimonMeasure_real_Iic hρ hk]
  ring

/-- A Yule–Simon variable exceeds zero with probability one. -/
theorem yuleSimonMeasure_real_Ioi_zero (hρ : 0 < ρ) : (yuleSimonMeasure ρ).real (Ioi 0) = 1 := by
  have := isProbabilityMeasure_yuleSimonMeasure hρ
  have hIic : (Iic 0 : Set ℕ) = {0} := Iic_bot
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, hIic, measureReal_def,
    yuleSimonMeasure_singleton_zero]
  simp

/-- The cdf of the real cast of a Yule–Simon law at a point `x ≥ 1` is
`1 - ⌊x⌋₊ B(⌊x⌋₊, ρ + 1)`. -/
theorem cdf_map_cast_yuleSimonMeasure (hρ : 0 < ρ) {x : ℝ} (hx : 1 ≤ x) :
    cdf ((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)) x =
      1 - ⌊x⌋₊ * beta ⌊x⌋₊ (ρ + 1) := by
  have := isProbabilityMeasure_yuleSimonMeasure hρ
  rw [Measure.cdf_map_natCast _ (zero_le_one.trans hx),
    yuleSimonMeasure_real_Iic hρ (Nat.one_le_floor_iff x |>.mpr hx |> Nat.one_le_iff_ne_zero.mp)]

/-- Below one, the cdf of the real cast of a Yule–Simon law vanishes. -/
theorem cdf_map_cast_yuleSimonMeasure_of_lt_one (hρ : 0 < ρ) {x : ℝ} (hx : x < 1) :
    cdf ((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  have := isProbabilityMeasure_yuleSimonMeasure hρ
  rcases lt_or_ge x 0 with hx0 | hx0
  · exact Measure.cdf_map_natCast_of_neg _ hx0
  · have hIic : (Iic 0 : Set ℕ) = {0} := Iic_bot
    rw [Measure.cdf_map_natCast _ hx0, Nat.floor_eq_zero.mpr hx, hIic, measureReal_def,
      yuleSimonMeasure_singleton_zero, ENNReal.toReal_zero]

/-! ### Parameter measurability -/

/-- The Yule–Simon family is measurable in its shape, including the totalized zero measure for
nonpositive shape. -/
@[fun_prop]
theorem measurable_yuleSimonMeasure : Measurable yuleSimonMeasure := by
  have hweight (k : ℕ) : Measurable fun ρ : ℝ => yuleSimonWeight ρ k := by
    unfold yuleSimonWeight yuleSimonWeightReal beta
    fun_prop
  unfold yuleSimonMeasure
  exact Measurable.ite measurableSet_Ioi (TauCeti.MeasureTheory.measurable_sum_smul_dirac hweight)
    measurable_const

end Probability

end TauCeti
