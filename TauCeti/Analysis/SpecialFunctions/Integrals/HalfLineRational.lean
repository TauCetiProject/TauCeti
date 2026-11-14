/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Rational integrals on the half-line

For all real `a` and `c`,

`∫_{y > 0} y² / ((y² + a²) (y² + c²)) dy = π / (2 (|a| + |c|))`,

where for `a = c = 0` the integrand is not integrable and both sides are zero.

The integrand is the product of the two functions `y / (y² + a²)` and `y / (y² + c²)`, and
integrals of this shape arise when two Lorentzian line shapes are paired on the half-line. It
depends on `a` and `c` only through their squares, so one may take `a, c ≥ 0`. For `a ≠ c` partial
fractions then give the antiderivative `(c arctan (y / c) - a arctan (y / a)) / (c² - a²)`, and
for `a = c > 0` the antiderivative is `arctan (y / a) / (2 a) - y / (2 (y² + a²))`. The integrand
is nonnegative, so integrability comes for free from the limits of these antiderivatives at
infinity.

We also evaluate the shifted inverse-power family `∫_{t > 0} 1 / (a + t) ^ (j + 2) dt =
1 / ((j + 1) * a ^ (j + 1))` for `0 ≤ a` and `j : ℕ`, characterizing integrability on `(0, ∞)` by
`0 < a`.

## Main results

* `TauCeti.hasDerivAt_mul_arctan_div`: `a arctan (y / a)` is an antiderivative of
  `a² / (y² + a²)` for every real `a`;
* `TauCeti.tendsto_mul_arctan_div`: `a arctan (y / a)` tends to `|a| π / 2` at infinity;
* `TauCeti.integrableOn_sq_div_sq_add_sq_mul_sq_add_sq_iff`: `y² / ((y² + a²) (y² + c²))` is
  integrable on `(0, ∞)` iff `a` and `c` are not both zero;
* `TauCeti.integral_Ioi_sq_div_sq_add_sq_mul_sq_add_sq`: the value of that integral;
* `TauCeti.integrableOn_Ioi_one_div_add_pow_iff` and `TauCeti.integral_Ioi_one_div_add_pow`:
  integrability criterion and exact value of `∫_{t > 0} 1 / (a + t) ^ (j + 2) dt`.
-/

public section

open Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti

/-- `a arctan (y / a)` is an antiderivative of `a² / (y² + a²)`, for every real `a`; both sides
vanish when `a = 0`. -/
theorem hasDerivAt_mul_arctan_div (a y : ℝ) :
    HasDerivAt (fun y ↦ a * arctan (y / a)) (a ^ 2 / (y ^ 2 + a ^ 2)) y := by
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using hasDerivAt_const y (0 : ℝ)
  refine (((hasDerivAt_id y).div_const a).arctan.const_mul a).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- For every real `a`, `a arctan (y / a)` tends to `|a| π / 2` as `y → ∞`. -/
theorem tendsto_mul_arctan_div (a : ℝ) :
    Tendsto (fun y ↦ a * arctan (y / a)) atTop (𝓝 (|a| * (π / 2))) := by
  have key (y : ℝ) : a * arctan (y / a) = |a| * arctan (y / |a|) := by
    rcases abs_choice a with h | h <;> simp [h, div_neg, arctan_neg]
  simp_rw [key]
  rcases (abs_nonneg a).eq_or_lt with ha | ha
  · simp [← ha]
  exact ((tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp
    (tendsto_id.atTop_div_const ha)).const_mul |a|

/-- An antiderivative of `y² / ((y² + a²) (y² + c²))` on `[0, ∞)` vanishing at `0`, with limit
`π / (2 (a + c))` at infinity. -/
private theorem exists_antiderivative {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : 0 < a + c) :
    ∃ G : ℝ → ℝ, ContinuousWithinAt G (Ici 0) 0 ∧
      (∀ y ∈ Ioi (0 : ℝ), HasDerivAt G (y ^ 2 / ((y ^ 2 + a ^ 2) * (y ^ 2 + c ^ 2))) y) ∧
      Tendsto G atTop (𝓝 (π / (2 * (a + c)))) ∧ G 0 = 0 := by
  rcases ne_or_eq a c with hne | rfl
  · -- Partial fractions:
    -- `y² / ((y² + a²)(y² + c²)) = (c² / (y² + c²) - a² / (y² + a²)) / (c² - a²)`.
    have hd : c ^ 2 - a ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by linarith) (sub_ne_zero.mpr hne.symm)
    refine ⟨fun y ↦ (c * arctan (y / c) - a * arctan (y / a)) / (c ^ 2 - a ^ 2), ?_, fun y hy ↦ ?_,
      ?_, by simp⟩
    · exact Continuous.continuousWithinAt (by fun_prop)
    · have hy : 0 < y := hy
      refine (((hasDerivAt_mul_arctan_div c y).sub (hasDerivAt_mul_arctan_div a y)).div_const
        (c ^ 2 - a ^ 2)).congr_deriv ?_
      have h₁ : y ^ 2 + a ^ 2 ≠ 0 := by positivity
      have h₂ : y ^ 2 + c ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    · convert ((tendsto_mul_arctan_div c).sub (tendsto_mul_arctan_div a)).div_const
        (c ^ 2 - a ^ 2) using 2
      rw [abs_of_nonneg ha, abs_of_nonneg hc, eq_div_iff hd, sq_sub_sq]
      field_simp
      ring
  · -- Equal parameters: `y² / (y² + a²)² = d/dy (arctan (y / a) / (2 a) - y / (2 (y² + a²)))`.
    have ha' : 0 < a := by linarith
    refine ⟨fun y ↦ a * arctan (y / a) / (2 * a ^ 2) - y / (2 * (y ^ 2 + a ^ 2)), ?_,
      fun y _ ↦ ?_, ?_, by simp⟩
    · refine Continuous.continuousWithinAt (Continuous.sub (by fun_prop) ?_)
      exact continuous_id.div (by fun_prop) fun y ↦ by positivity
    · have h₁ : y ^ 2 + a ^ 2 ≠ 0 := by positivity
      have hq : HasDerivAt (fun y : ℝ ↦ 2 * (y ^ 2 + a ^ 2)) (2 * (2 * y)) y := by
        simpa using (((hasDerivAt_id y).pow 2).add_const (a ^ 2)).const_mul 2
      refine (((hasDerivAt_mul_arctan_div a y).div_const (2 * a ^ 2)).sub
        ((hasDerivAt_id y).div hq (by positivity))).congr_deriv ?_
      simp only [id]
      field_simp
      ring
    · have hlim : Tendsto (fun y : ℝ ↦ y / (2 * (y ^ 2 + a ^ 2))) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          tendsto_inv_atTop_zero ?_ ?_
        · filter_upwards [eventually_ge_atTop 0] with y hy
          positivity
        · filter_upwards [eventually_gt_atTop 0] with y hy
          rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hy]
          nlinarith
      convert ((tendsto_mul_arctan_div a).div_const (2 * a ^ 2)).sub hlim using 2
      rw [abs_of_nonneg ha]
      field_simp
      ring

/-- The function `y² / ((y² + a²) (y² + c²))` is integrable on `(0, ∞)` exactly when `a` and `c`
are not both zero. -/
theorem integrableOn_sq_div_sq_add_sq_mul_sq_add_sq_iff {a c : ℝ} :
    IntegrableOn (fun y : ℝ ↦ y ^ 2 / ((y ^ 2 + a ^ 2) * (y ^ 2 + c ^ 2))) (Ioi 0) ↔
      a ≠ 0 ∨ c ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra! hac
    obtain ⟨rfl, rfl⟩ := hac
    refine not_integrableOn_Ioi_rpow (-2) (h.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi)
    have hy : 0 < y := hy
    rw [rpow_neg hy.le, rpow_two]
    field_simp
    ring
  · have hac : 0 < |a| + |c| := by rcases h with h | h <;> positivity
    obtain ⟨G, hcont, hderiv, hlim, -⟩ := exists_antiderivative (abs_nonneg a) (abs_nonneg c) hac
    simp only [sq_abs] at hderiv
    exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun y _ ↦ by positivity) hlim

/-- For all real `a` and `c`,
`∫_{y > 0} y² / ((y² + a²) (y² + c²)) dy = π / (2 (|a| + |c|))`. When `a = c = 0` the integrand
is not integrable and both sides are zero. -/
theorem integral_Ioi_sq_div_sq_add_sq_mul_sq_add_sq (a c : ℝ) :
    ∫ y in Ioi 0, y ^ 2 / ((y ^ 2 + a ^ 2) * (y ^ 2 + c ^ 2)) = π / (2 * (|a| + |c|)) := by
  by_cases h : a ≠ 0 ∨ c ≠ 0
  · have hac : 0 < |a| + |c| := by rcases h with h | h <;> positivity
    obtain ⟨G, hcont, hderiv, hlim, hG⟩ := exists_antiderivative (abs_nonneg a) (abs_nonneg c) hac
    simp only [sq_abs] at hderiv
    rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv (fun y _ ↦ by positivity) hlim, hG,
      sub_zero]
  · rw [integral_undef (mt integrableOn_sq_div_sq_add_sq_mul_sq_add_sq_iff.mp h)]
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := by simpa using h
    simp

/-- The shifted inverse power `1 / (a + t) ^ (j + 2)` is integrable on `(0, ∞)` if and only if
`0 < a`: for `a ≤ 0` the pole `t = -a` lies in `[0, ∞)` and has order `j + 2 ≥ 2`. -/
theorem integrableOn_Ioi_one_div_add_pow_iff {a : ℝ} {j : ℕ} :
    IntegrableOn (fun t : ℝ ↦ 1 / (a + t) ^ (j + 2)) (Ioi 0) ↔ 0 < a := by
  refine ⟨fun h ↦ ?_, fun ha ↦ ?_⟩
  · by_contra! ha
    have hsub : Ioo (-a) (-a + 1) ⊆ Ioi 0 := fun t ht ↦ mem_Ioi.mpr (by linarith [ht.1])
    have h1 : IntegrableOn (fun t : ℝ ↦ (t - (-a)) ^ (-1 : ℝ)) (Ioo (-a) (-a + 1)) := by
      refine (h.mono_set hsub).mono'
        ((ContinuousOn.rpow_const (f := fun t : ℝ ↦ t - (-a)) (by fun_prop)
          fun t ht ↦ Or.inl (by linarith [ht.1])).aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hpos : 0 < a + t := by linarith [ht.1]
      have hle1 : a + t ≤ 1 := by linarith [ht.2]
      rw [sub_neg_eq_add, add_comm t a, rpow_neg_one, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
        one_div]
      exact inv_anti₀ (pow_pos hpos _) (pow_le_of_le_one hpos.le hle1 (Nat.succ_ne_zero _))
    have h2 : IntervalIntegrable (fun u : ℝ ↦ u ^ (-1 : ℝ)) volume 0 1 := by
      have hi : IntervalIntegrable (fun t : ℝ ↦ (t - (-a)) ^ (-1 : ℝ)) volume (-a) (-a + 1) :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mpr h1
      simpa using hi.comp_add_right (-a)
    have h3 := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp h2)
    linarith
  · refine (integrableOn_add_rpow_Ioi_of_lt (a := -(j + 2 : ℝ)) (c := 0) (m := a)
      (by linarith) (by linarith)).congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
    dsimp only
    have hpos : 0 < t + a := by linarith [mem_Ioi.mp ht]
    rw [show -(j + 2 : ℝ) = -(((j + 2 : ℕ) : ℝ)) by push_cast; ring, rpow_neg hpos.le,
      rpow_natCast, add_comm t a, one_div]

/-- For `0 ≤ a` and `j : ℕ`, `∫_{t > 0} 1 / (a + t) ^ (j + 2) dt = 1 / ((j + 1) * a ^ (j + 1))`
(at `a = 0` the integrand is not integrable and both sides vanish). -/
theorem integral_Ioi_one_div_add_pow {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    ∫ t : ℝ in Ioi 0, 1 / (a + t) ^ (j + 2) = 1 / ((j + 1 : ℝ) * a ^ (j + 1)) := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [integral_undef (mt integrableOn_Ioi_one_div_add_pow_iff.mp (lt_irrefl 0))]
    simp [zero_pow (Nat.succ_ne_zero j)]
  · let G : ℝ → ℝ := fun t ↦ -1 / ((j + 1 : ℝ) * (a + t) ^ (j + 1))
    have hcont : ContinuousWithinAt G (Ici 0) 0 := by
      refine (continuousAt_const.div ?_ (by positivity)).continuousWithinAt
      exact continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow _)
    have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt G (1 / (a + t) ^ (j + 2)) t := fun t ht ↦ by
      have hpos : 0 < a + t := by linarith [mem_Ioi.mp ht]
      have hp : HasDerivAt (fun u : ℝ ↦ (j + 1 : ℝ) * (a + u) ^ (j + 1))
          ((j + 1 : ℝ) * ((j + 1 : ℕ) * (a + t) ^ j * 1)) t :=
        (((hasDerivAt_id' t).const_add a).pow (j + 1)).const_mul (j + 1 : ℝ)
      have hd := (hp.inv (by positivity)).neg
      refine hd.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ ?_) |>.congr_deriv ?_
      · simp [G, neg_div]
      · push_cast
        field_simp [hpos.ne']
        ring
    have hlim : Tendsto G atTop (𝓝 0) := by
      have htop : Tendsto (fun t : ℝ ↦ (j + 1 : ℝ) * (a + t) ^ (j + 1)) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity)
          ((tendsto_pow_atTop (Nat.succ_ne_zero j)).comp
            (tendsto_atTop_add_const_left atTop a tendsto_id))
      simpa [G, neg_div] using (tendsto_inv_atTop_zero.comp htop).neg
    rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv (fun t ht ↦ by
      have : 0 < a + t := by linarith [mem_Ioi.mp ht]
      positivity) hlim]
    simp only [G, add_zero]
    ring

end TauCeti
