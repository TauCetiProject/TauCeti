/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.PSeries
public import TauCeti.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

/-!
# `p`-series and weighted summability from sublevel counts

`∑' m : ℕ, m ^ (-t) ≤ 2` for every real `t ≥ 2`. Mathlib supplies the exact value at the endpoint,
`ζ (2) = π ^ 2 / 6`, and summability throughout `t > 1`, but no inequality valid across a range of
exponents; that is what this file adds.

The bound is deliberately lossy. The supremum over `t ≥ 2` is `ζ (2) = 1.6449…`, so `2` gives away
about 18%. A round constant is the useful thing to expose: consumers carry it through chains of
inequalities and none of them wants `π` in the goal.

Nothing here is specific to any application, and the file contains no number theory. The `m = 0`
term is `0`, by the junk value of `0 ^ (-t)`.

The file also records the value `π ^ 2 / 3` of `∑_{n ∈ ℤ} n⁻²`, and the summability over `ℤ` of
the shifted weights `(1 + |n|) ^ r` for `r < -1`, the form in which the `p`-series enters
weighted sequence spaces.

A weighted family of radii with finite sublevel sets also has summable reciprocal powers
when its weighted counts grow at a smaller exponent. The proof partitions the radii into
dyadic annuli and compares their contributions with a geometric series.

## Main results

* `TauCeti.tsum_nat_rpow_neg_le_two` — `∑' m : ℕ, m ^ (-t) ≤ 2` for `2 ≤ t`.
* `TauCeti.hasSum_int_inv_sq` — `∑_{n ∈ ℤ} n⁻² = π ^ 2 / 3`.
* `TauCeti.summable_one_add_abs_int_rpow` — `∑ n : ℤ, (1 + |n|) ^ r` converges for `r < -1`.
* `TauCeti.summable_mul_rpow_of_count_growth` — weighted reciprocal powers are summable
  when sublevel counts grow at a smaller exponent.
-/

public section

namespace TauCeti

/-- **The `p`-series over `ℕ` is at most `2` beyond exponent two.** For `2 ≤ t`,
`∑' m : ℕ, m ^ (-t) ≤ 2`, the case `t = 2` being `ζ(2) = π ^ 2 / 6 < 2`.  The `m = 0` term is
`0`, by the junk value of `0 ^ (-t)`. -/
theorem tsum_nat_rpow_neg_le_two {t : ℝ} (ht : 2 ≤ t) : ∑' m : ℕ, (m : ℝ) ^ (-t) ≤ 2 := by
  have hsum : ∀ u : ℝ, 1 < u → Summable fun m : ℕ ↦ (m : ℝ) ^ (-u) := fun u hu ↦
    Real.summable_nat_rpow.mpr (by linarith)
  have hfun : (fun m : ℕ ↦ (m : ℝ) ^ (-(2 : ℝ))) = fun m : ℕ ↦ (1 : ℝ) / (m : ℝ) ^ 2 := by
    funext m
    rw [Real.rpow_neg (Nat.cast_nonneg m), Real.rpow_two, one_div]
  have hzeta : ∑' m : ℕ, (m : ℝ) ^ (-(2 : ℝ)) = Real.pi ^ 2 / 6 := by
    rw [hfun]
    exact hasSum_zeta_two.tsum_eq
  refine le_trans (Summable.tsum_le_tsum (fun m ↦ ?_) (hsum t (by linarith))
    (hsum 2 one_lt_two)) ?_
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by norm_num)]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
  · rw [hzeta]
    nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- **`2 ζ(2)` as a sum over `ℤ`**: `∑_{n ∈ ℤ} n⁻² = π ^ 2 / 3`, the `n = 0` term being `0`
by the junk value of `0⁻¹`. -/
theorem hasSum_int_inv_sq : HasSum (fun n : ℤ ↦ ((n : ℝ) ^ 2)⁻¹) (Real.pi ^ 2 / 3) := by
  have h : HasSum (fun n : ℕ ↦ (((n : ℤ) : ℝ) ^ 2)⁻¹) (Real.pi ^ 2 / 6) := by
    simpa [one_div] using hasSum_zeta_two
  have h' : HasSum (fun n : ℕ ↦ (((-n : ℤ) : ℝ) ^ 2)⁻¹) (Real.pi ^ 2 / 6) := by
    simpa only [Int.cast_neg, neg_sq] using h
  convert HasSum.of_nat_of_neg (f := fun n : ℤ ↦ ((n : ℝ) ^ 2)⁻¹) h h' using 1
  simp only [Int.cast_zero, zero_pow two_ne_zero, inv_zero, sub_zero]
  ring

/-- The weights `(1 + |n|) ^ r` are summable over `ℤ` for `r < -1`. -/
theorem summable_one_add_abs_int_rpow {r : ℝ} (hr : r < -1) :
    Summable fun n : ℤ ↦ (1 + |(n : ℝ)|) ^ r := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow (b := -r) (by linarith))
    ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  rw [neg_neg, Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (abs_pos.2 (Int.cast_ne_zero.2 hn))
    (le_add_of_nonneg_left zero_le_one) (by linarith)

open Filter Topology


private theorem dyadic_rpow_scale (B p : ℝ) (n : ℕ) :
    ((2 : ℝ) ^ (n + 1)) ^ B * ((2 : ℝ) ^ n) ^ (-p) =
      2 ^ B * (2 ^ (B - p)) ^ n := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

/-- Weighted reciprocal powers are summable when the weighted sublevel counts grow at a
strictly smaller power. The radii are at least one and every sublevel set is finite. -/
theorem summable_mul_rpow_of_count_growth {ι : Type*} (r w : ι → ℝ)
    (hr : ∀ i, 1 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hfinite : ∀ R : ℝ, {i | r i ≤ R}.Finite)
    {C B p : ℝ} (hp : 0 ≤ p) (hBp : B < p)
    (hcount : ∀ᶠ R : ℝ in atTop,
      (∑' i : {i | r i ≤ R}, w i) ≤ C * R ^ B) :
    Summable (fun i ↦ w i * (r i) ^ (-p)) := by
  classical
  -- Partition the radii into dyadic annuli, each with a finite index set.
  let bin (i : ι) : ℕ := ⌊Real.logb 2 (r i)⌋₊
  have hb (i : ι) : (2 : ℝ) ^ bin i ≤ r i ∧ r i < (2 : ℝ) ^ (bin i + 1) :=
    Real.pow_nat_floor_logb_bounds (by norm_num : (1 : ℝ) < 2) (hr i)
  have hbinfinite (n : ℕ) : {i | bin i = n}.Finite :=
    (hfinite ((2 : ℝ) ^ (n + 1))).subset (fun i hi ↦ by
      have hi' : bin i = n := hi
      rw [Set.mem_ofPred_eq]
      simpa only [hi'] using (hb i).2.le)
  let (n : ℕ) : Fintype {i | bin i = n} := (hbinfinite n).fintype
  let (R : ℝ) : Fintype {i | r i ≤ R} := (hfinite R).fintype
  rw [summable_partition (fun i ↦ mul_nonneg (hw i) (Real.rpow_nonneg (by linarith [hr i]) _))
    (s := fun n ↦ {i | bin i = n}) (fun i ↦ ⟨bin i, rfl, fun n hn ↦ hn.symm⟩)]
  refine ⟨fun n ↦ Summable.of_finite, ?_⟩
  -- The annular upper bounds form a convergent geometric series because B < p.
  let q : ℝ := 2 ^ (B - p)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hBp)
  have hgeo := (summable_geometric_of_lt_one hq0 hq1).mul_left (C * 2 ^ B)
  apply hgeo.of_norm_bounded_eventually_nat
  have ht : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually hcount] with n hn
  have hsum0 : 0 ≤ ∑' i : {i | bin i = n}, w i * (r i) ^ (-p) :=
    tsum_nonneg (fun i ↦ mul_nonneg (hw i) (Real.rpow_nonneg (by linarith [hr i]) _))
  rw [Real.norm_eq_abs, abs_of_nonneg hsum0]
  -- Compare the weight of one annulus with the enclosing sublevel count.
  have hweight : (∑' i : {i | bin i = n}, w i) ≤
      ∑' i : {i | r i ≤ (2 : ℝ) ^ (n + 1)}, w i := by
    let e : {i | bin i = n} → {i | r i ≤ (2 : ℝ) ^ (n + 1)} :=
      fun i ↦ ⟨i, by
        have hi : bin i = n := i.property
        rw [Set.mem_ofPred_eq]
        simpa only [hi] using (hb i).2.le⟩
    apply Summable.tsum_le_tsum_of_inj e
      (fun i j h ↦ Subtype.ext (congrArg
        (fun t : {i | r i ≤ (2 : ℝ) ^ (n + 1)} ↦ (t : ι)) h))
      (fun i _ ↦ hw i) (fun i ↦ le_rfl) Summable.of_finite Summable.of_finite
  have hscale : ((2 : ℝ) ^ (n + 1)) ^ B * ((2 : ℝ) ^ n) ^ (-p) =
      2 ^ B * q ^ n := by simpa only [q] using dyadic_rpow_scale B p n
  calc
    _ ≤ ∑' i : {i | bin i = n}, w i * ((2 : ℝ) ^ n) ^ (-p) := by
      apply Summable.tsum_le_tsum _ Summable.of_finite Summable.of_finite
      intro i
      apply mul_le_mul_of_nonneg_left _ (hw i)
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hp)
      have hi : bin i = n := i.property
      simpa only [hi] using (hb i).1
    _ = (∑' i : {i | bin i = n}, w i) * ((2 : ℝ) ^ n) ^ (-p) := tsum_mul_right
    _ ≤ (C * ((2 : ℝ) ^ (n + 1)) ^ B) * ((2 : ℝ) ^ n) ^ (-p) :=
      mul_le_mul_of_nonneg_right (hweight.trans hn) (by positivity)
    _ = (C * 2 ^ B) * q ^ n := by rw [mul_assoc, hscale]; ring

end TauCeti

