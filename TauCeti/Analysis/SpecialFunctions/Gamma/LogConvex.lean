/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Log-convexity of shifted and rescaled Gamma

Mathlib's `Real.convexOn_log_Gamma` states that `log ∘ Γ` is convex on `(0, ∞)`. This file
transports it along the affine maps `x ↦ (x + c)/m` with `c ≥ 0` and `m > 0`, which send `(0, ∞)`
into itself, and sums the results over a finite set of shifts.

## Main results

* `Real.convexOn_log_Gamma_add_div`: `x ↦ log Γ((x + c)/m)` is convex on `(0, ∞)`.
* `Real.convexOn_sum_log_Gamma_add_div`: `x ↦ ∑_{i ∈ s} log Γ((x + c i)/m)` is convex on `(0, ∞)`.

These are the log-convexity inputs of the Bohr–Mollerup proof of Gauss's multiplication formula.

Log-convexity also bounds and orders the ratios of Gamma values at shifted points.

* `Real.rpow_one_sub_le_Gamma_add_one_div_Gamma_add`,
  `Real.Gamma_add_one_div_Gamma_add_le_rpow`: Wendel's inequalities for `0 ≤ s ≤ 1`, the lower
  bound `x^{1-s} ≤ Γ(x + 1)/Γ(x + s)` for `x ≥ 0` and the upper bound
  `Γ(x + 1)/Γ(x + s) ≤ (x + s)^{1-s}` for `x + s ≥ 0`. The classical inequalities are for
  `x > 0`; the boundary cases at a pole of `Γ` are extensions under Mathlib's conventions
  `Γ(0) = 0` and `a / 0 = 0`: the lower bound includes `(x, s) = (0, 0)`, where both sides are
  `0`, and the upper bound includes `x + s = 0`, where the ratio is `0`.
* `Real.isEquivalent_Gamma_add_one_div_Gamma_add`: for every real `s`,
  `Γ(x + 1)/Γ(x + s) ∼ x^{1-s}` as `x → ∞`.
* `ConvexOn.sub_le_sub_of_le`: increments of a convex function over a fixed width `c ≥ 0`
  increase.
* `Real.strictMonoOn_Gamma_add_div_Gamma`: for `c > 0`, `x ↦ Γ(x + c)/Γ(x)` is strictly
  increasing on `(0, ∞)`.

The statements of `Real.convexOn_log_Gamma_add_div` and `Real.convexOn_sum_log_Gamma_add_div` are
adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Gamma/Multiplication.lean`.
-/

public section

open Finset Filter Asymptotics

namespace Real

/-- For `c ≥ 0` and `m > 0`, `x ↦ log Γ((x + c)/m)` is convex on `(0, ∞)`. -/
theorem convexOn_log_Gamma_add_div {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => log (Gamma ((x + c) / m))) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : (x + c) / m ∈ Set.Ioi 0 :=
    div_pos (add_pos_of_pos_of_nonneg (Set.mem_Ioi.mp hx) hc) hm
  have hy' : (y + c) / m ∈ Set.Ioi 0 :=
    div_pos (add_pos_of_pos_of_nonneg (Set.mem_Ioi.mp hy) hc) hm
  have hcombo : a * ((x + c) / m) + b * ((y + c) / m) = (a * x + b * y + c) / m := by
    linear_combination (c / m) * hab
  simpa [smul_eq_mul, hcombo] using convexOn_log_Gamma.2 hx' hy' ha hb hab

/-- For shifts `c i ≥ 0` and `m > 0`, `x ↦ ∑_{i ∈ s} log Γ((x + c i)/m)` is convex on
`(0, ∞)`. -/
theorem convexOn_sum_log_Gamma_add_div {ι : Type*} (s : Finset ι) {c : ι → ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) {m : ℝ} (hm : 0 < m) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => ∑ i ∈ s, log (Gamma ((x + c i) / m))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) (convex_Ioi 0)
  | insert i s hi ih =>
    simp_rw [sum_insert hi]
    exact (convexOn_log_Gamma_add_div (hc i (mem_insert_self i s)) hm).add
      (ih fun j hj => hc j (mem_insert_of_mem hj))

/-- Complementary powers recombine: for `0 ≤ y`, `y^a · y^{1-a} = y`. -/
private theorem rpow_mul_rpow_one_sub {y : ℝ} (hy : 0 ≤ y) (a : ℝ) : y ^ a * y ^ (1 - a) = y := by
  simp [← rpow_add' hy (by simp : a + (1 - a) ≠ 0)]

/-- The interpolation step of Wendel's inequalities: for `0 < y` and `0 ≤ a ≤ 1`,
`Γ(y + a) ≤ y^a Γ(y)`, from the log-convexity of `Γ` between `y` and `y + 1`. -/
private theorem Gamma_add_le_rpow_mul_Gamma {y a : ℝ} (hy : 0 < y) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Gamma (y + a) ≤ y ^ a * Gamma y := by
  rcases ha0.eq_or_lt with rfl | ha0
  · simp
  rcases ha1.eq_or_lt with rfl | ha1
  · rw [rpow_one, Gamma_add_one hy.ne']
  have hΓ := Gamma_pos_of_pos hy
  calc Gamma (y + a) = Gamma ((1 - a) * y + a * (y + 1)) := by congr 1; ring
    _ ≤ Gamma y ^ (1 - a) * Gamma (y + 1) ^ a :=
      Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hy (by linarith) (sub_pos.2 ha1) ha0
        (sub_add_cancel 1 a)
    _ = y ^ a * (Gamma y ^ a * Gamma y ^ (1 - a)) := by
      rw [Gamma_add_one hy.ne', mul_rpow hy.le hΓ.le]
      ring
    _ = y ^ a * Gamma y := by rw [rpow_mul_rpow_one_sub hΓ.le]

/-- Wendel's lower bound: for `x ≥ 0` and `0 ≤ s ≤ 1`, `x^{1-s} ≤ Γ(x + 1)/Γ(x + s)`. The case
`(x, s) = (0, 0)`, a pole of `Γ(x + s)`, extends the classical inequality under Mathlib's
conventions `Γ(0) = 0` and `a / 0 = 0`; there both sides are `0`. -/
theorem rpow_one_sub_le_Gamma_add_one_div_Gamma_add {x s : ℝ} (hx : 0 ≤ x) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : x ^ (1 - s) ≤ Gamma (x + 1) / Gamma (x + s) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp only [zero_add, Gamma_one]
    rcases hs1.eq_or_lt with rfl | hs1
    · simp
    rw [zero_rpow (by linarith)]
    exact div_nonneg zero_le_one (Gamma_nonneg_of_nonneg hs0)
  rw [le_div_iff₀ (Gamma_pos_of_pos (by linarith)), Gamma_add_one hx.ne']
  calc x ^ (1 - s) * Gamma (x + s) ≤ x ^ (1 - s) * (x ^ s * Gamma x) :=
        mul_le_mul_of_nonneg_left (Gamma_add_le_rpow_mul_Gamma hx hs0 hs1) (by positivity)
    _ = (x ^ s * x ^ (1 - s)) * Gamma x := by ring
    _ = x * Gamma x := by rw [rpow_mul_rpow_one_sub hx.le]

/-- Wendel's upper bound: for `0 ≤ s ≤ 1` and `x + s ≥ 0`, `Γ(x + 1)/Γ(x + s) ≤ (x + s)^{1-s}`.
The case `x + s = 0`, a pole of `Γ(x + s)`, extends the classical inequality under Mathlib's
conventions `Γ(0) = 0` and `a / 0 = 0`; there the ratio is `0`. -/
theorem Gamma_add_one_div_Gamma_add_le_rpow {x s : ℝ} (hxs : 0 ≤ x + s) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : Gamma (x + 1) / Gamma (x + s) ≤ (x + s) ^ (1 - s) := by
  rcases hxs.eq_or_lt with h | hxs
  · rw [← h, Gamma_zero, div_zero]
    exact rpow_nonneg le_rfl _
  rw [div_le_iff₀ (Gamma_pos_of_pos hxs)]
  have h := Gamma_add_le_rpow_mul_Gamma hxs (sub_nonneg.2 hs1) (by linarith : 1 - s ≤ 1)
  rwa [add_add_sub_cancel] at h

/-- For `0 ≤ s ≤ 1`, `Γ(x + 1)/Γ(x + s) ∼ x^{1-s}` as `x → ∞`, from Wendel's inequalities. -/
private theorem isEquivalent_Gamma_add_one_div_Gamma_add_of_mem_Icc {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    (fun x : ℝ => Gamma (x + 1) / Gamma (x + s)) ~[atTop] fun x => x ^ (1 - s) := by
  refine isEquivalent_of_tendsto_one ?_
  have hlim : Tendsto (fun x : ℝ => (1 + s * x⁻¹) ^ (1 - s)) atTop (nhds 1) := by
    have h := ((tendsto_inv_atTop_zero.const_mul s).const_add 1).rpow_const
      (p := 1 - s) (Or.inr (by linarith))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Pi.div_apply, one_le_div (rpow_pos_of_pos hx _)]
    exact rpow_one_sub_le_Gamma_add_one_div_Gamma_add hx.le hs0 hs1
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hxs : (1 + s * x⁻¹) * x = x + s := by field_simp
    rw [Pi.div_apply, div_le_iff₀ (rpow_pos_of_pos hx _), ← mul_rpow (by positivity) hx.le, hxs]
    exact Gamma_add_one_div_Gamma_add_le_rpow (by linarith) hs0 hs1

/-- The asymptotic relation `Γ(x + 1)/Γ(x + s) ∼ x^{1-s}` is unchanged by `s ↦ s + 1`. -/
private theorem isEquivalent_Gamma_add_one_div_Gamma_add_iff_add_one (s : ℝ) :
    ((fun x : ℝ => Gamma (x + 1) / Gamma (x + s)) ~[atTop] fun x => x ^ (1 - s)) ↔
      ((fun x : ℝ => Gamma (x + 1) / Gamma (x + (s + 1))) ~[atTop]
        fun x => x ^ (1 - (s + 1))) := by
  have hlin : (fun x : ℝ => x + s) ~[atTop] fun x => x :=
    IsEquivalent.refl.add_isLittleO (isLittleO_const_id_atTop s)
  have hΓ : (fun x : ℝ => Gamma (x + 1) / Gamma (x + (s + 1)) * (x + s)) =ᶠ[atTop]
      fun x => Gamma (x + 1) / Gamma (x + s) := by
    filter_upwards [eventually_gt_atTop (-s)] with x hx
    have hne : x + s ≠ 0 := by linarith
    calc Gamma (x + 1) / Gamma (x + (s + 1)) * (x + s)
        = Gamma (x + 1) / Gamma (x + s) / (x + s) * (x + s) := by
          rw [← add_assoc, Gamma_add_one hne, div_div, mul_comm (Gamma (x + s))]
      _ = Gamma (x + 1) / Gamma (x + s) := div_mul_cancel₀ _ hne
  have hpow : (fun x : ℝ => x ^ (1 - (s + 1)) * x) =ᶠ[atTop] fun x => x ^ (1 - s) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    calc x ^ (1 - (s + 1)) * x = x ^ (1 - s) / x * x := by
          rw [sub_add_eq_sub_sub, rpow_sub_one hx.ne']
      _ = x ^ (1 - s) := div_mul_cancel₀ _ hx.ne'
  constructor
  · intro h
    refine ((h.div hlin).congr_left ?_).congr_right ?_
    · filter_upwards [hΓ, eventually_gt_atTop (-s)] with x hx hxs
      exact ((eq_div_iff (by linarith : x + s ≠ 0)).2 hx).symm
    · filter_upwards [hpow, eventually_gt_atTop 0] with x hx hx0
      exact ((eq_div_iff hx0.ne').2 hx).symm
  · intro h
    exact ((h.mul hlin).congr_left hΓ).congr_right hpow

/-- For every real `s`, `Γ(x + 1)/Γ(x + s) ∼ x^{1-s}` as `x → ∞`. -/
theorem isEquivalent_Gamma_add_one_div_Gamma_add (s : ℝ) :
    (fun x : ℝ => Gamma (x + 1) / Gamma (x + s)) ~[atTop] fun x => x ^ (1 - s) := by
  have key : ∀ n : ℤ, (fun x : ℝ => Gamma (x + 1) / Gamma (x + (Int.fract s + n))) ~[atTop]
      fun x => x ^ (1 - (Int.fract s + n)) := by
    intro n
    induction n using Int.induction_on with
    | zero =>
      simpa using isEquivalent_Gamma_add_one_div_Gamma_add_of_mem_Icc (Int.fract_nonneg s)
        (Int.fract_lt_one s).le
    | succ n ih =>
      push_cast
      rw [← add_assoc]
      exact (isEquivalent_Gamma_add_one_div_Gamma_add_iff_add_one _).1 ih
    | pred n ih =>
      refine (isEquivalent_Gamma_add_one_div_Gamma_add_iff_add_one _).2 ?_
      push_cast at ih ⊢
      have hn : Int.fract s + (-(n : ℝ) - 1) + 1 = Int.fract s + -(n : ℝ) := by ring
      rwa [hn]
  simpa [Int.fract_add_floor] using key ⌊s⌋

/-- For a convex function on `D ⊆ ℝ`, increments over a fixed width `c ≥ 0` increase: if `s ≤ t`
with `s ∈ D` and `t + c ∈ D`, then `f (s + c) - f s ≤ f (t + c) - f t`. -/
theorem _root_.ConvexOn.sub_le_sub_of_le {D : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ D f)
    {s t c : ℝ} (hs : s ∈ D) (htc : t + c ∈ D) (hc : 0 ≤ c) (hst : s ≤ t) :
    f (s + c) - f s ≤ f (t + c) - f t := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  have hsc : s + c ∈ D := hf.1.ordConnected.out hs htc ⟨by linarith, by linarith⟩
  have ht : t ∈ D := hf.1.ordConnected.out hs htc ⟨hst, by linarith⟩
  -- Both increments are compared with the common secant from `s` to `t + c`.
  have key : slope f s (s + c) ≤ slope f t (t + c) := calc
    slope f s (s + c) ≤ slope f s (t + c) := by
      rw [slope_def_field, slope_def_field]
      exact hf.secant_mono hs hsc htc (by linarith) (by linarith) (by linarith)
    _ = slope f (t + c) s := slope_comm f s (t + c)
    _ ≤ slope f (t + c) t := by
      rw [slope_def_field, slope_def_field]
      exact hf.secant_mono htc hs ht (by linarith) (by linarith) hst
    _ = slope f t (t + c) := slope_comm f (t + c) t
  simp only [slope_def_field, add_sub_cancel_left] at key
  exact (div_le_div_iff_of_pos_right hc).1 key

/-- For `c > 0`, `x ↦ Γ(x + c)/Γ(x)` is strictly increasing on `(0, ∞)`. -/
theorem strictMonoOn_Gamma_add_div_Gamma {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun x : ℝ => Gamma (x + c) / Gamma x) (Set.Ioi 0) := by
  have hmono : ∀ {s t : ℝ}, 0 < s → s ≤ t →
      log (Gamma (s + c)) - log (Gamma s) ≤ log (Gamma (t + c)) - log (Gamma t) :=
    fun hs hst => convexOn_log_Gamma.sub_le_sub_of_le (Set.mem_Ioi.mpr hs)
      (Set.mem_Ioi.mpr (by linarith [hs.trans_le hst])) hc.le hst
  -- The ratio is positive and its logarithm is the increment of `log ∘ Γ` over width `c`.
  have hratio : ∀ {x : ℝ}, 0 < x → 0 < Gamma (x + c) / Gamma x ∧
      log (Gamma (x + c) / Gamma x) = log (Gamma (x + c)) - log (Gamma x) := by
    intro x hx
    have hΓ := Gamma_pos_of_pos hx
    have hΓc := Gamma_pos_of_pos (add_pos hx hc)
    exact ⟨div_pos hΓc hΓ, log_div hΓc.ne' hΓ.ne'⟩
  have hlogΓ : ∀ {y : ℝ}, 0 < y → log (Gamma (y + 1)) = log y + log (Gamma y) := fun hy => by
    rw [Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne']
  have hshift : ∀ {x : ℝ}, 0 < x → log (Gamma (x + 1 + c)) - log (Gamma (x + 1)) =
      log (Gamma (x + c)) - log (Gamma x) + (log (x + c) - log x) := by
    intro x hx
    rw [add_right_comm, hlogΓ (add_pos hx hc), hlogΓ hx]
    ring
  intro s hsD t htD hst
  have hs : 0 < s := Set.mem_Ioi.mp hsD
  have ht : 0 < t := Set.mem_Ioi.mp htD
  have hD : log (t + c) - log t < log (s + c) - log s := by
    rw [← log_div (by linarith) ht.ne', ← log_div (by linarith) hs.ne']
    refine log_lt_log (div_pos (by linarith) ht) ?_
    rw [div_lt_div_iff₀ ht hs]
    nlinarith
  refine (log_lt_log_iff (hratio hs).1 (hratio ht).1).1 ?_
  rw [(hratio hs).2, (hratio ht).2]
  refine (hmono hs hst.le).lt_of_ne fun heq => ?_
  have h := hmono (by linarith : 0 < s + 1) (by linarith : s + 1 ≤ t + 1)
  rw [hshift hs, hshift ht, heq] at h
  linarith

end Real
