/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Bounds.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Bounded functions which double under a shift

A real function `g` which is bounded and at least doubles under the shift by `K` in both
directions, `2 g(s) ≤ g(s + K)` and `g(s - K) ≤ 2 g(s)`, vanishes identically: a positive value
would grow geometrically to the right, a negative one to the left
(`TauCeti.eq_zero_of_two_mul_le_add_of_sub_le_two_mul`).

The doubling typically comes from an integral control. If a monotone bounded function `A` is
controlled by a density `σ`, `|A(s) - a₀| ≤ K σ(s)`, whose integral over `[a, a + K]` is the
increment `A(a + K) - A(a)`, then integrating the control over `[s, s + K]` and `[s - K, s]`
shows that `A - a₀` doubles under the shift by `K`, so `A` is the constant `a₀`
(`TauCeti.eq_of_monotone_of_abs_sub_le_mul`). This is the shape of the action–energy argument
for Floer trajectories near a nondegenerate orbit, with `A` the action of the loops and `σ` the
energy of the slices. The averaging step is `TauCeti.le_setIntegral_Icc_add_of_le_mul` from
`TauCeti.MeasureTheory.Integral.Bochner.Set`: a pointwise bound `m ≤ K σ` on `[a, a + K]` gives
`m ≤ ∫_a^{a+K} σ`.
-/

public section

open Set MeasureTheory

namespace TauCeti

/-- A real function which is bounded and at least doubles under the shift by `K` in both
directions, `2 g(s) ≤ g(s + K)` and `g(s - K) ≤ 2 g(s)`, vanishes identically: a positive value
would grow geometrically to the right, a negative one to the left. -/
theorem eq_zero_of_two_mul_le_add_of_sub_le_two_mul {g : ℝ → ℝ} {K : ℝ}
    (hup : BddAbove (range g)) (hlow : BddBelow (range g)) (hfw : ∀ s, 2 * g s ≤ g (s + K))
    (hbw : ∀ s, g (s - K) ≤ 2 * g s) (s : ℝ) : g s = 0 := by
  obtain ⟨B₁, hB₁⟩ := hup
  obtain ⟨B₀, hB₀⟩ := hlow
  have hfw' (n : ℕ) : 2 ^ n * g s ≤ g (s + n * K) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc 2 ^ (n + 1) * g s = 2 * (2 ^ n * g s) := by ring
        _ ≤ 2 * g (s + n * K) := by linarith
        _ ≤ g (s + n * K + K) := hfw _
        _ = g (s + (n + 1 : ℕ) * K) := by congr 1; push_cast; ring
  have hbw' (n : ℕ) : g (s - n * K) ≤ 2 ^ n * g s := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc g (s - (n + 1 : ℕ) * K) = g (s - n * K - K) := by congr 1; push_cast; ring
        _ ≤ 2 * g (s - n * K) := hbw _
        _ ≤ 2 * (2 ^ n * g s) := by linarith
        _ = 2 ^ (n + 1) * g s := by ring
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B₀ / g s) one_lt_two
    rw [div_lt_iff_of_neg hneg] at hn
    linarith [(hB₀ (mem_range_self (s - n * K))).trans (hbw' n)]
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B₁ / g s) one_lt_two
    rw [div_lt_iff₀ hpos] at hn
    linarith [(hfw' n).trans (hB₁ (mem_range_self (s + n * K)))]

/-- A monotone bounded function `A` whose distance to `a₀` is controlled by a density `σ`,
`|A(s) - a₀| ≤ K σ(s)` with `K > 0`, whose integral over `[a, a + K]` is the increment
`A(a + K) - A(a)`, is the constant `a₀`. Integrating the control over `[s, s + K]` and `[s - K, s]`
shows that `A - a₀` at least doubles under the shift by `K` in both directions
(`TauCeti.eq_zero_of_two_mul_le_add_of_sub_le_two_mul`). -/
theorem eq_of_monotone_of_abs_sub_le_mul {A σ : ℝ → ℝ} {a₀ K : ℝ} (hK : 0 < K)
    (hmono : Monotone A) (hup : BddAbove (range A)) (hlow : BddBelow (range A))
    (hσ : ∀ s, |A s - a₀| ≤ K * σ s)
    (hint : ∀ a, IntegrableOn σ (Icc a (a + K)) ∧ ∫ r in Icc a (a + K), σ r = A (a + K) - A a)
    (s : ℝ) : A s = a₀ := by
  -- The increment over `[a, a + K]` is at least `m` as soon as `m ≤ K σ` there.
  have hstep (a m : ℝ) (hm : ∀ r ∈ Icc a (a + K), m ≤ K * σ r) : m ≤ A (a + K) - A a :=
    (le_setIntegral_Icc_add_of_le_mul hK (hint a).1 hm).trans_eq (hint a).2
  refine sub_eq_zero.1 (eq_zero_of_two_mul_le_add_of_sub_le_two_mul (g := fun s ↦ A s - a₀)
    (K := K) ?_ ?_ (fun s ↦ ?_) (fun s ↦ ?_) s)
  · obtain ⟨B, hB⟩ := hup
    exact ⟨B - a₀, forall_mem_range.2 fun s ↦ sub_le_sub_right (hB (mem_range_self s)) _⟩
  · obtain ⟨B, hB⟩ := hlow
    exact ⟨B - a₀, forall_mem_range.2 fun s ↦ sub_le_sub_right (hB (mem_range_self s)) _⟩
  · have h := hstep s (A s - a₀) fun r hr ↦
      (sub_le_sub_right (hmono hr.1) _).trans ((le_abs_self _).trans (hσ r))
    linarith
  · have h := hstep (s - K) (-(A s - a₀)) fun r hr ↦
      (neg_le_neg (sub_le_sub_right (hmono (by linarith [hr.2])) _)).trans
        ((neg_le_abs _).trans (hσ r))
    rw [sub_add_cancel] at h
    linarith

end TauCeti
