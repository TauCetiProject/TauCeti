/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Bounds.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Bounded functions which double under a shift

A real function `g` which is bounded and at least doubles under the shift by `K` in both
directions, `2 g(s) ≤ g(s + K)` and `g(s - K) ≤ 2 g(s)`, vanishes identically: a positive value
would grow geometrically to the right, a negative one to the left
(`TauCeti.eq_zero_of_two_mul_le_add_of_sub_le_two_mul`).

The doubling typically comes from an integral control. If a monotone bounded function `A` is
controlled by a density `σ`, `|A(s) - a₀| ≤ K σ(s)`, whose integral over `[a, a + K]` is the
increment `A(a + K) - A(a)`, then integrating the control over a step `[s, s + K]` shows that
`A - a₀` doubles over it, `2 (A(s) - a₀) ≤ A(s + K) - a₀` and `A(s) - a₀ ≤ 2 (A(s + K) - a₀)`
(`TauCeti.two_mul_sub_le_and_sub_le_two_mul_of_abs_sub_le_mul`). If this holds for every step, `A`
is the constant `a₀` (`TauCeti.eq_of_monotone_of_abs_sub_le_mul`). This is the shape of the
action–energy argument for Floer trajectories near a nondegenerate orbit, with `A` the action of
the loops and `σ` the energy of the slices. The averaging step is
`TauCeti.le_setIntegral_Icc_add_of_le_mul` from `TauCeti.MeasureTheory.Integral.Bochner.Set`: a
pointwise bound `m ≤ K σ` on `[a, a + K]` gives `m ≤ ∫_a^{a+K} σ`.

On an interval `[a, b]` a nondecreasing `g` which doubles in this sense over every step of length
`T` inside `[a, b]` decays exponentially away from both ends: its positive part doubles forwards
and its negative part doubles backwards, so its increase over `[s₁, s₂]` is at most
`4 (g b - g a)` times `exp (-κ (b - s₂)) + exp (-κ (s₁ - a))`, `κ = log 2 / T`
(`TauCeti.sub_le_mul_exp_add_exp_of_two_mul_le`). The decay of each part is the fixed-step
contraction estimate `TauCeti.le_div_mul_exp_of_antitoneOn_Icc` from
`TauCeti.Analysis.SpecificLimits.DiscreteGronwall`.
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

/-- **Doubling over one step from an integral control.** Let `A` be nondecreasing on `[s, s + K]`,
with `K > 0`, and let its distance to `a₀` be controlled by a density `σ`, `|A(r) - a₀| ≤ K σ(r)`
for `r ∈ [s, s + K]`, whose integral over `[s, s + K]` is the increment `A(s + K) - A(s)`. Then
over this step the positive part of `A - a₀` at least doubles forwards and its negative part at
least doubles backwards: `2 (A(s) - a₀) ≤ A(s + K) - a₀` and `A(s) - a₀ ≤ 2 (A(s + K) - a₀)`. -/
theorem two_mul_sub_le_and_sub_le_two_mul_of_abs_sub_le_mul {A σ : ℝ → ℝ} {a₀ s K : ℝ}
    (hK : 0 < K) (hmono : MonotoneOn A (Icc s (s + K)))
    (hσ : ∀ r ∈ Icc s (s + K), |A r - a₀| ≤ K * σ r) (hint : IntegrableOn σ (Icc s (s + K)))
    (heq : ∫ r in Icc s (s + K), σ r = A (s + K) - A s) :
    2 * (A s - a₀) ≤ A (s + K) - a₀ ∧ A s - a₀ ≤ 2 * (A (s + K) - a₀) := by
  have hs : s ∈ Icc s (s + K) := ⟨le_rfl, by linarith⟩
  have hsK : s + K ∈ Icc s (s + K) := ⟨by linarith, le_rfl⟩
  -- Integrate the lower bounds `A s - a₀ ≤ |A r - a₀|` and `-(A (s + K) - a₀) ≤ |A r - a₀|`.
  have h₁ := (le_setIntegral_Icc_add_of_le_mul hK hint fun r hr ↦
    (sub_le_sub_right (hmono hs hr hr.1) _).trans ((le_abs_self _).trans (hσ r hr))).trans_eq heq
  have h₂ := (le_setIntegral_Icc_add_of_le_mul hK hint (m := -(A (s + K) - a₀)) fun r hr ↦
    (neg_le_neg (sub_le_sub_right (hmono hr hsK hr.2) _)).trans
      ((neg_le_abs _).trans (hσ r hr))).trans_eq heq
  constructor <;> linarith

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
  have hdbl (a : ℝ) := two_mul_sub_le_and_sub_le_two_mul_of_abs_sub_le_mul hK
    (hmono.monotoneOn _) (fun r _ ↦ hσ r) (hint a).1 (hint a).2
  refine sub_eq_zero.1 (eq_zero_of_two_mul_le_add_of_sub_le_two_mul (g := fun s ↦ A s - a₀)
    (K := K) ?_ ?_ (fun s ↦ ?_) (fun s ↦ ?_) s)
  · obtain ⟨B, hB⟩ := hup
    exact ⟨B - a₀, forall_mem_range.2 fun s ↦ sub_le_sub_right (hB (mem_range_self s)) _⟩
  · obtain ⟨B, hB⟩ := hlow
    exact ⟨B - a₀, forall_mem_range.2 fun s ↦ sub_le_sub_right (hB (mem_range_self s)) _⟩
  · exact (hdbl s).1
  · simpa only [sub_add_cancel] using (hdbl (s - K)).2

/-- **Decay away from the right end from forward doubling.** Let `g` be nondecreasing on `[a, b]`,
and suppose that `2 g s ≤ g (s + T)` whenever `a ≤ s` and `s + T ≤ b`. Then the positive part of `g`
decays exponentially away from `b`: for `s ∈ [a, b]`,
`max (g s) 0 ≤ 2 max (g b) 0 exp (-(log 2 / T) (b - s))`. -/
theorem max_le_two_mul_max_mul_exp_of_two_mul_le {g : ℝ → ℝ} {a b T : ℝ}
    (hg : MonotoneOn g (Set.Icc a b)) (hstep : ∀ s, a ≤ s → s + T ≤ b → 2 * g s ≤ g (s + T))
    {s : ℝ} (hs : a ≤ s) (hsb : s ≤ b) :
    max (g s) 0 ≤ 2 * max (g b) 0 * Real.exp (-(Real.log 2 / T * (b - s))) := by
  -- The positive part, read backwards from `b`, halves over every step of length `T`.
  have h := le_div_mul_exp_of_antitoneOn_Icc (E := fun r ↦ max (g (b - r)) 0) (s₀ := 0)
    (s₁ := b - a) (T := T) (s := b - s) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (fun r hr r' hr' hrr' ↦ max_le_max_right 0
      (hg ⟨by linarith [hr'.2], by linarith [hr'.1]⟩ ⟨by linarith [hr.2], by linarith [hr.1]⟩
        (by linarith)))
    (le_max_right _ _)
    (fun r hr hrT ↦ by
      have h := hstep (b - (r + T)) (by linarith) (by linarith)
      rw [show b - (r + T) + T = b - r by ring] at h
      exact max_le (by linarith [le_max_left (g (b - r)) 0])
        (mul_nonneg (by norm_num) (le_max_right _ _)))
    (sub_nonneg.2 hsb) (by linarith)
  have hlog : Real.log (1 / 2) = -Real.log 2 := by simp
  calc max (g s) 0 = max (g (b - (b - s))) 0 := by rw [sub_sub_cancel]
    _ ≤ _ := h
    _ = _ := by rw [hlog, sub_zero, sub_zero]; ring_nf

/-- On an interval `[a, b]` of length at least `T > 0`, if a nondecreasing `g` satisfies
`2 g s ≤ g (s + T)` and `g s ≤ 2 g (s + T)` over every step of length `T`, then the positive part of
`g` at `b` and its negative part at `a` together are at most twice the increase `g b - g a`. -/
private theorem max_add_max_neg_le_two_mul_sub {g : ℝ → ℝ} {a b T : ℝ}
    (hg : MonotoneOn g (Set.Icc a b))
    (hstep : ∀ s, a ≤ s → s + T ≤ b → 2 * g s ≤ g (s + T) ∧ g s ≤ 2 * g (s + T)) (hT : 0 < T)
    (hlong : T ≤ b - a) : max (g b) 0 + max (-g a) 0 ≤ 2 * (g b - g a) := by
  have hdbl := hstep a le_rfl (by linarith)
  have hmono := hg ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : a + T ≤ b)
  have hmono' := hg ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith : a ≤ b - T)
  have hdbl' := hstep (b - T) (by linarith) (sub_add_cancel b T).le
  rw [sub_add_cancel] at hdbl'
  rcases le_total 0 (g a) with ha | ha <;> rcases le_total 0 (g b) with hb | hb
  · rw [max_eq_left hb, max_eq_right (by linarith)]
    linarith [hdbl.1, hmono]
  · rw [max_eq_right hb, max_eq_right (by linarith)]
    linarith [hg ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : a ≤ b)]
  · rw [max_eq_left hb, max_eq_left (by linarith)]
    linarith
  · rw [max_eq_right hb, max_eq_left (by linarith)]
    linarith [hdbl'.2, hmono']

/-- **Two-sided exponential decay on an interval from doubling.** Let `g` be nondecreasing on
`[a, b]`, and suppose that over every step of length `T` inside `[a, b]` its positive part at
least doubles forwards and its negative part at least doubles backwards: `2 g s ≤ g (s + T)` and
`g s ≤ 2 g (s + T)` whenever `a ≤ s` and `s + T ≤ b`. Then the increase of `g` over
`[s₁, s₂] ⊆ [a, b]` is exponentially small in the distances of `s₂` from `b` and of `s₁` from `a`,
relative to its total increase over `[a, b]`:
`g s₂ - g s₁ ≤ 4 (g b - g a) (exp (-κ (b - s₂)) + exp (-κ (s₁ - a)))` with `κ = log 2 / T`.

For a function with `|g| ≤ T g'` the doubling conditions hold, so this integrates the
differential inequality on an interval. It describes a quantity such as the action along a long
neck near a nondegenerate critical point, which is positive only near the right end and negative
only near the left end. -/
theorem sub_le_mul_exp_add_exp_of_two_mul_le {g : ℝ → ℝ} {a b T : ℝ}
    (hg : MonotoneOn g (Set.Icc a b))
    (hstep : ∀ s, a ≤ s → s + T ≤ b → 2 * g s ≤ g (s + T) ∧ g s ≤ 2 * g (s + T))
    {s₁ s₂ : ℝ} (h₁ : a ≤ s₁) (h₁₂ : s₁ ≤ s₂) (h₂ : s₂ ≤ b) :
    g s₂ - g s₁ ≤ 4 * (g b - g a) *
      (Real.exp (-(Real.log 2 / T * (b - s₂))) + Real.exp (-(Real.log 2 / T * (s₁ - a)))) := by
  set κ := Real.log 2 / T
  have hab : a ≤ b := h₁.trans (h₁₂.trans h₂)
  have hmem {s : ℝ} (h : a ≤ s) (h' : s ≤ b) : s ∈ Set.Icc a b := ⟨h, h'⟩
  have hD : 0 ≤ g b - g a := sub_nonneg.2 (hg (hmem le_rfl hab) (hmem hab le_rfl) hab)
  have hE₁ := (Real.exp_pos (-(κ * (b - s₂)))).le
  have hE₂ := (Real.exp_pos (-(κ * (s₁ - a)))).le
  have hinc : g s₂ - g s₁ ≤ g b - g a := by
    have := hg (hmem h₁ (h₁₂.trans h₂)) (hmem (h₁.trans h₁₂) h₂) h₁₂
    have := hg (hmem (h₁.trans h₁₂) h₂) (hmem hab le_rfl) h₂
    have := hg (hmem le_rfl hab) (hmem h₁ (h₁₂.trans h₂)) h₁
    linarith
  rcases le_or_gt T 0 with hT | hT
  · -- For `T ≤ 0` the exponents are nonnegative and the total increase suffices.
    have h1 : 1 ≤ Real.exp (-(κ * (b - s₂))) := Real.one_le_exp (by
      nlinarith [div_nonpos_of_nonneg_of_nonpos (Real.log_nonneg one_le_two) hT])
    nlinarith
  rcases lt_or_ge (b - a) T with hshort | hlong
  · -- On a short interval `exp (-κ (b - s₂)) ≥ 1 / 2` and the total increase suffices.
    have hκ : κ * (b - s₂) ≤ Real.log 2 := calc
      κ * (b - s₂) ≤ κ * T :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (Real.log_nonneg one_le_two) hT.le)
      _ = Real.log 2 := div_mul_cancel₀ _ hT.ne'
    have hhalf : 1 / 2 ≤ Real.exp (-(κ * (b - s₂))) := calc
      (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log two_pos, one_div]
      _ ≤ _ := Real.exp_le_exp.2 (neg_le_neg hκ)
    nlinarith
  -- The positive part of `g` decays away from `b`, and its negative part, the positive part of
  -- the reflection `r ↦ -g (a + b - r)`, decays away from `a`.
  have hp := max_le_two_mul_max_mul_exp_of_two_mul_le hg (fun s hs hsT ↦ (hstep s hs hsT).1)
    (h₁.trans h₁₂) h₂
  have hm := max_le_two_mul_max_mul_exp_of_two_mul_le (g := fun r ↦ -g (a + b - r)) (a := a)
    (b := b) (T := T)
    (fun r hr r' hr' hrr' ↦ neg_le_neg (hg ⟨by linarith [hr'.2], by linarith [hr'.1]⟩
      ⟨by linarith [hr.2], by linarith [hr.1]⟩ (by linarith)))
    (fun r hr hrT ↦ by
      have h := (hstep (a + b - (r + T)) (by linarith) (by linarith)).2
      rw [show a + b - (r + T) + T = a + b - r by ring] at h
      linarith)
    (s := a + b - s₁) (by linarith) (by linarith)
  simp only [show a + b - (a + b - s₁) = s₁ by ring, add_sub_cancel_right,
    show b - (a + b - s₁) = s₁ - a by ring] at hm
  -- On a long interval the two parts at the ends are bounded by twice the total increase.
  have hpm := max_add_max_neg_le_two_mul_sub hg hstep hT hlong
  have hp0 : 0 ≤ max (g b) 0 := le_max_right _ _
  have hm0 : 0 ≤ max (-g a) 0 := le_max_right _ _
  have := le_max_left (g s₂) 0
  have := le_max_left (-g s₁) 0
  nlinarith

end TauCeti
