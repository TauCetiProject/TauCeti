/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Functions on `ℝ` injective modulo a period

A function `γ : ℝ → α` is injective modulo `T` when `γ s = γ t` only if `s - t` is an integer
multiple of `T`, as for a closed curve without self-intersections parametrized with period `T`.
Such a function separates parameters less than `T` apart, and, when continuous into a metric
space, separates them by a uniform distance on compact sets of starting parameters.

## Main results

* `TauCeti.apply_ne_apply_add`: a function injective modulo `T` takes different values at
  parameters strictly between `0` and `T` apart.
* `TauCeti.exists_pos_le_dist_apply_add`: a continuous function injective modulo `T` moves a
  definite distance over parameter differences in `[δ, T - δ]`, uniformly over starting parameters
  in a compact set.
-/

public section

open Set

namespace TauCeti

variable {α : Type*} {γ : ℝ → α} {T : ℝ}

/-- A function injective modulo `T` takes different values at parameters strictly between `0` and
`T` apart. -/
theorem apply_ne_apply_add (hinj : ∀ s t, γ s = γ t → ∃ k : ℤ, s = t + k * T) {t h : ℝ}
    (hh : 0 < h) (hhT : h < T) : γ t ≠ γ (t + h) := fun heq ↦ by
  obtain ⟨k, hk⟩ := hinj _ _ heq
  rcases le_or_gt 0 k with hk0 | hk0
  · have : (0 : ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
    nlinarith

/-- A continuous function into a metric space, injective modulo `T`, moves a definite distance
over parameter differences in `[δ, T - δ]`, uniformly over starting parameters in a compact
set. -/
theorem exists_pos_le_dist_apply_add [MetricSpace α] (hγ : Continuous γ)
    (hinj : ∀ s t, γ s = γ t → ∃ k : ℤ, s = t + k * T) {s : Set ℝ} (hs : IsCompact s) {δ : ℝ}
    (hδ : 0 < δ) : ∃ η > 0, ∀ a ∈ s, ∀ d ∈ Icc δ (T - δ), η ≤ dist (γ (a + d)) (γ a) := by
  rcases (s ×ˢ Icc δ (T - δ)).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun a ha d hd ↦ (eq_empty_iff_forall_notMem.1 he (a, d) ⟨ha, hd⟩).elim⟩
  obtain ⟨p, hp, hmin⟩ := (hs.prod isCompact_Icc).exists_isMinOn hne
    (Continuous.continuousOn (f := fun p : ℝ × ℝ ↦ dist (γ (p.1 + p.2)) (γ p.1)) (by fun_prop))
  refine ⟨_, dist_pos.2 fun heq ↦ ?_, fun a ha d hd ↦ isMinOn_iff.1 hmin (a, d) ⟨ha, hd⟩⟩
  -- A coincidence `γ (a + d) = γ a` is impossible since `0 < d < T`.
  have hd₁ : δ ≤ p.2 := (mem_prod.1 hp).2.1
  have hd₂ : p.2 ≤ T - δ := (mem_prod.1 hp).2.2
  exact apply_ne_apply_add hinj (by linarith) (by linarith) heq.symm

end TauCeti
