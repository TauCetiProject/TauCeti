/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

import Mathlib.Algebra.Module.LinearMap.DivisionRing

/-!
# Strict half-spaces of a real normed space are unbounded

A strict half-space `{y | φ y < u}` cut out by a nonzero linear functional holds points of
arbitrarily large norm, and is therefore unbounded. Linearity alone suffices: `φ` need not be
continuous, so the results apply to a discontinuous functional on an infinite-dimensional space.
For such a `φ` the set need not be topologically open, which is why it is called strict rather
than open here.

## Main results

* `TauCeti.exists_apply_lt_and_lt_norm` and `TauCeti.exists_lt_apply_and_lt_norm` — either side
  of a nonzero linear functional holds points of arbitrarily large norm.
* `TauCeti.not_isBounded_halfSpace_lt` and `TauCeti.not_isBounded_halfSpace_gt` — either strict
  half-space is unbounded.
-/

public section

namespace TauCeti

open Bornology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A strict half-space contains points of arbitrarily large norm.** For a nonzero linear
functional `φ`, every bound `u` and every radius `R` admit a `y` with `φ y < u` and `R < ‖y‖`.
Linearity suffices; `φ` need not be continuous. -/
theorem exists_apply_lt_and_lt_norm {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u R : ℝ) :
    ∃ y : E, φ y < u ∧ R < ‖y‖ := by
  obtain ⟨v, hφv⟩ := LinearMap.surjective_iff_ne_zero.mpr hφ 1
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr fun h => by simp [h] at hφv
  -- Walk to `-t • v` for a `t` large enough to break both the bound `u` and the radius `R`.
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℝ, (R + 1) / ‖v‖ ≤ t ∧ |u| + 1 ≤ t :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have ht0 : 0 ≤ t := le_trans (by positivity) ht2
  refine ⟨(-t) • v, ?_, ?_⟩
  · rw [map_smul, hφv, smul_eq_mul, mul_one]
    linarith [neg_abs_le u]
  · rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg ht0]
    linarith [(div_le_iff₀ hvnorm).mp ht1]

/-- **The other side of a nonzero linear functional also contains points of arbitrarily large
norm**: every bound `u` and radius `R` admit a `y` with `u < φ y` and `R < ‖y‖`. -/
theorem exists_lt_apply_and_lt_norm {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u R : ℝ) :
    ∃ y : E, u < φ y ∧ R < ‖y‖ := by
  obtain ⟨y, hy, hn⟩ := exists_apply_lt_and_lt_norm (φ := -φ) (neg_ne_zero.mpr hφ) (-u) R
  exact ⟨y, by simpa using hy, hn⟩

/-- **A strict half-space cut out by a nonzero linear functional is unbounded.** No radius bounds
`{y | φ y < u}`. Linearity suffices; `φ` need not be continuous. -/
theorem not_isBounded_halfSpace_lt {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u : ℝ) :
    ¬ IsBounded {y | φ y < u} := by
  intro hbdd
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd
  obtain ⟨y, hy, hn⟩ := exists_apply_lt_and_lt_norm hφ u R
  exact absurd (hR y (by simpa using hy)) (not_le.mpr hn)

/-- **The half-space on the other side of a nonzero linear functional is unbounded.** No radius
bounds `{y | u < φ y}` either. Linearity suffices; `φ` need not be continuous. -/
theorem not_isBounded_halfSpace_gt {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u : ℝ) :
    ¬ IsBounded {y | u < φ y} := by
  intro hbdd
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd
  obtain ⟨y, hy, hn⟩ := exists_lt_apply_and_lt_norm hφ u R
  exact absurd (hR y (by simpa using hy)) (not_le.mpr hn)

end TauCeti
