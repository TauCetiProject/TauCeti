/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Point selection with controlled displacement

A bounded size function admits an earlier point with a doubling bound on nearby earlier values,
while preserving a reciprocal-size displacement budget. Choose above half the supremum among
budget-admissible points; any violating point would remain admissible and exceed that supremum.

This is the scalar point-selection step in curvature estimates; see the proof of Theorem 3.1
of B.-L. Chen, *Strong uniqueness of the Ricci flow*, arXiv:0706.3081v2, p. 10. Applying it to
the square root of curvature gives a factor-four curvature bound. No flow is constructed here.

Formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
and [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set

namespace TauCeti

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

/-- A bounded size function has an earlier point whose earlier nearby values
are at most twice its size. Its size does not decrease and the reciprocal-size
displacement budget is retained. Only the initial size must be positive. -/
theorem exists_point_with_doubling_bound
    {X : Type*} (S : Set X) (size radius time : X → 𝕜)
    (hbounded : BddAbove (size '' S)) {L : 𝕜} (hL : 0 ≤ L)
    {x : X} (hx : x ∈ S) (hxpos : 0 < size x) :
    ∃ y ∈ S, time y ≤ time x ∧ size x ≤ size y ∧
      radius y + 2 * L / size y ≤ radius x + 2 * L / size x ∧
      ∀ z ∈ S, time z ≤ time y → radius z ≤ radius y + L / size y →
        size z ≤ 2 * size y := by
  let A : Set X := {y | y ∈ S ∧ time y ≤ time x ∧ size x ≤ size y ∧
    radius y + 2 * L / size y ≤ radius x + 2 * L / size x}
  have hxA : x ∈ A := ⟨hx, le_rfl, le_rfl, le_rfl⟩
  have hAS : A ⊆ S := fun _ hy ↦ hy.1
  have hbound : BddAbove (size '' A) := hbounded.mono (image_mono hAS)
  have hsup : 0 < sSup (size '' A) :=
    hxpos.trans_le (le_csSup hbound (mem_image_of_mem size hxA))
  obtain ⟨_, ⟨y, hy, rfl⟩, hhalf⟩ := exists_lt_of_lt_csSup
    ⟨size x, mem_image_of_mem size hxA⟩ (half_lt_self hsup)
  refine ⟨y, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2, ?_⟩
  intro z hz htz hrz
  by_contra h
  have hqz : 2 * size y < size z := lt_of_not_ge h
  have hypos : 0 < size y := hxpos.trans_le hy.2.2.1
  have hstep : 2 * L / size z ≤ L / size y := by
    calc
      2 * L / size z ≤ 2 * L / (2 * size y) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hqz.le
      _ = L / size y := by field_simp
  have hr : radius z + 2 * L / size z ≤ radius y + 2 * L / size y := by
    simp only [mul_div_assoc] at hstep ⊢
    linarith
  have hzA : z ∈ A := ⟨hz, htz.trans hy.2.1,
    hy.2.2.1.trans (by linarith), hr.trans hy.2.2.2⟩
  have hupper := le_csSup hbound (mem_image_of_mem size hzA)
  linarith

end TauCeti
