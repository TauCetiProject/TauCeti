/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Support

/-!
# Test-function supports inside an open interval

A function on `ℝ` whose topological support is contained in `(0, R)` has its support inside
`(0, R')` for some `R' < R`: the support is closed and the interval is a ball in a proper space.
Likewise a compactly supported function supported in `(0, ∞)` vanishes on `(-∞, ε)` for some
`ε > 0`, its support having a least element.

## Main results

* `TauCeti.exists_lt_tsupport_subset_Ioo`: the support shrinks to `(0, R')` with `R' < R`.
* `HasCompactSupport.exists_pos_forall_eq_zero_of_tsupport_subset_Ioi`: a compactly supported
  function supported in `(0, ∞)` vanishes near `(-∞, 0]` and far out.
-/

public section

namespace TauCeti

open Metric Set

variable {R : ℝ} {F : Type*} [Zero F]

/-- A test function `ψ` supported in `(0, R)` is supported in some `(0, R')` with `R' < R`. -/
lemma exists_lt_tsupport_subset_Ioo (hR : 0 < R) {ψ : ℝ → F}
    (hψs : tsupport ψ ⊆ Ioo 0 R) : ∃ R', 0 < R' ∧ R' < R ∧ tsupport ψ ⊆ Ioo 0 R' := by
  have hball : Ioo (0 : ℝ) R = ball (R / 2) (R / 2) := by
    rw [Real.ball_eq_Ioo]
    congr 1 <;> ring
  obtain ⟨r, hr, hψr⟩ :=
    exists_pos_lt_subset_ball (half_pos hR) (isClosed_tsupport ψ) (hball ▸ hψs)
  rw [Real.ball_eq_Ioo] at hψr
  exact ⟨R / 2 + r, by linarith [hr.1], by linarith [hr.2],
    hψr.trans (Ioo_subset_Ioo (by linarith [hr.2]) le_rfl)⟩

/-- A compactly supported function supported in `(0, ∞)` vanishes on some `(-∞, ε)` with `ε > 0`
and on some `[T, ∞)`. -/
theorem _root_.HasCompactSupport.exists_pos_forall_eq_zero_of_tsupport_subset_Ioi {ψ : ℝ → F}
    (hc : HasCompactSupport ψ) (hψ : tsupport ψ ⊆ Ioi 0) :
    ∃ ε > 0, ∃ T, (∀ t < ε, ψ t = 0) ∧ ∀ t, T ≤ t → ψ t = 0 := by
  rcases (tsupport ψ).eq_empty_or_nonempty with h | h
  · have h0 (t : ℝ) : ψ t = 0 := image_eq_zero_of_notMem_tsupport (by simp [h])
    exact ⟨1, one_pos, 0, fun t _ ↦ h0 t, fun t _ ↦ h0 t⟩
  · obtain ⟨m, hm, hmin⟩ := hc.exists_isLeast h
    obtain ⟨M, hM⟩ := hc.isCompact.bddAbove
    refine ⟨m, hψ hm, M + 1, fun t ht ↦ image_eq_zero_of_notMem_tsupport fun htK ↦ ?_,
      fun t ht ↦ image_eq_zero_of_notMem_tsupport fun htK ↦ ?_⟩
    · exact absurd (hmin htK) (not_le.2 ht)
    · linarith [hM htK]

end TauCeti
