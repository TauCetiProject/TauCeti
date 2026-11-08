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

## Main results

* `TauCeti.exists_lt_tsupport_subset_Ioo`: the support shrinks to `(0, R')` with `R' < R`.
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

end TauCeti
