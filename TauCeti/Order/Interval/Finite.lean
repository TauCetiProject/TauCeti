/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Intervals avoiding a finite family of real points

A finite family of real points is bounded above, so an open interval beyond it contains a point.
-/

public section

open Set

namespace TauCeti

/-- There is a nonempty open real interval avoiding a finite family of real points. -/
theorem exists_Ioo_disjoint_range_of_finite {ι : Type*} [Finite ι] (a : ι → ℝ) :
    ∃ p q x : ℝ, (∀ i, a i ∉ Ioo p q) ∧ x ∈ Ioo p q := by
  obtain ⟨S, hbound⟩ := Finite.exists_le a
  let p := S + 1
  let x := p + 1
  let q := p + 2
  have ha : ∀ i, a i ∉ Ioo p q := by
    intro i hi
    have := hbound i
    dsimp [p] at hi
    exact (not_lt.mpr (by linarith : a i ≤ S + 1)) hi.1
  have hx : x ∈ Ioo p q := by dsimp [x, q]; constructor <;> linarith
  exact ⟨p, q, x, ha, hx⟩

end TauCeti
