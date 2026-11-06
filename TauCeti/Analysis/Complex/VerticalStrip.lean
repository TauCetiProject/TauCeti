/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Vertical strips

Basic topology of the vertical strips `a < re z < b` and `a ≤ re z ≤ b` of Mathlib's Hadamard
three lines theorem (`Complex.HadamardThreeLines.verticalStrip` and
`Complex.HadamardThreeLines.verticalClosedStrip`), and an unfolding of the boundedness hypothesis
`BddAbove ((norm ∘ f) '' s)` of that theorem.
-/

public section

open Set Complex Complex.HadamardThreeLines

namespace TauCeti

/-- The norm of `f` is bounded above on `s`, in the form of the hypothesis of Hadamard's three
lines theorem, exactly when there is a uniform bound `‖f z‖ ≤ A` on `s`. -/
theorem bddAbove_norm_comp_image_iff {α E : Type*} [Norm E] {f : α → E} {s : Set α} :
    BddAbove ((norm ∘ f) '' s) ↔ ∃ A, ∀ z ∈ s, ‖f z‖ ≤ A := by
  simp only [bddAbove_def, forall_mem_image, Function.comp_apply]

/-- The open vertical strip `a < re z < b` is open. -/
theorem isOpen_verticalStrip (a b : ℝ) : IsOpen (verticalStrip a b) :=
  isOpen_Ioo.preimage continuous_re

/-- The closure of the open vertical strip `a < re z < b` is the closed strip `a ≤ re z ≤ b`. -/
theorem closure_verticalStrip {a b : ℝ} (hab : a ≠ b) :
    closure (verticalStrip a b) = verticalClosedStrip a b := by
  rw [verticalStrip, closure_preimage_re, closure_Ioo hab, verticalClosedStrip]

/-- The open vertical strip is contained in the closed vertical strip. -/
theorem verticalStrip_subset_verticalClosedStrip (a b : ℝ) :
    verticalStrip a b ⊆ verticalClosedStrip a b :=
  preimage_mono Ioo_subset_Icc_self

end TauCeti
