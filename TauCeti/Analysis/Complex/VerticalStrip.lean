/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard

/-!
# Vertical strips

Mathlib's three-lines theorem is stated on the open strip `verticalStrip a b` and the closed
strip `verticalClosedStrip a b`, the preimages of `Ioo a b` and `Icc a b` under `Complex.re`.
This file records their membership criteria, behavior under reflection, and the topological
facts used when applying `DiffContOnCl` on the strip.
-/

public section

open Complex Complex.HadamardThreeLines Set

namespace TauCeti.Complex.HadamardThreeLines

variable {a b : ℝ} {z : ℂ}

@[simp]
theorem mem_verticalStrip_iff : z ∈ verticalStrip a b ↔ z.re ∈ Ioo a b :=
  Iff.rfl

@[simp]
theorem mem_verticalClosedStrip_iff : z ∈ verticalClosedStrip a b ↔ z.re ∈ Icc a b :=
  Iff.rfl

/-- Reflection by `z ↦ w - z` reverses the real endpoints of an open vertical strip. -/
theorem sub_mem_verticalStrip_iff (w z : ℂ) :
    w - z ∈ verticalStrip a b ↔ z ∈ verticalStrip (w.re - b) (w.re - a) := by
  simp only [mem_verticalStrip_iff, mem_Ioo, sub_re]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith

/-- Reflection by `z ↦ w - z` reverses the real endpoints of a closed vertical strip. -/
theorem sub_mem_verticalClosedStrip_iff (w z : ℂ) :
    w - z ∈ verticalClosedStrip a b ↔ z ∈ verticalClosedStrip (w.re - b) (w.re - a) := by
  simp only [mem_verticalClosedStrip_iff, mem_Icc, sub_re]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith

/-- Reflection in the middle of the unit strip preserves open-strip membership. -/
theorem one_sub_mem_verticalStrip_iff :
    1 - z ∈ verticalStrip 0 1 ↔ z ∈ verticalStrip 0 1 := by
  simpa only [one_re, sub_self, sub_zero] using
    sub_mem_verticalStrip_iff (a := 0) (b := 1) (1 : ℂ) z

/-- Reflection in the middle of the unit strip preserves closed-strip membership. -/
theorem one_sub_mem_verticalClosedStrip_iff :
    1 - z ∈ verticalClosedStrip 0 1 ↔ z ∈ verticalClosedStrip 0 1 := by
  simpa only [one_re, sub_self, sub_zero] using
    sub_mem_verticalClosedStrip_iff (a := 0) (b := 1) (1 : ℂ) z

theorem isOpen_verticalStrip (a b : ℝ) : IsOpen (verticalStrip a b) :=
  isOpen_Ioo.preimage continuous_re

theorem verticalStrip_subset_verticalClosedStrip (a b : ℝ) :
    verticalStrip a b ⊆ verticalClosedStrip a b :=
  preimage_mono Ioo_subset_Icc_self

theorem closure_verticalStrip_subset (a b : ℝ) :
    closure (verticalStrip a b) ⊆ verticalClosedStrip a b := by
  rw [verticalStrip, closure_preimage_re]
  exact preimage_mono (closure_minimal Ioo_subset_Icc_self isClosed_Icc)

end TauCeti.Complex.HadamardThreeLines
