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
This file records their membership criteria, the topological facts used when applying
`DiffContOnCl` on the strip, and the membership criterion for a point `x + t * I` in terms of
its real part `x`.
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

theorem isOpen_verticalStrip (a b : ℝ) : IsOpen (verticalStrip a b) :=
  isOpen_Ioo.preimage continuous_re

theorem isClosed_verticalClosedStrip (a b : ℝ) : IsClosed (verticalClosedStrip a b) :=
  isClosed_Icc.preimage continuous_re

theorem verticalStrip_subset_verticalClosedStrip (a b : ℝ) :
    verticalStrip a b ⊆ verticalClosedStrip a b :=
  preimage_mono Ioo_subset_Icc_self

theorem closure_verticalStrip_subset (a b : ℝ) :
    closure (verticalStrip a b) ⊆ verticalClosedStrip a b :=
  closure_minimal (verticalStrip_subset_verticalClosedStrip a b) (isClosed_verticalClosedStrip a b)

theorem ofReal_add_mul_I_mem_verticalStrip_iff {x t : ℝ} :
    ((x : ℂ) + t * I) ∈ verticalStrip a b ↔ x ∈ Ioo a b := by
  simp

theorem ofReal_add_mul_I_mem_verticalClosedStrip_iff {x t : ℝ} :
    ((x : ℂ) + t * I) ∈ verticalClosedStrip a b ↔ x ∈ Icc a b := by
  simp

end TauCeti.Complex.HadamardThreeLines
