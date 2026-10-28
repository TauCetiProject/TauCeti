/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic

/-!
# Dilates of a convex set containing the origin

A convex set `s` containing `0` is star-shaped about `0`, so its dilates are nested: for
`0 ≤ p ≤ q`, the dilate `p • s` lies in `q • s` (`Convex.smul_mono_of_zero_mem`). This is the
monotonicity in the dilation factor behind the successive minima of a set with respect to a
lattice, whose thresholds are the dilates `r • s` meeting the lattice in enough independent
vectors.

The statement and its name follow Mathlib's successive-minima proposal
(mathlib4 PR 35812 by Alex J. Best, Yaël Dillies and Kevin H. Wilson, file
`Mathlib/Analysis/Convex/Basic.lean` at revision `8423d1c`).
-/

public section

open scoped Pointwise

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] {s : Set E}

/-- The dilates of a convex set containing `0` are nested: `p • s ⊆ q • s` for `0 ≤ p ≤ q`. -/
theorem Convex.smul_mono_of_zero_mem (h_conv : Convex 𝕜 s) (zero_mem : (0 : E) ∈ s) {p q : 𝕜}
    (hp : 0 ≤ p) (hpq : p ≤ q) : p • s ⊆ q • s := by
  rintro _ ⟨y, hy, rfl⟩
  obtain rfl | hp := hp.eq_or_lt
  · exact ⟨0, zero_mem, by simp⟩
  have hq : 0 < q := hp.trans_le hpq
  refine ⟨(p / q) • y, h_conv.smul_mem_of_zero_mem zero_mem hy
    ⟨div_nonneg hp.le hq.le, div_le_one_of_le₀ hpq hq.le⟩, ?_⟩
  simp only [smul_smul, mul_div_cancel₀ p hq.ne']
