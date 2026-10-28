/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic

/-!
# Dilates of a star-convex set about the origin

The dilates of a set `s` star-convex about `0` are nested: for `0 ≤ p ≤ q`, the dilate `p • s`
lies in `q • s` (`StarConvex.smul_mono`). In particular this holds for a convex set containing `0`
(`Convex.smul_mono_of_zero_mem`). This is the monotonicity in the dilation factor behind the
successive minima of a set with respect to a lattice, whose thresholds are the dilates `r • s`
meeting the lattice in enough independent vectors.

The statement of `Convex.smul_mono_of_zero_mem` and its name follow Mathlib's successive-minima
proposal (mathlib4 PR 35812 by Alex J. Best, Yaël Dillies and Kevin H. Wilson, file
`Mathlib/Analysis/Convex/Basic.lean` at revision `8423d1c`).
-/

public section

open scoped Pointwise

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] {s : Set E}

/-- The dilates of a set star-convex about `0` are nested: `p • s ⊆ q • s` for `0 ≤ p ≤ q`. -/
theorem StarConvex.smul_mono (hs : StarConvex 𝕜 0 s) {p q : 𝕜} (hp : 0 ≤ p) (hpq : p ≤ q) :
    p • s ⊆ q • s := by
  rintro _ ⟨y, hy, rfl⟩
  obtain rfl | hp := hp.eq_or_lt
  · exact ⟨0, by simpa using hs.smul_mem hy le_rfl zero_le_one, by simp⟩
  have hq : 0 < q := hp.trans_le hpq
  refine ⟨(p / q) • y, hs.smul_mem hy (div_nonneg hp.le hq.le) (div_le_one_of_le₀ hpq hq.le), ?_⟩
  simp only [smul_smul, mul_div_cancel₀ p hq.ne']

/-- The dilates of a convex set containing `0` are nested: `p • s ⊆ q • s` for `0 ≤ p ≤ q`. -/
theorem Convex.smul_mono_of_zero_mem (h_conv : Convex 𝕜 s) (zero_mem : (0 : E) ∈ s) {p q : 𝕜}
    (hp : 0 ≤ p) (hpq : p ≤ q) : p • s ⊆ q • s :=
  (h_conv.starConvex zero_mem).smul_mono hp hpq
