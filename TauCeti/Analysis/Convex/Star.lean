/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Tactic.Linarith

/-!
# Star-convexity of the complement of a closed half-subspace

For a subspace `W` of a vector space `E` over a linearly ordered field and a linear functional
`φ` on `E`, the set `{x ∈ W | φ x ≤ 0}` is a closed half of `W`. Its complement in `E` is
star-convex about any `v ∈ W` with `0 < φ v`
(`TauCeti.starConvex_compl_setOf_mem_and_nonpos`): a segment from `v` that ends outside `W`
leaves `W` at once, and one that ends in `W` stays where `φ` is positive. This is the
subspace analogue of Mathlib's `starConvex_compl_Iic`.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

/-- The complement of the closed half-subspace `{x ∈ W | φ x ≤ 0}` is star-convex about any
`v ∈ W` with `0 < φ v`. -/
theorem starConvex_compl_setOf_mem_and_nonpos {W : Submodule 𝕜 E} {φ : E →ₗ[𝕜] 𝕜} {v : E}
    (hv : v ∈ W) (hφv : 0 < φ v) : StarConvex 𝕜 v {x | x ∈ W ∧ φ x ≤ 0}ᶜ := by
  rintro x hx a b ha hb hab ⟨hmem, hle⟩
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hle
  rcases hb.eq_or_lt with rfl | hb
  · rw [add_zero] at hab
    subst hab
    linarith
  · have hxW : x ∈ W := by
      have h : b • x ∈ W := by simpa using W.sub_mem hmem (W.smul_mem a hv)
      exact (W.smul_mem_iff hb.ne').1 h
    exact hx ⟨hxW, by nlinarith⟩

end TauCeti
