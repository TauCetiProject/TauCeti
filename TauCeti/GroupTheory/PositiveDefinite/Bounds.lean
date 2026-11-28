/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef.Basic

/-!
# Norm and real-part bounds for positive-definite functions on groups

For a normalized (`φ 1 = 1`) positive-definite function `φ : G → 𝕜` on a group, valued in an
`RCLike` field `𝕜`, the scalar Cauchy--Schwarz estimate from
`TauCeti.Analysis.Matrix.PosSemidef.Basic` gives `‖φ g‖ ≤ 1`, `0 ≤ 1 - re (φ g)`, and
`‖φ g - 1‖ ^ 2 ≤ 2 * (1 - re (φ g))`.

## Main declarations

* `Matrix.PosSemidef.norm_apply_le_one`: `‖φ g‖ ≤ 1` for a normalized positive-definite function.
* `Matrix.PosSemidef.one_sub_re_nonneg`: `0 ≤ 1 - re (φ g)`.
* `Matrix.PosSemidef.norm_sub_one_sq_le`: `‖φ g - 1‖ ^ 2 ≤ 2 * (1 - re (φ g))`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open scoped ComplexOrder

namespace Matrix.PosSemidef

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [Group G]

/-- A normalized positive-definite function on a group is bounded by `1` in norm. -/
theorem norm_apply_le_one {φ : G → 𝕜} (hφ : (of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)
    (h1 : φ 1 = 1) (g : G) : ‖φ g‖ ≤ 1 := by
  simpa using hφ.norm_le_one_of_apply_self_eq_one (a := 1) (b := g) (by simp [h1]) (by simp [h1])

/-- For a normalized positive-definite function `φ` on a group, `0 ≤ 1 - re (φ g)`. -/
theorem one_sub_re_nonneg {φ : G → 𝕜} (hφ : (of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)
    (h1 : φ 1 = 1) (g : G) : 0 ≤ 1 - RCLike.re (φ g) := by
  linarith [RCLike.re_le_norm (φ g), hφ.norm_apply_le_one h1 g]

/-- For a normalized positive-definite function `φ` on a group,
`‖φ g - 1‖ ^ 2 ≤ 2 * (1 - re (φ g))`. -/
theorem norm_sub_one_sq_le {φ : G → 𝕜} (hφ : (of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)
    (h1 : φ 1 = 1) (g : G) : ‖φ g - 1‖ ^ 2 ≤ 2 * (1 - RCLike.re (φ g)) := by
  have hsq : RCLike.normSq (φ g) ≤ 1 := by
    simpa [RCLike.normSq_eq_def'] using
      pow_le_pow_left₀ (norm_nonneg _) (hφ.norm_apply_le_one h1 g) 2
  rw [← RCLike.normSq_eq_def', RCLike.normSq_sub (φ g) 1, RCLike.normSq_one]
  simp only [map_one, mul_one]
  linarith

end Matrix.PosSemidef
