/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Expansive
import TauCeti.Analysis.Normed.Group.AddCircle

/-!
# The doubling map of the circle is positively expansive

The doubling map `x ↦ 2 • x` of `AddCircle p` is positively expansive with every constant
`δ < |p| / 4` (`AddCircle.isPositivelyExpansive_two_nsmul`). For distinct `x`, `y` the iterates
differ by `2 ^ k • (x - y)`, and doubling a nonzero point of norm less than `|p| / 4` doubles its
norm, so some `2 ^ k • (x - y)` has norm at least `|p| / 4`
(`AddCircle.exists_le_norm_two_pow_nsmul_of_ne_zero`).

This is the one-dimensional case of the positively expansive toral endomorphisms of
ClassicalErgodicTheory §5.3. The doubling map is not injective, so it is not an expansive
homeomorphism.

## Main results

* `AddCircle.isPositivelyExpansive_two_nsmul`: `x ↦ 2 • x` on `AddCircle p` is positively
  expansive with every constant `δ < |p| / 4`.
* `TauCeti.isPositivelyExpansive_two_nsmul_unitAddCircle`: the case of `UnitAddCircle`, with every
  constant `δ < 1 / 4`.
-/

public section

open TauCeti

namespace AddCircle

variable {p : ℝ}

/-- The doubling map `x ↦ 2 • x` of `AddCircle p` is positively expansive with every constant
`δ < |p| / 4`. -/
theorem isPositivelyExpansive_two_nsmul {δ : ℝ} (hδ : δ < |p| / 4) :
    IsPositivelyExpansive (fun x : AddCircle p ↦ 2 • x) δ := by
  refine isPositivelyExpansive_iff.2 fun x y hxy ↦ ?_
  obtain ⟨k, hk⟩ := exists_le_norm_two_pow_nsmul_of_ne_zero (sub_ne_zero.mpr hxy)
  refine ⟨k, hδ.trans_le ?_⟩
  rwa [smul_iterate_apply, smul_iterate_apply, dist_eq_norm, ← smul_sub]

end AddCircle

namespace TauCeti

/-- **Check.** The doubling map `x ↦ 2 • x` of `UnitAddCircle` is positively expansive with every
constant `δ < 1 / 4`. -/
theorem isPositivelyExpansive_two_nsmul_unitAddCircle {δ : ℝ} (hδ : δ < 1 / 4) :
    IsPositivelyExpansive (fun x : UnitAddCircle ↦ 2 • x) δ :=
  AddCircle.isPositivelyExpansive_two_nsmul (by simpa using hδ)

end TauCeti
