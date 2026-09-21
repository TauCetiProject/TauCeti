/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

/-!
# The action of units on the mixed space

This file provides basic compatibility and measurability lemmas for the action of number-field
units on the mixed space.

## Main results

* `TauCeti.NumberField.mixedEmbedding.unitSMul_comm`: two unit actions commute;
* `TauCeti.NumberField.mixedEmbedding.unitSMul_real_smul`: the unit action commutes with real
  scalar multiplication;
* `TauCeti.NumberField.mixedEmbedding.measurable_unitSMul`: the action of a fixed unit is
  measurable.
-/

public section

open NumberField

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K]

/-- The unit action on the mixed space is commutative: it is multiplication by the mixed embedding
of a unit, and the mixed space is a commutative ring. -/
theorem unitSMul_comm (u v : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K) :
    u • v • x = v • u • x := by
  rw [← mul_smul, ← mul_smul, mul_comm]

/-- The unit action on the mixed space commutes with the real scalar action. -/
theorem unitSMul_real_smul (u : (𝓞 K)ˣ) (c : ℝ) (x : mixedEmbedding.mixedSpace K) :
    u • (c • x) = c • (u • x) := by
  simpa only [mixedEmbedding.unitSMul_smul] using
    mul_smul_comm c (mixedEmbedding K (u : K)) x

/-- The action of a fixed unit on the mixed space is measurable. -/
theorem measurable_unitSMul [NumberField K] (u : (𝓞 K)ˣ) :
    Measurable fun x : mixedEmbedding.mixedSpace K ↦ u • x := by
  simpa only [mixedEmbedding.unitSMul_smul] using
    (continuous_const_mul (mixedEmbedding K (u : K))).measurable

end TauCeti.NumberField.mixedEmbedding
