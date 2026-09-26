/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

/-!
# The action of units on the mixed space

This file provides basic compatibility and measurability lemmas for the action of number-field
units on the mixed space.

## Main results

* `TauCeti.NumberField.Units.unitSMul_comm`: two unit actions commute;
* `TauCeti.NumberField.Units.unitSMul_real_smul`: the unit action commutes with real
  scalar multiplication;
* `MeasurableConstSMul (𝓞 K)ˣ (mixedEmbedding.mixedSpace K)`: the action of a fixed unit is
  measurable, so Mathlib's `measurable_const_smul` applies;
* `TauCeti.NumberField.Units.eq_one_of_unitSMul_mixedEmbedding_eq`: a unit fixing the image of a
  nonzero element of `K` is the identity.

It also identifies the units of the mixed space itself:

* `TauCeti.NumberField.mixedEmbedding.isUnit_iff_norm_ne_zero`: a point of the mixed space is a
  unit exactly when its norm is nonzero.
-/

public section

open NumberField

namespace TauCeti.NumberField.Units

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

/-- The action of a fixed unit on the mixed space is measurable.

Stated as the `MeasurableConstSMul` instance rather than as a bare lemma, because that is what
Mathlib's measure-theoretic API for group actions keys on: `measurable_const_smul` is then the
equation, and `measurePreserving_smul` and the `IsFundamentalDomain` lemmas become available
wherever the action is also measure-preserving. -/
instance [NumberField K] : MeasurableConstSMul (𝓞 K)ˣ (mixedEmbedding.mixedSpace K) :=
  ⟨fun u ↦ by
    simpa only [mixedEmbedding.unitSMul_smul] using
      (continuous_const_mul (mixedEmbedding K (u : K))).measurable⟩

/-- **The unit action on the mixed space is faithful away from zero.**  A unit fixing the image of
a nonzero element of `K` is the identity. -/
theorem eq_one_of_unitSMul_mixedEmbedding_eq [NumberField K] {x : K} (hx : x ≠ 0) {u : (𝓞 K)ˣ}
    (h : u • mixedEmbedding K x = mixedEmbedding K x) : u = 1 := by
  rw [mixedEmbedding.unitSMul_smul, ← map_mul, (mixedEmbedding_injective K).eq_iff,
    mul_eq_right₀ hx] at h
  exact Units.val_eq_one.mp (RingOfIntegers.coe_injective (h.trans (map_one _).symm))

end TauCeti.NumberField.Units

open NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

/-- **The units of the mixed space** are its points of nonzero norm: a point is invertible exactly
when none of its coordinates vanishes. -/
theorem isUnit_iff_norm_ne_zero {x : mixedSpace K} :
    IsUnit x ↔ mixedEmbedding.norm x ≠ 0 := by
  refine ⟨fun h ↦ (h.map mixedEmbedding.norm).ne_zero, fun hx ↦ ?_⟩
  rw [mixedEmbedding.norm_ne_zero_iff] at hx
  refine Prod.isUnit_iff.mpr ⟨Pi.isUnit_iff.mpr fun w ↦ ?_, Pi.isUnit_iff.mpr fun w ↦ ?_⟩
  · have hw := hx w.1
    rw [normAtPlace_apply_of_isReal w.2] at hw
    exact isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mp hw)
  · have hw := hx w.1
    rw [normAtPlace_apply_of_isComplex w.2] at hw
    exact isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mp hw)

end TauCeti.NumberField.mixedEmbedding
