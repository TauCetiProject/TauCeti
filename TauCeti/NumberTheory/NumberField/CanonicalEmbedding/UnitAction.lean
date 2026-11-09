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

This file provides basic compatibility and continuity lemmas for the action of number-field
units on the mixed space.

## Main results

* `SMulCommClass (𝓞 K)ˣ (𝓞 K)ˣ (mixedEmbedding.mixedSpace K)`: two unit actions commute;
* `SMulCommClass (𝓞 K)ˣ ℝ (mixedEmbedding.mixedSpace K)`: the unit action commutes with real
  scalar multiplication;
* `ContinuousConstSMul (𝓞 K)ˣ (mixedEmbedding.mixedSpace K)`: the action of a fixed unit is
  continuous, hence measurable, so Mathlib's `measurable_const_smul` applies;
* `TauCeti.NumberField.Units.unitSMul_mixedEmbedding_eq_self_iff`: a unit fixes the image of a
  nonzero element of `K` exactly when it is the identity.

It also identifies the units of the mixed space itself:

* `TauCeti.NumberField.mixedEmbedding.isUnit_iff_norm_ne_zero`: a point of the mixed space is a
  unit exactly when its norm is nonzero.
-/

public section

open NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K]

/-- The unit action on the mixed space is commutative: it is multiplication by the mixed embedding
of a unit, and the mixed space is a commutative ring.

This is Mathlib's `smulCommClass_self`, registered explicitly because instance search does not
find it for this action; with it, `smul_comm` applies to two units. -/
instance : SMulCommClass (𝓞 K)ˣ (𝓞 K)ˣ (mixedEmbedding.mixedSpace K) :=
  smulCommClass_self (𝓞 K)ˣ (mixedEmbedding.mixedSpace K)

/-- The unit action on the mixed space commutes with the real scalar action. -/
instance : SMulCommClass (𝓞 K)ˣ ℝ (mixedEmbedding.mixedSpace K) where
  smul_comm u c x := by
    simpa only [mixedEmbedding.unitSMul_smul] using
      mul_smul_comm c (mixedEmbedding K (u : K)) x

/-- The action of a fixed unit on the mixed space is continuous: it is multiplication by a fixed
element of a topological ring.

Through Mathlib's `ContinuousConstSMul.toMeasurableConstSMul` this also provides the
`MeasurableConstSMul` instance, so `measurable_const_smul` applies and `measurePreserving_smul`
and the `IsFundamentalDomain` lemmas become available wherever the action is also
measure-preserving. -/
instance : ContinuousConstSMul (𝓞 K)ˣ (mixedEmbedding.mixedSpace K) :=
  ⟨fun u ↦ by
    simpa only [mixedEmbedding.unitSMul_smul] using
      continuous_const_mul (mixedEmbedding K (u : K))⟩

/-- **The unit action on the mixed space is faithful away from zero.**  A unit fixes the image of
a nonzero element of `K` exactly when it is the identity. -/
theorem unitSMul_mixedEmbedding_eq_self_iff [NumberField K] {x : K} (hx : x ≠ 0)
    {u : (𝓞 K)ˣ} : u • mixedEmbedding K x = mixedEmbedding K x ↔ u = 1 := by
  rw [mixedEmbedding.unitSMul_smul, ← map_mul, (mixedEmbedding_injective K).eq_iff,
    mul_eq_right₀ hx]
  simp

end TauCeti.NumberField.Units

namespace Units

variable {K : Type*} [Field K]

open scoped nonZeroDivisors in
/-- Multiplication by a unit preserves every fractional-ideal lattice in the mixed space. -/
@[simp↓]
theorem unitSMul_mem_idealLattice_iff (u : (𝓞 K)ˣ)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : mixedEmbedding.mixedSpace K) :
    u • x ∈ mixedEmbedding.idealLattice K I ↔ x ∈ mixedEmbedding.idealLattice K I := by
  have h (v : (𝓞 K)ˣ) {z : mixedEmbedding.mixedSpace K}
      (hz : z ∈ mixedEmbedding.idealLattice K I) : v • z ∈ mixedEmbedding.idealLattice K I := by
    obtain ⟨a, ha, rfl⟩ := (mixedEmbedding.mem_idealLattice K I).mp hz
    rw [mixedEmbedding.unitSMul_smul, ← map_mul]
    exact (mixedEmbedding.mem_idealLattice K I).mpr
      ⟨(v : K) * a, (I : FractionalIdeal (𝓞 K)⁰ K).coeToSubmodule.smul_mem (v : 𝓞 K) ha, rfl⟩
  refine ⟨fun hx ↦ ?_, h u⟩
  have hx' := h u⁻¹ hx
  rwa [inv_smul_smul] at hx'

open scoped nonZeroDivisors in
/-- Multiplication by a unit permutes the points of every fractional-ideal lattice. -/
noncomputable def unitSMulIdealLatticeEquiv (u : (𝓞 K)ˣ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedEmbedding.idealLattice K I ≃ mixedEmbedding.idealLattice K I :=
  Equiv.subtypeEquiv (MulAction.toPerm u) fun x ↦ (u.unitSMul_mem_idealLattice_iff I x).symm

open scoped nonZeroDivisors in
@[simp]
theorem unitSMulIdealLatticeEquiv_apply (u : (𝓞 K)ˣ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : mixedEmbedding.idealLattice K I) :
    (u.unitSMulIdealLatticeEquiv I x : mixedEmbedding.mixedSpace K) =
      u • (x : mixedEmbedding.mixedSpace K) := (rfl)

end Units

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
  · simpa [normAtPlace_apply_of_isReal w.2] using hx w.1
  · simpa [normAtPlace_apply_of_isComplex w.2] using hx w.1

end TauCeti.NumberField.mixedEmbedding
