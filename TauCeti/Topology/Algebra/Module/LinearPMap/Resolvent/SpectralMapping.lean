/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Shift
public import Mathlib.Tactic.Module

/-!
# Spectral mapping for the resolvent of a partial linear map

At a resolvent point `z` of a partial linear map `A`, another scalar `w` is a
resolvent point precisely when `1 - (z - w) • A.resolvent z` is invertible.
This gives spectral mapping for the continuous operator `A.resolvent z`: for
a unit `u` over a commutative ring, `↑u` is outside its algebraic spectrum
exactly when `z - ↑u⁻¹` belongs to the resolvent set of `A`. Over a field, this
says that for `μ ≠ 0`, `μ` is outside the spectrum exactly when `z - μ⁻¹`
is a resolvent point.

The results use only a topological module with continuous addition and constant
scalar multiplication. In particular, they apply to bounded resolvents of
unbounded operators without a completeness or self-adjointness assumption.
The restriction `μ ≠ 0` is essential: zero can belong to the spectrum of the
resolvent of an unbounded operator.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Section IV.1 (spectral mapping for resolvents).
-/

public section

noncomputable section

namespace TauCeti.LinearPMap

open _root_.LinearPMap (IsResolventAt resolvent_sub_resolvent_apply subScalar subScalar_apply)

section CommRing

variable {𝕜 X : Type*} [CommRing 𝕜] [AddCommGroup X] [TopologicalSpace X]
  [Module 𝕜 X] [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
variable {A : X →ₗ.[𝕜] X} {z w : 𝕜}

/-- An invertible scalar perturbation of a resolvent gives the inverse at the
new spectral parameter, with no smallness assumption. -/
theorem isResolventAt_of_isUnit_one_sub_smul_resolvent (hz : z ∈ A.resolventSet)
    (h : IsUnit (1 - (z - w) • A.resolvent z)) :
    IsResolventAt A w
      (A.resolvent z * Ring.inverse (1 - (z - w) • A.resolvent z)) := by
  let B : X →L[𝕜] X := (z - w) • 1
  have hBR : B * A.resolvent z = (z - w) • A.resolvent z := by
    simp [B]
  have hp := B.isResolventAt_vadd_of_isUnit_one_sub_mul_resolvent hz (hBR ▸ h)
  have hshift : ((B : X →ₗ[𝕜] X) +ᵥ A) = subScalar A (w - z) := by
    refine _root_.LinearPMap.ext (by simp) fun x hx hy => ?_
    rw [LinearPMap.vadd_apply, subScalar_apply]
    simp only [B, ContinuousLinearMap.coe_coe, smul_apply, one_apply_eq_self]
    module
  simp only [hBR, hshift] at hp
  simpa only [add_sub, add_sub_cancel_left] using isResolventAt_subScalar_iff.mp hp

/-- The exact invertibility criterion for changing a resolvent parameter. -/
theorem mem_resolventSet_iff_isUnit_one_sub_smul_resolvent (hz : z ∈ A.resolventSet) :
    w ∈ A.resolventSet ↔ IsUnit (1 - (z - w) • A.resolvent z) := by
  constructor
  · intro hw
    refine isUnit_iff_exists.mpr ⟨1 + (z - w) • A.resolvent w, ?_, ?_⟩
    · ext y
      have hid := resolvent_sub_resolvent_apply hz hw y
      simp only [mul_apply_eq_comp, add_apply, sub_apply, smul_apply,
        one_apply_eq_self, map_add, map_smul]
      rw [sub_eq_iff_eq_add.mp hid]
      module
    · ext y
      have hid := resolvent_sub_resolvent_apply hw hz y
      simp only [mul_apply_eq_comp, add_apply, sub_apply, smul_apply,
        one_apply_eq_self, map_sub, map_smul]
      rw [sub_eq_iff_eq_add.mp hid]
      module
  · exact fun h => (isResolventAt_of_isUnit_one_sub_smul_resolvent hz h).mem_resolventSet

/-- The resolvent at a new parameter is obtained by inverting the scalar perturbation,
with no smallness assumption on the change of parameter. -/
theorem resolvent_eq_mul_inverse_one_sub_smul_resolvent (hz : z ∈ A.resolventSet)
    (h : IsUnit (1 - (z - w) • A.resolvent z)) :
    A.resolvent w = A.resolvent z * Ring.inverse (1 - (z - w) • A.resolvent z) :=
  _root_.LinearPMap.resolvent_eq_of_isResolventAt
    (isResolventAt_of_isUnit_one_sub_smul_resolvent hz h)

/-- The inverse of the scalar perturbation relating two resolvent parameters. -/
theorem inverse_one_sub_smul_resolvent (hz : z ∈ A.resolventSet)
    (hw : w ∈ A.resolventSet) :
    Ring.inverse (1 - (z - w) • A.resolvent z) = 1 + (z - w) • A.resolvent w := by
  have h := (mem_resolventSet_iff_isUnit_one_sub_smul_resolvent hz).mp hw
  have hcancel := Ring.mul_inverse_cancel _ h
  rw [sub_mul, one_mul, smul_mul_assoc,
    ← resolvent_eq_mul_inverse_one_sub_smul_resolvent hz h] at hcancel
  exact sub_eq_iff_eq_add.mp hcancel

/-- **Resolvent spectral mapping** for a unit over a commutative ring: `↑u` lies
outside the spectrum of `R(z)` exactly when `z - ↑u⁻¹` is a resolvent point of `A`. -/
theorem notMem_spectrum_resolvent_iff_of_unit (hz : z ∈ A.resolventSet) (u : 𝕜ˣ) :
    (u : 𝕜) ∉ spectrum 𝕜 (A.resolvent z) ↔ z - (↑u⁻¹ : 𝕜) ∈ A.resolventSet := by
  rw [spectrum.notMem_iff,
    mem_resolventSet_iff_isUnit_one_sub_smul_resolvent hz, sub_sub_cancel]
  simpa only [Units.smul_def, Algebra.algebraMap_eq_smul_one] using
    (IsUnit.smul_sub_iff_sub_inv_smul u (A.resolvent z))

end CommRing

section Field

variable {𝕜 X : Type*} [Field 𝕜] [AddCommGroup X] [TopologicalSpace X]
  [Module 𝕜 X] [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
variable {A : X →ₗ.[𝕜] X} {z μ : 𝕜}

/-- **Resolvent spectral mapping**, away from zero: `μ` lies outside the spectrum
of `R(z)` exactly when `z - μ⁻¹` is a resolvent point of `A`. -/
theorem notMem_spectrum_resolvent_iff (hz : z ∈ A.resolventSet) (hμ : μ ≠ 0) :
    μ ∉ spectrum 𝕜 (A.resolvent z) ↔ z - μ⁻¹ ∈ A.resolventSet := by
  simpa only [Units.val_mk0, Units.val_inv_eq_inv_val] using
    notMem_spectrum_resolvent_iff_of_unit hz (Units.mk0 μ hμ)

end Field

end TauCeti.LinearPMap
