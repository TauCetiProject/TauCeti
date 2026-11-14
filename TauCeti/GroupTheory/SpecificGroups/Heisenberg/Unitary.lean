/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Matrix
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The unitary root subgroup of the Heisenberg group

For an involution `σ` of a commutative ring, the equations `y = σ(x)` and
`z + σ(z) = x σ(x)` define a subgroup of the Heisenberg group. Its matrices are exactly the
upper unitriangular isometries of the signed reversal form
`!![0, 0, 1; 0, -1, 0; 1, 0, 0]`. Over a quadratic finite-field extension this is the twisted
root group in `SU₃`, including in characteristic two.

Multiplication and inversion are inherited from the Heisenberg group, so the parameters obey
`(x,z)(x',z') = (x+x', z+z'+x σ(x'))`. The commutator has parameters
`(0, x σ(x') - x' σ(x))` and is central. No division by two is used.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), Chapter 13.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti.HeisenbergGroup

variable {R : Type*} [CommRing R] (σ : R →+* R)

/-- The upper unitriangular isometries of the signed reversal form. For an involution,
the trace of the second free coordinate equals the norm of the first. -/
def unitarySubgroup : Subgroup (HeisenbergGroup R) :=
  (Matrix.specialIsometryGroup !![0, 0, 1; 0, -1, 0; 1, 0, 0] σ).comap toSpecialLinear

variable {σ}

/-- Membership in the unitary root subgroup is preservation of the signed reversal form. -/
theorem mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq {a : HeisenbergGroup R} :
    a ∈ unitarySubgroup σ ↔
      ((toMatrix a).map σ)ᵀ * !![0, 0, 1; 0, -1, 0; 1, 0, 0] * toMatrix a =
        !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by
  simp only [unitarySubgroup, Subgroup.mem_comap, Matrix.mem_specialIsometryGroup_iff,
    coe_toSpecialLinear]

namespace unitarySubgroup

/-- The middle coordinate of a unitary root element is the image of its first coordinate. -/
@[simp]
theorem y_eq (a : unitarySubgroup σ) :
    (a : HeisenbergGroup R).y = σ (a : HeisenbergGroup R).x := by
  have h := mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq.mp a.property
  have hy : -(a : HeisenbergGroup R).y + σ (a : HeisenbergGroup R).x = 0 := by
    simpa [toMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three] using
      congrFun (congrFun h 1) 2
  linear_combination -hy

/-- The trace of the last coordinate of a unitary root element is the norm of its first. -/
theorem z_add_map_z (a : unitarySubgroup σ) :
    (a : HeisenbergGroup R).z + σ (a : HeisenbergGroup R).z =
      (a : HeisenbergGroup R).x * σ (a : HeisenbergGroup R).x := by
  have h := mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq.mp a.property
  have hx : (a : HeisenbergGroup R).x - σ (a : HeisenbergGroup R).y = 0 := by
    simpa [toMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three, sub_eq_add_neg] using
      congrFun (congrFun h 2) 1
  have hz : (a : HeisenbergGroup R).z -
      σ (a : HeisenbergGroup R).y * (a : HeisenbergGroup R).y +
      σ (a : HeisenbergGroup R).z = 0 := by
    simpa [toMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three, sub_eq_add_neg] using
      congrFun (congrFun h 2) 2
  rw [y_eq a] at hx hz
  linear_combination hz - σ (a : HeisenbergGroup R).x * hx

end unitarySubgroup

variable (hσ : Function.Involutive σ)

/-- For an involution `σ`, a Heisenberg element preserves the signed reversal form exactly
when `y = σ x` and `z + σ z = x * σ x`. -/
@[simp]
theorem mem_unitarySubgroup (hσ : Function.Involutive σ) {a : HeisenbergGroup R} :
    a ∈ unitarySubgroup σ ↔ a.y = σ a.x ∧ a.z + σ a.z = a.x * σ a.x := by
  constructor
  · intro ha
    exact ⟨unitarySubgroup.y_eq ⟨a, ha⟩, unitarySubgroup.z_add_map_z ⟨a, ha⟩⟩
  · rintro ⟨hy, hz⟩
    rw [mem_unitarySubgroup_iff_transpose_map_toMatrix_mul_mul_eq]
    ext i j
    by_cases hij : i = 2 ∧ j = 2
    · obtain ⟨rfl, rfl⟩ := hij
      -- The (2,2) entry is exactly the trace-norm equation.
      simp [toMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three, hy, hσ a.x]
      linear_combination hz
    · fin_cases i <;> fin_cases j <;>
        simp_all [toMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three, hσ a.x]

/-- Construct a unitary root element from parameters whose trace is the norm. -/
def unitaryMk (σ : R →+* R) (hσ : Function.Involutive σ)
    (x z : R) (hz : z + σ z = x * σ x) : unitarySubgroup σ :=
  ⟨⟨x, σ x, z⟩, (mem_unitarySubgroup hσ).mpr ⟨rfl, hz⟩⟩

@[simp]
theorem coe_unitaryMk (x z : R) (hz : z + σ z = x * σ x) :
    (unitaryMk σ hσ x z hz : HeisenbergGroup R) = ⟨x, σ x, z⟩ := (rfl)

namespace unitarySubgroup

/-- The two parameters uniquely determine a unitary root element. -/
@[ext]
theorem ext {a b : unitarySubgroup σ}
    (hx : (a : HeisenbergGroup R).x = (b : HeisenbergGroup R).x)
    (hz : (a : HeisenbergGroup R).z = (b : HeisenbergGroup R).z) : a = b := by
  apply Subtype.ext
  exact HeisenbergGroup.ext hx
    (by rw [unitarySubgroup.y_eq a, unitarySubgroup.y_eq b, hx]) hz

/-- The multiplication law for the two parameters of the twisted root group. -/
theorem coe_mul (a b : unitarySubgroup σ) :
    ((a * b : unitarySubgroup σ) : HeisenbergGroup R) =
      ⟨(a : HeisenbergGroup R).x + (b : HeisenbergGroup R).x,
        σ ((a : HeisenbergGroup R).x + (b : HeisenbergGroup R).x),
        (a : HeisenbergGroup R).z + (b : HeisenbergGroup R).z +
          (a : HeisenbergGroup R).x * σ (b : HeisenbergGroup R).x⟩ := by
  ext <;> simp

/-- Inversion negates the first parameter and applies the involution to the second. -/
theorem coe_inv (a : unitarySubgroup σ) :
    ((a⁻¹ : unitarySubgroup σ) : HeisenbergGroup R) =
      ⟨-(a : HeisenbergGroup R).x, σ (-(a : HeisenbergGroup R).x),
        σ (a : HeisenbergGroup R).z⟩ := by
  apply HeisenbergGroup.ext
  · rfl
  · simp
  · simp only [Subgroup.coe_inv, inv_z, unitarySubgroup.y_eq a]
    linear_combination -(unitarySubgroup.z_add_map_z a)

/-- The commutator formula for the twisted root group. -/
theorem coe_commutatorElement (a b : unitarySubgroup σ) :
    ((⁅a, b⁆ : unitarySubgroup σ) : HeisenbergGroup R) =
      ⟨0, 0, (a : HeisenbergGroup R).x * σ (b : HeisenbergGroup R).x -
        (b : HeisenbergGroup R).x * σ (a : HeisenbergGroup R).x⟩ := by
  exact (map_commutatorElement (unitarySubgroup σ).subtype a b).trans
    ((commutatorElement_eq (a : HeisenbergGroup R) (b : HeisenbergGroup R)).trans
      (by rw [unitarySubgroup.y_eq a, unitarySubgroup.y_eq b]))

/-- Every commutator in the twisted root group is central. -/
theorem commutatorElement_mem_center (a b : unitarySubgroup σ) :
    ⁅a, b⁆ ∈ Subgroup.center (unitarySubgroup σ) := by
  apply Subgroup.mem_center_iff.mpr
  intro c
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (zAxis_le_center
    (commutatorElement_mem_zAxis (a : HeisenbergGroup R) (b : HeisenbergGroup R))) c

end unitarySubgroup

/-- Every unitary root element is given by its two parameters. -/
@[simp]
theorem unitaryMk_eta (a : unitarySubgroup σ) :
    unitaryMk σ hσ (a : HeisenbergGroup R).x (a : HeisenbergGroup R).z
      (unitarySubgroup.z_add_map_z a) = a := by
  apply unitarySubgroup.ext <;> rfl

/-- Zero parameters give the identity of the unitary root group. -/
@[simp]
theorem unitaryMk_zero_zero : unitaryMk σ hσ 0 0 (by simp) = 1 := by
  apply unitarySubgroup.ext <;> rfl

/-- Multiplication of root elements adds the first parameters and includes the cross term. -/
@[simp]
theorem unitaryMk_mul_unitaryMk (x z x' z' : R)
    (hz : z + σ z = x * σ x) (hz' : z' + σ z' = x' * σ x') :
    unitaryMk σ hσ x z hz * unitaryMk σ hσ x' z' hz' =
      unitaryMk σ hσ (x + x') (z + z' + x * σ x') (by
        simp only [map_add, map_mul, hσ x']
        linear_combination hz + hz') := by
  apply unitarySubgroup.ext <;> rfl

/-- Inversion negates the first parameter and maps the second parameter by `σ`. -/
@[simp]
theorem unitaryMk_inv (x z : R) (hz : z + σ z = x * σ x) :
    (unitaryMk σ hσ x z hz)⁻¹ =
      unitaryMk σ hσ (-x) (σ z) (by simpa [hσ z, add_comm] using hz) := by
  apply Subtype.ext
  exact (unitarySubgroup.coe_inv _).trans (by simp)

/-- Root elements are equal exactly when both parameters agree. -/
@[simp]
theorem unitaryMk_inj (x z x' z' : R)
    (hz : z + σ z = x * σ x) (hz' : z' + σ z' = x' * σ x') :
    unitaryMk σ hσ x z hz = unitaryMk σ hσ x' z' hz' ↔ x = x' ∧ z = z' := by
  constructor
  · intro h
    exact ⟨congrArg (fun a : unitarySubgroup σ ↦ (a : HeisenbergGroup R).x) h,
      congrArg (fun a : unitarySubgroup σ ↦ (a : HeisenbergGroup R).z) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A root element is the identity exactly when both parameters vanish. -/
@[simp]
theorem unitaryMk_eq_one_iff (x z : R) (hz : z + σ z = x * σ x) :
    unitaryMk σ hσ x z hz = 1 ↔ x = 0 ∧ z = 0 := by
  rw [← unitaryMk_zero_zero hσ, unitaryMk_inj]

/-- The commutator of root elements is the central root element given by the alternating norm. -/
theorem commutatorElement_unitaryMk (x z x' z' : R)
    (hz : z + σ z = x * σ x) (hz' : z' + σ z' = x' * σ x') :
    ⁅unitaryMk σ hσ x z hz, unitaryMk σ hσ x' z' hz'⁆ =
      unitaryMk σ hσ 0 (x * σ x' - x' * σ x) (by
        simp only [map_sub, map_mul, hσ x, hσ x', map_zero, zero_mul]
        ring) := by
  apply Subtype.ext
  exact (unitarySubgroup.coe_commutatorElement _ _).trans (by simp)

end TauCeti.HeisenbergGroup
