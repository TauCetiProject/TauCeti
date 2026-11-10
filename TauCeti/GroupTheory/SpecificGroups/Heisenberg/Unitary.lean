/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Matrix
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

variable {R : Type*} [CommRing R] (σ : R →+* R) (hσ : Function.Involutive σ)

/-- The unitary root subgroup, with trace equal to norm in its two free coordinates. -/
def unitarySubgroup : Subgroup (HeisenbergGroup R) where
  carrier := {a | a.y = σ a.x ∧ a.z + σ a.z = a.x * σ a.x}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨hay, haz⟩ ⟨hby, hbz⟩
    constructor
    · simp [hay, hby]
    · simp only [mul_z, mul_x, map_add, map_mul, hby, hσ b.x]
      linear_combination haz + hbz
  inv_mem' := by
    rintro a ⟨hay, haz⟩
    constructor
    · simp [hay]
    · simp only [inv_z, inv_x, map_add, map_neg, map_mul, hay, hσ a.x]
      linear_combination -haz

@[simp]
theorem mem_unitarySubgroup {a : HeisenbergGroup R} :
    a ∈ unitarySubgroup σ hσ ↔ a.y = σ a.x ∧ a.z + σ a.z = a.x * σ a.x := Iff.rfl

/-- Construct a unitary root element from parameters whose trace is the norm. -/
def unitaryMk (x z : R) (hz : z + σ z = x * σ x) : unitarySubgroup σ hσ :=
  ⟨⟨x, σ x, z⟩, rfl, hz⟩

@[simp]
theorem coe_unitaryMk (x z : R) (hz : z + σ z = x * σ x) :
    (unitaryMk σ hσ x z hz : HeisenbergGroup R) = ⟨x, σ x, z⟩ := (rfl)

/-- The two parameters uniquely determine a unitary root element. -/
@[ext]
theorem unitary_ext {a b : unitarySubgroup σ hσ}
    (hx : (a : HeisenbergGroup R).x = (b : HeisenbergGroup R).x)
    (hz : (a : HeisenbergGroup R).z = (b : HeisenbergGroup R).z) : a = b := by
  apply Subtype.ext
  exact HeisenbergGroup.ext hx (by rw [a.property.1, b.property.1, hx]) hz

/-- Every unitary root element is given by its two parameters. -/
@[simp]
theorem unitaryMk_eq (a : unitarySubgroup σ hσ) :
    unitaryMk σ hσ (a : HeisenbergGroup R).x (a : HeisenbergGroup R).z
      ((mem_unitarySubgroup σ hσ).mp a.property).2 = a := by
  apply unitary_ext <;> rfl

/-- The multiplication law for the two parameters of the twisted root group. -/
theorem coe_unitary_mul (a b : unitarySubgroup σ hσ) :
    ((a * b : unitarySubgroup σ hσ) : HeisenbergGroup R) =
      ⟨(a : HeisenbergGroup R).x + (b : HeisenbergGroup R).x,
        σ ((a : HeisenbergGroup R).x + (b : HeisenbergGroup R).x),
        (a : HeisenbergGroup R).z + (b : HeisenbergGroup R).z +
          (a : HeisenbergGroup R).x * σ (b : HeisenbergGroup R).x⟩ := by
  ext <;> simp [a.property.1, b.property.1]

/-- Inversion negates the first parameter and applies the involution to the second. -/
theorem coe_unitary_inv (a : unitarySubgroup σ hσ) :
    ((a⁻¹ : unitarySubgroup σ hσ) : HeisenbergGroup R) =
      ⟨-(a : HeisenbergGroup R).x, σ (-(a : HeisenbergGroup R).x),
        σ (a : HeisenbergGroup R).z⟩ := by
  apply HeisenbergGroup.ext
  · rfl
  · simp [a.property.1]
  · simp only [Subgroup.coe_inv, inv_z, a.property.1]
    linear_combination -((mem_unitarySubgroup σ hσ).mp a.property).2

/-- The commutator formula for the twisted root group. -/
theorem coe_unitary_commutator (a b : unitarySubgroup σ hσ) :
    ((⁅a, b⁆ : unitarySubgroup σ hσ) : HeisenbergGroup R) =
      ⟨0, 0, (a : HeisenbergGroup R).x * σ (b : HeisenbergGroup R).x -
        (b : HeisenbergGroup R).x * σ (a : HeisenbergGroup R).x⟩ := by
  exact (map_commutatorElement (unitarySubgroup σ hσ).subtype a b).trans
    ((commutatorElement_eq (a : HeisenbergGroup R) (b : HeisenbergGroup R)).trans
      (by rw [a.property.1, b.property.1]))

/-- Every commutator in the twisted root group is central. -/
theorem unitary_commutator_mem_center (a b : unitarySubgroup σ hσ) :
    ⁅a, b⁆ ∈ Subgroup.center (unitarySubgroup σ hσ) := by
  apply Subgroup.mem_center_iff.mpr
  intro c
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (zAxis_le_center
    (commutatorElement_mem_zAxis (a : HeisenbergGroup R) (b : HeisenbergGroup R))) c

/-- The unitary equations are precisely preservation of the signed reversal form by an upper
unitriangular matrix. -/
theorem transpose_map_toMatrix_mul_form_iff (a : HeisenbergGroup R) :
    ((toMatrix a).map σ)ᵀ * !![0, 0, 1; 0, -1, 0; 1, 0, 0] * toMatrix a =
        !![0, 0, 1; 0, -1, 0; 1, 0, 0] ↔ a ∈ unitarySubgroup σ hσ := by
  constructor
  · intro h
    have hy : -a.y + σ a.x = 0 := by
      simpa [toMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three] using
        congrFun (congrFun h 1) 2
    have hz : a.z + -(σ a.y * a.y) + σ a.z = 0 := by
      simpa [toMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three] using
        congrFun (congrFun h 2) 2
    have hy' : a.y = σ a.x := by linear_combination -hy
    refine ⟨hy', ?_⟩
    rw [hy', hσ a.x] at hz
    linear_combination hz
  · rintro ⟨hy, hz⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three, hy, hσ a.x]
    linear_combination hz

end TauCeti.HeisenbergGroup
