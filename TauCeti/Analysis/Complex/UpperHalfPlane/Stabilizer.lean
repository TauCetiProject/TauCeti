/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Derivative
public import Mathlib.RingTheory.IntegralDomain

/-!
# Point stabilizers in subgroups of `PSL(2, ℝ)`

The stabilizer of a point of the upper half-plane in a subgroup of `PSL(2, ℝ)` has a faithful
character into the multiplicative monoid of `ℂ`: the complex derivative of the Möbius action at
the fixed point. This identifies the order of every stabilizer element with the order of its
derivative, and shows that every finite point stabilizer is cyclic. For a discrete subgroup the
stabilizers are finite because its action on the upper half-plane is properly discontinuous.

## Main results

* `Subgroup.stabilizerDerivative`: the derivative as a character of a point stabilizer.
* `Subgroup.stabilizerDerivative_injective`: faithfulness of that character.
* `Subgroup.orderOf_stabilizerDerivative`: equality of the elliptic and derivative orders.
* `Subgroup.isCyclic_stabilizer`: every finite point stabilizer is cyclic.

## References

* [S. Katok, *Fuchsian Groups*, Chapter 2][katok1992]
-/

public section

open scoped MatrixGroups

noncomputable section

namespace Subgroup

open MulAction UpperHalfPlane Matrix.ProjectiveSpecialLinearGroup

/-- The derivative character of the stabilizer of a point in a subgroup of `PSL(2, ℝ)`. -/
def stabilizerDerivative (G : Subgroup PSL(2, ℝ)) (τ : ℍ) : stabilizer G τ →* ℂ where
  toFun g := derivative (g.1.1 : PSL(2, ℝ)) τ
  map_one' := by
    simp only [Subgroup.coe_one, derivative_one, Pi.one_apply]
  map_mul' g h := by
    simp only [Subgroup.coe_mul]
    rw [derivative_mul]
    have hfix : (h.1.1 : PSL(2, ℝ)) • τ = τ := by
      simpa only [Subgroup.smul_def] using (MulAction.mem_stabilizer_iff.mp h.property)
    rw [hfix]

/-- Evaluating the stabilizer derivative character is evaluating the projective derivative of the
underlying element. -/
@[simp]
theorem stabilizerDerivative_apply (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) :
    stabilizerDerivative G τ g = derivative (g.1.1 : PSL(2, ℝ)) τ := (rfl)

/-- The derivative character takes values in the nonzero complex numbers. -/
theorem stabilizerDerivative_ne_zero (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) : stabilizerDerivative G τ g ≠ 0 :=
  derivative_ne_zero _ _

/-- The derivative character takes values on the complex unit circle. -/
theorem norm_stabilizerDerivative (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) : ‖stabilizerDerivative G τ g‖ = 1 := by
  apply norm_derivative_eq_one_of_smul_eq_self
  simpa only [Subgroup.smul_def] using (MulAction.mem_stabilizer_iff.mp g.property)

/-- The derivative character of a point stabilizer is injective. -/
theorem stabilizerDerivative_injective (G : Subgroup PSL(2, ℝ)) (τ : ℍ) :
    Function.Injective (stabilizerDerivative G τ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hg
    apply Subtype.ext
    apply Subtype.ext
    apply eq_one_of_smul_eq_self_of_derivative_eq_one
    · simpa only [Subgroup.smul_def] using (MulAction.mem_stabilizer_iff.mp g.property)
    · exact hg
  · rintro rfl
    exact map_one (stabilizerDerivative G τ)

/-- The order of a stabilizer element equals the order of its derivative. -/
theorem orderOf_stabilizerDerivative (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) : orderOf (stabilizerDerivative G τ g) = orderOf g :=
  orderOf_injective (stabilizerDerivative G τ) (stabilizerDerivative_injective G τ) g

/-- Every finite point stabilizer in a subgroup of `PSL(2, ℝ)` is cyclic. -/
theorem isCyclic_stabilizer (G : Subgroup PSL(2, ℝ)) (τ : ℍ) [Finite (stabilizer G τ)] :
    IsCyclic (stabilizer G τ) :=
  isCyclic_of_injective_ringHom (stabilizerDerivative G τ)
    (stabilizerDerivative_injective G τ)

end Subgroup
