/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.Derivative
public import TauCeti.Topology.Algebra.ConstMulAction
public import Mathlib.RingTheory.IntegralDomain

/-!
# Stabilizers of Fuchsian groups

The stabilizer of a point of the upper half-plane in a discrete subgroup of `PSL(2, ℝ)` is
finite cyclic. Its faithful character into the multiplicative monoid of `ℂ` is the complex
derivative of the Möbius action at the fixed point. This identifies the order of every stabilizer
element with the order of its derivative.

## Main results

* `TauCeti.stabilizerDerivative`: the derivative as a character of a point stabilizer.
* `TauCeti.stabilizerDerivative_injective`: faithfulness of that character.
* `TauCeti.orderOf_stabilizerDerivative`: equality of the elliptic and derivative orders.
* `TauCeti.isCyclic_stabilizer`: every finite point stabilizer is cyclic.

## References

* [S. Katok, *Fuchsian Groups*, Chapter 2][katok1992]
-/

public section

open scoped MatrixGroups
open Matrix.SpecialLinearGroup

noncomputable section

namespace TauCeti

open MulAction

open _root_.UpperHalfPlane
open TauCeti.UpperHalfPlane

/-- The derivative character of the stabilizer of a point in a subgroup of `PSL(2, ℝ)`. -/
def stabilizerDerivative (G : Subgroup PSL(2, ℝ)) (τ : ℍ) : stabilizer G τ →* ℂ where
  toFun g := pslDerivative (g.1.1 : PSL(2, ℝ)) τ
  map_one' := by
    simp only [Subgroup.coe_one, pslDerivative_one]
  map_mul' g h := by
    simp only [Subgroup.coe_mul]
    rw [pslDerivative_mul]
    have hfix : (h.1.1 : PSL(2, ℝ)) • τ = τ := by
      simpa only [Subgroup.smul_def] using (MulAction.mem_stabilizer_iff.mp h.property)
    rw [hfix]

/-- Evaluating the stabilizer derivative character is evaluating the projective derivative of the
underlying element. -/
@[simp]
theorem stabilizerDerivative_apply (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) :
    stabilizerDerivative G τ g = pslDerivative (g.1.1 : PSL(2, ℝ)) τ := (rfl)

/-- The derivative character takes values in the nonzero complex numbers. -/
theorem stabilizerDerivative_ne_zero (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) : stabilizerDerivative G τ g ≠ 0 :=
  pslDerivative_ne_zero _ _

/-- The derivative character takes values on the complex unit circle. -/
theorem norm_stabilizerDerivative (G : Subgroup PSL(2, ℝ)) (τ : ℍ)
    (g : stabilizer G τ) : ‖stabilizerDerivative G τ g‖ = 1 := by
  apply norm_pslDerivative_eq_one_of_smul_eq_self
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
    apply eq_one_of_smul_eq_self_of_pslDerivative_eq_one
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

end TauCeti
