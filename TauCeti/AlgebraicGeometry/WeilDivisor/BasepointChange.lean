/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi

/-!
# Changing the base point in the abstract Abel-Jacobi class

This file adds the base-point-change calculus for the formal divisor-class shadow of the
Abel-Jacobi map from `TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi`.

For a weight `w : X → ℤ`, a weight-one base point `x₀`, and another weight-one base point `y₀`,
the degree-corrected point divisors satisfy

`[x] - w(x)[y₀] = ([x] - w(x)[x₀]) + w(x)([x₀] - [y₀])`.

Passing to divisor classes gives the corresponding formula in the abstract `Pic⁰` subgroup:
changing the Abel-Jacobi base point translates the class by the degree of the point times the
degree-zero class `[x₀] - [y₀]`.  In the unweighted/algebraically closed specialization, this is
the familiar identity

`AJ_{y₀}(x) = AJ_{x₀}(x) + AJ_{y₀}(x₀)`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A (`Pic⁰ X = ker deg`) and is
a direct formal prerequisite for Layer F's normalized Abel-Jacobi morphism `aj : X ⟶ Jac X`,
where choosing a rational base point forces `x₀ ↦ 0` and changing that choice should be a
translation.  No external mathematics is vendored; the proofs use only the existing
`WeilDivisor`, `OrderSystem.divisorClass`, and abstract Abel-Jacobi API.
-/

@[expose] public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

/-! ### Class-level base-point changes -/

namespace OrderSystem

variable (S : OrderSystem X G)

/-- The degree-zero class `[x₀] - [y₀]` measuring the translation between Abel-Jacobi maps
normalized at two weight-one base points. -/
noncomputable def weightedBasepointChangeClass (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ : X} (_hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) : picZero w hdeg :=
  S.weightedAbelJacobiClass w hdeg hy₀ x₀

@[simp]
lemma coe_weightedBasepointChangeClass (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) :
    (S.weightedBasepointChangeClass w hdeg hx₀ hy₀ : S.ClassGroup) =
      S.divisorClass (pointDifference x₀ y₀) :=
  by
    simp [weightedBasepointChangeClass,
      weightedPointBaseDifference_eq_pointDifference_of_weight_eq_one hx₀]

@[simp]
lemma weightedBasepointChangeClass_self (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) :
    S.weightedBasepointChangeClass w hdeg hx₀ hx₀ = 0 := by
  exact S.weightedAbelJacobiClass_base w hdeg hx₀

/-- Reversing the two base points negates the base-point-change class. -/
lemma weightedBasepointChangeClass_swap (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) :
    S.weightedBasepointChangeClass w hdeg hy₀ hx₀ =
      -S.weightedBasepointChangeClass w hdeg hx₀ hy₀ := by
  apply Subtype.ext
  simp only [coe_weightedBasepointChangeClass, NegMemClass.coe_neg]
  rw [← map_neg, ← pointDifference_swap]

/-- Base-point-change classes compose: the translation from `x₀` to `z₀` is the sum of the
translations from `x₀` to `y₀` and from `y₀` to `z₀`. -/
lemma weightedBasepointChangeClass_add (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ z₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) (hz₀ : w z₀ = 1) :
    S.weightedBasepointChangeClass w hdeg hx₀ hy₀ +
        S.weightedBasepointChangeClass w hdeg hy₀ hz₀ =
      S.weightedBasepointChangeClass w hdeg hx₀ hz₀ := by
  apply Subtype.ext
  simp only [coe_weightedBasepointChangeClass, AddMemClass.coe_add]
  rw [← map_add, pointDifference_add_pointDifference_cancel]

/-- Changing the Abel-Jacobi base point from `x₀` to `y₀` adds `w(x)` times the class
`[x₀] - [y₀]`. This is the weighted closed-point form, where `w(x)` is the residue degree. -/
lemma weightedAbelJacobiClass_change_base (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) (x : X) :
    S.weightedAbelJacobiClass w hdeg hy₀ x =
      S.weightedAbelJacobiClass w hdeg hx₀ x +
      w x • S.weightedBasepointChangeClass w hdeg hx₀ hy₀ := by
  apply Subtype.ext
  simp only [coe_weightedAbelJacobiClass, coe_weightedBasepointChangeClass,
    AddMemClass.coe_add, AddSubgroupClass.coe_zsmul]
  rw [← map_zsmul, ← map_add, ← weightedPointBaseDifference_change_base]

/-- The base-point-change class is the Abel-Jacobi class of the old base point with respect to
the new base point. -/
lemma weightedAbelJacobiClass_base_eq_basepointChangeClass (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) :
    S.weightedAbelJacobiClass w hdeg hy₀ x₀ =
      S.weightedBasepointChangeClass w hdeg hx₀ hy₀ := by
  rfl

/-- The base-point-change class equals the Abel-Jacobi class of the old base point with respect
to the new base point. -/
lemma weightedBasepointChangeClass_eq_abelJacobiClass (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) :
    S.weightedBasepointChangeClass w hdeg hx₀ hy₀ =
      S.weightedAbelJacobiClass w hdeg hy₀ x₀ := by
  rfl

/-- In the class group, the difference between two weighted Abel-Jacobi classes with different
base points is `w(x)` times the class `[x₀] - [y₀]`. -/
lemma weightedAbelJacobiClass_sub_change_base_coe (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (x : X) :
    (S.weightedAbelJacobiClass w hdeg hy₀ x : S.ClassGroup) -
        (S.weightedAbelJacobiClass w hdeg hx₀ x : S.ClassGroup) =
      w x • S.divisorClass (pointDifference x₀ y₀) := by
  rw [coe_weightedAbelJacobiClass, coe_weightedAbelJacobiClass, ← map_zsmul, ← map_sub,
    weightedPointBaseDifference_sub_change_base]

/-! ### Unweighted specialization -/

/-- The unweighted base-point-change class `[x₀] - [y₀]` in the abstract unweighted `Pic⁰`. -/
noncomputable def unweightedBasepointChangeClass (hdeg : S.IsUnweightedDegreeZero) (x₀ y₀ : X) :
    unweightedPicZero hdeg :=
  S.weightedBasepointChangeClass (fun _ => (1 : ℤ)) hdeg (x₀ := x₀) (y₀ := y₀) rfl rfl

@[simp]
lemma coe_unweightedBasepointChangeClass (hdeg : S.IsUnweightedDegreeZero) (x₀ y₀ : X) :
    (S.unweightedBasepointChangeClass hdeg x₀ y₀ : S.ClassGroup) =
      S.divisorClass (pointDifference x₀ y₀) :=
  by
    simp [unweightedBasepointChangeClass]

@[simp]
lemma unweightedBasepointChangeClass_self (hdeg : S.IsUnweightedDegreeZero) (x₀ : X) :
    S.unweightedBasepointChangeClass hdeg x₀ x₀ = 0 := by
  exact S.weightedBasepointChangeClass_self (fun _ : X => (1 : ℤ)) hdeg rfl

lemma unweightedBasepointChangeClass_swap (hdeg : S.IsUnweightedDegreeZero) (x₀ y₀ : X) :
    S.unweightedBasepointChangeClass hdeg y₀ x₀ =
      -S.unweightedBasepointChangeClass hdeg x₀ y₀ := by
  apply Subtype.ext
  simp only [coe_unweightedBasepointChangeClass, NegMemClass.coe_neg]
  rw [← map_neg, ← pointDifference_swap]

/-- Unweighted base-point-change classes compose additively. -/
lemma unweightedBasepointChangeClass_add (hdeg : S.IsUnweightedDegreeZero) (x₀ y₀ z₀ : X) :
    S.unweightedBasepointChangeClass hdeg x₀ y₀ +
        S.unweightedBasepointChangeClass hdeg y₀ z₀ =
      S.unweightedBasepointChangeClass hdeg x₀ z₀ := by
  apply Subtype.ext
  simp only [coe_unweightedBasepointChangeClass, AddMemClass.coe_add]
  rw [← map_add, pointDifference_add_pointDifference_cancel]

/-- Changing the base point in the unweighted abstract Abel-Jacobi class is translation by
`[x₀] - [y₀]`. -/
lemma unweightedAbelJacobiClass_change_base (hdeg : S.IsUnweightedDegreeZero) (x₀ y₀ x : X) :
    S.unweightedAbelJacobiClass hdeg y₀ x =
      S.unweightedAbelJacobiClass hdeg x₀ x +
        S.unweightedBasepointChangeClass hdeg x₀ y₀ := by
  apply Subtype.ext
  simp only [coe_unweightedAbelJacobiClass, coe_unweightedBasepointChangeClass,
    AddMemClass.coe_add]
  rw [← map_add]
  simp [pointDifference, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- The class `[x] - [y]` is the difference of two Abel-Jacobi classes with the same base point. -/
lemma unweightedAbelJacobiClass_sub_coe (hdeg : S.IsUnweightedDegreeZero) (x₀ x y : X) :
    (S.unweightedAbelJacobiClass hdeg x₀ x : S.ClassGroup) -
        (S.unweightedAbelJacobiClass hdeg x₀ y : S.ClassGroup) =
      S.divisorClass (pointDifference x y) := by
  rw [coe_unweightedAbelJacobiClass, coe_unweightedAbelJacobiClass, ← map_sub]
  simp [pointDifference, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- The unweighted Abel-Jacobi class based at `y` sends `x` to the base-point-change class
from `x` to `y`. -/
lemma unweightedAbelJacobiClass_eq_basepointChangeClass (hdeg : S.IsUnweightedDegreeZero)
    (x y : X) :
    S.unweightedAbelJacobiClass hdeg y x =
      S.unweightedBasepointChangeClass hdeg x y := by
  rfl

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
