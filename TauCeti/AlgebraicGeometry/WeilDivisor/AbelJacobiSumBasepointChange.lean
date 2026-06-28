/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobiSum
public import TauCeti.AlgebraicGeometry.WeilDivisor.BasepointChange
import Mathlib.Tactic.Abel

/-!
# Changing the base point in Abel-Jacobi divisor sums

This file combines the point-level base-point-change API for the abstract Abel-Jacobi class
with the divisor-level Abel-Jacobi sum.

For an order system whose principal divisors have weighted degree zero, and two weight-one
base points `x₀` and `y₀`, the divisor-level Abel-Jacobi sums satisfy

`AJ_{y₀}(D) = AJ_{x₀}(D) + deg(D) • ([x₀] - [y₀])`.

Here `deg(D)` is the weighted degree for the chosen weight `w`.  The unweighted specialization
is the same formula with the ordinary degree.  This is the formal divisor-class bookkeeping
behind the later Abel maps `D ↦ 𝒪_X(D - d·x₀)` used in the Jacobian roadmap: changing the
normalizing base point translates the degree-`d` Abel map by `d` times the class of
`[x₀] - [y₀]`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "`Pic⁰ X = ker deg` (as
an abstract group)", and supplies a direct prerequisite for the Layer D/F Abel-map lane
`D ↦ 𝒪_X(D - d·x₀)`.  No external mathematics is vendored; the proofs reuse Tau Ceti's
existing `weightedAbelJacobiDivisorClass`, `weightedBasepointChangeClass`, and divisor-class
API.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

namespace OrderSystem

variable (S : OrderSystem X G)

private lemma sub_zsmul_ofPoint_add_zsmul_pointDifference
    (D : WeilDivisor X) (n : ℤ) (x₀ y₀ : X) :
    D - n • ofPoint x₀ + n • pointDifference x₀ y₀ = D - n • ofPoint y₀ := by
  rw [pointDifference, zsmul_sub, sub_eq_add_neg]
  abel

private lemma sub_sub_zsmul_ofPoint_eq_zsmul_pointDifference
    (D : WeilDivisor X) (n : ℤ) (x₀ y₀ : X) :
    (D - n • ofPoint y₀) - (D - n • ofPoint x₀) =
      n • pointDifference x₀ y₀ := by
  rw [pointDifference, zsmul_sub, sub_eq_add_neg]
  abel

/-! ### Weighted base-point change for divisor sums -/

/-- Changing the base point in the weighted Abel-Jacobi sum adds the weighted degree times the
base-point-change class.

Geometrically, for the residue-degree weight and rational base points `x₀`, `y₀`, this is the
formal divisor-class identity
`[D - deg(D)y₀] = [D - deg(D)x₀] + deg(D)[x₀ - y₀]` in `Pic⁰`. -/
lemma weightedAbelJacobiDivisorClass_change_base (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (D : WeilDivisor X) :
    S.weightedAbelJacobiDivisorClass w h hy₀ D =
      S.weightedAbelJacobiDivisorClass w h hx₀ D +
        weightedDegree w D • S.weightedBasepointChangeClass w h (hx₀.trans hy₀.symm) := by
  apply Subtype.ext
  simp only [coe_weightedAbelJacobiDivisorClass_apply, coe_weightedBasepointChangeClass,
    AddMemClass.coe_add, AddSubgroupClass.coe_zsmul]
  rw [← map_zsmul, ← map_add,
    sub_zsmul_ofPoint_add_zsmul_pointDifference (D := D) (n := weightedDegree w D)]

/-- In the class group, the difference between weighted Abel-Jacobi divisor sums with two
base points is the weighted degree times the class `[x₀] - [y₀]`. -/
lemma weightedAbelJacobiDivisorClass_sub_change_base_coe (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (D : WeilDivisor X) :
    (S.weightedAbelJacobiDivisorClass w h hy₀ D : S.ClassGroup) -
        (S.weightedAbelJacobiDivisorClass w h hx₀ D : S.ClassGroup) =
      weightedDegree w D • S.divisorClass (pointDifference x₀ y₀) := by
  rw [coe_weightedAbelJacobiDivisorClass_apply, coe_weightedAbelJacobiDivisorClass_apply,
    ← map_zsmul, ← map_sub,
    sub_sub_zsmul_ofPoint_eq_zsmul_pointDifference (D := D) (n := weightedDegree w D)]

/-- If a divisor has weighted degree zero, its weighted Abel-Jacobi sum is independent of the
choice of weight-one base point. -/
lemma weightedAbelJacobiDivisorClass_eq_of_weightedDegree_eq_zero (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    {D : WeilDivisor X} (hD : weightedDegree w D = 0) :
    S.weightedAbelJacobiDivisorClass w h hx₀ D =
      S.weightedAbelJacobiDivisorClass w h hy₀ D := by
  rw [S.weightedAbelJacobiDivisorClass_change_base w h hx₀ hy₀ D, hD, zero_zsmul,
    add_zero]

/-! ### Unweighted specialization -/

/-- Changing the base point in the unweighted Abel-Jacobi divisor sum adds the ordinary degree
times the corresponding point Abel-Jacobi class. -/
lemma unweightedAbelJacobiDivisorClass_change_base (h : S.IsUnweightedDegreeZero)
    (x₀ y₀ : X) (D : WeilDivisor X) :
    S.unweightedAbelJacobiDivisorClass h y₀ D =
      S.unweightedAbelJacobiDivisorClass h x₀ D +
        degree D • S.unweightedAbelJacobiClass h y₀ x₀ := by
  have hchange :=
    S.weightedAbelJacobiDivisorClass_change_base (fun _ : X => (1 : ℤ))
      (show S.IsWeightedDegreeZero (fun _ : X => (1 : ℤ)) from h)
      (x₀ := x₀) (y₀ := y₀) rfl rfl D
  rw [S.weightedBasepointChangeClass_eq_abelJacobiClass (fun _ : X => (1 : ℤ))
    (show S.IsWeightedDegreeZero (fun _ : X => (1 : ℤ)) from h)
    (x₀ := x₀) (y₀ := y₀) rfl rfl] at hchange
  apply Subtype.ext
  have hchange' := congr_arg Subtype.val hchange
  simpa only [coe_unweightedAbelJacobiDivisorClass_apply, coe_weightedAbelJacobiDivisorClass_apply,
    weightedDegree_one_eq_degree, coe_unweightedAbelJacobiClass, coe_weightedAbelJacobiClass,
    weightedPointBaseDifference_eq_pointDifference, AddMemClass.coe_add,
    AddSubgroupClass.coe_zsmul] using hchange'

/-- In the class group, the difference between unweighted Abel-Jacobi divisor sums with two
base points is the degree times `[x₀] - [y₀]`. -/
lemma unweightedAbelJacobiDivisorClass_sub_change_base_coe (h : S.IsUnweightedDegreeZero)
    (x₀ y₀ : X) (D : WeilDivisor X) :
    (S.unweightedAbelJacobiDivisorClass h y₀ D : S.ClassGroup) -
        (S.unweightedAbelJacobiDivisorClass h x₀ D : S.ClassGroup) =
      degree D • S.divisorClass (pointDifference x₀ y₀) := by
  rw [coe_unweightedAbelJacobiDivisorClass_apply, coe_unweightedAbelJacobiDivisorClass_apply,
    ← map_zsmul, ← map_sub,
    sub_sub_zsmul_ofPoint_eq_zsmul_pointDifference (D := D) (n := degree D)]

/-- An unweighted degree-zero divisor has an Abel-Jacobi sum independent of the base point. -/
lemma unweightedAbelJacobiDivisorClass_eq_of_degree_eq_zero (h : S.IsUnweightedDegreeZero)
    (x₀ y₀ : X) {D : WeilDivisor X} (hD : degree D = 0) :
    S.unweightedAbelJacobiDivisorClass h x₀ D =
      S.unweightedAbelJacobiDivisorClass h y₀ D := by
  rw [S.unweightedAbelJacobiDivisorClass_change_base h x₀ y₀ D, hD, zero_zsmul, add_zero]

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
