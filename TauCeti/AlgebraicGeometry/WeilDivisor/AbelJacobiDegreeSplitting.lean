/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi
public import TauCeti.AlgebraicGeometry.WeilDivisor.DegreeSplitting

/-!
# Abel-Jacobi classes and the degree splitting

This file records how the abstract Abel-Jacobi divisor class from
`TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi` interacts with the class-group splitting
from `TauCeti.AlgebraicGeometry.WeilDivisor.DegreeSplitting`.

For an order system whose principal divisors have weighted degree zero, a weight-one base point
`x₀` splits the divisor class group as

`Cl(X) ≃+ Pic⁰(X) × ℤ`.

Under this splitting, the class of a point divisor `[x]` has `Pic⁰` component equal to the
weighted Abel-Jacobi class of `x`, and degree component `w x`. Equivalently, the degree-corrected
class `[x] - w(x)[x₀]` maps to the Abel-Jacobi class together with degree `0`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, the "`Pic⁰ X = ker deg`
(as an abstract group)" item and the rational-point degree splitting used by the later
normalized Abel-Jacobi morphism. No external mathematics is vendored; the proofs combine Tau
Ceti's existing `OrderSystem.picZero`, `weightedAbelJacobiClass`, and
`classGroupAddEquivPicZeroProdInt` APIs.
-/

@[expose] public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

namespace OrderSystem

variable (S : OrderSystem X G)

/-! ### Degree correction of point classes -/

/-- Correcting the degree of the point class `[x]` by the base point `x₀` gives exactly the
class-group representative of the weighted Abel-Jacobi class of `x`. -/
lemma degreeCorrection_divisorClass_ofPoint (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.degreeCorrection w h x₀ (S.divisorClass (ofPoint x)) =
      (S.weightedAbelJacobiClass w h hx₀ x : S.ClassGroup) := by
  classical
  rw [degreeCorrection_apply, weightedDegreeClass_divisorClass_ofPoint,
    coe_weightedAbelJacobiClass]
  rw [← map_zsmul, ← map_sub]
  congr 1
  ext y
  rw [coeff_sub, coeff_weightedPointBaseDifference]
  change (ofPoint x) y - (w x • ofPoint x₀) y =
    (if y = x then 1 else 0) - if y = x₀ then w x else 0
  rw [show (ofPoint x) y = coeff (ofPoint x) y by rfl,
    show (w x • ofPoint x₀) y = w x * coeff (ofPoint x₀) y by rfl]
  by_cases hyx : y = x
  · subst y
    by_cases hx₀ : x = x₀
    · simp [hx₀]
    · simp [hx₀]
  · by_cases hy₀ : y = x₀
    · subst y
      have hx₀ : x₀ ≠ x := hyx
      simp [hx₀]
    · simp [hyx, hy₀]

/-- A class already in `Pic⁰` is unchanged by degree correction. -/
lemma degreeCorrection_eq_self_of_mem_picZero (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    (x₀ : X) {c : S.ClassGroup} (hc : c ∈ picZero w h) :
    S.degreeCorrection w h x₀ c = c := by
  rw [degreeCorrection_apply, (mem_picZero w h).mp hc, zero_zsmul, sub_zero]

/-- The degree correction of a coerced `Pic⁰` class is the same class in the ambient class
group. -/
@[simp]
lemma degreeCorrection_coe_picZero (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    (x₀ : X) (p : picZero w h) :
    S.degreeCorrection w h x₀ (p : S.ClassGroup) = p :=
  S.degreeCorrection_eq_self_of_mem_picZero w h x₀ p.property

/-! ### Weighted splitting formulas -/

/-- Under the splitting `Cl(X) ≃+ Pic⁰ × ℤ`, the class of the point divisor `[x]` has
`Pic⁰` component the weighted Abel-Jacobi class of `x`, and degree component `w x`. -/
@[simp]
lemma classGroupAddEquivPicZeroProdInt_divisorClass_ofPoint (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.classGroupAddEquivPicZeroProdInt w h hx₀ (S.divisorClass (ofPoint x)) =
      (S.weightedAbelJacobiClass w h hx₀ x, w x) := by
  rw [classGroupAddEquivPicZeroProdInt_apply, weightedDegreeClass_divisorClass_ofPoint]
  apply Prod.ext
  · apply Subtype.ext
    exact S.degreeCorrection_divisorClass_ofPoint w h hx₀ x
  · rfl

/-- Under the splitting `Cl(X) ≃+ Pic⁰ × ℤ`, a coerced weighted Abel-Jacobi class has degree
zero and `Pic⁰` component itself. -/
@[simp]
lemma classGroupAddEquivPicZeroProdInt_coe_weightedAbelJacobiClass (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.classGroupAddEquivPicZeroProdInt w h hx₀
        (S.weightedAbelJacobiClass w h hx₀ x : S.ClassGroup) =
      (S.weightedAbelJacobiClass w h hx₀ x, 0) := by
  rw [classGroupAddEquivPicZeroProdInt_apply]
  apply Prod.ext
  · apply Subtype.ext
    exact S.degreeCorrection_coe_picZero w h x₀ (S.weightedAbelJacobiClass w h hx₀ x)
  · exact (mem_picZero w h).mp (S.weightedAbelJacobiClass w h hx₀ x).property

/-- The degree-corrected point divisor `[x] - w(x)[x₀]` maps to the weighted Abel-Jacobi class
and degree `0` under the splitting `Cl(X) ≃+ Pic⁰ × ℤ`. -/
@[simp]
lemma classGroupAddEquivPicZeroProdInt_divisorClass_weightedPointBaseDifference
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.classGroupAddEquivPicZeroProdInt w h hx₀
        (S.divisorClass (weightedPointBaseDifference w x₀ x)) =
      (S.weightedAbelJacobiClass w h hx₀ x, 0) := by
  rw [← S.coe_weightedAbelJacobiClass w h hx₀ x,
    S.classGroupAddEquivPicZeroProdInt_coe_weightedAbelJacobiClass w h hx₀ x]

/-- The inverse splitting reconstructs the point class `[x]` from its weighted Abel-Jacobi
component and its degree `w x`. -/
@[simp]
lemma classGroupAddEquivPicZeroProdInt_symm_weightedAbelJacobiClass (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    (S.classGroupAddEquivPicZeroProdInt w h hx₀).symm
        (S.weightedAbelJacobiClass w h hx₀ x, w x) =
      S.divisorClass (ofPoint x) := by
  rw [← S.classGroupAddEquivPicZeroProdInt_divisorClass_ofPoint w h hx₀ x]
  simp

/-! ### Unweighted specialization -/

/-- In the unweighted specialization, correcting the degree of `[x]` by `x₀` gives the ambient
class of the unweighted Abel-Jacobi class. -/
lemma degreeCorrection_divisorClass_ofPoint_unweighted (h : S.IsUnweightedDegreeZero)
    (x₀ x : X) :
    S.degreeCorrection (fun _ : X => (1 : ℤ)) h x₀ (S.divisorClass (ofPoint x)) =
      (S.unweightedAbelJacobiClass h x₀ x : S.ClassGroup) := by
  simpa [unweightedAbelJacobiClass] using
    S.degreeCorrection_divisorClass_ofPoint (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl x

/-- Under the unweighted splitting `Cl(X) ≃+ Pic⁰ × ℤ`, the class of `[x]` has `Pic⁰`
component the unweighted Abel-Jacobi class of `x`, and degree component `1`. -/
@[simp]
lemma classGroupAddEquivUnweightedPicZeroProdInt_divisorClass_ofPoint
    (h : S.IsUnweightedDegreeZero) (x₀ x : X) :
    S.classGroupAddEquivUnweightedPicZeroProdInt h x₀ (S.divisorClass (ofPoint x)) =
      (S.unweightedAbelJacobiClass h x₀ x, 1) := by
  rw [classGroupAddEquivUnweightedPicZeroProdInt]
  change S.classGroupAddEquivPicZeroProdInt (fun _ : X => (1 : ℤ)) h rfl
      (S.divisorClass (ofPoint x)) =
    (S.weightedAbelJacobiClass (fun _ : X => (1 : ℤ)) h rfl x, 1)
  exact S.classGroupAddEquivPicZeroProdInt_divisorClass_ofPoint
    (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl x

/-- Under the unweighted splitting, a coerced unweighted Abel-Jacobi class has degree zero and
`Pic⁰` component itself. -/
@[simp]
lemma classGroupAddEquivUnweightedPicZeroProdInt_coe_unweightedAbelJacobiClass
    (h : S.IsUnweightedDegreeZero) (x₀ x : X) :
    S.classGroupAddEquivUnweightedPicZeroProdInt h x₀
        (S.unweightedAbelJacobiClass h x₀ x : S.ClassGroup) =
      (S.unweightedAbelJacobiClass h x₀ x, 0) := by
  rw [classGroupAddEquivUnweightedPicZeroProdInt]
  change S.classGroupAddEquivPicZeroProdInt (fun _ : X => (1 : ℤ)) h rfl
      (S.weightedAbelJacobiClass (fun _ : X => (1 : ℤ)) h rfl x : S.ClassGroup) =
    (S.weightedAbelJacobiClass (fun _ : X => (1 : ℤ)) h rfl x, 0)
  exact S.classGroupAddEquivPicZeroProdInt_coe_weightedAbelJacobiClass
    (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl x

/-- The inverse unweighted splitting reconstructs the point class `[x]` from its Abel-Jacobi
component and degree `1`. -/
@[simp]
lemma classGroupAddEquivUnweightedPicZeroProdInt_symm_unweightedAbelJacobiClass
    (h : S.IsUnweightedDegreeZero) (x₀ x : X) :
    (S.classGroupAddEquivUnweightedPicZeroProdInt h x₀).symm
        (S.unweightedAbelJacobiClass h x₀ x, 1) =
      S.divisorClass (ofPoint x) := by
  rw [← S.classGroupAddEquivUnweightedPicZeroProdInt_divisorClass_ofPoint h x₀ x]
  simp

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
