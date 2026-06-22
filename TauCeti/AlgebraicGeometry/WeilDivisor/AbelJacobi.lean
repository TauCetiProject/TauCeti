/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.AlgebraicGeometry.WeilDivisor.Principal

/-!
# The abstract Abel-Jacobi divisor class map

This file adds the point-level divisor-class shadow of the Abel-Jacobi map to the formal
Layer A divisor API.  Once the Jacobian is constructed as `Pic⁰(X)`, the Abel-Jacobi morphism
attached to a base point `x₀` sends a point `x` to the degree-zero line bundle
`𝒪_X(x - x₀)` over an algebraically closed field.  For closed points over a non-algebraically
closed field, the degree-corrected divisor is `x - deg(x) x₀`, when `x₀` has residue degree
`1`.

Here the geometry is still abstracted to an `OrderSystem` and an integer-valued weight
`w : X → ℤ`.  We define the formal divisor `[x] - w(x)[x₀]`, prove it has weighted degree zero
when `w x₀ = 1`, and take its divisor class as an element of the abstract `Pic⁰` subgroup
already built in `WeilDivisor.Principal`.  The unweighted specialization recovers
`x ↦ [x] - [x₀]`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A (`Pic⁰ X = ker deg`) as a
direct prerequisite for Layer F's Abel-Jacobi morphism `aj : X ⟶ Jac X`, while staying at the
formal divisor-class level available before line bundles, the Picard scheme, or the Jacobian
variety exist.  No external mathematics is vendored; this reuses Tau Ceti's `WeilDivisor`,
`OrderSystem.divisorClass`, and `OrderSystem.picZero` API.
-/

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

/-! ### Degree-corrected point divisors -/

/-- The divisor `[x] - w(x)[x₀]`.

For the geometric weight `w x = [κ(x) : k]` and a rational base point `x₀` with `w x₀ = 1`,
this is the degree-zero divisor underlying the Abel-Jacobi class of the closed point `x`.
In the algebraically closed/unweighted specialization, use
`unweightedPointBaseDifference`, which is definitionally `[x] - [x₀]`. -/
noncomputable def weightedPointBaseDifference (w : X → ℤ) (x₀ x : X) : WeilDivisor X :=
  ofPoint x - w x • ofPoint x₀

@[simp]
lemma weightedPointBaseDifference_eq_pointDifference (x₀ x : X) :
    weightedPointBaseDifference (fun _ : X => (1 : ℤ)) x₀ x = pointDifference x x₀ := by
  simp [weightedPointBaseDifference, pointDifference]

@[simp]
lemma coeff_weightedPointBaseDifference [DecidableEq X] (w : X → ℤ) (x₀ x y : X) :
    coeff (weightedPointBaseDifference w x₀ x) y =
      (if y = x then 1 else 0) - if y = x₀ then w x else 0 := by
  by_cases hyx : y = x
  · subst y
    by_cases hx₀ : x = x₀ <;> simp [weightedPointBaseDifference, ofPoint, coeff, hx₀]
  · by_cases hy₀ : y = x₀
    · subst y
      have hx₀ : x₀ ≠ x := by simpa using hyx
      simp [weightedPointBaseDifference, ofPoint, coeff, hx₀]
    · simp [weightedPointBaseDifference, ofPoint, coeff, hyx, hy₀]

/-- The support of `[x] - w(x)[x₀]` is contained in `{x, x₀}`. -/
lemma support_weightedPointBaseDifference_subset [DecidableEq X] (w : X → ℤ) (x₀ x : X) :
    (weightedPointBaseDifference w x₀ x).support ⊆ {x, x₀} := by
  intro y hy
  rw [Finset.mem_insert, Finset.mem_singleton]
  by_contra hyx
  push Not at hyx
  exact Finsupp.mem_support_iff.mp hy (by
    simp [weightedPointBaseDifference, ofPoint, hyx.1, hyx.2])

/-- If the base point has weight `1`, the divisor `[x₀] - w(x₀)[x₀]` is zero. -/
@[simp]
lemma weightedPointBaseDifference_self {w : X → ℤ} {x₀ : X} (hx₀ : w x₀ = 1) :
    weightedPointBaseDifference w x₀ x₀ = 0 := by
  simp [weightedPointBaseDifference, hx₀]

/-- The weighted degree of `[x] - w(x)[x₀]` is `w(x) * (1 - w(x₀))`. -/
@[simp]
lemma weightedDegree_weightedPointBaseDifference (w : X → ℤ) (x₀ x : X) :
    weightedDegree w (weightedPointBaseDifference w x₀ x) = w x * (1 - w x₀) := by
  simp [weightedPointBaseDifference]
  ring

/-- If the base point has weight `1`, then `[x] - w(x)[x₀]` has weighted degree zero. -/
@[simp]
lemma weightedPointBaseDifference_mem_weightedDegreeZeroSubgroup {w : X → ℤ} {x₀ : X}
    (hx₀ : w x₀ = 1) (x : X) :
    weightedPointBaseDifference w x₀ x ∈ weightedDegreeZeroSubgroup w := by
  simp [hx₀]

/-- The unweighted divisor `[x] - [x₀]`, the algebraically closed form of the Abel-Jacobi
point divisor. -/
noncomputable abbrev unweightedPointBaseDifference (x₀ x : X) : WeilDivisor X :=
  weightedPointBaseDifference (fun _ : X => (1 : ℤ)) x₀ x

@[simp]
lemma unweightedPointBaseDifference_eq_pointDifference (x₀ x : X) :
    unweightedPointBaseDifference x₀ x = pointDifference x x₀ :=
  weightedPointBaseDifference_eq_pointDifference x₀ x

@[simp]
lemma degree_unweightedPointBaseDifference (x₀ x : X) :
    degree (unweightedPointBaseDifference x₀ x) = 0 := by
  simp

/-- The unweighted point divisor `[x] - [x₀]` lies in the degree-zero divisor subgroup. -/
@[simp]
lemma unweightedPointBaseDifference_mem_degreeZeroSubgroup (x₀ x : X) :
    unweightedPointBaseDifference x₀ x ∈ degreeZeroSubgroup X := by
  simp

/-! ### Abel-Jacobi classes in the abstract Picard group -/

namespace OrderSystem

variable (S : OrderSystem X G)

/-- The weighted abstract Abel-Jacobi class of a point.

For a geometric weight `w x = [κ(x) : k]` and a rational base point `x₀` (`w x₀ = 1`), this is
the class of `[x] - w(x)[x₀]` in the abstract weighted-degree-zero Picard group. -/
noncomputable def weightedAbelJacobiClass (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (x : X) : picZero w hdeg :=
  ⟨S.divisorClass (weightedPointBaseDifference w x₀ x), by
    rw [divisorClass_mem_picZero]
    exact weightedPointBaseDifference_mem_weightedDegreeZeroSubgroup hx₀ x⟩

@[simp]
lemma coe_weightedAbelJacobiClass (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    (S.weightedAbelJacobiClass w hdeg hx₀ x : S.ClassGroup) =
      S.divisorClass (weightedPointBaseDifference w x₀ x) :=
  rfl

/-- The weighted abstract Abel-Jacobi class of the base point is zero. -/
@[simp]
lemma weightedAbelJacobiClass_base (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) :
    S.weightedAbelJacobiClass w hdeg hx₀ x₀ = 0 := by
  apply Subtype.ext
  simp [weightedAbelJacobiClass, hx₀]

/-- Equality of weighted Abel-Jacobi classes is equality of the corresponding divisor classes. -/
lemma weightedAbelJacobiClass_eq_iff_divisorClass (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) {x y : X} :
    S.weightedAbelJacobiClass w hdeg hx₀ x = S.weightedAbelJacobiClass w hdeg hx₀ y ↔
      S.divisorClass (weightedPointBaseDifference w x₀ x) =
        S.divisorClass (weightedPointBaseDifference w x₀ y) := by
  constructor
  · intro h
    exact congr_arg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Equality of weighted Abel-Jacobi classes is linear equivalence of the corresponding
degree-corrected point divisors. -/
lemma weightedAbelJacobiClass_eq_iff_linearlyEquivalent (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) {x y : X} :
    S.weightedAbelJacobiClass w hdeg hx₀ x = S.weightedAbelJacobiClass w hdeg hx₀ y ↔
      S.LinearlyEquivalent (weightedPointBaseDifference w x₀ x)
        (weightedPointBaseDifference w x₀ y) := by
  rw [S.weightedAbelJacobiClass_eq_iff_divisorClass w hdeg hx₀, S.divisorClass_eq_iff]

/-- The unweighted abstract Abel-Jacobi class `x ↦ [[x] - [x₀]]` in the abstract `Pic⁰`
subgroup. -/
noncomputable def unweightedAbelJacobiClass (hdeg : S.IsUnweightedDegreeZero) (x₀ x : X) :
    unweightedPicZero hdeg :=
  ⟨S.divisorClass (pointDifference x x₀), by simp⟩

@[simp]
lemma coe_unweightedAbelJacobiClass (hdeg : S.IsUnweightedDegreeZero) (x₀ x : X) :
    (S.unweightedAbelJacobiClass hdeg x₀ x : S.ClassGroup) =
      S.divisorClass (pointDifference x x₀) :=
  rfl

/-- The unweighted abstract Abel-Jacobi class sends the base point to zero. -/
@[simp]
lemma unweightedAbelJacobiClass_base (hdeg : S.IsUnweightedDegreeZero) (x₀ : X) :
    S.unweightedAbelJacobiClass hdeg x₀ x₀ = 0 := by
  apply Subtype.ext
  simp [unweightedAbelJacobiClass]

/-- Equality of unweighted Abel-Jacobi classes is equality of the corresponding divisor
classes. -/
lemma unweightedAbelJacobiClass_eq_iff_divisorClass (hdeg : S.IsUnweightedDegreeZero)
    (x₀ : X) {x y : X} :
    S.unweightedAbelJacobiClass hdeg x₀ x = S.unweightedAbelJacobiClass hdeg x₀ y ↔
      S.divisorClass (pointDifference x x₀) = S.divisorClass (pointDifference y x₀) := by
  constructor
  · intro h
    exact congr_arg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Equality of unweighted Abel-Jacobi classes is linear equivalence of the point-difference
divisors. -/
lemma unweightedAbelJacobiClass_eq_iff_linearlyEquivalent (hdeg : S.IsUnweightedDegreeZero)
    (x₀ : X) {x y : X} :
    S.unweightedAbelJacobiClass hdeg x₀ x = S.unweightedAbelJacobiClass hdeg x₀ y ↔
      S.LinearlyEquivalent (pointDifference x x₀) (pointDifference y x₀) := by
  rw [S.unweightedAbelJacobiClass_eq_iff_divisorClass hdeg x₀, S.divisorClass_eq_iff]

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
