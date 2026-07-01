/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobiSum
public import TauCeti.AlgebraicGeometry.WeilDivisor.PicZeroQuotient

/-!
# Abel-Jacobi sums through the degree-zero quotient

This file connects two existing Layer A models in the Jacobian roadmap.  The file
`WeilDivisor.AbelJacobiSum` defines the formal Abel-Jacobi sum of a divisor as an element of
the abstract `Pic⁰`, while `WeilDivisor.PicZeroQuotient` identifies `Pic⁰` with degree-zero
divisors modulo principal divisors.  Here we record the corresponding quotient representative:

`D ↦ [D - deg(D) • x₀]` in `(degree-zero divisors) / (principal divisors)`.

Under the quotient equivalence, this representative maps to the existing Abel-Jacobi divisor
class.  For point divisors this recovers the point Abel-Jacobi class.  This is the quotient-level
form of the Abel map `D ↦ 𝒪_X(D - d·x₀)` used later for symmetric powers in the construction of
the Jacobian.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, specifically the "`Pic⁰ X =
ker deg` (as an abstract group)" item and the Layer D/F Abel-map prerequisite
`D ↦ 𝒪_X(D - d·x₀)`.  No external mathematics is vendored; the proofs reuse Tau Ceti's existing
`weightedAbelJacobiDivisorClass` and quotient equivalence
`weightedDegreeZeroQuotientEquivPicZero`.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

noncomputable section

/-! ### Weighted quotient representatives -/

/-- The degree-corrected representative of a divisor in the weighted degree-zero divisor group.

For a weight-one base point `x₀`, this is `D - weightedDegree(D) • [x₀]`, viewed as a
weighted-degree-zero divisor. -/
@[expose] def weightedAbelJacobiDegreeZeroDivisor (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) : weightedDegreeZeroSubgroup w :=
  ⟨D - weightedDegree w D • ofPoint x₀, by
    rw [mem_weightedDegreeZeroSubgroup, map_sub, map_zsmul, weightedDegree_ofPoint, hx₀]
    simp⟩

@[simp]
lemma coe_weightedAbelJacobiDegreeZeroDivisor (w : X → ℤ) {x₀ : X}
    (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    (weightedAbelJacobiDegreeZeroDivisor w hx₀ D : WeilDivisor X) =
      D - weightedDegree w D • ofPoint x₀ :=
  rfl

/-- The quotient class of the degree-corrected representative
`D - weightedDegree(D) • [x₀]`. -/
@[expose] def weightedAbelJacobiQuotientClass (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) :
    weightedDegreeZeroSubgroup w ⧸ S.principalSubgroupOfWeightedDegreeZero w :=
  QuotientAddGroup.mk (weightedAbelJacobiDegreeZeroDivisor w hx₀ D)

@[simp]
lemma weightedAbelJacobiQuotientClass_mk (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
      QuotientAddGroup.mk (weightedAbelJacobiDegreeZeroDivisor w hx₀ D) :=
  rfl

/-- The quotient representative maps to the weighted Abel-Jacobi divisor class under the
degree-zero quotient equivalence. -/
@[simp]
lemma weightedDegreeZeroQuotientEquivPicZero_weightedAbelJacobiQuotientClass
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) :
    S.weightedDegreeZeroQuotientEquivPicZero w h
        (S.weightedAbelJacobiQuotientClass w hx₀ D) =
      S.weightedAbelJacobiDivisorClass w h hx₀ D := by
  rw [weightedAbelJacobiQuotientClass_mk, weightedDegreeZeroQuotientEquivPicZero_mk]
  apply Subtype.ext
  rw [coe_weightedDegreeZeroClassHom_apply, coe_weightedAbelJacobiDivisorClass_apply,
    coe_weightedAbelJacobiDegreeZeroDivisor]

/-- For point divisors, the quotient representative maps to the point Abel-Jacobi class. -/
@[simp]
lemma weightedDegreeZeroQuotientEquivPicZero_weightedAbelJacobiQuotientClass_ofPoint
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.weightedDegreeZeroQuotientEquivPicZero w h
        (S.weightedAbelJacobiQuotientClass w hx₀ (ofPoint x)) =
      S.weightedAbelJacobiClass w h hx₀ x := by
  rw [S.weightedDegreeZeroQuotientEquivPicZero_weightedAbelJacobiQuotientClass,
    S.weightedAbelJacobiDivisorClass_ofPoint]

/-- The base-point divisor represents zero in the degree-zero quotient. -/
@[simp]
lemma weightedAbelJacobiQuotientClass_ofPoint_base (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1) :
    S.weightedAbelJacobiQuotientClass w hx₀ (ofPoint x₀) = 0 := by
  rw [weightedAbelJacobiQuotientClass_mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  rw [mem_principalSubgroupOfWeightedDegreeZero, coe_weightedAbelJacobiDegreeZeroDivisor,
    weightedDegree_ofPoint, hx₀, one_zsmul, sub_self]
  exact S.principalSubgroup.zero_mem

/-! ### Unweighted quotient representatives -/

/-- The degree-corrected representative of a divisor in the unweighted degree-zero divisor
group.  This is `D - degree(D) • [x₀]`. -/
@[expose] def unweightedAbelJacobiDegreeZeroDivisor (x₀ : X) (D : WeilDivisor X) :
    degreeZeroSubgroup X :=
  ⟨D - degree D • ofPoint x₀, by
    rw [mem_degreeZeroSubgroup, map_sub, map_zsmul, degree_ofPoint]
    simp⟩

@[simp]
lemma coe_unweightedAbelJacobiDegreeZeroDivisor (x₀ : X) (D : WeilDivisor X) :
    (unweightedAbelJacobiDegreeZeroDivisor x₀ D : WeilDivisor X) =
      D - degree D • ofPoint x₀ :=
  rfl

/-- The quotient class of the unweighted degree-corrected representative
`D - degree(D) • [x₀]`. -/
@[expose] def unweightedAbelJacobiQuotientClass (x₀ : X) (D : WeilDivisor X) :
    degreeZeroSubgroup X ⧸ S.principalSubgroupOfDegreeZero :=
  QuotientAddGroup.mk (unweightedAbelJacobiDegreeZeroDivisor x₀ D)

@[simp]
lemma unweightedAbelJacobiQuotientClass_mk (x₀ : X) (D : WeilDivisor X) :
    S.unweightedAbelJacobiQuotientClass x₀ D =
      QuotientAddGroup.mk (unweightedAbelJacobiDegreeZeroDivisor x₀ D) :=
  rfl

/-- The quotient representative maps to the unweighted Abel-Jacobi divisor class under the
degree-zero quotient equivalence. -/
@[simp]
lemma degreeZeroQuotientEquivUnweightedPicZero_unweightedAbelJacobiQuotientClass
    (h : S.IsUnweightedDegreeZero) (x₀ : X) (D : WeilDivisor X) :
    S.degreeZeroQuotientEquivUnweightedPicZero h
        (S.unweightedAbelJacobiQuotientClass x₀ D) =
      S.unweightedAbelJacobiDivisorClass h x₀ D := by
  rw [unweightedAbelJacobiQuotientClass_mk, degreeZeroQuotientEquivUnweightedPicZero_mk]
  apply Subtype.ext
  rw [coe_degreeZeroClassHom_apply, coe_unweightedAbelJacobiDivisorClass_apply,
    coe_unweightedAbelJacobiDegreeZeroDivisor]

/-- For point divisors, the unweighted quotient representative maps to the point
Abel-Jacobi class. -/
@[simp]
lemma degreeZeroQuotientEquivUnweightedPicZero_unweightedAbelJacobiQuotientClass_ofPoint
    (h : S.IsUnweightedDegreeZero) (x₀ x : X) :
    S.degreeZeroQuotientEquivUnweightedPicZero h
        (S.unweightedAbelJacobiQuotientClass x₀ (ofPoint x)) =
      S.unweightedAbelJacobiClass h x₀ x := by
  rw [S.degreeZeroQuotientEquivUnweightedPicZero_unweightedAbelJacobiQuotientClass,
    S.unweightedAbelJacobiDivisorClass_ofPoint]

/-- The unweighted base-point divisor represents zero in the degree-zero quotient. -/
@[simp]
lemma unweightedAbelJacobiQuotientClass_ofPoint_base (x₀ : X) :
    S.unweightedAbelJacobiQuotientClass x₀ (ofPoint x₀) = 0 := by
  rw [unweightedAbelJacobiQuotientClass_mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  rw [mem_principalSubgroupOfDegreeZero, coe_unweightedAbelJacobiDegreeZeroDivisor,
    degree_ofPoint, one_zsmul, sub_self]
  exact S.principalSubgroup.zero_mem

end

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
