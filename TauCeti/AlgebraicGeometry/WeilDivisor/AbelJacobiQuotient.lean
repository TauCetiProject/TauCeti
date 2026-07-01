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

private lemma ofPoint_eq_single_one (x : X) :
    ofPoint x = Finsupp.single x (1 : ℤ) := by
  ext y
  by_cases hy : y = x
  · subst y
    rw [coeff_ofPoint_self, coeff, Finsupp.single_eq_same]
  · rw [coeff_ofPoint_of_ne hy, coeff, Finsupp.single_eq_of_ne hy]

private lemma zsmul_ofPoint_eq_single (n : ℤ) (x : X) :
    n • ofPoint x = Finsupp.single x n := by
  rw [ofPoint_eq_single_one, Finsupp.smul_single_one]

/-! ### Weighted quotient representatives -/

/-- The degree-corrected representative of a divisor in the weighted degree-zero divisor group.

For a weight-one base point `x₀`, this is `D - weightedDegree(D) • [x₀]`, viewed as a
weighted-degree-zero divisor. -/
abbrev weightedAbelJacobiDegreeZeroDivisor (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
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
abbrev weightedAbelJacobiQuotientClass (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1) :
    WeilDivisor X →+
      weightedDegreeZeroSubgroup w ⧸ S.principalSubgroupOfWeightedDegreeZero w where
  toFun D := QuotientAddGroup.mk (weightedAbelJacobiDegreeZeroDivisor w hx₀ D)
  map_zero' := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    rw [mem_principalSubgroupOfWeightedDegreeZero, coe_weightedAbelJacobiDegreeZeroDivisor]
    simp
  map_add' D E := by
    have hdiv :
        weightedAbelJacobiDegreeZeroDivisor w hx₀ (D + E) =
          weightedAbelJacobiDegreeZeroDivisor w hx₀ D +
            weightedAbelJacobiDegreeZeroDivisor w hx₀ E := by
      ext x
      simp [map_add, add_zsmul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    change QuotientAddGroup.mk (weightedAbelJacobiDegreeZeroDivisor w hx₀ (D + E)) =
      QuotientAddGroup.mk (weightedAbelJacobiDegreeZeroDivisor w hx₀ D) +
        QuotientAddGroup.mk (weightedAbelJacobiDegreeZeroDivisor w hx₀ E)
    rw [hdiv]
    exact map_add (QuotientAddGroup.mk' (S.principalSubgroupOfWeightedDegreeZero w))
      (weightedAbelJacobiDegreeZeroDivisor w hx₀ D)
      (weightedAbelJacobiDegreeZeroDivisor w hx₀ E)

@[simp]
lemma weightedAbelJacobiQuotientClass_mk (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
      QuotientAddGroup.mk (weightedAbelJacobiDegreeZeroDivisor w hx₀ D) :=
  rfl

/-- The quotient Abel-Jacobi representative of a sum is the sum of the quotient
representatives. -/
@[simp]
lemma weightedAbelJacobiQuotientClass_add (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D E : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ (D + E) =
      S.weightedAbelJacobiQuotientClass w hx₀ D +
        S.weightedAbelJacobiQuotientClass w hx₀ E :=
  map_add (S.weightedAbelJacobiQuotientClass w hx₀) D E

/-- The quotient Abel-Jacobi representative of an integral multiple is the corresponding
multiple of the quotient representative. -/
@[simp]
lemma weightedAbelJacobiQuotientClass_zsmul (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (n : ℤ) (D : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ (n • D) =
      n • S.weightedAbelJacobiQuotientClass w hx₀ D :=
  map_zsmul (S.weightedAbelJacobiQuotientClass w hx₀) n D

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

/-- The quotient Abel-Jacobi representative of a finitely supported formal divisor is the
finite sum of the quotient representatives of its point divisors. -/
lemma weightedAbelJacobiQuotientClass_eq_sum (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
      D.sum fun x n => n • S.weightedAbelJacobiQuotientClass w hx₀ (ofPoint x) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero =>
      simp
  | single x n =>
      rw [Finsupp.sum_single_index]
      · rw [← zsmul_ofPoint_eq_single n x,
          S.weightedAbelJacobiQuotientClass_zsmul w hx₀ n (ofPoint x)]
      · simp
  | add D E hD hE =>
      rw [S.weightedAbelJacobiQuotientClass_add w hx₀, Finsupp.sum_add_index, hD, hE]
      · intro x
        simp
      · intro x a b
        simp [add_zsmul]

/-- The base-point divisor represents zero in the degree-zero quotient. -/
@[simp]
lemma weightedAbelJacobiQuotientClass_ofPoint_base (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1) :
    S.weightedAbelJacobiQuotientClass w hx₀ (ofPoint x₀) = 0 := by
  rw [weightedAbelJacobiQuotientClass_mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  rw [mem_principalSubgroupOfWeightedDegreeZero, coe_weightedAbelJacobiDegreeZeroDivisor,
    weightedDegree_ofPoint, hx₀, one_zsmul, sub_self]
  exact S.principalSubgroup.zero_mem

/-- A principal divisor has zero weighted quotient Abel-Jacobi representative. -/
@[simp]
lemma weightedAbelJacobiQuotientClass_principalDivisor (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (g : G) :
    S.weightedAbelJacobiQuotientClass w hx₀ (S.principalDivisor g) = 0 := by
  apply (S.weightedDegreeZeroQuotientEquivPicZero w h).injective
  rw [S.weightedDegreeZeroQuotientEquivPicZero_weightedAbelJacobiQuotientClass,
    S.weightedAbelJacobiDivisorClass_principalDivisor]
  simp

/-- Equality of weighted quotient Abel-Jacobi representatives is equality of the corresponding
degree-corrected divisor classes. -/
lemma weightedAbelJacobiQuotientClass_eq_iff_divisorClass
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1)
    {D E : WeilDivisor X} :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
        S.weightedAbelJacobiQuotientClass w hx₀ E ↔
      S.divisorClass (D - weightedDegree w D • ofPoint x₀) =
        S.divisorClass (E - weightedDegree w E • ofPoint x₀) := by
  rw [← (S.weightedDegreeZeroQuotientEquivPicZero w h).apply_eq_iff_eq,
    S.weightedDegreeZeroQuotientEquivPicZero_weightedAbelJacobiQuotientClass,
    S.weightedDegreeZeroQuotientEquivPicZero_weightedAbelJacobiQuotientClass,
    S.weightedAbelJacobiDivisorClass_eq_iff_divisorClass w h hx₀]

/-- Equality of weighted quotient Abel-Jacobi representatives is linear equivalence of the
corresponding degree-corrected divisors. -/
lemma weightedAbelJacobiQuotientClass_eq_iff_linearlyEquivalent
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1)
    {D E : WeilDivisor X} :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
        S.weightedAbelJacobiQuotientClass w hx₀ E ↔
      S.LinearlyEquivalent (D - weightedDegree w D • ofPoint x₀)
        (E - weightedDegree w E • ofPoint x₀) := by
  rw [S.weightedAbelJacobiQuotientClass_eq_iff_divisorClass w h hx₀, S.divisorClass_eq_iff]

/-! ### Unweighted quotient representatives -/

/-- The degree-corrected representative of a divisor in the unweighted degree-zero divisor
group.  This is `D - degree(D) • [x₀]`. -/
abbrev unweightedAbelJacobiDegreeZeroDivisor (x₀ : X) (D : WeilDivisor X) :
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
abbrev unweightedAbelJacobiQuotientClass (x₀ : X) :
    WeilDivisor X →+ degreeZeroSubgroup X ⧸ S.principalSubgroupOfDegreeZero where
  toFun D := QuotientAddGroup.mk (unweightedAbelJacobiDegreeZeroDivisor x₀ D)
  map_zero' := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    rw [mem_principalSubgroupOfDegreeZero, coe_unweightedAbelJacobiDegreeZeroDivisor]
    simp
  map_add' D E := by
    have hdiv :
        unweightedAbelJacobiDegreeZeroDivisor x₀ (D + E) =
          unweightedAbelJacobiDegreeZeroDivisor x₀ D +
            unweightedAbelJacobiDegreeZeroDivisor x₀ E := by
      ext x
      simp [map_add, add_zsmul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    change QuotientAddGroup.mk (unweightedAbelJacobiDegreeZeroDivisor x₀ (D + E)) =
      QuotientAddGroup.mk (unweightedAbelJacobiDegreeZeroDivisor x₀ D) +
        QuotientAddGroup.mk (unweightedAbelJacobiDegreeZeroDivisor x₀ E)
    rw [hdiv]
    exact map_add (QuotientAddGroup.mk' S.principalSubgroupOfDegreeZero)
      (unweightedAbelJacobiDegreeZeroDivisor x₀ D)
      (unweightedAbelJacobiDegreeZeroDivisor x₀ E)

@[simp]
lemma unweightedAbelJacobiQuotientClass_mk (x₀ : X) (D : WeilDivisor X) :
    S.unweightedAbelJacobiQuotientClass x₀ D =
      QuotientAddGroup.mk (unweightedAbelJacobiDegreeZeroDivisor x₀ D) :=
  rfl

/-- The unweighted quotient Abel-Jacobi representative of a sum is the sum of the quotient
representatives. -/
@[simp]
lemma unweightedAbelJacobiQuotientClass_add (x₀ : X) (D E : WeilDivisor X) :
    S.unweightedAbelJacobiQuotientClass x₀ (D + E) =
      S.unweightedAbelJacobiQuotientClass x₀ D +
        S.unweightedAbelJacobiQuotientClass x₀ E :=
  map_add (S.unweightedAbelJacobiQuotientClass x₀) D E

/-- The unweighted quotient Abel-Jacobi representative of an integral multiple is the
corresponding multiple of the quotient representative. -/
@[simp]
lemma unweightedAbelJacobiQuotientClass_zsmul (x₀ : X) (n : ℤ) (D : WeilDivisor X) :
    S.unweightedAbelJacobiQuotientClass x₀ (n • D) =
      n • S.unweightedAbelJacobiQuotientClass x₀ D :=
  map_zsmul (S.unweightedAbelJacobiQuotientClass x₀) n D

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

/-- The unweighted quotient Abel-Jacobi representative of a finitely supported formal divisor is
the finite sum of the quotient representatives of its point divisors. -/
lemma unweightedAbelJacobiQuotientClass_eq_sum (x₀ : X) (D : WeilDivisor X) :
    S.unweightedAbelJacobiQuotientClass x₀ D =
      D.sum fun x n => n • S.unweightedAbelJacobiQuotientClass x₀ (ofPoint x) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero =>
      simp
  | single x n =>
      rw [Finsupp.sum_single_index]
      · rw [← zsmul_ofPoint_eq_single n x,
          S.unweightedAbelJacobiQuotientClass_zsmul x₀ n (ofPoint x)]
      · simp
  | add D E hD hE =>
      rw [S.unweightedAbelJacobiQuotientClass_add x₀, Finsupp.sum_add_index, hD, hE]
      · intro x
        simp
      · intro x a b
        simp [add_zsmul]

/-- The unweighted base-point divisor represents zero in the degree-zero quotient. -/
@[simp]
lemma unweightedAbelJacobiQuotientClass_ofPoint_base (x₀ : X) :
    S.unweightedAbelJacobiQuotientClass x₀ (ofPoint x₀) = 0 := by
  rw [unweightedAbelJacobiQuotientClass_mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  rw [mem_principalSubgroupOfDegreeZero, coe_unweightedAbelJacobiDegreeZeroDivisor,
    degree_ofPoint, one_zsmul, sub_self]
  exact S.principalSubgroup.zero_mem

/-- A principal divisor has zero unweighted quotient Abel-Jacobi representative. -/
@[simp]
lemma unweightedAbelJacobiQuotientClass_principalDivisor (h : S.IsUnweightedDegreeZero)
    (x₀ : X) (g : G) :
    S.unweightedAbelJacobiQuotientClass x₀ (S.principalDivisor g) = 0 := by
  apply (S.degreeZeroQuotientEquivUnweightedPicZero h).injective
  rw [S.degreeZeroQuotientEquivUnweightedPicZero_unweightedAbelJacobiQuotientClass,
    S.unweightedAbelJacobiDivisorClass_principalDivisor]
  simp

/-- Equality of unweighted quotient Abel-Jacobi representatives is equality of the corresponding
degree-corrected divisor classes. -/
lemma unweightedAbelJacobiQuotientClass_eq_iff_divisorClass
    (h : S.IsUnweightedDegreeZero) (x₀ : X) {D E : WeilDivisor X} :
    S.unweightedAbelJacobiQuotientClass x₀ D =
        S.unweightedAbelJacobiQuotientClass x₀ E ↔
      S.divisorClass (D - degree D • ofPoint x₀) =
        S.divisorClass (E - degree E • ofPoint x₀) := by
  rw [← (S.degreeZeroQuotientEquivUnweightedPicZero h).apply_eq_iff_eq,
    S.degreeZeroQuotientEquivUnweightedPicZero_unweightedAbelJacobiQuotientClass,
    S.degreeZeroQuotientEquivUnweightedPicZero_unweightedAbelJacobiQuotientClass,
    S.unweightedAbelJacobiDivisorClass_eq_iff_divisorClass h x₀]

/-- Equality of unweighted quotient Abel-Jacobi representatives is linear equivalence of the
corresponding degree-corrected divisors. -/
lemma unweightedAbelJacobiQuotientClass_eq_iff_linearlyEquivalent
    (h : S.IsUnweightedDegreeZero) (x₀ : X) {D E : WeilDivisor X} :
    S.unweightedAbelJacobiQuotientClass x₀ D =
        S.unweightedAbelJacobiQuotientClass x₀ E ↔
      S.LinearlyEquivalent (D - degree D • ofPoint x₀) (E - degree E • ofPoint x₀) := by
  rw [S.unweightedAbelJacobiQuotientClass_eq_iff_divisorClass h x₀, S.divisorClass_eq_iff]

end

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
