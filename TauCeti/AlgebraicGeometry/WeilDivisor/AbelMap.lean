/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.BasepointChange
import Mathlib.Tactic.Ring

/-!
# Divisor-level Abel classes

This file extends the abstract divisor-class Abel-Jacobi API from points to arbitrary formal
Weil divisors.  Given a weight `w : X → ℤ` and a base point `x₀` with `w x₀ = 1`, the divisor

`D - weightedDegree w D • [x₀]`

has weighted degree zero.  Its divisor class is therefore an element of the abstract `Pic⁰`
subgroup attached to an `OrderSystem`.  This is the formal Layer A shadow of the normalized
Abel maps used later in the Jacobian roadmap:

`AJ_d : Symᵈ X → Pic⁰`, sending an effective divisor `D` of degree `d` to
`𝒪_X(D - d·x₀)`.

No symmetric powers, line bundles, or Picard schemes are introduced here.  The file only builds
the reusable divisor-class operation available from the existing Weil-divisor and `OrderSystem`
infrastructure.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer D, the symmetric-powers /
Abel-maps item, as a clean prerequisite built at the formal divisor-class level.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

/-! ### Normalizing a divisor by a base point -/

/-- The degree-normalized divisor `D - weightedDegree w D • [x₀]`.

When `w x₀ = 1`, this has weighted degree zero.  For an effective divisor `D` of weighted
degree `d`, it is the formal divisor underlying the normalized Abel map
`D ↦ 𝒪_X(D - d·x₀)`. -/
@[expose] noncomputable def weightedDivisorBaseDifference (w : X → ℤ) (x₀ : X) (D : WeilDivisor X) :
    WeilDivisor X :=
  D - weightedDegree w D • ofPoint x₀

/-- The normalized divisor of a point divisor is the point-level weighted Abel-Jacobi divisor. -/
@[simp]
lemma weightedDivisorBaseDifference_ofPoint (w : X → ℤ) (x₀ x : X) :
    weightedDivisorBaseDifference w x₀ (ofPoint x) = weightedPointBaseDifference w x₀ x := by
  simp [weightedDivisorBaseDifference, weightedPointBaseDifference]

@[simp]
lemma weightedDivisorBaseDifference_zero (w : X → ℤ) (x₀ : X) :
    weightedDivisorBaseDifference w x₀ 0 = 0 := by
  simp [weightedDivisorBaseDifference]

/-- The weighted degree of the normalized divisor is `deg_w(D) * (1 - w x₀)`. -/
@[simp]
lemma weightedDegree_weightedDivisorBaseDifference (w : X → ℤ) (x₀ : X)
    (D : WeilDivisor X) :
    weightedDegree w (weightedDivisorBaseDifference w x₀ D) =
      weightedDegree w D * (1 - w x₀) := by
  simp [weightedDivisorBaseDifference]
  ring

/-- If the base point has weight `1`, then `D - deg_w(D) • [x₀]` has weighted degree zero. -/
@[simp]
lemma weightedDivisorBaseDifference_mem_weightedDegreeZeroSubgroup {w : X → ℤ} {x₀ : X}
    (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    weightedDivisorBaseDifference w x₀ D ∈ weightedDegreeZeroSubgroup w := by
  simp [hx₀]

/-- Normalization by a weight-one base point as a homomorphism into the weighted-degree-zero
divisor subgroup. -/
@[expose] noncomputable def weightedDivisorBaseDifferenceHom (w : X → ℤ) {x₀ : X}
    (hx₀ : w x₀ = 1) :
    WeilDivisor X →+ weightedDegreeZeroSubgroup w where
  toFun D :=
    ⟨weightedDivisorBaseDifference w x₀ D,
      weightedDivisorBaseDifference_mem_weightedDegreeZeroSubgroup hx₀ D⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' D E := by
    apply Subtype.ext
    simp [weightedDivisorBaseDifference, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      add_zsmul]

@[simp]
lemma weightedDivisorBaseDifferenceHom_apply (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) :
    (weightedDivisorBaseDifferenceHom w hx₀ D : WeilDivisor X) =
      weightedDivisorBaseDifference w x₀ D :=
  rfl

/-- Changing the base point in the normalized divisor adds `deg_w(D)` times `[x₀] - [y₀]`. -/
lemma weightedDivisorBaseDifference_change_base (w : X → ℤ) (x₀ y₀ : X)
    (D : WeilDivisor X) :
    weightedDivisorBaseDifference w y₀ D =
      weightedDivisorBaseDifference w x₀ D + weightedDegree w D • pointDifference x₀ y₀ := by
    simp [weightedDivisorBaseDifference, pointDifference, sub_eq_add_neg, add_assoc,
      add_left_comm]

/-- The difference between normalizations at two base points is
`deg_w(D) • ([x₀] - [y₀])`. -/
lemma weightedDivisorBaseDifference_sub_change_base (w : X → ℤ) (x₀ y₀ : X)
    (D : WeilDivisor X) :
    weightedDivisorBaseDifference w y₀ D - weightedDivisorBaseDifference w x₀ D =
      weightedDegree w D • pointDifference x₀ y₀ := by
  rw [weightedDivisorBaseDifference_change_base, add_sub_cancel_left]

/-- Two divisors of the same weighted degree have normalized divisors whose difference is the
ordinary difference `D - E`; the base-point terms cancel. -/
lemma weightedDivisorBaseDifference_sub_same_base {w : X → ℤ} {x₀ : X}
    {D E : WeilDivisor X} (hDE : weightedDegree w D = weightedDegree w E) :
    weightedDivisorBaseDifference w x₀ D - weightedDivisorBaseDifference w x₀ E = D - E := by
  simp [weightedDivisorBaseDifference, hDE, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-! ### Divisor Abel classes in the abstract Picard group -/

namespace OrderSystem

variable (S : OrderSystem X G)

/-- The normalized Abel class of a formal divisor in the abstract weighted `Pic⁰`.

For an effective divisor `D` of weighted degree `d`, this is the divisor-class version of
`𝒪_X(D - d·x₀)`, before the Picard scheme and the symmetric power of the curve are available. -/
@[expose] noncomputable def weightedDivisorAbelClass (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (D : WeilDivisor X) : picZero w hdeg :=
  ⟨S.divisorClass (weightedDivisorBaseDifference w x₀ D), by
    rw [divisorClass_mem_picZero]
    exact weightedDivisorBaseDifference_mem_weightedDegreeZeroSubgroup hx₀ D⟩

@[simp]
lemma coe_weightedDivisorAbelClass (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    (S.weightedDivisorAbelClass w hdeg hx₀ D : S.ClassGroup) =
      S.divisorClass (weightedDivisorBaseDifference w x₀ D) :=
  rfl

@[simp]
lemma weightedDivisorAbelClass_zero (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) :
    S.weightedDivisorAbelClass w hdeg hx₀ 0 = 0 := by
  apply Subtype.ext
  simp [weightedDivisorAbelClass]

/-- The normalized Abel class of a point divisor is the existing point Abel-Jacobi class. -/
@[simp]
lemma weightedDivisorAbelClass_ofPoint (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.weightedDivisorAbelClass w hdeg hx₀ (ofPoint x) =
      S.weightedAbelJacobiClass w hdeg hx₀ x := by
  apply Subtype.ext
  simp [weightedDivisorAbelClass, weightedAbelJacobiClass]

/-- The normalized Abel class is additive in divisors. -/
lemma weightedDivisorAbelClass_add (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (D E : WeilDivisor X) :
    S.weightedDivisorAbelClass w hdeg hx₀ (D + E) =
      S.weightedDivisorAbelClass w hdeg hx₀ D +
        S.weightedDivisorAbelClass w hdeg hx₀ E := by
  apply Subtype.ext
  simp [weightedDivisorAbelClass, weightedDivisorBaseDifference, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm, add_zsmul]

/-- Equality of normalized divisor Abel classes is equality of the normalized divisor classes. -/
lemma weightedDivisorAbelClass_eq_iff_divisorClass (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) {D E : WeilDivisor X} :
    S.weightedDivisorAbelClass w hdeg hx₀ D = S.weightedDivisorAbelClass w hdeg hx₀ E ↔
      S.divisorClass (weightedDivisorBaseDifference w x₀ D) =
        S.divisorClass (weightedDivisorBaseDifference w x₀ E) := by
  constructor
  · intro h
    simpa using congr_arg Subtype.val h
  · intro h
    apply Subtype.ext
    simpa using h

/-- Equality of normalized divisor Abel classes is linear equivalence of the normalized
divisors. -/
lemma weightedDivisorAbelClass_eq_iff_linearlyEquivalent (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) {D E : WeilDivisor X} :
    S.weightedDivisorAbelClass w hdeg hx₀ D = S.weightedDivisorAbelClass w hdeg hx₀ E ↔
      S.LinearlyEquivalent (weightedDivisorBaseDifference w x₀ D)
        (weightedDivisorBaseDifference w x₀ E) := by
  rw [S.weightedDivisorAbelClass_eq_iff_divisorClass w hdeg hx₀, S.divisorClass_eq_iff]

/-- If two divisors have the same weighted degree, equality of their normalized Abel classes is
the same as equality of their ordinary divisor classes. -/
lemma weightedDivisorAbelClass_eq_iff_divisorClass_of_weightedDegree_eq (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) {D E : WeilDivisor X}
    (hDE : weightedDegree w D = weightedDegree w E) :
    S.weightedDivisorAbelClass w hdeg hx₀ D = S.weightedDivisorAbelClass w hdeg hx₀ E ↔
      S.divisorClass D = S.divisorClass E := by
  rw [S.weightedDivisorAbelClass_eq_iff_linearlyEquivalent w hdeg hx₀, S.divisorClass_eq_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hsub := h
    rw [linearlyEquivalent_iff] at hsub ⊢
    rwa [weightedDivisorBaseDifference_sub_same_base hDE] at hsub
  · rw [linearlyEquivalent_iff] at h ⊢
    rwa [weightedDivisorBaseDifference_sub_same_base hDE]

/-- Changing the base point in the normalized divisor Abel class adds `deg_w(D)` times the
base-point-change class. -/
lemma weightedDivisorAbelClass_change_base (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) (D : WeilDivisor X) :
    S.weightedDivisorAbelClass w hdeg hy₀ D =
      S.weightedDivisorAbelClass w hdeg hx₀ D +
        weightedDegree w D • S.weightedBasepointChangeClass w hdeg (hx₀.trans hy₀.symm) := by
  apply Subtype.ext
  simp only [coe_weightedDivisorAbelClass, coe_weightedBasepointChangeClass,
    AddMemClass.coe_add, AddSubgroupClass.coe_zsmul]
  rw [← map_zsmul, ← map_add, ← weightedDivisorBaseDifference_change_base]

/-! ### Unweighted specialization -/

/-- The unweighted normalized Abel class of a divisor, `D ↦ [D - deg(D)·[x₀]]`. -/
noncomputable def unweightedDivisorAbelClass (hdeg : S.IsUnweightedDegreeZero) (x₀ : X)
    (D : WeilDivisor X) : unweightedPicZero hdeg :=
  S.weightedDivisorAbelClass (fun _ => (1 : ℤ)) hdeg (x₀ := x₀) rfl D

@[simp]
lemma coe_unweightedDivisorAbelClass (hdeg : S.IsUnweightedDegreeZero) (x₀ : X)
    (D : WeilDivisor X) :
    (S.unweightedDivisorAbelClass hdeg x₀ D : S.ClassGroup) =
      S.divisorClass (D - degree D • ofPoint x₀) := by
  simp [unweightedDivisorAbelClass, weightedDivisorBaseDifference, weightedDegree_one_eq_degree]

@[simp]
lemma unweightedDivisorAbelClass_ofPoint (hdeg : S.IsUnweightedDegreeZero) (x₀ x : X) :
    S.unweightedDivisorAbelClass hdeg x₀ (ofPoint x) =
      S.unweightedAbelJacobiClass hdeg x₀ x := by
  apply Subtype.ext
  simp [unweightedDivisorAbelClass, unweightedAbelJacobiClass]

/-- The unweighted normalized Abel class is additive in divisors. -/
lemma unweightedDivisorAbelClass_add (hdeg : S.IsUnweightedDegreeZero) (x₀ : X)
    (D E : WeilDivisor X) :
    S.unweightedDivisorAbelClass hdeg x₀ (D + E) =
      S.unweightedDivisorAbelClass hdeg x₀ D +
        S.unweightedDivisorAbelClass hdeg x₀ E :=
  S.weightedDivisorAbelClass_add (fun _ : X => (1 : ℤ)) hdeg rfl D E

/-- For equal-degree divisors, equality of unweighted normalized Abel classes is equality of
ordinary divisor classes. -/
lemma unweightedDivisorAbelClass_eq_iff_divisorClass_of_degree_eq
    (hdeg : S.IsUnweightedDegreeZero) (x₀ : X) {D E : WeilDivisor X} (hDE : degree D = degree E) :
    S.unweightedDivisorAbelClass hdeg x₀ D = S.unweightedDivisorAbelClass hdeg x₀ E ↔
      S.divisorClass D = S.divisorClass E := by
  change
    S.weightedDivisorAbelClass (fun _ : X => (1 : ℤ)) hdeg (x₀ := x₀) rfl D =
      S.weightedDivisorAbelClass (fun _ : X => (1 : ℤ)) hdeg (x₀ := x₀) rfl E ↔
        S.divisorClass D = S.divisorClass E
  simpa only [weightedDegree_one_eq_degree] using
    S.weightedDivisorAbelClass_eq_iff_divisorClass_of_weightedDegree_eq
      (fun _ : X => (1 : ℤ)) hdeg (x₀ := x₀) rfl (by
        rw [weightedDegree_one_eq_degree, weightedDegree_one_eq_degree]
        exact hDE)

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
