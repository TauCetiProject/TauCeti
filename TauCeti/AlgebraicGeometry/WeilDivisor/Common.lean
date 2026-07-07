/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FixedDegreeSubtraction

/-!
# Common parts of fixed-degree effective Weil divisors

This file packages the pointwise minimum of two effective fixed-degree Weil divisors as their
common effective part.  If `D` and `E` are effective divisors, `D ⊓ E` is the largest divisor
lying below both.  Removing it from `D` and from `E` gives two residual effective divisors with
disjoint support.

This is formal divisor bookkeeping for the Jacobian challenge roadmap's Layer C symmetric-power
lane (`TauCetiRoadmap/JacobianChallenge/README.md`, "Relative effective Cartier divisors and
symmetric powers `Symᵈ X`").  The later Abel-map and linear-system arguments need to split
unordered effective divisors into their common sub-divisor and the two remaining parts; this file
supplies that operation at the existing formal Weil-divisor level, before scheme-level symmetric
powers or relative Cartier divisors are available.  No external mathematics is vendored; the
proofs reuse Mathlib's pointwise lattice structure on finitely supported functions through
Tau Ceti's `WeilDivisor.Order` API.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace EffectiveDivisorOfDegree

variable {X : Type*} {d e : ℕ}

noncomputable section

/-- The common effective part of two fixed-degree effective divisors.

Its underlying Weil divisor is the pointwise minimum `D ⊓ E`; its degree index is the actual
degree of that minimum. -/
@[expose]
def commonPart (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    EffectiveDivisorOfDegree X (degree ((D : WeilDivisor X) ⊓ E)).toNat :=
  ⟨(D : WeilDivisor X) ⊓ E, D.isEffective.inf E.isEffective,
    (Int.toNat_of_nonneg (D.isEffective.inf E.isEffective).degree_nonneg).symm⟩

@[simp]
lemma coe_commonPart (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (commonPart D E : WeilDivisor X) = (D : WeilDivisor X) ⊓ E :=
  rfl

/-- The coefficient of the common part is the minimum of the two coefficients. -/
@[simp]
lemma coeff_commonPart (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e)
    (x : X) :
    coeff (commonPart D E : WeilDivisor X) x =
      coeff (D : WeilDivisor X) x ⊓ coeff (E : WeilDivisor X) x := by
  rw [coe_commonPart, WeilDivisor.coeff_inf]

/-- The common part lies below the left input divisor. -/
lemma commonPart_le_left (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    (commonPart D E : WeilDivisor X) ≤ D := by
  rw [coe_commonPart]
  exact inf_le_left

/-- The common part lies below the right input divisor. -/
lemma commonPart_le_right (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    (commonPart D E : WeilDivisor X) ≤ E := by
  rw [coe_commonPart]
  exact inf_le_right

/-- A fixed-degree effective divisor below both inputs lies below their common part. -/
lemma le_commonPart {n : ℕ} {F : EffectiveDivisorOfDegree X n}
    {D : EffectiveDivisorOfDegree X d} {E : EffectiveDivisorOfDegree X e}
    (hFD : (F : WeilDivisor X) ≤ D) (hFE : (F : WeilDivisor X) ≤ E) :
    (F : WeilDivisor X) ≤ commonPart D E := by
  rw [coe_commonPart]
  exact le_inf hFD hFE

/-- The common part is the left input exactly when the left input is below the right input. -/
lemma commonPart_eq_left_iff_le {D : EffectiveDivisorOfDegree X d}
    {E : EffectiveDivisorOfDegree X e} :
    (commonPart D E : WeilDivisor X) = D ↔ (D : WeilDivisor X) ≤ E := by
  rw [coe_commonPart]
  exact inf_eq_left

/-- The common part is the right input exactly when the right input is below the left input. -/
lemma commonPart_eq_right_iff_le {D : EffectiveDivisorOfDegree X d}
    {E : EffectiveDivisorOfDegree X e} :
    (commonPart D E : WeilDivisor X) = E ↔ (E : WeilDivisor X) ≤ D := by
  rw [coe_commonPart]
  exact inf_eq_right

/-- The degree of the common part is bounded by the left degree index. -/
lemma commonPart_degree_le_left (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    (degree ((D : WeilDivisor X) ⊓ E)).toNat ≤ d :=
  degree_le_of_le (commonPart_le_left D E)

/-- The degree of the common part is bounded by the right degree index. -/
lemma commonPart_degree_le_right (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    (degree ((D : WeilDivisor X) ⊓ E)).toNat ≤ e :=
  degree_le_of_le (commonPart_le_right D E)

/-- The residual part of the left divisor after removing the common part. -/
abbrev leftResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    EffectiveDivisorOfDegree X (d - (degree ((D : WeilDivisor X) ⊓ E)).toNat) :=
  subOfLe D (commonPart D E) (commonPart_le_left D E)

/-- The residual part of the right divisor after removing the common part. -/
abbrev rightResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    EffectiveDivisorOfDegree X (e - (degree ((D : WeilDivisor X) ⊓ E)).toNat) :=
  subOfLe E (commonPart D E) (commonPart_le_right D E)

@[simp]
lemma coe_leftResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (leftResidual D E : WeilDivisor X) = (D : WeilDivisor X) - commonPart D E :=
  rfl

@[simp]
lemma coe_rightResidual (D : EffectiveDivisorOfDegree X d) (E : EffectiveDivisorOfDegree X e) :
    (rightResidual D E : WeilDivisor X) = (E : WeilDivisor X) - commonPart D E :=
  rfl

/-- The coefficient of the left residual is `coeff D x - min (coeff D x) (coeff E x)`. -/
@[simp]
lemma coeff_leftResidual (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) (x : X) :
    coeff (leftResidual D E : WeilDivisor X) x =
      coeff (D : WeilDivisor X) x -
        (coeff (D : WeilDivisor X) x ⊓ coeff (E : WeilDivisor X) x) := by
  rw [coe_leftResidual, WeilDivisor.coeff_sub, coeff_commonPart]

/-- The coefficient of the right residual is `coeff E x - min (coeff D x) (coeff E x)`. -/
@[simp]
lemma coeff_rightResidual (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) (x : X) :
    coeff (rightResidual D E : WeilDivisor X) x =
      coeff (E : WeilDivisor X) x -
        (coeff (D : WeilDivisor X) x ⊓ coeff (E : WeilDivisor X) x) := by
  rw [coe_rightResidual, WeilDivisor.coeff_sub, coeff_commonPart]

private lemma sub_inf_inf_sub_inf_eq_zero (a b : ℤ) :
    (a - (a ⊓ b)) ⊓ (b - (a ⊓ b)) = 0 := by
  rcases le_total a b with hab | hba
  · have hmin : a ⊓ b = a := inf_eq_left.mpr hab
    have hnonneg : 0 ≤ b - a := sub_nonneg.mpr hab
    rw [hmin, sub_self, inf_eq_left]
    exact hnonneg
  · have hmin : a ⊓ b = b := inf_eq_right.mpr hba
    have hnonneg : 0 ≤ a - b := sub_nonneg.mpr hba
    rw [hmin, sub_self, inf_eq_right]
    exact hnonneg

/-- The two residual divisors left after removing the common part are coefficientwise
disjoint. -/
@[simp]
lemma leftResidual_inf_rightResidual (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    ((leftResidual D E : WeilDivisor X) ⊓ rightResidual D E) = 0 := by
  ext x
  rw [WeilDivisor.coeff_inf, coeff_leftResidual, coeff_rightResidual, coeff_zero]
  exact sub_inf_inf_sub_inf_eq_zero _ _

/-- Removing the common part from the left divisor and adding it back recovers the left
divisor, up to the natural degree-index cast. -/
@[simp]
lemma leftResidual_add_commonPart (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    add (leftResidual D E) (commonPart D E) =
      EffectiveDivisorOfDegree.cast
        (Nat.sub_add_cancel (commonPart_degree_le_left D E)).symm D := by
  exact subOfLe_add D (commonPart D E) (commonPart_le_left D E)

/-- Adding the common part before the left residual also recovers the left divisor, up to the
natural degree-index cast. -/
@[simp]
lemma commonPart_add_leftResidual (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    add (commonPart D E) (leftResidual D E) =
      EffectiveDivisorOfDegree.cast
        (Nat.add_sub_of_le (commonPart_degree_le_left D E)).symm D := by
  exact add_subOfLe D (commonPart D E) (commonPart_le_left D E)

/-- Removing the common part from the right divisor and adding it back recovers the right
divisor, up to the natural degree-index cast. -/
@[simp]
lemma rightResidual_add_commonPart (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    add (rightResidual D E) (commonPart D E) =
      EffectiveDivisorOfDegree.cast
        (Nat.sub_add_cancel (commonPart_degree_le_right D E)).symm E := by
  exact subOfLe_add E (commonPart D E) (commonPart_le_right D E)

/-- Adding the common part before the right residual also recovers the right divisor, up to the
natural degree-index cast. -/
@[simp]
lemma commonPart_add_rightResidual (D : EffectiveDivisorOfDegree X d)
    (E : EffectiveDivisorOfDegree X e) :
    add (commonPart D E) (rightResidual D E) =
      EffectiveDivisorOfDegree.cast
        (Nat.add_sub_of_le (commonPart_degree_le_right D E)).symm E := by
  exact add_subOfLe E (commonPart D E) (commonPart_le_right D E)

end

end EffectiveDivisorOfDegree

end WeilDivisor

end AlgebraicGeometry

end TauCeti
