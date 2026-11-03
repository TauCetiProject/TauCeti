/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix

/-!
# Opposite-root Gauss factorization in the doubled E₆ carrier

The numbered positive and negative simple-root points of `V(ϖ₁) ⊕ V(ϖ₆)` satisfy the
rank-one Gauss relation. The simple coroot is given in fundamental-weight coordinates by
`Pi.mulSingle i u`. Both multiplication orders are covered over every commutative value
ring, assuming only that the pivot `1 + a * b` is a unit. Neither parameter need be
invertible, and value rings may be nonreduced. The signed action on coordinate vectors
keeps track of the negative root-matrix coefficients in the dual summand.

The carrier is not identified here with the independently pinned simply connected group
scheme of type E₆; transfer of these identities to that group requires such an identification.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, the rank-one relations.
* R. W. Carter, *Simple Groups of Lie Type*, §6.1.
* The root matrices and their signed columns are those of
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix`.
-/

public section

open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

universe v

variable {A : Type v} [CommRing A]

/-- A root point acts on a coordinate vector along its signed raising or lowering edge. -/
@[simp↓]
theorem rootSubgroupPoints_mulVec_single (j : Fin 6 ⊕ Fin 6) (t x : A) (k : Fin 54) :
    ((rootSubgroupPoints j A (Multiplicative.ofAdd t) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) *ᵥ
          Pi.single k x =
      Pi.single k x +
        if matrixWeight k (Sum.elim id id j) =
            (Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) j : ℤ) then
          Pi.single (matrixIndexEquiv (reflection (Sum.elim id id j)
            (matrixIndexEquiv.symm k)))
              (t * (summandSign (matrixIndexEquiv.symm k) : A) * x)
        else 0 := by
  rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_single]
  ext l
  simp [Matrix.col_apply, rootIntMatrix_apply, Pi.single_apply]
  split_ifs <;> simp_all [mul_left_comm, mul_comm]

private theorem weightTorusPoints_mulVec_single (i : Fin 6) (u : Aˣ) (k : Fin 54) (x : A) :
    ((weightTorusPoints A (Pi.mulSingle i u) : Matrix.GeneralLinearGroup (Fin 54) A) :
        Matrix (Fin 54) (Fin 54) A) *ᵥ Pi.single k x =
      Pi.single k (((u ^ matrixWeight k i : Aˣ) : A) * x) := by
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
  simp only [torusCharacter_mulSingle, Matrix.diagonal_mulVec_single]

/-- The positive-negative simple-root product admits Gauss factorization with pivot
`u = 1 + a * b` and simple-coroot factor `αᵢ∨(u)`. -/
theorem rootSubgroupPoints_inl_mul_inr (i : Fin 6) (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i u) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  apply Matrix.ext_of_mulVec_single
  intro k
  let r := matrixIndexEquiv (reflection i (matrixIndexEquiv.symm k))
  let s : A := summandSign (matrixIndexEquiv.symm k)
  -- These equalities name the reflected coordinate and its signed matrix coefficient.
  have hrdef : matrixIndexEquiv (reflection i (matrixIndexEquiv.symm k)) = r := rfl
  have hsdef : (summandSign (matrixIndexEquiv.symm k) : A) = s := rfl
  have hrback : matrixIndexEquiv (reflection i (matrixIndexEquiv.symm r)) = k := by
    simp [r]
  have hs : s * s = 1 := by
    dsimp [s]
    cases h : matrixIndexEquiv.symm k <;> simp
  have hsr : (summandSign (matrixIndexEquiv.symm r) : A) = s := by
    dsimp [r, s]
    cases h : matrixIndexEquiv.symm k <;> simp
  have hweight : matrixWeight r i = -matrixWeight k i := by
    simp [r, matrixWeight_apply]
  -- Scalar block identities retain the dual summand's sign until its square cancels.
  have hcancel : (u : A) * (a * ↑u⁻¹ * s) = a * s := by
    simpa only [mul_assoc, mul_comm (↑u⁻¹ : A), mul_left_comm] using
      u.mul_inv_cancel_left (a * s)
  have hsum : (↑u⁻¹ : A) + b * ↑u⁻¹ * s * (a * s) = 1 := by
    calc
      (↑u⁻¹ : A) + b * ↑u⁻¹ * s * (a * s) =
          ↑u⁻¹ + a * b * ↑u⁻¹ * (s * s) := by ring
      _ = (1 + a * b) * ↑u⁻¹ := by rw [hs, mul_one, add_mul, one_mul]
      _ = 1 := by rw [← hu, Units.mul_inv]
  have hprod : a * s * (b * s) = a * b := by
    calc
      a * s * (b * s) = a * b * (s * s) := by ring
      _ = a * b := by rw [hs, mul_one]
  have hcancel' : b * ↑u⁻¹ * s * (u : A) = b * s := by
    calc
      b * ↑u⁻¹ * s * (u : A) = b * s * (↑u⁻¹ * ↑u) := by ring
      _ = b * s := by rw [Units.inv_mul, mul_one]
  -- At weights -1 and 1 the reflection pair is an SL₂ block; weight zero is fixed.
  simp only [← Matrix.mulVec_mulVec]
  rcases DynkinType.e6DoubledMinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one
    (matrixIndexEquiv.symm k) i with hk | hk | hk
  all_goals rw [← matrixWeight_apply] at hk
  · have hr : matrixWeight r i = 1 := by rw [hweight, hk]; decide
    have hblock : (Pi.single k 1 : Fin 54 → A) + Pi.single r (a * s) =
        (Pi.single k (↑u⁻¹ : A) : Fin 54 → A) +
          ((Pi.single r (a * s) : Fin 54 → A) + Pi.single k (b * ↑u⁻¹ * s * (a * s))) := by
      rw [add_comm (Pi.single r (a * s) : Fin 54 → A), ← add_assoc, ← Pi.single_add, hsum]
    simpa [rootSubgroupPoints_mulVec_single, weightTorusPoints_mulVec_single,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_add, hk, hr, hsr, hcancel, hrdef, hrback, hsdef,
      -coe_rootSubgroupPoints, -coe_weightTorusPoints, -matrixWeight_apply,
      -Matrix.mulVec_single] using hblock
  · simp [rootSubgroupPoints_mulVec_single, weightTorusPoints_mulVec_single,
      hk, -coe_rootSubgroupPoints, -coe_weightTorusPoints,
      -matrixWeight_apply, -Matrix.mulVec_single]
  · have hr : matrixWeight r i = -1 := by rw [hweight, hk]
    have hblock : (Pi.single k 1 : Fin 54 → A) +
        ((Pi.single r (b * s) : Fin 54 → A) + Pi.single k (a * b)) =
          (Pi.single k (u : A) : Fin 54 → A) + Pi.single r (b * s) := by
      rw [add_comm (Pi.single r (b * s) : Fin 54 → A), ← add_assoc, ← Pi.single_add, ← hu]
    simpa [rootSubgroupPoints_mulVec_single, weightTorusPoints_mulVec_single,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_add, hk, hr, hsr, hprod, hcancel', hrdef, hrback, hsdef,
      -coe_rootSubgroupPoints, -coe_weightTorusPoints, -matrixWeight_apply,
      -Matrix.mulVec_single] using hblock

/-- The negative-positive simple-root product has the reverse Gauss factorization, with
simple-coroot factor `αᵢ∨(u⁻¹)` for the same pivot `u = 1 + a * b`. -/
theorem rootSubgroupPoints_inr_mul_inl (i : Fin 6) (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i u⁻¹) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  have hpivot : (u : A) = 1 + (-b) * (-a) := by
    rw [neg_mul_neg, mul_comm b a]
    exact hu
  have h := congrArg Inv.inv (rootSubgroupPoints_inl_mul_inr i (-b) (-a) u hpivot)
  simpa [mul_inv_rev, ← map_inv, ← ofAdd_neg, neg_mul, ← Pi.mulSingle_inv, mul_assoc] using h

end TauCeti.E6DoubledMinuscule
