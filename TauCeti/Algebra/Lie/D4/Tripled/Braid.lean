/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.GroupScheme

/-!
# Braid relations in the tripled D₄ carrier

The pinned words `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the tripled representation
`V(ϖ₁) ⊕ V(ϖ₃) ⊕ V(ϖ₄)` satisfy the commuting and length-three braid relations.
These identities make Weyl-word transport of the numbered root subgroups compatible with
braid moves. They hold over every commutative ring, including nonreduced rings and rings of
characteristic two; they do not identify this carrier with an independently pinned group.

The integral calculation uses the existing minuscule column formulas: each pinned word is a
signed permutation of the twenty-four weight vectors. Both the permutation and its signs
are checked, before changing coefficients.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* The matrices and weight basis are those of
  `TauCeti.Algebra.Lie.D4.Tripled.Basic`.
-/

public section

open scoped Matrix

namespace TauCeti.D4Tripled

open DynkinType

private def weylInt (i : Fin 4) : Matrix (Fin 24) (Fin 24) ℤ :=
  (1 + raisingMatrix i) * (1 - loweringMatrix i) * (1 + raisingMatrix i)

private theorem raising_mulVec_single (i : Fin 4) (a : Fin 24) :
    raisingMatrix i *ᵥ Pi.single a (1 : ℤ) =
      if d4TripledWeight a i = -1 then Pi.single (d4TripledReflection i a) 1 else 0 := by
  have h := weightTable.raisingMatrix_map_col (R := ℤ) i a
  ext b
  simpa [Matrix.mulVec_single_one, Matrix.col_apply, raisingMatrix_def,
    weightTable_weight, weightTable_reflection] using congrFun h b

private theorem lowering_mulVec_single (i : Fin 4) (a : Fin 24) :
    loweringMatrix i *ᵥ Pi.single a (1 : ℤ) =
      if d4TripledWeight a i = 1 then Pi.single (d4TripledReflection i a) 1 else 0 := by
  have h := weightTable.loweringMatrix_map_col (R := ℤ) i a
  ext b
  simpa [Matrix.mulVec_single_one, Matrix.col_apply, loweringMatrix_def,
    weightTable_weight, weightTable_reflection] using congrFun h b

private theorem weylInt_mulVec_single (i : Fin 4) (a : Fin 24) :
    weylInt i *ᵥ Pi.single a (1 : ℤ) =
      (if d4TripledWeight a i = 1 then -1 else 1) •
        Pi.single (d4TripledReflection i a) 1 := by
  have href : d4TripledWeight (d4TripledReflection i a) i = -d4TripledWeight a i := by
    simpa only [weightTable_weight, weightTable_reflection] using
      weightTable.weight_reflection_self i a
  have hzero (h : d4TripledWeight a i = 0) : d4TripledReflection i a = a := by
    simpa only [weightTable_reflection] using
      (weightTable.reflection_eq_self_iff i a).2
        (by simpa only [weightTable_weight] using h)
  rcases d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h
  · simp [weylInt, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_sub, raising_mulVec_single, lowering_mulVec_single,
      h, href, d4TripledReflection_apply_apply, -Matrix.mulVec_single]
  · simp [weylInt, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
      raising_mulVec_single, lowering_mulVec_single, h, hzero h, -Matrix.mulVec_single]
  · simp [weylInt, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.mulVec_sub, raising_mulVec_single, lowering_mulVec_single,
      h, href, d4TripledReflection_apply_apply, -Matrix.mulVec_single]

private abbrev stepSign (i : Fin 4) (a : Fin 24) : ℤ :=
  if d4TripledWeight a i = 1 then -1 else 1

-- These certificates check the signs as well as the underlying reflection permutations.
private theorem commuting_certificate (i j : Fin 4) (a : Fin 24)
    (hij : CartanMatrix.D 4 i j = 0) :
    d4TripledReflection i (d4TripledReflection j a) =
        d4TripledReflection j (d4TripledReflection i a) ∧
      stepSign j a * stepSign i (d4TripledReflection j a) =
        stepSign i a * stepSign j (d4TripledReflection i a) := by
  have hij' : weightTable.cartanMatrix i j = 0 := by
    simpa only [weightTable_cartanMatrix] using hij
  have hji := (weightTable.cartanMatrix_zero_comm i j).mp hij'
  constructor
  · simpa only [weightTable_reflection] using
      weightTable.reflection_comm_of_cartanMatrix_eq_zero i j a hij'
  · simp only [stepSign, ← weightTable_weight, ← weightTable_reflection,
      weightTable.weight_reflection_of_cartanMatrix_eq_zero j i a hji,
      weightTable.weight_reflection_of_cartanMatrix_eq_zero i j a hij']
    exact mul_comm _ _

private theorem braid_certificate (i j : Fin 4) (a : Fin 24)
    (hij : CartanMatrix.D 4 i j = -1) :
    d4TripledReflection i (d4TripledReflection j (d4TripledReflection i a)) =
        d4TripledReflection j (d4TripledReflection i (d4TripledReflection j a)) ∧
      (stepSign i a * stepSign j (d4TripledReflection i a)) *
          stepSign i (d4TripledReflection j (d4TripledReflection i a)) =
        (stepSign j a * stepSign i (d4TripledReflection j a)) *
          stepSign j (d4TripledReflection i (d4TripledReflection j a)) := by
  fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.D_four] at hij
  all_goals revert a; decide +kernel

private theorem commute_weylInt (i j : Fin 4) (hij : CartanMatrix.D 4 i j = 0) :
    weylInt i * weylInt j = weylInt j * weylInt i := by
  apply Matrix.ext_of_mulVec_single
  intro a
  have h := commuting_certificate i j a hij
  simp only [← Matrix.mulVec_mulVec, weylInt_mulVec_single, Matrix.mulVec_smul,
    smul_smul, h.1, h.2]

private theorem braid_weylInt (i j : Fin 4) (hij : CartanMatrix.D 4 i j = -1) :
    weylInt i * weylInt j * weylInt i = weylInt j * weylInt i * weylInt j := by
  apply Matrix.ext_of_mulVec_single
  intro a
  have h := braid_certificate i j a hij
  simpa only [← Matrix.mulVec_mulVec, weylInt_mulVec_single, Matrix.mulVec_smul,
    smul_smul, h.1, mul_assoc] using
      congrArg (fun c : ℤ ↦ c • (Pi.single
        (d4TripledReflection j (d4TripledReflection i (d4TripledReflection j a)))
        (1 : ℤ) : Fin 24 → ℤ)) h.2

private noncomputable def weylWord (A : Type*) [CommRing A] (i : Fin 4) : points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

private theorem coe_weylWord (A : Type*) [CommRing A] (i : Fin 4) :
    ((weylWord A i : Matrix.GeneralLinearGroup (Fin 24) A) : Matrix (Fin 24) (Fin 24) A) =
      (Int.castRingHom A).mapMatrix (weylInt i) := by
  simp only [weylWord, Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_inl,
    coe_rootSubgroupPoints_inr, toAdd_ofAdd, one_smul, neg_one_smul,
    weylInt, map_mul, map_add, map_neg, map_one, sub_eq_add_neg]
  -- The coefficient homomorphism underlying `mapMatrix` is the canonical integer cast.
  rfl

/-- Pinned simple-root Weyl words at orthogonal D₄ nodes commute over every commutative ring. -/
theorem commute_rootSubgroupPoints_weylWord_of_cartanMatrix_eq_zero (i j : Fin 4)
    (hij : CartanMatrix.D 4 i j = 0) (A : Type*) [CommRing A] :
    let w := fun k : Fin 4 ↦
      rootSubgroupPoints (.inl k) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr k) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl k) A (Multiplicative.ofAdd 1)
    Commute (w i) (w j) := by
  -- The displayed local word is precisely `weylWord`; keep its matrix comparison bundled
  -- while passing through the subgroup and unit inclusions.
  change weylWord A i * weylWord A j = weylWord A j * weylWord A i
  apply Subtype.ext
  apply Units.ext
  have h := congrArg ((Int.castRingHom A).mapMatrix) (commute_weylInt i j hij)
  simp only [map_mul, ← coe_weylWord] at h
  exact h

/-- Pinned simple-root Weyl words at adjacent D₄ nodes satisfy the length-three braid relation,
with their signs unchanged, over every commutative ring. -/
theorem rootSubgroupPoints_weylWord_braid_of_cartanMatrix_eq_neg_one (i j : Fin 4)
    (hij : CartanMatrix.D 4 i j = -1) (A : Type*) [CommRing A] :
    let w := fun k : Fin 4 ↦
      rootSubgroupPoints (.inl k) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr k) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl k) A (Multiplicative.ofAdd 1)
    w i * w j * w i = w j * w i * w j := by
  -- The displayed local word is `weylWord`; its matrix is the scalar extension of `weylInt`.
  change weylWord A i * weylWord A j * weylWord A i =
    weylWord A j * weylWord A i * weylWord A j
  apply Subtype.ext
  apply Units.ext
  have h := congrArg ((Int.castRingHom A).mapMatrix) (braid_weylInt i j hij)
  simp only [map_mul, ← coe_weylWord] at h
  exact h

end TauCeti.D4Tripled
