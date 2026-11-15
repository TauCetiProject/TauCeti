/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Opposite-root Gauss factorization in the E₆ minuscule carrier

At each numbered simple root, collect a positive root point followed by a negative root point
into negative-root, coroot, and positive-root factors. Only `1 + a * b` must be a unit;
the root parameters themselves need not be units. The coroot is evaluated through the existing
weight torus in fundamental-weight coordinates, so its value is `Pi.mulSingle i u`.
The reverse multiplication order uses the inverse coroot value.

The identities hold over every commutative ring, including nonreduced rings and rings of bad
characteristic. They are rank-one relations for the explicitly constructed carrier, not an
identification with the pinned simply connected group scheme.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.1.
* The formal construction uses `TauCeti.E6Minuscule.rootSubgroupPoints`, its minuscule matrix
  formulas, and `TauCeti.MinusculeWeightTable.raisingMatrix_map_col` and
  `loweringMatrix_map_col` for the sparse action on weight vectors.
-/

public section

open scoped Matrix

namespace TauCeti.E6Minuscule

open TauCeti.DynkinType TauCeti.UniversalEnvelopingAlgebra

universe v

variable {A : Type v} [CommRing A]

private theorem positive_mulVec_single (i : Fin 6) (t c : A) (a : Fin 27) :
    ((rootSubgroupPoints (.inl i) A (.ofAdd t) : Matrix.GeneralLinearGroup (Fin 27) A) :
        Matrix (Fin 27) (Fin 27) A) *ᵥ Pi.single a c =
      Pi.single a c +
        if e6MinusculeWeight a i = -1 then Pi.single (e6MinusculeReflection i a) (t * c)
        else 0 := by
  rw [coe_rootSubgroupPoints_inl, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_single]
  have h := weightTable.raisingMatrix_map_col (R := A) i a
  simp only [weightTable_weight, weightTable_reflection] at h
  ext b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toAdd_ofAdd,
    Pi.zero_apply, ite_apply]
  rw [congrFun h b]
  split_ifs <;> simp_all [Pi.single_apply]

private theorem negative_mulVec_single (i : Fin 6) (t c : A) (a : Fin 27) :
    ((rootSubgroupPoints (.inr i) A (.ofAdd t) : Matrix.GeneralLinearGroup (Fin 27) A) :
        Matrix (Fin 27) (Fin 27) A) *ᵥ Pi.single a c =
      Pi.single a c +
        if e6MinusculeWeight a i = 1 then Pi.single (e6MinusculeReflection i a) (t * c)
        else 0 := by
  rw [coe_rootSubgroupPoints_inr, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.mulVec_single]
  have h := weightTable.loweringMatrix_map_col (R := A) i a
  simp only [weightTable_weight, weightTable_reflection] at h
  ext b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toAdd_ofAdd,
    Pi.zero_apply, ite_apply]
  rw [congrFun h b]
  split_ifs <;> simp_all [Pi.single_apply]

private theorem coroot_mulVec_single (i : Fin 6) (u : Aˣ) (c : A) (a : Fin 27) :
    ((weightTorusPoints A (Pi.mulSingle i u) : Matrix.GeneralLinearGroup (Fin 27) A) :
        Matrix (Fin 27) (Fin 27) A) *ᵥ Pi.single a c =
      Pi.single a ((↑(u ^ e6MinusculeWeight a i) : A) * c) := by
  rw [coe_weightTorusPoints, kostantTorusMatrix_apply, diagGL_coe]
  ext b
  by_cases h : b = a
  · subst b
    simp [Matrix.mulVec_single, torusCharacter_mulSingle]
  · simp [Matrix.mulVec_single, h]

/-- The opposite-simple-root Gauss relation in the E₆ minuscule carrier. In fundamental-weight
coordinates `Pi.mulSingle i u` is the value of the numbered simple coroot. No invertibility of
`a` or `b` is required. -/
theorem rootSubgroupPoints_inl_mul_inr (i : Fin 6) (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (.ofAdd a) *
        rootSubgroupPoints (.inr i) A (.ofAdd b) =
      rootSubgroupPoints (.inr i) A (.ofAdd (b * ↑u⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i u) *
        rootSubgroupPoints (.inl i) A (.ofAdd (a * ↑u⁻¹)) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  apply Matrix.ext_of_mulVec_single
  intro w
  have hs := weightTable.reflection_apply_apply i w
  simp only [weightTable_reflection] at hs
  have hinv : (↑u⁻¹ : A) * (1 + a * b) = 1 := by
    rw [← hu]
    exact Units.inv_mul u
  have hcancel : (↑u : A) * (a * ↑u⁻¹) = a := by
    simpa only [mul_comm a (↑u⁻¹ : A)] using Units.mul_inv_cancel_left u a
  have hcancel' : b * (↑u⁻¹ : A) * ↑u = b := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  -- The weight basis splits into trivial strings and two-dimensional simple-root strings.
  rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one w i with hw | hw | hw
  all_goals
    have hr := e6MinusculeWeight_reflection_apply_self i w
    rw [hw] at hr
    norm_num only at hr
    simp only [← Matrix.mulVec_mulVec, positive_mulVec_single, negative_mulVec_single,
      coroot_mulVec_single, Matrix.mulVec_add, hw,
      zpow_neg_one, zpow_zero, zpow_one, Units.val_one, mul_one]
    norm_num only
    simp only [ite_true, ite_false, Matrix.mulVec_zero, add_zero,
      positive_mulVec_single, negative_mulVec_single, coroot_mulVec_single,
      hr, hs, zpow_one, hcancel, hcancel']
  -- After collecting each string, only the scalar identity u⁻¹(1 + ab) = 1 remains.
  all_goals
    ext k
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;>
      (try simp only [add_zero, zero_add, hu]) <;>
      first | ring1 | linear_combination -hinv

/-- The reverse opposite-simple-root Gauss relation. The middle factor is the inverse
simple-coroot value, while the two root parameters are divided by `1 + a * b`. -/
theorem rootSubgroupPoints_inr_mul_inl (i : Fin 6) (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inr i) A (.ofAdd a) *
        rootSubgroupPoints (.inl i) A (.ofAdd b) =
      rootSubgroupPoints (.inl i) A (.ofAdd (b * ↑u⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i u⁻¹) *
        rootSubgroupPoints (.inr i) A (.ofAdd (a * ↑u⁻¹)) := by
  have h := congrArg Inv.inv
    (rootSubgroupPoints_inl_mul_inr i (-b) (-a) u (by simpa [mul_comm] using hu))
  simpa [mul_inv_rev, ← map_inv, ← Pi.mulSingle_inv, mul_assoc] using h

end TauCeti.E6Minuscule
