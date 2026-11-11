/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier

/-!
# Opposite-root Gauss factorization in the E₇ minuscule carrier

At each numbered simple root, a product of positive and negative root points admits a
negative–torus–positive factorization whenever `1 + a * b` is a unit. The middle factor is
its simple-coroot value in the existing weight torus. The reverse multiplication order gives
the inverse coroot. Both identities hold over arbitrary commutative rings, including rings
with nilpotents and rings of characteristic two.

The calculation uses the nontrivial length-two weight strings of `E7Minuscule.weightTable`,
the root matrices and diagonal weight torus of `TauCeti.Algebra.Lie.E7.Minuscule.Carrier`.
It does not identify this explicit carrier with an independently pinned simply connected group
scheme.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, the rank-one relations.
* R. W. Carter, *Simple Groups of Lie Type*.
-/

public section

namespace TauCeti.E7Minuscule

open DynkinType _root_.Matrix
open scoped Matrix
open Multiplicative

universe v

variable {A : Type v} [CommRing A]

private theorem positive_mulVec_single (i : Fin 7) (a c : A) (w : Fin 56) :
    ((rootSubgroupPoints (.inl i) A (ofAdd a) : GeneralLinearGroup (Fin 56) A) :
        Matrix (Fin 56) (Fin 56) A) *ᵥ Pi.single w c =
      Pi.single w c + if e7MinusculeWeight w i = -1 then
        Pi.single (e7MinusculeReflection i w) (a * c) else 0 := by
  rw [coe_rootSubgroupPoints_inl, ← weightTable_raisingMatrix]
  simp only [toAdd_ofAdd, add_mulVec, one_mulVec, smul_mulVec]
  simp only [mulVec_single, weightTable.raisingMatrix_map_col,
    weightTable_weight, weightTable_reflection]
  split <;> simp [← Pi.single_smul', smul_eq_mul]

private theorem negative_mulVec_single (i : Fin 7) (b c : A) (w : Fin 56) :
    ((rootSubgroupPoints (.inr i) A (ofAdd b) : GeneralLinearGroup (Fin 56) A) :
        Matrix (Fin 56) (Fin 56) A) *ᵥ Pi.single w c =
      Pi.single w c + if e7MinusculeWeight w i = 1 then
        Pi.single (e7MinusculeReflection i w) (b * c) else 0 := by
  rw [coe_rootSubgroupPoints_inr, ← weightTable_loweringMatrix]
  simp only [toAdd_ofAdd, add_mulVec, one_mulVec, smul_mulVec]
  simp only [mulVec_single, weightTable.loweringMatrix_map_col,
    weightTable_weight, weightTable_reflection]
  split <;> simp [← Pi.single_smul', smul_eq_mul]

private theorem coroot_mulVec_single (i : Fin 7) (u : Aˣ) (c : A) (w : Fin 56) :
    ((weightTorusPoints A (Pi.mulSingle i u) : GeneralLinearGroup (Fin 56) A) :
        Matrix (Fin 56) (Fin 56) A) *ᵥ Pi.single w c =
      Pi.single w ((u ^ e7MinusculeWeight w i : Aˣ) * c) := by
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    diagGL_coe, diagonal_mulVec_single]
  simp

/-- Opposite simple-root points factor in negative–coroot–positive order on the open set
where `1 + a * b` is invertible. The torus parameter is the numbered simple coroot. -/
theorem rootSubgroupPoints_inl_mul_inr (i : Fin 7) (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (ofAdd a) * rootSubgroupPoints (.inr i) A (ofAdd b) =
      rootSubgroupPoints (.inr i) A (ofAdd (b * ↑(u⁻¹))) *
        weightTorusPoints A (Pi.mulSingle i u) *
        rootSubgroupPoints (.inl i) A (ofAdd (a * ↑(u⁻¹))) := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro w
  have href : e7MinusculeWeight (e7MinusculeReflection i w) i =
      -e7MinusculeWeight w i := by
    simpa only [weightTable_weight, weightTable_reflection] using
      weightTable.weight_reflection_self i w
  have hinv : (1 + a * b) * (↑(u⁻¹) : A) = 1 := by
    rw [← hu]
    exact Units.mul_inv u
  simp only [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec,
    positive_mulVec_single, negative_mulVec_single, mulVec_add, coroot_mulVec_single]
  rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one w i with hw | hw | hw
  all_goals
    simp only [positive_mulVec_single, negative_mulVec_single, coroot_mulVec_single,
      hw, href, neg_neg, zero_ne_one, ↓reduceIte,
      e7MinusculeReflection_apply_apply, _root_.zpow_neg_one, zpow_zero, zpow_one,
      Units.val_one, mul_one, add_zero, mulVec_zero]
    ext r
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> (try simp only [mulVec_zero, Pi.zero_apply, add_zero, zero_add]) <;> grind

/-- In the reverse order, opposite simple-root points factor in positive–coroot–negative
order, with inverse simple-coroot parameter. -/
theorem rootSubgroupPoints_inr_mul_inl (i : Fin 7) (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inr i) A (ofAdd b) * rootSubgroupPoints (.inl i) A (ofAdd a) =
      rootSubgroupPoints (.inl i) A (ofAdd (a * ↑(u⁻¹))) *
        weightTorusPoints A (Pi.mulSingle i u⁻¹) *
        rootSubgroupPoints (.inr i) A (ofAdd (b * ↑(u⁻¹))) := by
  have h := congrArg Inv.inv (rootSubgroupPoints_inl_mul_inr i (-a) (-b) u (by
    simpa using hu))
  simpa only [_root_.mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv, neg_mul,
    ← Pi.mulSingle_inv, mul_assoc] using h

end TauCeti.E7Minuscule
