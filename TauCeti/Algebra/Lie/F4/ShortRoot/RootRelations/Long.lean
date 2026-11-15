/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.RootSubgroup
import TauCeti.Algebra.Ring.Commutator
import TauCeti.LinearAlgebra.Matrix.Step

/-!
# The adjacent-long-root Chevalley relation in the short-root F₄ carrier

The two long simple roots at Bourbaki nodes zero and one span a subsystem of type A₂.
Their commutator is the root subgroup at their sum, parametrized by conjugating the
second simple-root subgroup by the pinned Weyl representative of the first node:
`[x₀(a), x₁(b)] = n₀ x₁(ab) n₀⁻¹`.

This fixes the sign of the nonsimple-root parameter against an existing Weyl presentation,
not an independently chosen root vector. The relation holds over every commutative ring,
including rings with nilpotents. It follows from the integral generator matrices and
`Units.val_commutatorElement_eq_one_add_lie`; no division by a bad prime is used.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.

The matrix transport follows
`TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`.
-/

public section

namespace TauCeti.F4ShortRoot

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

universe v

private theorem raising_zero_one_zero :
    raisingMatrix 0 * raisingMatrix 1 * raisingMatrix 0 = 0 := by
  have h0 := Matrix.isStep_of_apply (raisingMatrix_apply 0)
  have h1 := Matrix.isStep_of_apply (raisingMatrix_apply 1)
  ext a b
  rw [((h0.mul h1).mul h0).apply, Matrix.zero_apply]
  revert a b
  decide +kernel

private theorem raising_one_zero_one :
    raisingMatrix 1 * raisingMatrix 0 * raisingMatrix 1 = 0 := by
  have h0 := Matrix.isStep_of_apply (raisingMatrix_apply 0)
  have h1 := Matrix.isStep_of_apply (raisingMatrix_apply 1)
  ext a b
  rw [((h1.mul h0).mul h1).apply, Matrix.zero_apply]
  revert a b
  decide +kernel

private theorem long_weyl_mul_raising :
    ((1 + raisingMatrix 0) * (1 - loweringMatrix 0) * (1 + raisingMatrix 0)) *
        raisingMatrix 1 =
      (raisingMatrix 0 * raisingMatrix 1 - raisingMatrix 1 * raisingMatrix 0) *
        ((1 + raisingMatrix 0) * (1 - loweringMatrix 0) * (1 + raisingMatrix 0)) := by
  have h0 := Matrix.isStep_of_apply (raisingMatrix_apply 0)
  have h1 := Matrix.isStep_of_apply (raisingMatrix_apply 1)
  have hf := Matrix.isStep_of_apply (loweringMatrix_apply 0)
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, ← mul_assoc]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply]
  simp only [h1.apply, (h0.mul h1).apply, (hf.mul h1).apply,
    ((h0.mul h0).mul h1).apply, (((h0.mul h1).mul h0).mul h0).apply,
    (((h1.mul h0).mul h0).mul h0).apply,
    ((h0.mul hf).mul h1).apply, ((hf.mul h0).mul h1).apply,
    (((h0.mul hf).mul h0).mul h1).apply,
    ((h0.mul h1).mul h0).apply, ((h0.mul h1).mul hf).apply,
    (((h0.mul h1).mul h0).mul hf).apply, (((h0.mul h1).mul hf).mul h0).apply,
    ((((h0.mul h1).mul h0).mul hf).mul h0).apply,
    (h1.mul h0).apply, ((h1.mul h0).mul h0).apply,
    ((h1.mul h0).mul hf).apply, (((h1.mul h0).mul h0).mul hf).apply,
    (((h1.mul h0).mul hf).mul h0).apply,
    ((((h1.mul h0).mul h0).mul hf).mul h0).apply]
  revert a b
  decide +kernel

private theorem coe_weylRootSubgroupPoints_zero_one (A : Type v) [CommRing A] (t : A) :
    ((weylRootSubgroupPoints [0] 1 A (Multiplicative.ofAdd t) :
        Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) =
      1 + t • (raisingMatrix 0 * raisingMatrix 1 - raisingMatrix 1 * raisingMatrix 0).map
        (Int.cast : ℤ → A) := by
  let f : Matrix (Fin 26) (Fin 26) ℤ →+* Matrix (Fin 26) (Fin 26) A :=
    (Int.castRingHom A).mapMatrix
  let N := (1 + raisingMatrix 0) * (1 - loweringMatrix 0) * (1 + raisingMatrix 0)
  have hf (X : Matrix (Fin 26) (Fin 26) ℤ) :
      f X = X.map (Int.cast : ℤ → A) := by
    ext i j
    simp [f]
  have hn : ((simpleWeylPoint 0 A : Matrix.GeneralLinearGroup (Fin 26) A) :
      Matrix (Fin 26) (Fin 26) A) = f N := by
    simp only [simpleWeylPoint_def, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      coe_rootSubgroupPoints_inl_of_lt_two 0 (by decide),
      coe_rootSubgroupPoints_inr_of_lt_two 0 (by decide), toAdd_ofAdd,
      one_smul, neg_smul]
    simp only [N, map_mul, map_add, map_sub, map_one]
    simp only [hf, sub_eq_add_neg]
  have hc : f N * f (raisingMatrix 1) =
      f (raisingMatrix 0 * raisingMatrix 1 - raisingMatrix 1 * raisingMatrix 0) * f N := by
    simpa only [N, map_mul] using congrArg f long_weyl_mul_raising
  apply (Units.mul_left_inj (simpleWeylPoint 0 A :
    Matrix.GeneralLinearGroup (Fin 26) A)).mp
  rw [weylRootSubgroupPoints_cons, weylRootSubgroupPoints_nil]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one, Units.val_mul,
    coe_rootSubgroupPoints_inl_of_lt_two 1 (by decide), toAdd_ofAdd, hn]
  -- The ring homomorphism `f` is entrywise integer casting; expose it to match `hc`.
  change f N * (1 + t • f (raisingMatrix 1)) =
    (1 + t • f (raisingMatrix 0 * raisingMatrix 1 - raisingMatrix 1 * raisingMatrix 0)) * f N
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
  rw [hc]

/-- **The nonzero Chevalley relation at the adjacent long simple roots of F₄.**
The sum-root parametrization is the pinned Weyl conjugate `n₀ x₁(t) n₀⁻¹`, so its
parameter is exactly `a * b`, with no unspecified sign. -/
theorem commutatorElement_rootSubgroupPoints_long (A : Type v) [CommRing A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd a),
      rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd b)⁆ =
        weylRootSubgroupPoints [0] 1 A (Multiplicative.ofAdd (a * b)) := by
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_weylRootSubgroupPoints_zero_one]
  let f : Matrix (Fin 26) (Fin 26) ℤ →+* Matrix (Fin 26) (Fin 26) A :=
    (Int.castRingHom A).mapMatrix
  have hf (X : Matrix (Fin 26) (Fin 26) ℤ) :
      f X = X.map (Int.cast : ℤ → A) := by
    ext i j
    simp [f]
  have hAA : f (raisingMatrix 0) * f (raisingMatrix 0) = 0 := by
    rw [← map_mul, raisingMatrix_mul_self_of_lt_two 0 (by decide), map_zero]
  have hBB : f (raisingMatrix 1) * f (raisingMatrix 1) = 0 := by
    rw [← map_mul, raisingMatrix_mul_self_of_lt_two 1 (by decide), map_zero]
  have hABA : f (raisingMatrix 0) * f (raisingMatrix 1) * f (raisingMatrix 0) = 0 := by
    rw [← map_mul, ← map_mul, raising_zero_one_zero, map_zero]
  have hBAB : f (raisingMatrix 1) * f (raisingMatrix 0) * f (raisingMatrix 1) = 0 := by
    rw [← map_mul, ← map_mul, raising_one_zero_one, map_zero]
  rw [← hf]
  rw [Units.val_commutatorElement_eq_one_add_lie _ _ (a • f (raisingMatrix 0))
    (b • f (raisingMatrix 1))]
  · simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub,
      mul_comm, map_sub, map_mul]
  · rw [coe_rootSubgroupPoints_inl_of_lt_two 0 (by decide), hf]
    rfl
  · rw [coe_rootSubgroupPoints_inl_of_lt_two 1 (by decide), hf]
    rfl
  · simp only [smul_mul_assoc, mul_smul_comm, hAA, smul_zero]
  · simp only [smul_mul_assoc, mul_smul_comm, hBB, smul_zero]
  · simp only [smul_mul_assoc, mul_smul_comm, hABA, smul_zero]
  · simp only [smul_mul_assoc, mul_smul_comm, hBAB, smul_zero]

/-- Reversing the adjacent long roots negates the parameter in the same sum-root
parametrization. -/
theorem commutatorElement_rootSubgroupPoints_long_reverse (A : Type v) [CommRing A]
    (a b : A) :
    ⁅rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd b),
      rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd a)⁆ =
        weylRootSubgroupPoints [0] 1 A (Multiplicative.ofAdd (-(a * b))) := by
  rw [← commutatorElement_inv, commutatorElement_rootSubgroupPoints_long,
    ← map_inv, ← ofAdd_neg]

end TauCeti.F4ShortRoot
