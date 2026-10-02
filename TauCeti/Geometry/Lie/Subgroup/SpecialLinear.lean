/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Exponential.Matrix.SpecialLinear
public import TauCeti.Geometry.Lie.Subgroup.Units

/-!
# The Lie algebra of the real special linear group

The special linear group sits inside the general linear group as the image of
`Matrix.SpecialLinearGroup.toGL`, a subgroup of `GL n ℝ = (Matrix n n ℝ)ˣ`, which is a Lie group.
This file computes the Lie algebra that `TauCeti.Lie.lieSubalgebraOfSubgroup` assigns to it: in
the canonical matrix coordinates of the general linear Lie algebra it is Mathlib's special linear
Lie algebra `LieAlgebra.SpecialLinear.sl n ℝ`, the matrices of trace zero.

Two inputs meet here: the matrix-level characterization of the exponential lines that stay inside
the special linear group, `Matrix.forall_det_exp_smul_eq_one_iff_mem_sl`, which rests on
`det (exp A) = exp (trace A)`, and the algebra-coordinate form of the Lie algebra of a closed
subgroup of units, `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff`,
whose closedness hypothesis is supplied by Mathlib's
`Matrix.SpecialLinearGroup.isClosedEmbedding_toGL`.

## Main results

* `TauCeti.Lie.forall_lieExp_mem_range_toGL_iff_mem_sl`: in canonical matrix coordinates, the
  abstract exponential line of `A` stays inside the special linear subgroup exactly when `A` has
  trace zero.
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sl`: **the Lie
  algebra of the special linear group is `sl`.**
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

-- Select the matrix topology underlying the operator norm used for the general linear Lie group.
attribute [local instance] Matrix.linftyOpTopologicalSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- In the canonical matrix coordinates of the general linear Lie algebra, an element generates a
one-parameter subgroup inside the special linear group exactly when it has trace zero. -/
-- Normalize the whole exponential-line predicate before subgroup membership expands.
@[simp↓]
theorem forall_lieExp_mem_range_toGL_iff_mem_sl (A : Matrix n n ℝ) :
    (∀ t : ℝ, lieExp ((unitsLieAlgebraLieEquiv (R := Matrix n n ℝ)).symm (t • A)) ∈
        (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup n ℝ →* GL n ℝ).range) ↔
      A ∈ LieAlgebra.SpecialLinear.sl n ℝ := by
  rw [forall_lieExp_unitsLieAlgebraLieEquiv_symm_smul_mem_iff,
    ← Matrix.forall_det_exp_smul_eq_one_iff_mem_sl]
  simp only [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, Units.ext_iff,
    Matrix.GeneralLinearGroup.val_det_apply, TauCeti.expUnit_coe, Units.val_one]
  -- Both sides now read `∀ t, (exp (t • A)).det = 1`. They differ only in the instances inside
  -- `exp`: the ring and topology of the operator-norm normed ring on the left, the default matrix
  -- ring and the entrywise topology on the right, which agree definitionally.
  exact Iff.rfl

/-- **The Lie algebra of the real special linear group is `sl`.** A matrix has trace zero exactly
when its inverse image under the canonical units Lie equivalence belongs to the Lie subalgebra of
the special linear subgroup of the general linear group. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sl
    (A : Matrix n n ℝ) :
    (unitsLieAlgebraLieEquiv (R := Matrix n n ℝ)).symm A ∈
        lieSubalgebraOfSubgroup
          ((Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup n ℝ →* GL n ℝ).range :
            Subgroup (Matrix n n ℝ)ˣ) ↔
      A ∈ LieAlgebra.SpecialLinear.sl n ℝ := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff
      (MonoidHom.coe_range (Matrix.SpecialLinearGroup.toGL (n := n) (R := ℝ)) ▸
        Matrix.SpecialLinearGroup.isClosedEmbedding_toGL.isClosed_range),
    ← Matrix.forall_det_exp_smul_eq_one_iff_mem_sl]
  simp only [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, Units.ext_iff,
    Matrix.GeneralLinearGroup.val_det_apply, TauCeti.expUnit_coe, Units.val_one]
  -- Both sides now read `∀ t, (exp (t • A)).det = 1`. They differ only in the instances inside
  -- `exp`: the ring and topology of the operator-norm normed ring on the left, the default matrix
  -- ring and the entrywise topology on the right, which agree definitionally.
  exact Iff.rfl

end TauCeti.Lie
