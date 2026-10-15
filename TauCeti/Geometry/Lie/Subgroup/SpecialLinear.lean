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
# The Lie algebra of the special linear group

Over `ℝ` or `ℂ` (any `RCLike` field `𝕂`) the special linear group sits inside the general linear
group as the image of `Matrix.SpecialLinearGroup.toGL`, a subgroup of `GL n 𝕂 = (Matrix n n 𝕂)ˣ`,
which is a Lie group over `ℝ`.  This file computes the Lie algebra that
`TauCeti.Lie.lieSubalgebraOfSubgroup` assigns to it: in the canonical matrix coordinates of the
general linear Lie algebra it is Mathlib's special linear Lie algebra
`LieAlgebra.SpecialLinear.sl n 𝕂`, the matrices of trace zero.

Two inputs meet here: the matrix-level characterization of the exponential lines that stay inside
the special linear group, `Matrix.forall_det_exp_smul_eq_one_iff_mem_sl`, which rests on
`det (exp A) = exp (trace A)`, and the algebra-coordinate form of the Lie algebra of a closed
subgroup of units, `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff`,
whose closedness hypothesis is supplied by Mathlib's
`Matrix.SpecialLinearGroup.isClosedEmbedding_toGL`.

Over `ℂ` the Lie algebra is taken over `ℝ`, as it must be: `GL n ℂ` is here a *real* Lie group of
twice the complex dimension, and `sl n ℂ` is its real Lie subalgebra of trace-zero matrices,
which happens to be a complex subspace.  The determinant condition still cuts out trace zero
rather than only `trace A ∈ 2πiℤ`, because the whole exponential line is required to have
determinant one.

## Main results

* `TauCeti.Lie.forall_lieExp_mem_range_toGL_iff_mem_sl`: in canonical matrix coordinates, the
  abstract exponential line of `A` stays inside the special linear subgroup exactly when `A` has
  trace zero.
* `TauCeti.Lie.isClosed_range_toGL`: the special linear subgroup of the units is closed, the
  hypothesis every closed-subgroup statement about it needs.
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

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕂 : Type*} [RCLike 𝕂]

/-- **The special linear subgroup of the units is closed.**  Its carrier is the range of the
closed embedding `Matrix.SpecialLinearGroup.toGL`.  This is the form in which the closed-subgroup
theorem, and every statement resting on it, consumes the special linear group. -/
theorem isClosed_range_toGL :
    IsClosed (((Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup n 𝕂 →* GL n 𝕂).range : Subgroup (Matrix n n 𝕂)ˣ) :
      Set (Matrix n n 𝕂)ˣ) :=
  MonoidHom.coe_range (Matrix.SpecialLinearGroup.toGL (n := n) (R := 𝕂)) ▸
    Matrix.SpecialLinearGroup.isClosedEmbedding_toGL.isClosed_range

/-- In the canonical matrix coordinates of the general linear Lie algebra, an element generates a
one-parameter subgroup inside the special linear group exactly when it has trace zero. -/
-- Normalize the whole exponential-line predicate before subgroup membership expands.
@[simp↓]
theorem forall_lieExp_mem_range_toGL_iff_mem_sl (A : Matrix n n 𝕂) :
    (∀ t : ℝ, lieExp ((unitsLieAlgebraLieEquiv (R := Matrix n n 𝕂)).symm (t • A)) ∈
        (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup n 𝕂 →* GL n 𝕂).range) ↔
      A ∈ LieAlgebra.SpecialLinear.sl n 𝕂 := by
  rw [forall_lieExp_unitsLieAlgebraLieEquiv_symm_smul_mem_iff,
    ← Matrix.forall_det_exp_smul_eq_one_iff_mem_sl]
  simp only [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, Units.ext_iff,
    Matrix.GeneralLinearGroup.val_det_apply, TauCeti.expUnit_coe, Units.val_one]
  -- Both sides now read `∀ t, (exp (t • A)).det = 1`. They differ only in the instances inside
  -- `exp`: the ring and topology of the operator-norm normed ring on the left, the default matrix
  -- ring and the entrywise topology on the right, which agree definitionally.
  exact Iff.rfl

/-- **The Lie algebra of the special linear group is `sl`.** A matrix has trace zero exactly
when its inverse image under the canonical units Lie equivalence belongs to the Lie subalgebra of
the special linear subgroup of the general linear group. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sl
    (A : Matrix n n 𝕂) :
    (unitsLieAlgebraLieEquiv (R := Matrix n n 𝕂)).symm A ∈
        lieSubalgebraOfSubgroup
          ((Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup n 𝕂 →* GL n 𝕂).range :
            Subgroup (Matrix n n 𝕂)ˣ) ↔
      A ∈ LieAlgebra.SpecialLinear.sl n 𝕂 := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff isClosed_range_toGL,
    ← Matrix.forall_det_exp_smul_eq_one_iff_mem_sl]
  simp only [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, Units.ext_iff,
    Matrix.GeneralLinearGroup.val_det_apply, TauCeti.expUnit_coe, Units.val_one]
  -- Both sides now read `∀ t, (exp (t • A)).det = 1`. They differ only in the instances inside
  -- `exp`: the ring and topology of the operator-norm normed ring on the left, the default matrix
  -- ring and the entrywise topology on the right, which agree definitionally.
  exact Iff.rfl

end TauCeti.Lie
