/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.Basic
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Exponential.Unitary
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.Topology.Algebra.Star.Unitary
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.RCLike.Basic

/-!
# The Lie algebra of the unitary group

For a finite-dimensional real normed star algebra `R`, the unitary elements of `Rˣ` form a closed
subgroup `unitarySubgroup Rˣ` of the Lie group `Rˣ`.  This file computes the Lie algebra that
`TauCeti.Lie.lieSubalgebraOfSubgroup` assigns to it: in the canonical algebra coordinates of
`TauCeti.Lie.unitsLieAlgebraLieEquiv` it is `skewAdjoint R`, the elements with `star x = -x`.

Two inputs meet here: the characterization of the exponential lines that stay unitary,
`TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint`, and the algebra-coordinate form of the
Lie algebra of a closed subgroup of units,
`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff`, whose closedness
hypothesis is supplied by `TauCeti.isClosed_unitarySubgroup_units`.

Specialized to `R = Matrix n n 𝕜` with `𝕜 = ℝ` or `ℂ` this is the classical statement that the
Lie algebra of the unitary matrix group is the skew-Hermitian matrices, `Aᴴ = -A`: over `ℂ` the
unitary Lie algebra `𝔲 n`, and over `ℝ`, where the conjugate transpose is the transpose, the
orthogonal Lie algebra `LieAlgebra.Orthogonal.so n ℝ`.  The subgroup appearing there,
`unitarySubgroup (Matrix n n 𝕜)ˣ`, is the preimage of Mathlib's `Matrix.unitaryGroup n 𝕜`, which
is `unitary (Matrix n n 𝕜)`, under the coercion `Units.val`; that is Mathlib's
`Units.unitary_eq`.  Unlike the symplectic and special orthogonal computations, which are
matrix-level from the start, nothing here is special to matrices, so the general algebra is the
natural altitude and the matrix groups are read off from it.

Over `ℝ` this meets `TauCeti/Geometry/Lie/Subgroup/SpecialOrthogonal.lean` without overlapping
it: that file computes the Lie algebra of the *special* orthogonal carrier cut out by a quadratic
form, this one the Lie algebra of the full orthogonal group `unitarySubgroup (Matrix n n ℝ)ˣ`.
The two subgroups differ, and their Lie algebras agree because the special orthogonal group is
open in the orthogonal one, so the two have the same exponential lines through `1`.

The *special* unitary group needs `det (exp A) = exp (Matrix.trace A)` to cut it out of the
unitary group, and is not treated here.

## Main results

* `TauCeti.Lie.forall_lieExp_mem_unitarySubgroup_iff_mem_skewAdjoint`: in algebra coordinates, the
  abstract exponential line of `x` stays unitary exactly when `x` is skew-adjoint.
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_skewAdjoint`:
  **the Lie algebra of the unitary group is the skew-adjoint elements.**
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg`:
  the matrix form, with the skew-adjointness spelled out as `Aᴴ = -A`.
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_so`: over `ℝ` the
  unitary matrix group is the orthogonal group, and its Lie algebra is Mathlib's `so`.
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

section Algebra

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] [StarRing R]
  [ContinuousStar R] [StarModule ℝ R]

local instance finiteDimensionalCompleteSpaceUnitary : CompleteSpace R :=
  FiniteDimensional.complete ℝ R

/-- In the canonical algebra coordinates of the Lie algebra of `Rˣ`, an element generates a
one-parameter subgroup of unitaries exactly when it is skew-adjoint. -/
-- Normalize the whole exponential-line predicate before subgroup membership expands.
@[simp↓]
theorem forall_lieExp_mem_unitarySubgroup_iff_mem_skewAdjoint (x : R) :
    (∀ t : ℝ, lieExp ((unitsLieAlgebraLieEquiv (R := R)).symm (t • x)) ∈
        unitarySubgroup Rˣ) ↔ x ∈ skewAdjoint R := by
  rw [forall_lieExp_unitsLieAlgebraLieEquiv_symm_smul_mem_iff,
    ← forall_exp_smul_mem_unitary_iff_mem_skewAdjoint]
  simp only [mem_unitarySubgroup_iff, Units.unitary_eq, Submonoid.mem_comap,
    Units.coeHom_apply, TauCeti.expUnit_coe]

/-- **The Lie algebra of the unitary group is the skew-adjoint elements.**  An element of a
finite-dimensional real normed star algebra belongs to the Lie algebra of the closed subgroup of
unitary units exactly when `star x = -x`. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_skewAdjoint (x : R) :
    (unitsLieAlgebraLieEquiv (R := R)).symm x ∈
        lieSubalgebraOfSubgroup (unitarySubgroup Rˣ) ↔ x ∈ skewAdjoint R :=
  -- Membership in the Lie algebra is the exponential line of `x` staying unitary, which is the
  -- previous theorem once the line is read in algebra coordinates.
  (unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff
        (isClosed_unitarySubgroup_units R) x).trans
    ((forall_lieExp_unitsLieAlgebraLieEquiv_symm_smul_mem_iff _ x).symm.trans
      (forall_lieExp_mem_unitarySubgroup_iff_mem_skewAdjoint x))

end Algebra

section Matrix

-- Select the matrix topology underlying the operator norm used for the general linear Lie group,
-- together with continuity of the conjugate transpose for it.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **The Lie algebra of the unitary matrix group is the skew-Hermitian matrices.**  Over `ℂ`
this is `𝔲 n`; over `ℝ`, where the conjugate transpose is the transpose, it is the orthogonal Lie
algebra. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg
    (A : Matrix n n 𝕜) :
    (unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).symm A ∈
        lieSubalgebraOfSubgroup (unitarySubgroup (Matrix n n 𝕜)ˣ) ↔ Aᴴ = -A := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_skewAdjoint,
    skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose]

/-- The real unitary matrix Lie algebra is Mathlib's orthogonal Lie algebra: over `ℝ` the
conjugate transpose is the transpose, so skew-Hermitian is skew-symmetric. -/
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_so (A : Matrix n n ℝ) :
    (unitsLieAlgebraLieEquiv (R := Matrix n n ℝ)).symm A ∈
        lieSubalgebraOfSubgroup (unitarySubgroup (Matrix n n ℝ)ˣ) ↔
      A ∈ LieAlgebra.Orthogonal.so n ℝ :=
  (unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_skewAdjoint A).trans
    (Matrix.mem_so_iff_mem_skewAdjoint A).symm

end Matrix

end TauCeti.Lie
