/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Exponential.Matrix.Symplectic
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.Topology.Algebra.SymplecticGroup

/-!
# The Lie algebra of the real symplectic group

The symplectic group sits inside the general linear group as `TauCeti.GLSymplectic`, a subgroup of
`GL (l ⊕ l) ℝ = (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ`, which is a Lie group. This file computes the Lie
algebra that `TauCeti.Lie.lieSubalgebraOfSubgroup` assigns to it: in the canonical matrix
coordinates of the general linear Lie algebra it is Mathlib's symplectic Lie algebra
`LieAlgebra.Symplectic.sp l ℝ`, the matrices that are skew-adjoint for the canonical
skew-symmetric matrix `J`.

Two inputs meet here: the matrix-level characterization of the exponential lines that stay inside
the symplectic group, `Matrix.forall_exp_smul_mem_symplecticGroup_iff_mem_sp`, and the
algebra-coordinate form of the Lie algebra of a closed subgroup of units,
`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff`, whose closedness
hypothesis is supplied by `TauCeti.isClosed_GLSymplectic`.

## Main results

* `TauCeti.Lie.forall_lieExp_mem_GLSymplectic_iff_mem_sp`: in canonical matrix coordinates, the
  abstract exponential line of `A` stays inside the symplectic subgroup exactly when `A` is
  skew-adjoint for `J`.
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sp`: **the Lie
  algebra of the symplectic group is `sp`.**
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

-- Select the matrix topology underlying the operator norm used for the general linear Lie group.
attribute [local instance] Matrix.linftyOpTopologicalSpace

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- In the canonical matrix coordinates of the general linear Lie algebra, an element generates a
one-parameter subgroup inside the symplectic group exactly when it is skew-adjoint for the
canonical skew-symmetric matrix. -/
-- Normalize the whole exponential-line predicate before subgroup membership expands.
@[simp↓]
theorem forall_lieExp_mem_GLSymplectic_iff_mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    (∀ t : ℝ, lieExp ((unitsLieAlgebraLieEquiv
        (R := Matrix (l ⊕ l) (l ⊕ l) ℝ)).symm (t • A)) ∈ GLSymplectic l ℝ) ↔
      A ∈ LieAlgebra.Symplectic.sp l ℝ := by
  rw [forall_lieExp_unitsLieAlgebraLieEquiv_symm_smul_mem_iff,
    ← Matrix.forall_exp_smul_mem_symplecticGroup_iff_mem_sp]
  simp only [GLSymplectic.mem_iff_mem_symplecticGroup, TauCeti.expUnit_coe]
  -- Both sides are now the same condition; only the `GL (l ⊕ l) ℝ` abbreviation for the matrix
  -- units still has to be unfolded.
  exact Iff.rfl

/-- **The Lie algebra of the real symplectic group is `sp`.** A matrix belongs to Mathlib's
symplectic Lie algebra exactly when its inverse image under the canonical units Lie equivalence
belongs to the Lie subalgebra of the symplectic subgroup of the general linear group. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sp
    (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    (unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) ℝ)).symm A ∈
        lieSubalgebraOfSubgroup (GLSymplectic l ℝ : Subgroup (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ) ↔
      A ∈ LieAlgebra.Symplectic.sp l ℝ := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff (isClosed_GLSymplectic l ℝ),
    ← Matrix.forall_exp_smul_mem_symplecticGroup_iff_mem_sp]
  simp only [GLSymplectic.mem_iff_mem_symplecticGroup, TauCeti.expUnit_coe]
  -- Both sides are now the same condition; only the `GL (l ⊕ l) ℝ` abbreviation for the matrix
  -- units still has to be unfolded.
  exact Iff.rfl

end TauCeti.Lie
