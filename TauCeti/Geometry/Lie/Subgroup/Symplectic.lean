/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Adjoint.Units.Basic
public import TauCeti.Geometry.Lie.Exponential.Matrix.Compatibility
public import TauCeti.Geometry.Lie.Exponential.Matrix.Symplectic
public import TauCeti.Geometry.Lie.Subgroup.LieAlgebra
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# The Lie algebra of the real symplectic group

The symplectic group sits inside the general linear group as `TauCeti.GLSymplectic`, a subgroup of
`GL (l ⊕ l) ℝ = (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ`, which is a Lie group. This file computes the Lie
algebra that `TauCeti.Lie.lieSubalgebraOfSubgroup` assigns to it: in the canonical matrix
coordinates of the general linear Lie algebra it is Mathlib's symplectic Lie algebra
`LieAlgebra.Symplectic.sp l ℝ`, the matrices that are skew-adjoint for the canonical
skew-symmetric matrix `J`.

Two inputs meet here. The matrix-level characterization of the exponential lines that stay inside
the symplectic group is `Matrix.forall_exp_smul_mem_symplecticGroup_iff_mem_sp`; transporting it
along `TauCeti.unitsLieAlgebraLieEquiv` and `lieExp_generalLinearGroup_coe` turns it into a
statement about the abstract Lie-group exponential. Turning that in turn into a statement about
`lieSubalgebraOfSubgroup` needs `TauCeti.Lie.mem_lieSubalgebraOfSubgroup`, whose hypothesis is that
the subgroup is closed; `TauCeti.Lie.isClosed_GLSymplectic` supplies it, the symplectic condition
`M J Mᵀ = J` being a closed condition on the matrix entries. Unlike the orthogonal group the
symplectic group is not compact, so closedness is proved directly rather than read off a
compactness statement.

## Main results

* `TauCeti.Lie.isClosed_GLSymplectic`: the symplectic subgroup of the general linear group is
  closed.
* `TauCeti.Lie.forall_lieExp_mem_GLSymplectic_iff_mem_sp`: in canonical matrix coordinates, the
  abstract exponential line of `A` stays inside the symplectic subgroup exactly when `A` is
  skew-adjoint for `J`.
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sp`: **the Lie
  algebra of the symplectic group is `sp`.**

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 2, "Consequences": the matrix groups are Lie groups, with their Lie
  algebras named explicitly.
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

/-- The symplectic subgroup of the general linear group is closed: it is the preimage, under the
continuous inclusion of the units, of the closed condition `M J Mᵀ = J` on matrices. -/
theorem isClosed_GLSymplectic (l : Type*) [DecidableEq l] [Fintype l] :
    IsClosed ((GLSymplectic l ℝ : Subgroup (GL (l ⊕ l) ℝ)) : Set (GL (l ⊕ l) ℝ)) := by
  have hcont : Continuous fun A : Matrix (l ⊕ l) (l ⊕ l) ℝ => A * Matrix.J l ℝ * Aᵀ :=
    (continuous_id.matrix_mul continuous_const).matrix_mul continuous_id.matrix_transpose
  have hset : IsClosed
      {A : Matrix (l ⊕ l) (l ⊕ l) ℝ | A * Matrix.J l ℝ * Aᵀ = Matrix.J l ℝ} :=
    isClosed_eq hcont continuous_const
  have hpre : ((GLSymplectic l ℝ : Subgroup (GL (l ⊕ l) ℝ)) : Set (GL (l ⊕ l) ℝ)) =
      Units.val ⁻¹' {A : Matrix (l ⊕ l) (l ⊕ l) ℝ | A * Matrix.J l ℝ * Aᵀ = Matrix.J l ℝ} := by
    ext M
    simpa only [SetLike.mem_coe, Set.mem_preimage, Set.mem_ofPred_eq] using GLSymplectic.mem_iff
  rw [hpre]
  exact hset.preimage Units.continuous_val

/-- In the canonical matrix coordinates of the general linear Lie algebra, an element generates a
one-parameter subgroup inside the symplectic group exactly when it is skew-adjoint for the
canonical skew-symmetric matrix. -/
-- Normalize the whole exponential-line predicate before subgroup membership expands.
@[simp↓]
theorem forall_lieExp_mem_GLSymplectic_iff_mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    (∀ t : ℝ, lieExp ((unitsLieAlgebraLieEquiv
        (R := Matrix (l ⊕ l) (l ⊕ l) ℝ)).symm (t • A)) ∈ GLSymplectic l ℝ) ↔
      A ∈ LieAlgebra.Symplectic.sp l ℝ := by
  rw [← Matrix.forall_exp_smul_mem_symplecticGroup_iff_mem_sp]
  constructor
  · intro h t
    have ht := h t
    rw [GLSymplectic.mem_iff_mem_symplecticGroup] at ht
    simpa only [unitsLieAlgebraLieEquiv_symm_apply, lieExp_generalLinearGroup_coe] using ht
  · intro h t
    rw [GLSymplectic.mem_iff_mem_symplecticGroup]
    simpa only [unitsLieAlgebraLieEquiv_symm_apply, lieExp_generalLinearGroup_coe] using h t

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
  rw [mem_lieSubalgebraOfSubgroup (isClosed_GLSymplectic l)]
  simpa only [map_smul] using forall_lieExp_mem_GLSymplectic_iff_mem_sp A

end TauCeti.Lie
