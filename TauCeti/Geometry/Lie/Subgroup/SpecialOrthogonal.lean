/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Adjoint.Units.Basic
public import TauCeti.Geometry.Lie.Exponential.Matrix.Compatibility
public import TauCeti.Geometry.Lie.Exponential.Matrix.SpecialOrthogonal
public import TauCeti.Geometry.Lie.Subgroup.LieAlgebra
public import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal

/-!
# Lie algebra of the real special orthogonal group

This file transports the matrix-exponential characterization of the real orthogonal Lie algebra to
the positive-definite `realCliffordForm n 0` special-orthogonal carrier. The result supplies the
carrier-side coordinates needed to compare its one-parameter subgroups with skew-adjoint
infinitesimal actions.

## Main results

* `unitsLieAlgebraLieEquiv_symm_mem_realCliffordForm_lieSubalgebra_iff_mem_so` identifies the Lie
  subalgebra of the positive-definite carrier with the real orthogonal Lie algebra in canonical
  matrix coordinates.
* `TauCeti.Lie.forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff_mem_so`
  gives the underlying exponential-line characterization.
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The matrix topology selected by the operator norm used for the general linear Lie group. -/
local instance matrixOperatorTopologicalSpace (n : Type*) [Fintype n] :
    TopologicalSpace (Matrix n n ℝ) :=
  Matrix.linftyOpTopologicalSpace n n ℝ

/-- In the canonical matrix coordinates of the general linear Lie algebra, an element generates a
one-parameter subgroup in the range of the positive-definite `realCliffordForm n 0`
special-orthogonal carrier exactly when it is skew-symmetric. -/
-- Normalize the whole exponential-line predicate before range membership expands.
@[simp↓]
theorem forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff_mem_so
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ t : ℝ, lieExp ((unitsLieAlgebraLieEquiv
        (R := Matrix (Fin n) (Fin n) ℝ)).symm (t • A)) ∈
      MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (realCliffordForm n 0))) ↔
      A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  rw [← Matrix.forall_exp_smul_mem_specialOrthogonalGroup_iff_mem_so]
  constructor
  · intro h t
    have ht := h t
    rw [QuadraticMap.mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff] at ht
    simpa only [unitsLieAlgebraLieEquiv_symm_apply,
      lieExp_generalLinearGroup_coe] using ht
  · intro h t
    rw [QuadraticMap.mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff]
    simpa only [unitsLieAlgebraLieEquiv_symm_apply,
      lieExp_generalLinearGroup_coe] using h t

/-- A matrix belongs to the real orthogonal Lie algebra exactly when its inverse image under the
canonical units Lie equivalence belongs to the Lie subalgebra of the positive-definite
`realCliffordForm n 0` special-orthogonal carrier. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_realCliffordForm_lieSubalgebra_iff_mem_so
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    -- `realCliffordForm n 0` is indexed by `Fin (n + 0)`; retyping it over `Fin n` aligns the
    -- carrier with the canonical matrix and operator-topology instances used in this statement.
    (unitsLieAlgebraLieEquiv (R := Matrix (Fin n) (Fin n) ℝ)).symm A ∈
        lieSubalgebraOfSubgroup
          (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
            (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)) :
              Subgroup (Matrix (Fin n) (Fin n) ℝ)ˣ) ↔
      A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  have hclosed : IsClosed
      ((MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)) :
          Subgroup (Matrix (Fin n) (Fin n) ℝ)ˣ) :
        Set (Matrix (Fin n) (Fin n) ℝ)ˣ) := by
    rw [MonoidHom.coe_range]
    exact QuadraticMap.isClosed_range_specialOrthogonalToGeneralLinear_realCliffordForm n
  rw [mem_lieSubalgebraOfSubgroup hclosed]
  simpa only [map_smul] using
    forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff_mem_so n A

end TauCeti.Lie
