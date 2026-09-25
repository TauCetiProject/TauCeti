/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Units.Basic
public import TauCeti.Geometry.Lie.Exponential.Matrix.SpecialOrthogonal
public import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal

/-!
# Lie algebra of the real special orthogonal group

This file transports the matrix-exponential characterization of the real orthogonal Lie algebra to
the positive-definite `realCliffordForm n 0` special-orthogonal carrier. The result supplies the
carrier-side coordinates needed to compare its one-parameter subgroups with skew-adjoint
infinitesimal actions.

## Main results

* `TauCeti.Lie.forall_lieExp_mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff_mem_so`
  identifies the positive-definite carrier's exponential lines in the canonical Lie-algebra
  coordinates of the general linear group.
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Classical.decEq

/-- In the canonical matrix coordinates of the general linear Lie algebra, an element generates a
one-parameter subgroup in the range of the positive-definite `realCliffordForm n 0`
special-orthogonal carrier exactly when it is skew-symmetric. -/
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

end TauCeti.Lie
