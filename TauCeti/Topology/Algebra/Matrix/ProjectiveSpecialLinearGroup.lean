/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo

import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Topology on `PSL(2, ℝ)`

The quotient topology on the projective special linear group `PSL(2, ℝ)` is Hausdorff
because the center of `SL(2, ℝ)` is finite, hence closed. Conjugation preserves discrete
subgroups, and the translations `Matrix.ProjectiveSpecialLinearGroup.upperRightHom x` depend
continuously on `x`.
-/

public section

open scoped MatrixGroups Pointwise

open Matrix.SpecialLinearGroup

namespace TauCeti

/-- The projective special linear group `PSL(2, ℝ)` is Hausdorff. -/
instance : T2Space PSL(2, ℝ) := by
  let _ : Finite (Subgroup.center SL(2, ℝ)) :=
    Matrix.SpecialLinearGroup.finite_center (R := ℝ)
  let _ : IsClosed ((Subgroup.center SL(2, ℝ) : Subgroup SL(2, ℝ)) : Set SL(2, ℝ)) :=
    Set.toFinite _ |>.isClosed
  infer_instance

end TauCeti

namespace Subgroup

/-- A conjugate `g Γ g⁻¹` of a discrete subgroup of `PSL(2, ℝ)` is discrete. -/
instance discreteTopology_conjAct_smul {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]
    (g : PSL(2, ℝ)) :
    DiscreteTopology (ConjAct.toConjAct g • Γ : Subgroup PSL(2, ℝ)) :=
  DiscreteTopology.of_continuous_injective
    (f := (equivSMul (ConjAct.toConjAct g) Γ).symm) (by fun_prop)
    (equivSMul (ConjAct.toConjAct g) Γ).symm.injective

end Subgroup

namespace Matrix.ProjectiveSpecialLinearGroup

/-- The translation `upperRightHom x ∈ PSL(2, R)` depends continuously on `x`. -/
@[fun_prop]
theorem continuous_upperRightHom {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (upperRightHom : R → PSL(2, R)) := by
  have : Continuous fun x : R ↦ SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) x :=
    Continuous.subtype_mk (continuous_const.add (continuous_matrix fun i j ↦ by
      simp only [single_apply]
      split_ifs <;> fun_prop)) _
  exact (continuous_quot_mk.comp this).congr fun x ↦ (upperRightHom_apply x).symm

end Matrix.ProjectiveSpecialLinearGroup
