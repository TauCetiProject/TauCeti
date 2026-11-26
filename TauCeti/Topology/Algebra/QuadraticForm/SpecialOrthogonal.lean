/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup

/-!
# Topology on special orthogonal groups in coordinates

For a quadratic map `Q` on a finite coordinate space `n → R`, this file induces the
standard coordinate topology from the faithful map of `specialOrthogonalGroup Q` into `GL(n, R)`
defined in `TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic`. Over a topological ring the
resulting special orthogonal group is a topological group, and it is Hausdorff when `R` is
Hausdorff.

The construction applies to an arbitrary quadratic map on the coordinate space. It does not use a
Clifford algebra or a Spin group.

## Main results

* `TauCeti.QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear` records that it is a
  topological embedding.
* `TauCeti.QuadraticMap.continuous_coe_specialOrthogonalGroup_pi`: the inclusion into the linear
  automorphism group is continuous for the coordinate topology.
* `QuadraticMap.IsometryEquiv.continuous_specialOrthogonalGroupCongr_pi` and
  `QuadraticMap.IsometryEquiv.specialOrthogonalGroupCongrContinuousMulEquivPi`: transport of
  special orthogonal groups in coordinates along a quadratic isometry equivalence is a topological
  group isomorphism.
-/

public section


namespace TauCeti

namespace QuadraticMap

noncomputable section

universe u v w

attribute [local instance] Classical.decEq

variable {n : Type u} [Fintype n]
  {R : Type v} [CommRing R] [TopologicalSpace R]
  {N : Type w} [AddCommMonoid N] [Module R N]

/-- The canonical topology on a special orthogonal group in coordinates is induced by its
faithful representation in `GL(n, R)`. -/
instance _root_.TauCeti.QuadraticMap.instTopologicalSpaceSpecialOrthogonalGroupPi
    (Q : QuadraticMap R (n → R) N) :
    TopologicalSpace (specialOrthogonalGroup Q) :=
  TopologicalSpace.induced (Q.specialOrthogonalToGeneralLinear) inferInstance

/-- The coordinate inclusion of a special orthogonal group is a topological embedding. -/
theorem _root_.TauCeti.QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear
    (Q : QuadraticMap R (n → R) N) :
    Topology.IsEmbedding (Q.specialOrthogonalToGeneralLinear) :=
  (Q.specialOrthogonalToGeneralLinear_injective).isEmbedding_induced

/-- A special orthogonal group in coordinates over a topological ring is a topological group. -/
instance _root_.TauCeti.QuadraticMap.instIsTopologicalGroupSpecialOrthogonalGroupPi
    [IsTopologicalRing R]
    (Q : QuadraticMap R (n → R) N) :
    IsTopologicalGroup (specialOrthogonalGroup Q) :=
  isTopologicalGroup_induced (Q.specialOrthogonalToGeneralLinear)

/-- A special orthogonal group in Hausdorff coordinates is Hausdorff. -/
instance _root_.TauCeti.QuadraticMap.instT2SpaceSpecialOrthogonalGroupPi [T2Space R]
    (Q : QuadraticMap R (n → R) N) :
    T2Space (specialOrthogonalGroup Q) :=
  (isEmbedding_specialOrthogonalToGeneralLinear Q).t2Space

/-- The inclusion of a special orthogonal group in coordinates into the linear automorphism
group is continuous for the coordinate topology. So every subset of `SO(Q)` that is open for its
subspace topology in the linear automorphism group is also open for the coordinate topology. -/
theorem _root_.TauCeti.QuadraticMap.continuous_coe_specialOrthogonalGroup_pi
    [IsTopologicalRing R] (Q : QuadraticMap R (n → R) N) :
    Continuous ((↑) : specialOrthogonalGroup Q → (n → R) ≃ₗ[R] (n → R)) := by
  have hcoe : Continuous fun g : specialOrthogonalGroup Q ↦
      ((g : (n → R) ≃ₗ[R] (n → R)) : Module.End R (n → R)) := by
    refine ((Pi.basisFun R n).continuous_iff_apply _).mpr fun j ↦ continuous_pi fun i ↦ ?_
    simpa using (Units.continuous_val.comp
      (isEmbedding_specialOrthogonalToGeneralLinear Q).continuous).matrix_elem i j
  refine continuous_linearEquiv_iff.mpr ⟨hcoe, ?_⟩
  exact (hcoe.comp continuous_inv).congr fun g ↦ by rw [Function.comp_apply, Subgroup.coe_inv]

end


end QuadraticMap

end TauCeti

namespace QuadraticMap.IsometryEquiv

open TauCeti.QuadraticMap

noncomputable section

attribute [local instance] Classical.decEq

variable {n₁ n₂ R N : Type*} [Fintype n₁] [Fintype n₂] [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [AddCommMonoid N] [Module R N]
  {Q₁ : QuadraticMap R (n₁ → R) N} {Q₂ : QuadraticMap R (n₂ → R) N}

/-- Transport of special orthogonal groups in coordinates along a quadratic isometry equivalence is
continuous for the coordinate topologies. -/
@[fun_prop]
theorem continuous_specialOrthogonalGroupCongr_pi (e : Q₁.IsometryEquiv Q₂) :
    Continuous e.specialOrthogonalGroupCongr := by
  let E : Matrix n₂ n₁ R := e.toLinearEquiv.toLinearMap.toMatrix'
  let Einv : Matrix n₁ n₂ R := e.symm.toLinearEquiv.toLinearMap.toMatrix'
  have hA : Continuous fun g : specialOrthogonalGroup Q₁ ↦
      ((Q₁.specialOrthogonalToGeneralLinear g : Matrix.GeneralLinearGroup n₁ R) : Matrix n₁ n₁ R) :=
    Units.continuous_val.comp (isEmbedding_specialOrthogonalToGeneralLinear Q₁).continuous
  have hfwd : Continuous fun g : specialOrthogonalGroup Q₁ ↦
      ((Q₂.specialOrthogonalToGeneralLinear (e.specialOrthogonalGroupCongr g) :
        Matrix.GeneralLinearGroup n₂ R) : Matrix n₂ n₂ R) := by
    refine (((continuous_const (y := E)).matrix_mul hA).matrix_mul
      (continuous_const (y := Einv))).congr fun g ↦ ?_
    symm
    rw [Q₂.coe_specialOrthogonalToGeneralLinear, Q₁.coe_specialOrthogonalToGeneralLinear,
      ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    exact congrArg LinearMap.toMatrix' (LinearMap.ext fun v ↦ funext fun i ↦ by simp)
  exact continuous_induced_rng.mpr <| Units.continuous_iff.mpr
    ⟨hfwd, (hfwd.comp continuous_inv).congr fun g ↦ by simp only [Function.comp_apply, map_inv]⟩

/-- Transport of special orthogonal groups in coordinates along a quadratic isometry equivalence,
packaged as an isomorphism of topological groups. -/
def specialOrthogonalGroupCongrContinuousMulEquivPi (e : Q₁.IsometryEquiv Q₂) :
    specialOrthogonalGroup Q₁ ≃ₜ* specialOrthogonalGroup Q₂ where
  toMulEquiv := e.specialOrthogonalGroupCongr
  continuous_toFun := e.continuous_specialOrthogonalGroupCongr_pi
  continuous_invFun := e.symm.continuous_specialOrthogonalGroupCongr_pi.congr fun g ↦
    congrArg (· g) e.specialOrthogonalGroupCongr_symm.symm

/-- Evaluating `specialOrthogonalGroupCongrContinuousMulEquivPi` applies
`specialOrthogonalGroupCongr`. -/
@[simp]
theorem specialOrthogonalGroupCongrContinuousMulEquivPi_apply (e : Q₁.IsometryEquiv Q₂)
    (g : specialOrthogonalGroup Q₁) :
    e.specialOrthogonalGroupCongrContinuousMulEquivPi g = e.specialOrthogonalGroupCongr g := (rfl)

/-- The inverse of `specialOrthogonalGroupCongrContinuousMulEquivPi` is induced by `e.symm`. -/
@[simp]
theorem specialOrthogonalGroupCongrContinuousMulEquivPi_symm (e : Q₁.IsometryEquiv Q₂) :
    e.specialOrthogonalGroupCongrContinuousMulEquivPi.symm =
      e.symm.specialOrthogonalGroupCongrContinuousMulEquivPi :=
  ContinuousMulEquiv.ext fun g ↦ congrArg (· g) e.specialOrthogonalGroupCongr_symm

end

end QuadraticMap.IsometryEquiv
