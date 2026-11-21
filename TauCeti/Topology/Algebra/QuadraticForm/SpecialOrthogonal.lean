/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup
public import TauCeti.Topology.Algebra.QuadraticForm.Continuity
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Coordinate
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Topology and general-linear range of special orthogonal groups in coordinates

For a quadratic map `Q` on a finite coordinate space `n → R`, this file induces the
standard coordinate topology from the faithful map of `specialOrthogonalGroup Q` into `GL(n, R)`
defined in `TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic` and proves that the
coordinate ranges of `O(Q)` and `SO(Q)` inside `GL(n, R)` are closed for a quadratic form over a
Hausdorff topological ring. Over a topological ring the resulting special orthogonal group is a
topological group, topologically isomorphic to its range in `GL(n, R)`, and it is Hausdorff when
`R` is Hausdorff.

The construction applies to an arbitrary quadratic map on the coordinate space. It does not use a
Clifford algebra or a Spin group.

## Main results

* `QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear` and
  `QuadraticMap.specialOrthogonalContinuousMulEquivRange`: the coordinate inclusion is a
  topological embedding for any `[DecidableEq n]` and identifies `SO(Q)` with its range in
  `GL(n, R)` as a topological group.
* `QuadraticMap.isClosed_range_orthogonalToGeneralLinear` and
  `QuadraticMap.isClosed_range_specialOrthogonalToGeneralLinear`: the coordinate ranges of
  `O(Q)` and `SO(Q)` are closed in `GL(n, R)` over a Hausdorff topological ring.
* `TauCeti.QuadraticMap.continuous_coe_specialOrthogonalGroup_pi`: the inclusion into the linear
  automorphism group is continuous for the coordinate topology.
-/

public section

open scoped Matrix

namespace TauCeti

namespace QuadraticMap

noncomputable section

universe u v w

variable {n : Type u} [Fintype n]
  {R : Type v} [CommRing R] [TopologicalSpace R]
  {N : Type w} [AddCommMonoid N] [Module R N]

section ClassicalTopology

attribute [local instance] Classical.decEq

/-- The canonical topology on a special orthogonal group in coordinates is induced by its
faithful representation in `GL(n, R)`. -/
instance _root_.TauCeti.QuadraticMap.instTopologicalSpaceSpecialOrthogonalGroupPi
    (Q : QuadraticMap R (n → R) N) :
    TopologicalSpace (specialOrthogonalGroup Q) :=
  TopologicalSpace.induced (Q.specialOrthogonalToGeneralLinear) inferInstance

/-- A special orthogonal group in coordinates over a topological ring is a topological group. -/
instance _root_.TauCeti.QuadraticMap.instIsTopologicalGroupSpecialOrthogonalGroupPi
    [IsTopologicalRing R]
    (Q : QuadraticMap R (n → R) N) :
    IsTopologicalGroup (specialOrthogonalGroup Q) :=
  isTopologicalGroup_induced (Q.specialOrthogonalToGeneralLinear)

end ClassicalTopology

/-- The coordinate inclusion of a special orthogonal group is a topological embedding for any
decidable-equality instance on `n`. -/
theorem _root_.QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear
    [inst : DecidableEq n] (Q : QuadraticMap R (n → R) N) :
    Topology.IsEmbedding (Q.specialOrthogonalToGeneralLinear) := by
  obtain rfl : inst = Classical.decEq n := Subsingleton.elim _ _
  classical
  exact (Q.specialOrthogonalToGeneralLinear_injective).isEmbedding_induced

section ClassicalConsequences

attribute [local instance] Classical.decEq

/-- A special orthogonal group in Hausdorff coordinates is Hausdorff. -/
instance _root_.TauCeti.QuadraticMap.instT2SpaceSpecialOrthogonalGroupPi [T2Space R]
    (Q : QuadraticMap R (n → R) N) :
    T2Space (specialOrthogonalGroup Q) :=
  Q.isEmbedding_specialOrthogonalToGeneralLinear.t2Space

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
      Q.isEmbedding_specialOrthogonalToGeneralLinear.continuous).matrix_elem i j
  refine continuous_linearEquiv_iff.mpr ⟨hcoe, ?_⟩
  exact (hcoe.comp continuous_inv).congr fun g ↦ by rw [Function.comp_apply, Subgroup.coe_inv]

end ClassicalConsequences

end

end QuadraticMap

end TauCeti

namespace QuadraticMap

open TauCeti.QuadraticMap (specialOrthogonalGroup)

noncomputable section

universe u v w

section RangeEquiv

variable {n : Type u} [Fintype n] [DecidableEq n]
  {R : Type v} [CommRing R] [TopologicalSpace R]
  {N : Type w} [AddCommMonoid N] [Module R N]

/-- A special orthogonal group in coordinates is topologically isomorphic to its range in
`GL(n, R)`. -/
def specialOrthogonalContinuousMulEquivRange (Q : QuadraticMap R (n → R) N) :
    specialOrthogonalGroup Q ≃ₜ* MonoidHom.range Q.specialOrthogonalToGeneralLinear :=
  (⟨Q.specialOrthogonalToGeneralLinear,
    Q.isEmbedding_specialOrthogonalToGeneralLinear.continuous⟩ :
      specialOrthogonalGroup Q →ₜ* Matrix.GeneralLinearGroup n R).equivRangeOfIsEmbedding
    Q.isEmbedding_specialOrthogonalToGeneralLinear

/-- The topological equivalence with the general-linear range sends an element of `SO(Q)` to its
coordinate matrix unit. -/
@[simp]
theorem specialOrthogonalContinuousMulEquivRange_apply
    (Q : QuadraticMap R (n → R) N) (g : specialOrthogonalGroup Q) :
    Q.specialOrthogonalContinuousMulEquivRange g =
      ⟨Q.specialOrthogonalToGeneralLinear g, ⟨g, rfl⟩⟩ :=
  ContinuousMonoidHom.equivRangeOfIsEmbedding_apply _ _ g

/-- The inverse topological equivalence recovers an element of `SO(Q)` from its coordinate matrix
unit. -/
@[simp]
theorem specialOrthogonalContinuousMulEquivRange_symm_apply
    (Q : QuadraticMap R (n → R) N) (g : specialOrthogonalGroup Q) :
    Q.specialOrthogonalContinuousMulEquivRange.symm
        ⟨Q.specialOrthogonalToGeneralLinear g, ⟨g, rfl⟩⟩ = g := by
  rw [← specialOrthogonalContinuousMulEquivRange_apply]
  exact Q.specialOrthogonalContinuousMulEquivRange.symm_apply_apply g

end RangeEquiv

section ClosedRange

variable {n : Type u} [Fintype n] [DecidableEq n]
  {R : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

/-- The coordinate range of the orthogonal group of a quadratic form over a Hausdorff topological
ring is closed in `GL(n, R)`. -/
theorem isClosed_range_orthogonalToGeneralLinear (Q : QuadraticForm R (n → R)) :
    IsClosed (Set.range Q.orthogonalToGeneralLinear) := by
  have hset : Set.range Q.orthogonalToGeneralLinear =
      ⋂ x : n → R, {U : Matrix.GeneralLinearGroup n R | Q ((U : Matrix n n R) *ᵥ x) = Q x} := by
    ext U
    simp only [← MonoidHom.coe_range, SetLike.mem_coe, mem_range_orthogonalToGeneralLinear_iff,
      Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  refine isClosed_iInter fun x ↦ isClosed_eq ?_ continuous_const
  exact Q.continuous.comp (Units.continuous_val.matrix_mulVec continuous_const)

/-- The coordinate range of the special orthogonal group of a quadratic form over a Hausdorff
topological ring is closed in `GL(n, R)`. -/
theorem isClosed_range_specialOrthogonalToGeneralLinear (Q : QuadraticForm R (n → R)) :
    IsClosed (Set.range Q.specialOrthogonalToGeneralLinear) := by
  have hset : Set.range Q.specialOrthogonalToGeneralLinear =
      Set.range Q.orthogonalToGeneralLinear ∩
        {U : Matrix.GeneralLinearGroup n R | (U : Matrix n n R).det = 1} := by
    ext U
    simp only [← MonoidHom.coe_range, SetLike.mem_coe,
      mem_range_specialOrthogonalToGeneralLinear_iff, mem_range_orthogonalToGeneralLinear_iff,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hset]
  exact (isClosed_range_orthogonalToGeneralLinear Q).inter <|
    isClosed_eq (Units.continuous_val.matrix_det) continuous_const

end ClosedRange

end

end QuadraticMap
