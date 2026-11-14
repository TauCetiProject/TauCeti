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
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Topology and general-linear range of special orthogonal groups in coordinates

For a quadratic map `Q` on a finite coordinate space `n → R`, this file induces the
standard coordinate topology from the faithful map of `specialOrthogonalGroup Q` into `GL(n, R)`
defined in `TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic`, characterizes the ranges of
the coordinate inclusions of `O(Q)` and `SO(Q)` inside `GL(n, R)`, and proves that those ranges are
closed for a quadratic form over a Hausdorff topological ring. Over a topological ring the
resulting special orthogonal group is a topological group, topologically isomorphic to its range in
`GL(n, R)`, and it is Hausdorff when `R` is Hausdorff.

The construction applies to an arbitrary quadratic map on the coordinate space. It does not use a
Clifford algebra or a Spin group.

## Main results

* `QuadraticMap.mem_range_orthogonalToGeneralLinear_iff` and
  `QuadraticMap.mem_range_specialOrthogonalToGeneralLinear_iff`: matrix-level membership
  characterizations of the coordinate ranges of `O(Q)` and `SO(Q)` in `GL(n, R)`, together with
  `QuadraticMap.mem_range_specialOrthogonalToGeneralLinear_iff_polarBilin` in terms of the polar
  Gram matrix.
* `TauCeti.QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear` and
  `QuadraticMap.specialOrthogonalContinuousMulEquivRange`: the coordinate inclusion is a
  topological embedding and identifies `SO(Q)` with its range in `GL(n, R)` as a topological group.
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

namespace QuadraticMap

open TauCeti (matrixGeneralLinearEquiv matrixGeneralLinearEquiv_apply)
open TauCeti.QuadraticMap (orthogonalGroup specialOrthogonalGroup mem_orthogonalGroup_iff
  mem_orthogonalGroup_iff_polar mem_specialOrthogonalGroup_iff det_coe_specialOrthogonalGroup
  isEmbedding_specialOrthogonalToGeneralLinear)

noncomputable section

universe u v w

section Range

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- A general-linear matrix lies in the coordinate range of `O(Q)` if and only if its
matrix-vector action preserves `Q`. -/
theorem mem_range_orthogonalToGeneralLinear_iff
    {R : Type v} [CommSemiring R] {N : Type w} [AddCommMonoid N] [Module R N]
    (Q : QuadraticMap R (n → R) N) (U : Matrix.GeneralLinearGroup n R) :
    U ∈ MonoidHom.range Q.orthogonalToGeneralLinear ↔
      ∀ x : n → R, Q ((U : Matrix n n R) *ᵥ x) = Q x := by
  constructor
  · rintro ⟨g, rfl⟩ x
    rw [coe_orthogonalToGeneralLinear, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
    exact (mem_orthogonalGroup_iff.mp g.prop) x
  · intro hU
    let e : (n → R) ≃ₗ[R] (n → R) :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv R (n → R) (matrixGeneralLinearEquiv U)
    have he (x : n → R) : e x = (U : Matrix n n R) *ᵥ x := by
      simp [e, matrixGeneralLinearEquiv_apply]
    refine ⟨⟨e, mem_orthogonalGroup_iff.mpr fun x ↦ (congrArg Q (he x)).trans (hU x)⟩, ?_⟩
    apply Units.ext
    ext i j
    rw [orthogonalToGeneralLinear_apply, Subtype.coe_mk, he, Matrix.mulVec_single_one,
      Matrix.col_apply]

/-- A general-linear matrix lies in the coordinate range of `SO(Q)` if and only if its
matrix-vector action preserves `Q` and its determinant is one. -/
theorem mem_range_specialOrthogonalToGeneralLinear_iff
    {R : Type v} [CommRing R] {N : Type w} [AddCommMonoid N] [Module R N]
    (Q : QuadraticMap R (n → R) N) (U : Matrix.GeneralLinearGroup n R) :
    U ∈ MonoidHom.range Q.specialOrthogonalToGeneralLinear ↔
      (∀ x : n → R, Q ((U : Matrix n n R) *ᵥ x) = Q x) ∧ (U : Matrix n n R).det = 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨fun x ↦ ?_, ?_⟩
    · rw [specialOrthogonalToGeneralLinear_mulVec]
      exact (mem_orthogonalGroup_iff.mp (mem_specialOrthogonalGroup_iff.mp g.prop).1) x
    · rw [coe_specialOrthogonalToGeneralLinear, LinearMap.det_toMatrix',
        ← LinearEquiv.coe_det, det_coe_specialOrthogonalGroup, Units.val_one]
  · rintro ⟨hQ, hdet⟩
    obtain ⟨g, hg⟩ := (mem_range_orthogonalToGeneralLinear_iff Q U).mpr hQ
    have hgdet : LinearEquiv.det (g : (n → R) ≃ₗ[R] (n → R)) = 1 := by
      apply Units.ext
      rw [Units.val_one, LinearEquiv.coe_det, ← LinearMap.det_toMatrix',
        ← coe_orthogonalToGeneralLinear, hg, hdet]
    refine ⟨⟨(g : (n → R) ≃ₗ[R] (n → R)),
      mem_specialOrthogonalGroup_iff.mpr ⟨g.prop, hgdet⟩⟩, ?_⟩
    apply Units.ext
    ext i j
    rw [specialOrthogonalToGeneralLinear_apply, Subtype.coe_mk,
      ← orthogonalToGeneralLinear_apply, hg]

/-- When multiplication by `2` is injective on `R`, a general-linear matrix lies in the coordinate
range of `SO(Q)` if and only if it preserves the polar Gram matrix in standard coordinates and has
determinant one. -/
theorem mem_range_specialOrthogonalToGeneralLinear_iff_polarBilin
    {R : Type v} [CommRing R]
    (Q : QuadraticForm R (n → R)) (h2 : IsSMulRegular R (2 : R))
    (U : Matrix.GeneralLinearGroup n R) :
    U ∈ MonoidHom.range Q.specialOrthogonalToGeneralLinear ↔
      (U : Matrix n n R)ᵀ * LinearMap.BilinForm.toMatrix' Q.polarBilin * (U : Matrix n n R) =
          LinearMap.BilinForm.toMatrix' Q.polarBilin ∧
        (U : Matrix n n R).det = 1 := by
  rw [mem_range_specialOrthogonalToGeneralLinear_iff]
  refine and_congr_left fun _ ↦ ?_
  let e : (n → R) ≃ₗ[R] (n → R) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv R (n → R) (matrixGeneralLinearEquiv U)
  have he (x : n → R) : e x = (U : Matrix n n R) *ᵥ x := by
    simp [e, matrixGeneralLinearEquiv_apply]
  have hQ : (∀ x : n → R, Q ((U : Matrix n n R) *ᵥ x) = Q x) ↔ e ∈ orthogonalGroup Q := by
    simp only [mem_orthogonalGroup_iff, he]
  rw [hQ, mem_orthogonalGroup_iff_polar h2]
  have hcomp :
      (U : Matrix n n R)ᵀ * LinearMap.BilinForm.toMatrix' Q.polarBilin * (U : Matrix n n R) =
        LinearMap.BilinForm.toMatrix'
          (LinearMap.BilinForm.comp Q.polarBilin (Matrix.toLin' (U : Matrix n n R))
            (Matrix.toLin' (U : Matrix n n R))) := by
    simpa only [Matrix.transpose_transpose] using
      LinearMap.BilinForm.mul_toMatrix'_mul Q.polarBilin (U : Matrix n n R)ᵀ (U : Matrix n n R)
  rw [hcomp, LinearMap.BilinForm.toMatrix'.injective.eq_iff, LinearMap.BilinForm.ext_iff]
  simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, he, polarBilin_apply_apply]

end Range

section RangeEquiv

variable {n : Type u} [Fintype n] [DecidableEq n]
  {R : Type v} [CommRing R] [TopologicalSpace R]
  {N : Type w} [AddCommMonoid N] [Module R N]

private theorem isEmbedding_specialOrthogonalToGeneralLinear_decEq
    (Q : QuadraticMap R (n → R) N) :
    Topology.IsEmbedding Q.specialOrthogonalToGeneralLinear := by
  -- The coordinate topology on `SO(Q)` is induced using `Classical.decEq`, while the explicit
  -- coordinate inclusion uses the `[DecidableEq n]` parameter; `convert` identifies the two
  -- subsingleton instances.
  convert isEmbedding_specialOrthogonalToGeneralLinear Q

/-- A special orthogonal group in coordinates is topologically isomorphic to its range in
`GL(n, R)`. -/
def specialOrthogonalContinuousMulEquivRange (Q : QuadraticMap R (n → R) N) :
    specialOrthogonalGroup Q ≃ₜ* MonoidHom.range Q.specialOrthogonalToGeneralLinear :=
  (⟨Q.specialOrthogonalToGeneralLinear,
    (isEmbedding_specialOrthogonalToGeneralLinear_decEq Q).continuous⟩ :
      specialOrthogonalGroup Q →ₜ* Matrix.GeneralLinearGroup n R).equivRangeOfIsEmbedding
    (isEmbedding_specialOrthogonalToGeneralLinear_decEq Q)

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
