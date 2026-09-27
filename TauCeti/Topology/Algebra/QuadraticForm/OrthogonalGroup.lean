/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal
import TauCeti.Topology.Algebra.QuadraticForm.Continuity

/-!
# Coordinate topology on orthogonal groups

For a quadratic map on a finite coordinate module, the orthogonal group inherits the topology of
the matrix general linear group through its faithful coordinate representation. This topology
makes multiplication and inversion continuous. The determinant-one group has its existing
coordinate topology, and its inclusion into the orthogonal group is a topological embedding.

This gives both groups the same ambient topology, which is needed to compare their local point
groups and to study compactness of real and nonarchimedean isometry groups.
-/

public section

namespace TauCeti.QuadraticMap

open _root_.QuadraticMap
open Matrix

noncomputable section

universe u v w

variable {n : Type u} [Fintype n]
  {R : Type v} [CommRing R] [TopologicalSpace R]
  {N : Type w} [AddCommMonoid N] [Module R N]

attribute [local instance] Classical.decEq

/-- The topology on the orthogonal group of a coordinate quadratic map is induced by its
faithful matrix representation in `GL(n, R)`. -/
instance instTopologicalSpaceOrthogonalGroupPi (Q : QuadraticMap R (n → R) N) :
    TopologicalSpace (orthogonalGroup Q) :=
  TopologicalSpace.induced (orthogonalToGeneralLinear Q) inferInstance

/-- The coordinate representation of an orthogonal group is a topological embedding. -/
theorem isEmbedding_orthogonalToGeneralLinear (Q : QuadraticMap R (n → R) N) :
    Topology.IsEmbedding (orthogonalToGeneralLinear Q) :=
  (orthogonalToGeneralLinear_injective Q).isEmbedding_induced

/-- The orthogonal group in coordinates is a topological group over a topological ring. -/
instance instIsTopologicalGroupOrthogonalGroupPi [IsTopologicalRing R]
    (Q : QuadraticMap R (n → R) N) :
    IsTopologicalGroup (orthogonalGroup Q) :=
  isTopologicalGroup_induced (orthogonalToGeneralLinear Q)

/-- The coordinate orthogonal group over a Hausdorff ring is Hausdorff. -/
instance instT2SpaceOrthogonalGroupPi [T2Space R]
    (Q : QuadraticMap R (n → R) N) :
    T2Space (orthogonalGroup Q) :=
  (isEmbedding_orthogonalToGeneralLinear Q).t2Space

omit [TopologicalSpace R] in
/-- The coordinate matrix of a special orthogonal element is unchanged by its inclusion in the
orthogonal group. -/
@[simp]
theorem orthogonalToGeneralLinear_specialOrthogonalToOrthogonal
    (Q : QuadraticMap R (n → R) N) (g : specialOrthogonalGroup Q) :
    orthogonalToGeneralLinear Q (specialOrthogonalToOrthogonal Q g) =
      specialOrthogonalToGeneralLinear Q g := by
  apply Units.ext
  ext i j
  simp only [orthogonalToGeneralLinear_apply, specialOrthogonalToGeneralLinear_apply,
    coe_specialOrthogonalToOrthogonal]

/-- The determinant-one subgroup has the subspace topology from the orthogonal group. -/
theorem isEmbedding_specialOrthogonalToOrthogonal
    (Q : QuadraticMap R (n → R) N) :
    Topology.IsEmbedding (specialOrthogonalToOrthogonal Q) := by
  have hcomp : Topology.IsEmbedding
      (orthogonalToGeneralLinear Q ∘ specialOrthogonalToOrthogonal Q) := by
    convert isEmbedding_specialOrthogonalToGeneralLinear Q using 1
    funext g
    exact orthogonalToGeneralLinear_specialOrthogonalToOrthogonal Q g
  exact (isEmbedding_orthogonalToGeneralLinear Q).of_comp_iff.mp hcomp

/-- The action of the coordinate orthogonal group on its underlying module is jointly
continuous. -/
@[fun_prop]
theorem continuous_orthogonalGroup_action [IsTopologicalRing R]
    (Q : QuadraticMap R (n → R) N) :
    Continuous (fun p : orthogonalGroup Q × (n → R) =>
      (p.1 : (n → R) ≃ₗ[R] (n → R)) p.2) := by
  have hmat : Continuous (fun p : orthogonalGroup Q × (n → R) =>
      ((orthogonalToGeneralLinear Q p.1 : Matrix.GeneralLinearGroup n R) : Matrix n n R)) :=
    Units.continuous_val.comp
      ((isEmbedding_orthogonalToGeneralLinear Q).continuous.comp continuous_fst)
  have h : Continuous (fun p : orthogonalGroup Q × (n → R) =>
      ((orthogonalToGeneralLinear Q p.1 : Matrix.GeneralLinearGroup n R) : Matrix n n R) *ᵥ
        p.2) := hmat.matrix_mulVec continuous_snd
  convert h using 1
  funext p
  rw [coe_orthogonalToGeneralLinear, LinearMap.toMatrix'_mulVec]
  rfl

/-- Applying a coordinate orthogonal transformation to a fixed vector is continuous. -/
@[fun_prop]
theorem continuous_orthogonalGroup_apply [IsTopologicalRing R]
    (Q : QuadraticMap R (n → R) N) (x : n → R) :
    Continuous (fun g : orthogonalGroup Q => (g : (n → R) ≃ₗ[R] (n → R)) x) := by
  have hpair : Continuous (fun g : orthogonalGroup Q => (g, x)) := by fun_prop
  exact (continuous_orthogonalGroup_action Q).comp hpair

/-- The coordinate orthogonal group is a closed subgroup of matrix `GL` over a Hausdorff
topological ring in which two is invertible. -/
theorem isClosed_range_orthogonalToGeneralLinear [IsTopologicalRing R] [T2Space R]
    [Invertible (2 : R)] (Q : QuadraticForm R (n → R)) :
    IsClosed (Set.range (orthogonalToGeneralLinear Q)) := by
  have hQ : Continuous Q := Q.continuous
  have hset : Set.range (orthogonalToGeneralLinear Q) =
      ⋂ x : n → R, {U : Matrix.GeneralLinearGroup n R |
        Q (((U : Matrix n n R) *ᵥ x)) = Q x} := by
    ext U
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, rfl⟩ x
      rw [coe_orthogonalToGeneralLinear, LinearMap.toMatrix'_mulVec]
      exact (mem_orthogonalGroup_iff.mp g.prop) x
    · intro h
      let e : (n → R) ≃ₗ[R] (n → R) :=
        (LinearMap.GeneralLinearGroup.generalLinearEquiv R (n → R))
          (Matrix.GeneralLinearGroup.toLin U)
      have he (x : n → R) : e x = (U : Matrix n n R) *ᵥ x := by
        rfl
      let g : orthogonalGroup Q :=
        ⟨e, mem_orthogonalGroup_iff.mpr (fun x => by rw [he]; exact h x)⟩
      refine ⟨g, ?_⟩
      apply Units.ext
      ext i j
      simpa [orthogonalToGeneralLinear_apply, Matrix.mulVec_single, g] using
        congrArg (fun x : n → R => x i) (he (Pi.single j 1))
  rw [hset]
  apply isClosed_iInter
  intro x
  have hmul : Continuous (fun U : Matrix.GeneralLinearGroup n R =>
      (U : Matrix n n R) *ᵥ x) :=
    Units.continuous_val.matrix_mulVec continuous_const
  exact isClosed_eq (hQ.comp hmul) continuous_const

/-- The coordinate orthogonal group is a closed topological subgroup of matrix `GL`. -/
theorem isClosedEmbedding_orthogonalToGeneralLinear [IsTopologicalRing R] [T2Space R]
    [Invertible (2 : R)] (Q : QuadraticForm R (n → R)) :
    Topology.IsClosedEmbedding (orthogonalToGeneralLinear Q) :=
  ⟨isEmbedding_orthogonalToGeneralLinear Q,
    isClosed_range_orthogonalToGeneralLinear Q⟩

/-- The determinant of a coordinate orthogonal transformation is continuous. -/
@[fun_prop]
theorem continuous_orthogonalDet [IsTopologicalRing R]
    (Q : QuadraticMap R (n → R) N) :
    Continuous (orthogonalDet Q) := by
  have h : Continuous (fun g : orthogonalGroup Q =>
      Matrix.GeneralLinearGroup.det (orthogonalToGeneralLinear Q g)) :=
    Matrix.GeneralLinearGroup.continuous_det.comp
      (isEmbedding_orthogonalToGeneralLinear Q).continuous
  convert h using 1
  funext g
  apply Units.ext
  rw [orthogonalDet_apply, LinearEquiv.coe_det, ← LinearMap.det_toMatrix',
    ← coe_orthogonalToGeneralLinear]
  rfl

/-- The determinant-one subgroup is closed in the coordinate orthogonal group over a
Hausdorff topological ring. -/
theorem isClosed_specialOrthogonalWithin [IsTopologicalRing R] [T2Space R]
    (Q : QuadraticMap R (n → R) N) :
    IsClosed (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) := by
  have hset : (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) =
      (orthogonalDet Q) ⁻¹' {1} := by
    ext g
    simpa only [SetLike.mem_coe, Set.mem_preimage, Set.mem_singleton_iff,
      orthogonalDet_apply] using
      (mem_specialOrthogonalWithin_iff (Q := Q) (g := g))
  rw [hset]
  exact isClosed_singleton.preimage (continuous_orthogonalDet Q)

end

end TauCeti.QuadraticMap
