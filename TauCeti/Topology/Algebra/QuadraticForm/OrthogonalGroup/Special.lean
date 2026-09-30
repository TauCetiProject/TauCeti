/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Determinant
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup

/-!
# The determinant-one subgroup of an orthogonal group

For a nondegenerate quadratic form over a Hausdorff topological field of characteristic
different from two, every orthogonal determinant is `1` or `-1`. Continuity of the
determinant therefore makes the special orthogonal group both open and closed in the
orthogonal group. The topology is the one induced from linear automorphisms.
-/

public section

namespace QuadraticMap

open TauCeti TauCeti.QuadraticMap

open scoped Topology

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (Q : QuadraticForm K V)

/-- The scalar determinant is continuous on the orthogonal group. -/
@[fun_prop]
theorem continuous_orthogonalDet_val :
    Continuous (fun g : orthogonalGroup Q => (orthogonalDet Q g : K)) := by
  have hsub : Continuous (fun g : orthogonalGroup Q => (g : V ≃ₗ[K] V)) :=
    continuous_subtype_val
  have hmap : Continuous (fun g : orthogonalGroup Q =>
      ((g : V ≃ₗ[K] V) : Module.End K V)) :=
    continuous_linearEquiv_toLinearMap.comp hsub
  have h := LinearMap.continuous_det_moduleTopology.comp hmap
  simpa only [Function.comp_def, orthogonalDet_apply, LinearEquiv.coe_det] using h

variable [T2Space K]

/-- The determinant-one subgroup is closed in the orthogonal group. -/
theorem isClosed_specialOrthogonalWithin :
    IsClosed (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) := by
  have hset : (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) =
      {g | (orthogonalDet Q g : K) = 1} := by
    ext g
    simp only [Set.mem_ofPred_eq, orthogonalDet_apply]
    constructor
    · intro hg
      exact congrArg Units.val (mem_specialOrthogonalWithin_iff.mp hg)
    · intro hg
      exact mem_specialOrthogonalWithin_iff.mpr (Units.val_injective hg)
  rw [hset]
  exact isClosed_singleton.preimage (continuous_orthogonalDet_val Q)

variable [NeZero (2 : K)]

/-- The determinant-one subgroup is open in the orthogonal group. -/
theorem isOpen_specialOrthogonalWithin (hQ : Q.Nondegenerate) :
    IsOpen (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne 2)
  have hset : (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) =
      {g | (orthogonalDet Q g : K) ≠ -1} := by
    ext g
    have hg : (orthogonalDet Q g : K) ^ 2 = 1 := by
      have hpolar : Q.polarBilin.SeparatingLeft :=
        (nondegenerate_polar_iff.mpr hQ).1
      simpa using congrArg Units.val (orthogonalDet_sq hpolar g)
    have htwo := (sq_eq_one_iff).mp hg
    simp only [orthogonalDet_apply] at htwo
    simp only [Set.mem_ofPred_eq, orthogonalDet_apply]
    constructor
    · intro h
      have hval : (LinearEquiv.det (g : V ≃ₗ[K] V) : K) = 1 := by
        simpa using congrArg Units.val (mem_specialOrthogonalWithin_iff.mp h)
      rw [hval]
      intro hneg
      apply (NeZero.ne (2 : K))
      calc
        (2 : K) = 1 - (-1) := by ring
        _ = 0 := sub_eq_zero.mpr hneg
    · intro h
      exact mem_specialOrthogonalWithin_iff.mpr
        (Units.val_injective (htwo.resolve_right h))
  rw [hset]
  exact (isClosed_singleton.preimage (continuous_orthogonalDet_val Q)).isOpen_compl

end QuadraticMap
