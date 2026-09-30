/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Determinant
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# The determinant-one subgroup of an orthogonal group

For a nondegenerate quadratic form over a Hausdorff topological field of characteristic
different from two, every orthogonal determinant is `1` or `-1`. Continuity of the
determinant therefore makes the special orthogonal group both open and closed in the
orthogonal group. The topology is the one induced from linear automorphisms.
-/

public section

namespace TauCeti

namespace QuadraticMap

open TauCeti _root_.QuadraticMap

open scoped Topology

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (Q : QuadraticForm K V)

/-- The determinant is continuous on the orthogonal group. -/
@[continuity, fun_prop]
theorem continuous_orthogonalDet : Continuous (orthogonalDet Q) := by
  have hsub : Continuous (fun g : orthogonalGroup Q => (g : V ≃ₗ[K] V)) :=
    continuous_subtype_val
  have hmap : Continuous (fun g : orthogonalGroup Q =>
      ((g : V ≃ₗ[K] V) : Module.End K V)) :=
    continuous_linearEquiv_toLinearMap.comp hsub
  have h := LinearMap.continuous_det_moduleTopology.comp hmap
  have hval : Continuous (fun g : orthogonalGroup Q => (orthogonalDet Q g : K)) := by
    simpa only [Function.comp_def, orthogonalDet_apply, LinearEquiv.coe_det] using h
  apply Units.continuous_iff.mpr
  refine ⟨hval, ?_⟩
  simpa only [Function.comp_def, map_inv, Units.val_inv_eq_inv_val] using
    hval.comp (continuous_inv : Continuous fun g : orthogonalGroup Q => g⁻¹)

/-- The scalar determinant is continuous on the orthogonal group. -/
@[continuity, fun_prop]
theorem continuous_orthogonalDet_val :
    Continuous (fun g : orthogonalGroup Q => (orthogonalDet Q g : K)) :=
  Units.continuous_val.comp (continuous_orthogonalDet Q)

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
  classical
  rcases subsingleton_or_nontrivial V with h | h
  · let _ := h
    rw [specialOrthogonalWithin_eq_top]
    exact isOpen_univ
  · let _ := h
    let _ : (specialOrthogonalWithin Q).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by rw [index_specialOrthogonalWithin hQ]; decide)
    exact (specialOrthogonalWithin Q).isOpen_of_isClosed_of_finiteIndex
      (isClosed_specialOrthogonalWithin Q)

end QuadraticMap

end TauCeti
