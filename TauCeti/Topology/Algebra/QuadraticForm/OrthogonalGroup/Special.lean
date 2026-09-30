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

Over a Hausdorff topological commutative ring, the determinant-one subgroup is closed
when the underlying module is finite free. For a nondegenerate quadratic form over a
field of characteristic different from two, every orthogonal determinant is `1` or
`-1`, so this subgroup is also open. The topology is the one induced from linear
automorphisms.
-/

public section

namespace TauCeti

namespace QuadraticMap

open TauCeti _root_.QuadraticMap

open scoped Topology

section CommRing

variable {K V : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V] (Q : QuadraticForm K V)

/-- The determinant is continuous on the orthogonal group. -/
@[continuity, fun_prop]
theorem continuous_orthogonalDet : Continuous (orthogonalDet Q) := by
  have hsub : Continuous (fun g : orthogonalGroup Q => (g : V ≃ₗ[K] V)) :=
    continuous_subtype_val
  obtain ⟨hmap, hmap_inv⟩ := continuous_linearEquiv_iff.mp hsub
  have h := LinearMap.continuous_det_moduleTopology.comp hmap
  have hval : Continuous (fun g : orthogonalGroup Q => (orthogonalDet Q g : K)) := by
    simpa only [Function.comp_def, orthogonalDet_apply, LinearEquiv.coe_det] using h
  apply Units.continuous_iff.mpr
  refine ⟨hval, ?_⟩
  have h := LinearMap.continuous_det_moduleTopology.comp hmap_inv
  simpa only [Function.comp_def, ← LinearEquiv.coe_det, map_inv,
    orthogonalDet_apply, Units.val_inv_eq_inv_val] using h

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

end CommRing

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [NeZero (2 : K)] (Q : QuadraticForm K V)

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
