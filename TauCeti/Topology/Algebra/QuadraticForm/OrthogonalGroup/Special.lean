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
when the underlying module is finite free. For a quadratic form over a domain with
left-separating polar form, every orthogonal determinant is `1` or `-1`, so this
subgroup is also open. The topology is the one induced from linear automorphisms.
-/

public section

namespace TauCeti

namespace QuadraticMap

open TauCeti _root_.QuadraticMap

open scoped Topology

section CommRing

variable {K V N : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V] [AddCommMonoid N] [Module K N]
  [Module.Free K V] [Module.Finite K V] (Q : QuadraticMap K V N)

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

variable {K V : Type*} [CommRing K] [IsDomain K] [TopologicalSpace K]
  [IsTopologicalRing K] [T2Space K] [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V] (Q : QuadraticForm K V)

/-- The determinant-one subgroup is open in the orthogonal group. -/
theorem isOpen_specialOrthogonalWithin (hQ : Q.polarBilin.SeparatingLeft) :
    IsOpen (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) := by
  have hrange : Set.range (fun g : orthogonalGroup Q => (orthogonalDet Q g : K)) ⊆
      ({1, -1} : Set K) := by
    rintro u ⟨g, rfl⟩
    have hs : (orthogonalDet Q g : K) ^ 2 = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg Units.val (orthogonalDet_sq hQ g)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (sq_eq_one_iff.mp hs)
  by_cases hchar : (1 : K) = -1
  · have htop : (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) = Set.univ := by
      ext g
      simp only [Set.mem_univ, iff_true]
      apply mem_specialOrthogonalWithin_iff.mpr
      apply Units.ext
      rcases Set.mem_insert_iff.mp (hrange (Set.mem_range_self g)) with h | h
      · simpa only [orthogonalDet_apply, Units.val_one] using h
      · simpa only [Set.mem_singleton_iff, orthogonalDet_apply, Units.val_one, ← hchar]
          using h
    rw [htop]
    exact isOpen_univ
  · have hclosed : IsClosed {g : orthogonalGroup Q | (orthogonalDet Q g : K) = -1} :=
      isClosed_singleton.preimage (continuous_orthogonalDet_val Q)
    have hset : (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) =
        {g | (orthogonalDet Q g : K) ≠ -1} := by
      ext g
      constructor
      · intro hg
        have h : (orthogonalDet Q g : K) = 1 := by
          simpa only [orthogonalDet_apply, Units.val_one] using
            congrArg Units.val (mem_specialOrthogonalWithin_iff.mp hg)
        change (orthogonalDet Q g : K) ≠ -1
        simpa only [h] using hchar
      · intro hg
        apply mem_specialOrthogonalWithin_iff.mpr
        apply Units.ext
        rcases Set.mem_insert_iff.mp (hrange (Set.mem_range_self g)) with h | h
        · simpa only [orthogonalDet_apply, Units.val_one] using h
        · exact (hg (Set.mem_singleton_iff.mp h)).elim
    rw [hset]
    simpa only [Set.compl_ofPred] using hclosed.isOpen_compl

end QuadraticMap

end TauCeti
