/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Determinant
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import TauCeti.Topology.Algebra.ContinuousMonoidHom
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The determinant-one subgroup of an orthogonal group

Over a T₁ topological commutative ring, the determinant-one subgroup is closed
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
theorem _root_.QuadraticMap.continuous_orthogonalDet : Continuous (orthogonalDet Q) := by
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
theorem _root_.QuadraticMap.continuous_orthogonalDet_val :
    Continuous (fun g : orthogonalGroup Q => (orthogonalDet Q g : K)) :=
  Units.continuous_val.comp (continuous_orthogonalDet Q)

variable [T1Space K]

/-- The determinant-one subgroup is closed in the orthogonal group. -/
theorem _root_.QuadraticMap.isClosed_specialOrthogonalWithin :
    IsClosed (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) := by
  let det : orthogonalGroup Q →ₜ* Kˣ := ⟨orthogonalDet Q, continuous_orthogonalDet Q⟩
  simpa only [specialOrthogonalWithin] using det.isClosed_ker

end CommRing

variable {K V : Type*} [CommRing K] [IsDomain K] [TopologicalSpace K]
  [IsTopologicalRing K] [T1Space K] [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V] (Q : QuadraticForm K V)

/-- The determinant-one subgroup is open in the orthogonal group. -/
theorem _root_.QuadraticMap.isOpen_specialOrthogonalWithin (hQ : Q.polarBilin.SeparatingLeft) :
    IsOpen (specialOrthogonalWithin Q : Set (orthogonalGroup Q)) := by
  have hrange : Set.range (orthogonalDet Q) ⊆ ({1, -1} : Set Kˣ) := by
    rintro u ⟨g, rfl⟩
    have hs : (orthogonalDet Q g : K) ^ 2 = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg Units.val (orthogonalDet_sq hQ g)
    rcases sq_eq_one_iff.mp hs with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl (Units.val_injective (by simpa using h)))
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr
        (Units.val_injective (by simpa using h))))
  have : Finite (orthogonalDet Q).range :=
    (Set.Finite.subset (Set.toFinite _) hrange).to_subtype
  have : Module.Finite K (Module.End K V) := Module.Finite.linearMap K K V V
  have : (specialOrthogonalWithin Q).FiniteIndex := by
    simpa only [specialOrthogonalWithin] using
      (Subgroup.finiteIndex_ker (orthogonalDet Q))
  exact (specialOrthogonalWithin Q).isOpen_of_isClosed_of_finiteIndex
    (isClosed_specialOrthogonalWithin Q)

end QuadraticMap

end TauCeti
