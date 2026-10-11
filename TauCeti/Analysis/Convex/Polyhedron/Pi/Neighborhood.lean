/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Pi.Basic

/-!
# Polyhedral neighbourhoods in real coordinate products

In an arbitrary product of real lines, boxes constraining finitely many coordinates are
convex polyhedra and form a neighbourhood basis. Unlike boxes constraining every coordinate,
these cylinders remain neighbourhoods when the coordinate type is infinite.

These neighbourhoods allow local affine decompositions to be restricted to polyhedral cells
before taking a finite subcover of a compact set.
-/

public section

open Set Filter Topology Metric

namespace TauCeti

variable {ι : Type*}

/-- A cylinder imposing interval bounds on finitely many coordinates is a convex polyhedron
in the product topology, with no finiteness assumption on the ambient coordinate type. -/
theorem isConvexPolyhedron_pi_Icc_of_finite {I : Set ι} (hI : I.Finite) (a b : ι → ℝ) :
    IsConvexPolyhedron (I.pi fun i => Icc (a i) (b i)) := by
  have : Finite I := hI.to_subtype
  let R : (ι → ℝ) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.1
  convert (isConvexPolyhedron_pi_Icc (fun i : I => a i) (fun i : I => b i)).preimage
    R.toContinuousAffineMap using 1
  ext x
  simp [R, Set.mem_pi, Pi.le_def, ← forall_and]

/-- Every neighbourhood in a real coordinate product contains a convex polyhedral
neighbourhood. The product may have infinitely many coordinates. -/
theorem exists_isConvexPolyhedron_mem_nhds_pi {x : ι → ℝ} {U : Set (ι → ℝ)}
    (hU : U ∈ 𝓝 x) : ∃ C ∈ 𝓝 x, IsConvexPolyhedron C ∧ C ⊆ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  choose r hr hball using fun i => nhds_basis_closedBall.mem_iff.mp (ht i)
  refine ⟨(I : Set ι).pi (fun i => closedBall (x i) (r i)),
    set_pi_mem_nhds I.finite_toSet (fun i _ => closedBall_mem_nhds _ (hr i)), ?_, ?_⟩
  · simpa only [Real.closedBall_eq_Icc] using
      isConvexPolyhedron_pi_Icc_of_finite I.finite_toSet
        (fun i => x i - r i) (fun i => x i + r i)
  · exact (Set.pi_mono fun i _ => hball i).trans hsub

end TauCeti
