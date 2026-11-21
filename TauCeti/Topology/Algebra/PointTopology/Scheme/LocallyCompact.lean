/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Scheme.Charts
public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Local compactness of scheme-valued points

Let `R` be a local topological `k`-algebra with open units and continuous inversion on the
units, T1 (for instance Hausdorff) and locally compact. If `X` is locally of finite type over
`k`, then the chart topology on `X(R)` is locally compact. Every point lies in the image of an
affine open chart, which is an open embedding; the algebra of that chart is of finite type over
`k` (`AlgebraicGeometry.LocallyOfFiniteType.Spec_algebraMap_iff`), so its
coordinate-evaluation point space is locally compact.

## Main results

* `TauCeti.SchemePointTopology.locallyCompactSpace_of_locallyOfFiniteType`: `X(R)` is locally
  compact for `X` locally of finite type over `k`; a scoped instance in the namespace
  `TauCeti.SchemePointTopology`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 3.1, p. 4.
-/

public section

open CategoryTheory AlgebraicGeometry Topology
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

variable [TopologicalSpace R] [IsTopologicalSemiring R] [IsLocalRing R] [IsOpenUnits R]
  [T1Space R] [LocallyCompactSpace R]

/-- Over a T1, locally compact local topological ring with open units and continuous
inversion on the units, the points of a scheme locally of finite type over `k` form a locally
compact space. -/
theorem locallyCompactSpace_of_locallyOfFiniteType [LocallyOfFiniteType f] :
    LocallyCompactSpace (Points (R := R) f) where
  local_compact_nhds x n hn := by
    obtain ⟨A, i, hi, _, z, rfl⟩ := exists_mem_range_chartPoint f x
    have : Algebra.FiniteType k A :=
      LocallyOfFiniteType.Spec_algebraMap_iff.mp (hi ▸ inferInstance)
    have := PointTopology.locallyCompactSpace_of_finiteType (k := k) (A := A) (R := R)
    have he := isOpenEmbedding_chartPoint (R := R) f A i hi
    obtain ⟨s, hs, hsn, hsc⟩ :=
      local_compact_nhds (x := z) (he.continuous.continuousAt.preimage_mem_nhds hn)
    exact ⟨_, he.isOpenMap.image_mem_nhds hs, Set.image_subset_iff.mpr hsn,
      hsc.image he.continuous⟩

attribute [scoped instance] locallyCompactSpace_of_locallyOfFiniteType

end TauCeti.SchemePointTopology
