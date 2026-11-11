/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Scheme.Charts
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Local compactness of scheme-valued points

Let `R` be a local topological `k`-algebra with open units and continuous inversion on the
units, T1 (for instance Hausdorff) and locally compact. If `X` is locally of finite type over
`k`, then the chart topology on `X(R)` is locally compact. Every point lies in the image of an
affine open chart, which is an open embedding; the algebra of that chart is of finite type over
`k`, so its coordinate-evaluation point space is locally compact.

## Main results

* `TauCeti.SchemePointTopology.finiteType_of_chart`: the algebra of an affine open chart of a
  scheme locally of finite type over `k` is of finite type over `k`.
* `TauCeti.SchemePointTopology.locallyCompactSpace_of_locallyOfFiniteType`: `X(R)` is locally
  compact for `X` locally of finite type over `k`.

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

/-- The algebra of an affine open chart of a scheme locally of finite type over `k` is of finite
type over `k`. -/
theorem finiteType_of_chart [LocallyOfFiniteType f] (A : CommAlgCat.{u} k)
    (i : Spec (.of A) ⟶ X) (hi : i ≫ f = Spec.algebraMap k A) [IsOpenImmersion i] :
    Algebra.FiniteType k A := by
  have : LocallyOfFiniteType (Spec.algebraMap k A) := hi ▸ inferInstance
  exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp this)

variable [TopologicalSpace R] [IsTopologicalSemiring R] [IsLocalRing R] [IsOpenUnits R]
  [T1Space R] [LocallyCompactSpace R]

/-- Over a T1, locally compact local topological ring with open units and continuous
inversion on the units, the points of a scheme locally of finite type over `k` form a locally
compact space. -/
theorem locallyCompactSpace_of_locallyOfFiniteType [LocallyOfFiniteType f] :
    LocallyCompactSpace (Points (R := R) f) where
  local_compact_nhds x n hn := by
    obtain ⟨A, i, hi, _, z, rfl⟩ := exists_mem_range_chartPoint f x
    have : Algebra.FiniteType k A := finiteType_of_chart f A i hi
    have := PointTopology.locallyCompactSpace_of_finiteType (k := k) (A := A) (R := R)
    have he := isOpenEmbedding_chartPoint (R := R) f A i hi
    obtain ⟨s, hs, hsn, hsc⟩ :=
      local_compact_nhds (x := z) (he.continuous.continuousAt.preimage_mem_nhds hn)
    exact ⟨_, he.isOpenMap.image_mem_nhds hs, Set.image_subset_iff.mpr hsn,
      hsc.image he.continuous⟩

end TauCeti.SchemePointTopology
