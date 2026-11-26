/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Proper.Constructions
public import TauCeti.Geometry.Manifold.Groupoid.Prod
public import TauCeti.Topology.CategoryTheory.Etale

/-!
# Consequences of proper étaleness

For a Hausdorff proper étale Lie groupoid `TauCeti.IsProperEtaleGroupoid I J C` (defined in
`TauCeti.Geometry.Manifold.Etale.Proper.Basic`), this file specializes the unbundled finite-chart
theory of `TauCeti.Topology.CategoryTheory.Etale` and `TauCeti.Geometry.Manifold.Groupoid.Basic`:

* source and target are local homeomorphisms
  (`TauCeti.IsProperEtaleGroupoid.isLocalHomeomorph_source`,
  `TauCeti.IsProperEtaleGroupoid.isLocalHomeomorph_target`);
* on a nonempty object manifold, the arrow and object models have the same dimension
  (`TauCeti.IsProperEtaleGroupoid.finrank_eq`);
* there are finitely many arrows between any two objects, so every isotropy group is finite
  (`TauCeti.IsProperEtaleGroupoid.finite_hom`, `TauCeti.IsProperEtaleGroupoid.finite_aut`);
* the identity arrows form a clopen subset of the arrows
  (`TauCeti.IsProperEtaleGroupoid.isClopen_range_unit`).

It also registers the product of two proper étale Lie groupoids as an instance
(`TauCeti.IsProperEtaleGroupoid.instProd`), for the product Lie groupoid structure
`TauCeti.IsLieGroupoid.prod`, using `TauCeti.IsProperEtaleGroupoid.prod`.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 1.
-/

public section

open CategoryTheory Module Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace IsProperEtaleGroupoid

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
  {C : Type*} [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)]
  [IsProperEtaleGroupoid I J C]

include I J in
/-- The source map of a proper étale Lie groupoid is a local homeomorphism. -/
theorem isLocalHomeomorph_source :
    IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C) :=
  (isLocalDiffeomorph_source (I := I) (J := J)).isLocalHomeomorph

include I J in
/-- The target map of a proper étale Lie groupoid is a local homeomorphism. -/
theorem isLocalHomeomorph_target :
    IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C) :=
  (isLocalDiffeomorph_target (I := I) (J := J)).isLocalHomeomorph

include I J in
/-- On a nonempty object manifold, the arrow and object models of a proper étale Lie groupoid have
the same dimension. -/
theorem finrank_eq [Nonempty C] : finrank ℝ E' = finrank ℝ E :=
  (IsLieGroupoid.isLocalDiffeomorph_source_iff_finrank_eq I J C).1 isLocalDiffeomorph_source

include I J in
/-- A proper étale Lie groupoid has finitely many arrows between any two objects. -/
theorem finite_hom (x y : C) : Finite (x ⟶ y) :=
  finite_hom_of_proper_source_target (isProperMap_source_target (I := I) (J := J))
    (isLocalHomeomorph_source I J) x y

include I J in
/-- Every isotropy group of a proper étale Lie groupoid is finite. -/
theorem finite_aut (x : C) : Finite (Aut x) :=
  finite_aut_of_proper_source_target (isProperMap_source_target (I := I) (J := J))
    (isLocalHomeomorph_source I J) x

include I J in
/-- The identity arrows of a proper étale Lie groupoid form a clopen subset of the arrows. -/
theorem isClopen_range_unit :
    IsClopen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  have := t2Space_arrows (I := I) (J := J) (C := C)
  TauCeti.isClopen_range_unit (IsLieGroupoid.contMDiff_unit (I := I) (J := J)).continuous
    (isLocalHomeomorph_source I J)

end IsProperEtaleGroupoid

/-! ### Products -/

namespace IsProperEtaleGroupoid

variable {E H E' H' F G F' G' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {I' : ModelWithCorners ℝ F G} [I'.Boundaryless]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] [TopologicalSpace G']
  {J' : ModelWithCorners ℝ F' G'} [J'.Boundaryless]
  {C : Type*} [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsProperEtaleGroupoid I J C]
  {D : Type*} [Category D] [IsGroupoid D]
  [TopologicalSpace D] [ChartedSpace G D] [IsManifold I' ∞ D]
  [TopologicalSpace (Quiver.Total D)] [ChartedSpace G' (Quiver.Total D)]
  [IsManifold J' ∞ (Quiver.Total D)] [IsProperEtaleGroupoid I' J' D]

/-- **The product of two proper étale Lie groupoids is a proper étale Lie groupoid**, with the
product Lie groupoid structure `TauCeti.IsLieGroupoid.prod`. -/
instance instProd : IsProperEtaleGroupoid (I.prod I') (J.prod J') (C × D) :=
  IsProperEtaleGroupoid.prod J J' I I'

end IsProperEtaleGroupoid

end TauCeti
