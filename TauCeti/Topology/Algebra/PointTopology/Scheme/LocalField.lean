/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.Topology.Algebra.PointTopology.Scheme.LocallyCompact
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Separation
public import TauCeti.Topology.Algebra.ValuativeRel.Integer
import TauCeti.NumberTheory.LocalField.NormedField
import TauCeti.Topology.Algebra.PointTopology.Scheme.Smooth

/-!
# Points of schemes over a nonarchimedean local field

Let `E` be a nonarchimedean local field with valuation ring `𝒪[E]`. Both `E` and `𝒪[E]` are
Hausdorff, locally compact local topological rings with open units and continuous inversion on
the units: for `E` because it is a topological field, for `𝒪[E]` by
`TauCeti.instIsOpenUnitsInteger`, its units being the open subset of elements of valuation one.
So the chart topology on scheme-valued points applies over both rings, and
`TauCeti.SchemePointTopology.t2Space_of_isSeparated` and
`TauCeti.SchemePointTopology.locallyCompactSpace_of_locallyOfFiniteType` apply to them.

For a scheme `X` separated and locally of finite type over `E`, the points `X(E)` form a
Hausdorff, locally compact space; for a scheme `𝒳` locally of finite type over `𝒪[E]`, such as an
integral model of finite type of an algebraic group, the points `𝒳(𝒪[E])` form a locally compact
space. These are the spaces of points of groups over local fields on which Haar measures and
compact open subgroups live. A smooth map over any commutative ring with an `E`-algebra
structure induces an open map on its `E`-points, by using the normalized norm and transporting
the openness back
to the valuative topology.

## Applying the general results

With `TauCeti.SchemePointTopology` open, the general results apply over `E` and `𝒪[E]`, as the
examples below show.

* `TauCeti.SchemePointTopology.t2Space_of_isSeparated` and
  `TauCeti.SchemePointTopology.locallyCompactSpace_of_locallyOfFiniteType`: `X(E)` is Hausdorff
  and locally compact for `X` separated and locally of finite type over `E`.
* `TauCeti.SchemePointTopology.locallyCompactSpace_of_locallyOfFiniteType`: `𝒳(𝒪[E])` is locally
  compact for `𝒳` locally of finite type over `𝒪[E]`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2, and Prop. 3.1 and Rem. 3.2, p. 4.
-/

public section

open CategoryTheory AlgebraicGeometry ValuativeRel
open scoped TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable (E : Type u) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/- The points of a scheme separated and locally of finite type over a nonarchimedean local field
`E` form a Hausdorff, locally compact space for the chart topology. -/
example {X : Scheme.{u}} (f : X ⟶ Spec (.of E)) [IsSeparated f] :
    T2Space (Points (R := E) f) :=
  t2Space_of_isSeparated f

example {X : Scheme.{u}} (f : X ⟶ Spec (.of E)) [LocallyOfFiniteType f] :
    LocallyCompactSpace (Points (R := E) f) :=
  locallyCompactSpace_of_locallyOfFiniteType f

/- The integral points of a scheme locally of finite type over `𝒪[E]` are locally compact, by the
general result applied over `𝒪[E]`, whose open units come from `TauCeti.instIsOpenUnitsInteger`. -/
example {X : Scheme.{u}} (f : X ⟶ Spec (.of 𝒪[E])) [LocallyOfFiniteType f] :
    LocallyCompactSpace (Points (R := 𝒪[E]) f) :=
  locallyCompactSpace_of_locallyOfFiniteType f

/-- A smooth morphism over a commutative ring induces an open map on points valued in a
nonarchimedean local field algebra, with the valuative point topology. -/
theorem isOpenMap_map_of_smooth_of_isNonarchimedeanLocalField
    {k : Type u} [CommRing k] [Algebra k E]
    {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)}
    (g : X ⟶ Y) (hg : g ≫ fY = fX) [Smooth g] :
    IsOpenMap (map (R := E) g hg) := by
  have h : @IsOpenMap _ _
      (@topology k E _ _ _ X fX (normalizedNormedFieldTopology E))
      (@topology k E _ _ _ Y fY (normalizedNormedFieldTopology E)) (map (R := E) g hg) := by
    let _ := normalizedNontriviallyNormedField E
    let _ := normalizedNormedField_completeSpace E
    exact isOpenMap_map_of_smooth g hg
  rwa [normalizedNormedField_topology_eq E] at h

end TauCeti.SchemePointTopology
