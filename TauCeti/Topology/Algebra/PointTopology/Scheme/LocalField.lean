/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.Topology.Algebra.PointTopology.Scheme.LocallyCompact
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Separation
public import TauCeti.Topology.Algebra.ValuativeRel.Integer

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
compact open subgroups live.

## Main results

* `TauCeti.SchemePointTopology.locallyCompactSpace_of_localField`: `X(E)` is Hausdorff and locally
  compact for `X` separated and locally of finite type over `E`.

Over `𝒪[E]`, `TauCeti.SchemePointTopology.locallyCompactSpace_of_locallyOfFiniteType` applies
directly: `𝒳(𝒪[E])` is locally compact for `𝒳` locally of finite type over `𝒪[E]`.

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

/-- The points of a scheme separated and locally of finite type over a nonarchimedean local field
`E` form a Hausdorff, locally compact space for the chart topology. -/
theorem locallyCompactSpace_of_localField {X : Scheme.{u}} (f : X ⟶ Spec (.of E))
    [IsSeparated f] [LocallyOfFiniteType f] :
    T2Space (Points (R := E) f) ∧ LocallyCompactSpace (Points (R := E) f) :=
  ⟨t2Space_of_isSeparated f, locallyCompactSpace_of_locallyOfFiniteType f⟩

/- The integral points of a scheme locally of finite type over `𝒪[E]` are locally compact, by the
general result applied over `𝒪[E]`, whose open units come from `TauCeti.instIsOpenUnitsInteger`. -/
example {X : Scheme.{u}} (f : X ⟶ Spec (.of 𝒪[E])) [LocallyOfFiniteType f] :
    LocallyCompactSpace (Points (R := 𝒪[E]) f) :=
  locallyCompactSpace_of_locallyOfFiniteType f

end TauCeti.SchemePointTopology
