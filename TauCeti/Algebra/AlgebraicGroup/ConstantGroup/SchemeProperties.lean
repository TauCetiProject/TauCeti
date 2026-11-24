/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Connected
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Scheme

/-!
# Connectedness and commutativity of constant group schemes

Let `G` be a finite group. The constant group scheme attached to `G` over a field `K` is finite
and étale, hence proper and smooth. This file records the two properties that separate it from an
abelian scheme as soon as `G` is nontrivial or noncommutative:

* over a nontrivial ring it is disconnected when `G` is nontrivial, and so over a field it is not
  geometrically connected: a connected group maps to a finite constant group only trivially, so
  if `Spec R^G` were connected, evaluation at every element of `G` would be the identity point;
* over a nontrivial ring it is not commutative when `G` is not: its group of points over the base
  contains `G`.

## Main results

* `TauCeti.ConstantGroup.not_connectedSpace_groupScheme`: a nontrivial constant group scheme
  over a nontrivial ring is disconnected.
* `TauCeti.ConstantGroup.not_geometricallyConnected_groupScheme`: a nontrivial constant group
  scheme over a field is not geometrically connected.
* `TauCeti.ConstantGroup.not_isCommMonObj_groupScheme`: the constant group scheme of a
  noncommutative finite group over a nontrivial ring is not a commutative group object.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.ConstantGroup

universe u

variable (G : Type u) [Group G] [Finite G]

/-- **A nontrivial constant group scheme over a nontrivial ring is disconnected**: otherwise its
identity map to the constant group would be trivial on points, while evaluation at `g ≠ 1` is a
nonidentity point. -/
theorem not_connectedSpace_groupScheme (R : Type u) [CommRing R] [Nontrivial R] [Nontrivial G] :
    ¬ ConnectedSpace (groupScheme R G).X.left := by
  intro hX
  rw [groupScheme_X_left] at hX
  -- The underlying space of `Spec R` is `PrimeSpectrum R` by definition.
  have hX' : ConnectedSpace (PrimeSpectrum (coordinateRing R G)) := hX
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  -- The identity map of a connected group to the constant group is trivial on points.
  have h1 := point_comp_eq_one_of_connected G hX' (BialgHom.id R _) (eval R G g)
  refine hg (toPoints_injective R G ?_)
  rw [map_one, ← h1]
  apply WithConv.ofConv_injective
  ext
  simp

/-- **A nontrivial constant group scheme over a field is not geometrically connected**: already
the scheme itself is disconnected. -/
theorem not_geometricallyConnected_groupScheme (K : Type u) [Field K] [Nontrivial G] :
    ¬ GeometricallyConnected (groupScheme K G).X.hom := fun h ↦
  not_connectedSpace_groupScheme G K
    (self_of_isIntegral_of_geometrically h.geometrically_connectedSpace)

/-- **The constant group scheme of a noncommutative finite group is not commutative**: its group
of points over the base ring contains `G` itself. -/
theorem not_isCommMonObj_groupScheme (R : Type u) [CommRing R] [Nontrivial R]
    (h : ¬ IsMulCommutative G) : ¬ IsCommMonObj (groupScheme R G).X := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro hc
  -- Points over the base contain `G`.
  let e := (groupSchemePointMulEquiv R G R).toMonoidHom.comp (toPoints R G)
  have he : Function.Injective e :=
    (groupSchemePointMulEquiv R G R).injective.comp (toPoints_injective R G)
  refine h ⟨⟨fun a b ↦ he ?_⟩⟩
  rw [map_mul, map_mul,
    (hc ((Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of R)))).is_comm.comm]

end TauCeti.ConstantGroup
