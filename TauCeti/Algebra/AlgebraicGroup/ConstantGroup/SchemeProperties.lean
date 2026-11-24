/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Scheme

/-!
# Connectedness and commutativity of constant group schemes

Let `G` be a finite group and `K` a field. The constant group scheme attached to `G` over `K` is
finite and étale, hence proper and smooth. This file records the two properties that separate it
from an abelian scheme as soon as `G` is nontrivial or noncommutative:

* it is not geometrically connected when `G` is nontrivial: the indicator function of the
  identity is an idempotent of the function algebra `K^G` other than `0` and `1`, so `Spec K^G`
  is disconnected;
* it is not commutative when `G` is not: its group of points over the base is `G` itself.

## Main results

* `TauCeti.ConstantGroup.not_geometricallyConnected_groupScheme`: a nontrivial constant group
  scheme over a field is not geometrically connected.
* `TauCeti.ConstantGroup.not_isCommMonObj_groupScheme`: the constant group scheme of a
  noncommutative finite group is not a commutative group object.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.ConstantGroup

universe u

variable (K : Type u) [Field K] (G : Type u) [Group G] [Finite G]

/-- **A nontrivial constant group scheme over a field is not geometrically connected**: the
indicator function of the identity is an idempotent of its coordinate ring `K^G` other than `0`
and `1`, so already the scheme itself is disconnected. -/
theorem not_geometricallyConnected_groupScheme [Nontrivial G] :
    ¬ GeometricallyConnected (groupScheme K G).X.hom := by
  intro h
  have hX : ConnectedSpace (groupScheme K G).X.left :=
    self_of_isIntegral_of_geometrically h.geometrically_connectedSpace
  rw [groupScheme_X_left] at hX
  have hX' : ConnectedSpace (PrimeSpectrum (coordinateRing K G)) := hX
  classical
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  -- The indicator function of the identity, as an element of the coordinate ring.
  let e := (functionAlgEquiv K G).symm (Pi.single 1 1)
  have h1 : IsIdempotentElem (Pi.single (M := fun _ : G ↦ K) 1 1) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  have he : IsIdempotentElem e := h1.map (functionAlgEquiv K G).symm
  rcases he.eq_zero_or_eq_one_of_preconnectedSpace with h0 | h1
  · have := congr_fun (congr_arg (functionAlgEquiv K G) h0) 1
    rw [AlgEquiv.apply_symm_apply, map_zero] at this
    simp at this
  · have := congr_fun (congr_arg (functionAlgEquiv K G) h1) g
    rw [AlgEquiv.apply_symm_apply, map_one] at this
    simp [hg] at this

/-- **The constant group scheme of a noncommutative finite group is not commutative**: its group
of points over the base field is the group `G` itself. -/
theorem not_isCommMonObj_groupScheme (h : ∃ a b : G, a * b ≠ b * a) :
    ¬ IsCommMonObj (groupScheme K G).X := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro hc
  obtain ⟨a, b, hab⟩ := h
  -- Points over the base are `G`.
  let e := (pointsMulEquiv K G).trans (groupSchemePointMulEquiv K G K)
  have := (hc ((Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of K)))).is_comm.comm
    (e a) (e b)
  exact hab (e.injective (by rw [map_mul, map_mul, this]))

end TauCeti.ConstantGroup
