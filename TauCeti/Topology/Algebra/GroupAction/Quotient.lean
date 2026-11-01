/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Continuous maps from group quotients

This file records continuity results for maps out of group quotients that do not require
transitivity of an action.

## Main results

* `TauCeti.continuous_ofQuotientStabilizer` proves continuity of the orbit map descended to a
  stabilizer quotient when the corresponding orbit map is continuous.
* `TauCeti.continuous_orbitRelQuotientLift_iff`: the descent of a `G`-invariant map to the orbit
  space is continuous exactly when the map is.
* `SubMulAction.isOpenEmbedding_orbitRelQuotientMap`: for an open slice `S` for a subgroup `H`, an
  `H`-invariant open set moved into itself only by elements of `H`, the map `S / H → X / G` of
  orbit spaces is an open embedding. For `H = ⊥` this recovers
  `TauCeti.isOpenEmbedding_quotientMk_domRestrict_of_disjoint_smul`.
-/

public section

open MulAction

namespace TauCeti

section Lift

variable {G X Y : Type*} [Group G] [MulAction G X] [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} {hf : ∀ (g : G) (x : X), f (g • x) = f x}

/-- The descent of a `G`-invariant map to the orbit space is continuous exactly when the map is. -/
theorem continuous_orbitRelQuotientLift_iff :
    Continuous (MulAction.orbitRelQuotientLift f hf) ↔ Continuous f := by
  have hq : Topology.IsQuotientMap (Quotient.mk (MulAction.orbitRel G X)) := isQuotientMap_quot_mk
  rw [hq.continuous_iff, MulAction.orbitRelQuotientLift_comp_mk]

end Lift

section Slice

open Set Topology

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X] [ContinuousConstSMul G X]

/-- **Orbit spaces of open slices.** Let `S` be an open `H`-invariant subset of `X` such that every
element of `G` carrying a point of `S` into `S` lies in `H`. Then the map `S / H → X / G` sending
an `H`-orbit to its `G`-orbit is an open embedding of orbit spaces. -/
theorem _root_.SubMulAction.isOpenEmbedding_orbitRelQuotientMap {H : Subgroup G}
    (S : SubMulAction H X) (hS_open : IsOpen (S : Set X))
    (hS : ∀ (g : G) (y : X), y ∈ S → g • y ∈ S → g ∈ H) :
    IsOpenEmbedding S.orbitRelQuotientMap := by
  -- Composed with the orbit projection of `S`, the map is the orbit projection of `X` on `S`.
  have hcont : Continuous S.orbitRelQuotientMap := by
    rw [isQuotientMap_quotient_mk'.continuous_iff]
    exact S.orbitRelQuotientMap_comp_mk ▸ continuous_quot_mk.comp continuous_subtype_val
  refine .of_continuous_injective_isOpenMap hcont (S.orbitRelQuotientMap_injective hS)
    fun U hU ↦ ?_
  -- The image of `U` is the image in `X / G` of the open set of points of `S` lying over `U`.
  rw [← Quotient.mk_surjective.image_preimage U, ← image_comp, S.orbitRelQuotientMap_comp_mk,
    image_comp]
  exact isOpenMap_quotient_mk'_mul _
    (hS_open.isOpenMap_subtype_val _ (hU.preimage continuous_quot_mk))

end Slice

variable (G : Type*) {X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace X]
  [MulAction G X]

/-- The orbit map descended to the stabilizer quotient is continuous when the orbit map is. -/
@[fun_prop]
theorem continuous_ofQuotientStabilizer (b : X) (hb : Continuous fun g : G => g • b) :
    Continuous (ofQuotientStabilizer G b) := by
  unfold ofQuotientStabilizer
  exact hb.quotient_liftOn' _

end TauCeti
