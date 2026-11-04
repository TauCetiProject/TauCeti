/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order

/-!
# Transporting places of the rational function field along the coefficient map

A field isomorphism `σ : k ≃+* k'` induces the coefficient map
`RatFunc.mapRingEquiv σ : k(t) ≃+* k'(t)`, and hence a bijection
`TauCeti.Place.equivOfRingEquiv σ (RatFunc.mapRingEquiv σ) _` between the places of `k(t)` and
those of `k'(t)`. This file computes that bijection on the degree-one finite places.

## Main results

* `TauCeti.Place.equivOfRingEquiv_mapRingEquiv_adicOfIrreducible_X_sub_C`: the bijection carries
  the place `t = a` to the place `t = σ a`.
-/

public section

open RatFunc

namespace TauCeti.Place

variable {k k' : Type*} [Field k] [Field k'] (σ : k ≃+* k')

/-- **The coefficient map moves the place `t = a` to the place `t = σ a`**: the bijection between
the places of `k(t)` and those of `k'(t)` induced by the coefficient map of `σ : k ≃+* k'`
carries the zero of `t - a` to the zero of `t - σ a`. -/
@[simp]
theorem equivOfRingEquiv_mapRingEquiv_adicOfIrreducible_X_sub_C (a : k) :
    equivOfRingEquiv σ (RatFunc.mapRingEquiv σ) (RatFunc.mapRingEquiv_algebraMap_const σ)
      (adicOfIrreducible (Polynomial.irreducible_X_sub_C a)) =
      adicOfIrreducible (Polynomial.irreducible_X_sub_C (σ a)) := by
  refine ord_X_sub_C_pos_iff.mp ?_
  rw [ord_equivOfRingEquiv, RatFunc.mapRingEquiv_symm, map_sub, RatFunc.mapRingEquiv_X,
    RatFunc.mapRingEquiv_C, RingEquiv.symm_apply_apply]
  exact ord_X_sub_C_pos_iff.mpr rfl

end TauCeti.Place
