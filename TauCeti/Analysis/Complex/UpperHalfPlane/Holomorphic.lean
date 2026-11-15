/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Holomorphy in the upper half-plane under moving infinity to a real point

For real `c` the Möbius map `z ↦ c - z⁻¹` is a holomorphic self-map of the open upper half-plane,
which exchanges `0` with infinity and infinity with `c`. Precomposing a function holomorphic in the
upper half-plane with it therefore gives a function holomorphic there, whatever value is assigned
at `0`. This is the holomorphic counterpart of the continuity, limit, image and injectivity facts
about moving infinity to a real point in `TauCeti.Analysis.Complex.UpperHalfPlane.Topology`.

## Main results

* `TauCeti.differentiableOn_update_comp_const_sub_inv` -- holomorphy is kept when moving infinity
  to a real point.
-/

public section

open Function Set UpperHalfPlane

namespace TauCeti

/-- **Moving infinity to a real point, holomorphy.** Precomposing a function `g` holomorphic in
the upper half-plane with the Möbius map `z ↦ c - z⁻¹`, whatever its value at `0`, gives a function
holomorphic in the upper half-plane. -/
theorem differentiableOn_update_comp_const_sub_inv {g : ℂ → ℂ}
    (hgd : DifferentiableOn ℂ g upperHalfPlaneSet) (c : ℝ) (L : ℂ) :
    DifferentiableOn ℂ (update (fun z : ℂ => g ((c : ℂ) - z⁻¹)) 0 L) upperHalfPlaneSet := by
  have hH0 : ∀ z ∈ upperHalfPlaneSet, z ≠ 0 := fun z (hz : 0 < z.im) h => by simp [h] at hz
  exact (hgd.comp ((differentiableOn_const _).sub (differentiableOn_id.inv hH0))
    (bijOn_const_sub_inv_upperHalfPlaneSet c).mapsTo).congr fun z hz => update_of_ne (hH0 z hz) _ _

end TauCeti
