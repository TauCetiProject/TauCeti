/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Basic
public import TauCeti.Analysis.Calculus.UniformLimitsDeriv

/-!
# Spatial derivative graphs on a parabolic slab

At a fixed time `t`, the spatial Fréchet derivative identity between a bounded continuous value
field and a bounded continuous gradient field on the closed slab `E × [a, b]` is closed under
uniform convergence. This is the closed graph from which complete spaces of spatially
differentiable maps on the slab are built.

The proof restricts both fields to the spatial slice at time `t` and applies
`TauCeti.isClosed_setOf_hasFDerivAt`.

## Main declarations

* `TauCeti.ParabolicSpaceTime.isClosed_setOf_hasFDerivAt_spatialSlice`: the fixed-time spatial
  derivative graph is closed.
-/

public section

namespace TauCeti

open Set
open scoped BoundedContinuousFunction

namespace ParabolicSpaceTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}

/-- At a fixed time `t`, the spatial derivative identity between a bounded continuous value
field and a bounded continuous gradient field on the slab is a closed condition. -/
theorem isClosed_setOf_hasFDerivAt_spatialSlice {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (t : Icc a b) :
    IsClosed {p : (slab (E := E) a b →ᵇ G) × (slab (E := E) a b →ᵇ (E →L[ℝ] G)) |
      ∀ x, HasFDerivAt (fun y ↦ p.1 (slabMk y t)) (p.2 (slabMk x t)) x} := by
  simpa only [preimage_ofPred_eq, Prod.map_fst, Prod.map_snd,
    BoundedContinuousFunction.coe_compContinuous, BoundedContinuousFunction.compContinuous_apply,
    Function.comp_def, spatialSlice_apply] using
    (isClosed_setOf_hasFDerivAt (𝕜 := ℝ) (E := E) (Y := G)).preimage
      ((BoundedContinuousFunction.continuous_compContinuous (spatialSlice t)).prodMap
        (BoundedContinuousFunction.continuous_compContinuous (spatialSlice t)))

end ParabolicSpaceTime

end TauCeti
