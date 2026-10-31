/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import TauCeti.Topology.Algebra.Star.Completion

/-!
# Isometric star operations on completions

The norm of the completion of a seminormed additive group extends the norm of the group by
continuity, and the star operation extends through `UniformSpace.Completion.map`. An isometric
star operation therefore stays isometric on the completion. Together with
`UniformSpace.Completion.instNonUnitalNormedRing` and `UniformSpace.Completion.instStarRing`, this
makes the completion of a nonunital seminormed ⋆-ring with isometric star, such as an `L¹`
convolution algebra on compactly supported functions, a nonunital Banach ⋆-algebra.

## Main results

* `UniformSpace.Completion.instNormedStarGroup`: an isometric star operation stays isometric on
  the completion.
-/

public section

open UniformSpace

/-- **An isometric star operation on a seminormed group stays isometric on its completion.** -/
instance UniformSpace.Completion.instNormedStarGroup {E : Type*} [SeminormedAddCommGroup E]
    [StarAddMonoid E] [NormedStarGroup E] : NormedStarGroup (Completion E) where
  norm_star_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a => rw [← Completion.coe_star, Completion.norm_coe, Completion.norm_coe, norm_star]
