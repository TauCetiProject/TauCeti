/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Basic facts about manifold derivatives

This file collects general facts about `mfderiv` that need nothing beyond Mathlib's basic
manifold-derivative API.

## Main results

* `TauCeti.mfderiv_comp_of_apply_eq_self`: the chain rule at a fixed point `f x = x`, with both
  derivatives taken at `x`, so the composite is an endomorphism of the single tangent space
  `T_x M`.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] {x : M}

/-- The chain rule at a fixed point: if `f x = x`, the derivative of `g ∘ f` at `x` is the
composite of the derivatives of `g` and `f` at `x`, the tangent space at `f x` being that at `x`. -/
theorem mfderiv_comp_of_apply_eq_self {f g : M → M} (hg : MDifferentiableAt I I g x)
    (hf : MDifferentiableAt I I f x) (hfx : f x = x) :
    mfderiv I I (g ∘ f) x = (mfderiv I I g x).comp (mfderiv I I f x) := by
  have h := mfderiv_comp_of_eq hg hf hfx
  -- `mfderiv_comp_of_eq` takes the derivative of `g` at `f x`; replace that point by `x`.
  generalize hz : f x = z at h
  obtain rfl : z = x := hz.symm.trans hfx
  exact h

end TauCeti
