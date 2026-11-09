/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Basic facts about manifold derivatives

This file collects general facts about `mfderiv` that need nothing beyond Mathlib's basic
manifold-derivative API.

## Main results

* `TauCeti.mfderiv_comp_of_apply_eq_self`: the chain rule at a fixed point `f x = x`, with both
  derivatives taken at `x`, so the composite is an endomorphism of the single tangent space
  `T_x M`.
* `HasMFDerivAt.iterate`: the chain rule for iterates at a fixed point, `d(f^[n])_x = (df_x) ^ n`.
* `TauCeti.mfderiv_injective_of_leftInverse`: a map with a left inverse differentiable along its
  image has injective derivative.
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

/-- **The chain rule for iterates at a fixed point.** If `f x = x` and `f` has differential `f'`
at `x`, an endomorphism of `T_x M`, then `f^[n]` has differential `f' ^ n` at `x`. This is the
manifold version of `HasFDerivAt.iterate`. -/
theorem _root_.HasMFDerivAt.iterate {f : M → M} {f' : TangentSpace I x →L[𝕜] TangentSpace I x}
    (hf : HasMFDerivAt I I f x f') (hx : f x = x) (n : ℕ) :
    HasMFDerivAt I I f^[n] x (f' ^ n) := by
  induction n with
  | zero => exact hasMFDerivAt_id x
  | succ n ihn =>
    rw [Function.iterate_succ, pow_succ]
    -- Move the derivative of `f^[n]` to the point `f x`, where the chain rule evaluates it.
    have ihn' : HasMFDerivAt I I f^[n] (f x) (f' ^ n) := by rw [hx]; exact ihn
    exact ihn'.comp x hf

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N] in
/-- A map `f` with a left inverse `g` has injective derivative at every point `x` where `f` is
differentiable and `g` is differentiable at `f x`: by the chain rule, `dg_(f x)` is a left inverse
of `df_x`. -/
theorem mfderiv_injective_of_leftInverse {f : M → N} {g : N → M}
    (hg : MDifferentiableAt J I g (f x)) (hf : MDifferentiableAt I J f x)
    (hgf : Function.LeftInverse g f) : Function.Injective (mfderiv I J f x) := by
  have h := mfderiv_comp x hg hf
  rw [hgf.comp_eq_id, mfderiv_id] at h
  exact Function.LeftInverse.injective (g := mfderiv J I g (f x)) fun v ↦
    (DFunLike.congr_fun h v).symm

end TauCeti
