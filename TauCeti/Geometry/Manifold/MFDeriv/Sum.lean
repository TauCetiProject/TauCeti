/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Differentials of maps through a disjoint union

The differentials of the inclusions `Sum.inl : M → M ⊕ M'` and `Sum.inr : M' → M ⊕ M'` are the
identity of the model space (`mfderiv_sumInl`, `mfderiv_sumInr`). Hence following a differentiable
map by an inclusion, or precomposing a differentiable map on the disjoint union with an inclusion,
does not change its differential applied to a tangent vector.

## Main results

* `TauCeti.mfderiv_sumInl_comp_apply`, `TauCeti.mfderiv_sumInr_comp_apply`: following a map by an
  inclusion into a disjoint union.
* `TauCeti.mfderiv_comp_sumInl_apply`, `TauCeti.mfderiv_comp_sumInr_apply`: restricting a map on a
  disjoint union to one of its summands.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M M' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H M']
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Following a differentiable map by the inclusion `Sum.inl` does not change its differential. -/
theorem mfderiv_sumInl_comp_apply {f : N → M} {x : N} (hf : MDifferentiableAt J I f x)
    (v : TangentSpace J x) :
    mfderiv J I ((Sum.inl : M → M ⊕ M') ∘ f) x v = mfderiv J I f x v := by
  rw [mfderiv_comp x (ContMDiff.inl.mdifferentiableAt one_ne_zero) hf,
    ContinuousLinearMap.comp_apply, mfderiv_sumInl (p := Sum.inl (f x))]
  -- The identity of `E` is typed on the tangent space at `Sum.inl (f x)` rather than at `f x`.
  rfl

/-- Following a differentiable map by the inclusion `Sum.inr` does not change its differential. -/
theorem mfderiv_sumInr_comp_apply {f : N → M'} {x : N} (hf : MDifferentiableAt J I f x)
    (v : TangentSpace J x) :
    mfderiv J I ((Sum.inr : M' → M ⊕ M') ∘ f) x v = mfderiv J I f x v := by
  rw [mfderiv_comp x (ContMDiff.inr.mdifferentiableAt one_ne_zero) hf,
    ContinuousLinearMap.comp_apply, mfderiv_sumInr (M := M) (q' := f x)]
  -- The identity of `E` is typed on the tangent space at `Sum.inr (f x)` rather than at `f x`.
  rfl

/-- Restricting a differentiable map on `M ⊕ M'` to `M` does not change its differential. -/
theorem mfderiv_comp_sumInl_apply {g : M ⊕ M' → N} {x : M}
    (hg : MDifferentiableAt I J g (Sum.inl x)) (v : TangentSpace I x) :
    mfderiv I J (g ∘ Sum.inl) x v = mfderiv I J g (Sum.inl x) v := by
  rw [mfderiv_comp x hg (ContMDiff.inl.mdifferentiableAt one_ne_zero),
    ContinuousLinearMap.comp_apply, mfderiv_sumInl (p := Sum.inl x)]
  -- The identity of `E` is typed on the tangent space at `Sum.inl x` rather than at `x`.
  rfl

/-- Restricting a differentiable map on `M ⊕ M'` to `M'` does not change its differential. -/
theorem mfderiv_comp_sumInr_apply {g : M ⊕ M' → N} {x : M'}
    (hg : MDifferentiableAt I J g (Sum.inr x)) (v : TangentSpace I x) :
    mfderiv I J (g ∘ Sum.inr) x v = mfderiv I J g (Sum.inr x) v := by
  rw [mfderiv_comp x hg (ContMDiff.inr.mdifferentiableAt one_ne_zero),
    ContinuousLinearMap.comp_apply, mfderiv_sumInr (M := M) (q' := x)]
  -- The identity of `E` is typed on the tangent space at `Sum.inr x` rather than at `x`.
  rfl

end TauCeti
