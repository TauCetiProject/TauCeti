/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function

/-!
# Composition of convex functions

An injective affine pullback preserves strict convexity, and composing a monotone convex outer
function on `E` with a convex inner map taking `D` into `E` yields a convex function on `D`
without requiring `g '' D` to be convex.

The affine pullback lemma is extracted from the tangent argument adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Convex/ContactMeasure.lean#L993).
-/

public section

open Set

/-- An injective affine change of variables preserves strict convexity on the preimage. -/
theorem StrictConvexOn.comp_affineMap_of_injective
    {𝕜 E F β : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
    {S : Set E} {v : E → β} (hv : StrictConvexOn 𝕜 S v) (A : F →ᵃ[𝕜] E)
    (hA : Function.Injective A) : StrictConvexOn 𝕜 (A ⁻¹' S) (v ∘ A) := by
  refine ⟨hv.1.affine_preimage A, fun a ha b hb hab p q hp hq hpq => ?_⟩
  simp only [Function.comp_apply, Convex.combo_affine_apply hpq]
  exact hv.2 ha hb (fun h => hab (hA h)) hp hq hpq

/-- Composing a convex function `h` that is monotone on `E` with a convex map `g` taking `D` into
`E` yields a convex function on `D`, without requiring `g '' D` to be convex. -/
theorem ConvexOn.comp_of_mapsTo
    {𝕜 X Y β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid X] [SMul 𝕜 X]
    [AddCommMonoid Y] [PartialOrder Y] [SMul 𝕜 Y]
    [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
    {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β}
    (hh : ConvexOn 𝕜 E h) (hg : ConvexOn 𝕜 D g) (hDE : MapsTo g D E) (hm : MonotoneOn h E) :
    ConvexOn 𝕜 D (h ∘ g) :=
  ⟨hg.1, fun _ hx _ hy _ _ ha hb hab =>
    (hm (hDE (hg.1 hx hy ha hb hab)) (hh.1 (hDE hx) (hDE hy) ha hb hab)
      (hg.2 hx hy ha hb hab)).trans (hh.2 (hDE hx) (hDE hy) ha hb hab)⟩
