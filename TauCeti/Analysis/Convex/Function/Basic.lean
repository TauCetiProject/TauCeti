/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function

/-!
# Convexity of affine maps and affine changes of variables

An affine map between modules is both convex and concave on any convex set (`AffineMap.convexOn`,
`AffineMap.concaveOn`), complementing `LinearMap.convexOn` and `LinearMap.concaveOn`. Moreover, an
injective affine pullback preserves strict convexity (`StrictConvexOn.comp_affineMap_of_injective`);
this is used to restrict a strictly convex function to a line before applying the strict tangent
inequality.

The strict pullback lemma is extracted from the tangent argument adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Convex/ContactMeasure.lean#L993).
-/

public section

open Set

/-- An affine map is convex on any convex set. -/
theorem AffineMap.convexOn {𝕜 E β : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E]
    [AddCommGroup β] [PartialOrder β] [Module 𝕜 E] [Module 𝕜 β] (f : E →ᵃ[𝕜] β) {s : Set E}
    (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_affine_apply hab).le⟩

/-- An affine map is concave on any convex set. -/
theorem AffineMap.concaveOn {𝕜 E β : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E]
    [AddCommGroup β] [PartialOrder β] [Module 𝕜 E] [Module 𝕜 β] (f : E →ᵃ[𝕜] β) {s : Set E}
    (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_affine_apply hab).ge⟩

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
