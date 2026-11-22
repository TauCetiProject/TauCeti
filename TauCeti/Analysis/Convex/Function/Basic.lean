/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Slope

/-!
# Strictly convex functions: affine pullback and level sets

An injective affine pullback preserves strict convexity. This algebraic fact is used to
restrict a strictly convex function to a line before applying the strict tangent inequality.

A strictly convex function of one variable takes each value at most twice
(`StrictConvexOn.eq_or_eq_of_apply_eq`), since its slopes on adjacent intervals strictly increase.

`StrictConvexOn.comp_affineMap_of_injective` is extracted from the tangent argument adapted
from the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Convex/ContactMeasure.lean#L993).
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

/-- A strictly convex function takes each value at most twice: if `f x = f y = c` with `x < y`,
then every `z` with `f z = c` is `x` or `y`. -/
theorem StrictConvexOn.eq_or_eq_of_apply_eq {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {S : Set 𝕜} {f : 𝕜 → 𝕜} {x y z c : 𝕜}
    (hf : StrictConvexOn 𝕜 S f) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxy : x < y)
    (hfx : f x = c) (hfy : f y = c) (hfz : f z = c) : z = x ∨ z = y := by
  -- Three points of `S` in increasing order cannot share the value `c`.
  have key : ∀ {a b d : 𝕜}, a ∈ S → d ∈ S → a < b → b < d → f a = c → f b = c → f d = c →
      False := fun ha hd hab hbd hfa hfb hfd => by
    have := hf.slope_strict_mono_adjacent ha hd hab hbd
    rw [hfa, hfb, hfd, sub_self, zero_div, zero_div] at this
    exact lt_irrefl _ this
  by_contra! h
  rcases lt_trichotomy z x with hzx | hzx | hxz
  · exact key hz hy hzx hxy hfz hfx hfy
  · exact h.1 hzx
  rcases lt_trichotomy z y with hzy | hzy | hyz
  · exact key hx hy hxz hzy hfx hfz hfy
  · exact h.2 hzy
  · exact key hx hz hxy hyz hfx hfy hfz
