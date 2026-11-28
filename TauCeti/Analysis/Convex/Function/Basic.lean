/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Slope
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Tactic.Linarith

/-!
# Convex functions: affine maps, affine pullback, level sets and increments

An affine map between modules is both convex and concave on any convex set (`AffineMap.convexOn`,
`AffineMap.concaveOn`), complementing `LinearMap.convexOn` and `LinearMap.concaveOn`. Moreover, an
injective affine pullback preserves strict convexity (`StrictConvexOn.comp_affineMap_of_injective`);
this is used to restrict a strictly convex function to a line before applying the strict tangent
inequality.

A strictly convex function of one variable takes each value at most twice
(`StrictConvexOn.eq_or_eq_of_apply_eq`), since its slopes on adjacent intervals strictly increase.
The increments of a convex function of one variable over a fixed width `c ≥ 0` increase
(`ConvexOn.sub_le_sub_of_le`).

`StrictConvexOn.comp_affineMap_of_injective` is extracted from the tangent argument adapted
from the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Convex/ContactMeasure.lean#L993).
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

/-- For a convex function on `D ⊆ 𝕜`, increments over a fixed width `c ≥ 0` increase: if `s ≤ t`
with `s ∈ D` and `t + c ∈ D`, then `f (s + c) - f s ≤ f (t + c) - f t`. -/
theorem ConvexOn.sub_le_sub_of_le {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {D : Set 𝕜} {f : 𝕜 → 𝕜} (hf : ConvexOn 𝕜 D f) {s t c : 𝕜}
    (hs : s ∈ D) (htc : t + c ∈ D) (hc : 0 ≤ c) (hst : s ≤ t) :
    f (s + c) - f s ≤ f (t + c) - f t := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  have hsc : s + c ∈ D := hf.1.ordConnected.out hs htc ⟨by linarith, by linarith⟩
  have ht : t ∈ D := hf.1.ordConnected.out hs htc ⟨hst, by linarith⟩
  -- Both increments are compared with the common secant from `s` to `t + c`.
  have key : slope f s (s + c) ≤ slope f t (t + c) := calc
    slope f s (s + c) ≤ slope f s (t + c) := by
      rw [slope_def_field, slope_def_field]
      exact hf.secant_mono hs hsc htc (by linarith) (by linarith) (by linarith)
    _ = slope f (t + c) s := slope_comm f s (t + c)
    _ ≤ slope f (t + c) t := by
      rw [slope_def_field, slope_def_field]
      exact hf.secant_mono htc hs ht (by linarith) (by linarith) hst
    _ = slope f t (t + c) := slope_comm f (t + c) t
  simp only [slope_def_field, add_sub_cancel_left] at key
  exact (div_le_div_iff_of_pos_right hc).1 key
