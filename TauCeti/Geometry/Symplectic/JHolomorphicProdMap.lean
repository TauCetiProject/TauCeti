/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphicProd

/-!
# Product maps of `J`-holomorphic maps

This file adds the source-and-target product calculus for the pointwise `J`-holomorphic
predicate used in the analytic Heegaard Floer roadmap. The existing product file handles maps
with a common source and product target. Here the source is also a product: if
`f : V → V'` and `g : W → W'` are `J`-holomorphic, then
`Prod.map f g : V × W → V' × W'` is `J`-holomorphic for the direct-sum almost complex
structures, both on arbitrary product-source subsets and on rectangular product sets.

The same API records the affine coordinate inclusions `v ↦ (v, w₀)` and `w ↦ (v₀, w)`,
and restriction of a product-source `J`-holomorphic map along either inclusion. These are the
local product-chart facts needed before strip, disk, product, and symmetric-product
constructions can use the Cauchy--Riemann equation without unfolding it.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: product almost complex structures act componentwise and the Cauchy--Riemann
equation is preserved by products and coordinate inclusions.
-/

public section

namespace TauCeti

variable {V W V' W' X : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup V'] [NormedSpace ℝ V']
variable [NormedAddCommGroup W'] [NormedSpace ℝ W']
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

section CoordinateInclusions

variable (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W)

/-- The affine inclusion of the first coordinate into a product is `J`-holomorphic. -/
lemma isJHolomorphicAt_prodMk_left (w₀ : W) (v : V) :
    IsJHolomorphicAt J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) v :=
  (isJHolomorphicAt_id J₁ v).prodMk (isJHolomorphicAt_const J₁ J₂ w₀ v)

/-- The affine inclusion of the second coordinate into a product is `J`-holomorphic. -/
lemma isJHolomorphicAt_prodMk_right (v₀ : V) (w : W) :
    IsJHolomorphicAt J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) w :=
  (isJHolomorphicAt_const J₂ J₁ v₀ w).prodMk (isJHolomorphicAt_id J₂ w)

/-- The affine inclusion of the first coordinate into a product is `J`-holomorphic within
every set. -/
lemma isJHolomorphicWithinAt_prodMk_left (w₀ : W) (s : Set V) (v : V) :
    IsJHolomorphicWithinAt J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) s v :=
  (isJHolomorphicAt_prodMk_left J₁ J₂ w₀ v).isJHolomorphicWithinAt

/-- The affine inclusion of the second coordinate into a product is `J`-holomorphic within
every set. -/
lemma isJHolomorphicWithinAt_prodMk_right (v₀ : V) (s : Set W) (w : W) :
    IsJHolomorphicWithinAt J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) s w :=
  (isJHolomorphicAt_prodMk_right J₁ J₂ v₀ w).isJHolomorphicWithinAt

/-- The affine inclusion of the first coordinate into a product is `J`-holomorphic on every
set. -/
lemma isJHolomorphicOn_prodMk_left (w₀ : W) (s : Set V) :
    IsJHolomorphicOn J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) s :=
  fun v _ => isJHolomorphicWithinAt_prodMk_left J₁ J₂ w₀ s v

/-- The affine inclusion of the second coordinate into a product is `J`-holomorphic on every
set. -/
lemma isJHolomorphicOn_prodMk_right (v₀ : V) (s : Set W) :
    IsJHolomorphicOn J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) s :=
  fun w _ => isJHolomorphicWithinAt_prodMk_right J₁ J₂ v₀ s w

/-- The affine inclusion of the first coordinate into a product is globally
`J`-holomorphic. -/
lemma isJHolomorphic_prodMk_left (w₀ : W) :
    IsJHolomorphic J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) :=
  fun v => isJHolomorphicAt_prodMk_left J₁ J₂ w₀ v

/-- The affine inclusion of the second coordinate into a product is globally
`J`-holomorphic. -/
lemma isJHolomorphic_prodMk_right (v₀ : V) :
    IsJHolomorphic J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) :=
  fun w => isJHolomorphicAt_prodMk_right J₁ J₂ v₀ w

end CoordinateInclusions

section CoordinateRestrictions

variable {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}
variable {K : AlmostComplexStructure X}

/-- Restricting a product-source `J`-holomorphic map to a fixed second coordinate preserves
`J`-holomorphicity. -/
lemma IsJHolomorphicAt.comp_prodMk_left {f : V × W → X} {v : V} {w : W}
    (hf : IsJHolomorphicAt (J₁.prod J₂) K f (v, w)) :
    IsJHolomorphicAt J₁ K (fun v' : V => f (v', w)) v := by
  simpa [Function.comp_def] using
    IsJHolomorphicAt.comp (J := J₁) (J' := J₁.prod J₂) (J'' := K)
      (f := fun v' : V => (v', w)) (g := f) (x := v) hf
      (isJHolomorphicAt_prodMk_left J₁ J₂ w v)

/-- Restricting a product-source `J`-holomorphic map to a fixed first coordinate preserves
`J`-holomorphicity. -/
lemma IsJHolomorphicAt.comp_prodMk_right {f : V × W → X} {v : V} {w : W}
    (hf : IsJHolomorphicAt (J₁.prod J₂) K f (v, w)) :
    IsJHolomorphicAt J₂ K (fun w' : W => f (v, w')) w := by
  simpa [Function.comp_def] using
    IsJHolomorphicAt.comp (J := J₂) (J' := J₁.prod J₂) (J'' := K)
      (f := fun w' : W => (v, w')) (g := f) (x := w) hf
      (isJHolomorphicAt_prodMk_right J₁ J₂ v w)

/-- Restricting a product-source map along a fixed second-coordinate inclusion preserves
within-set `J`-holomorphicity. -/
lemma IsJHolomorphicWithinAt.comp_prodMk_left {f : V × W → X} {u : Set (V × W)}
    {s : Set V} {v : V} {w : W} (hf : IsJHolomorphicWithinAt (J₁.prod J₂) K f u (v, w))
    (hsu : Set.MapsTo (fun v' : V => (v', w)) s u) :
    IsJHolomorphicWithinAt J₁ K (fun v' : V => f (v', w)) s v := by
  simpa [Function.comp_def] using
    IsJHolomorphicWithinAt.comp (J := J₁) (J' := J₁.prod J₂) (J'' := K)
      (f := fun v' : V => (v', w)) (g := f) (s := s) (t := u) (x := v) hf
      (isJHolomorphicWithinAt_prodMk_left J₁ J₂ w s v) hsu

/-- Restricting a product-source map along a fixed first-coordinate inclusion preserves
within-set `J`-holomorphicity. -/
lemma IsJHolomorphicWithinAt.comp_prodMk_right {f : V × W → X} {u : Set (V × W)}
    {t : Set W} {v : V} {w : W} (hf : IsJHolomorphicWithinAt (J₁.prod J₂) K f u (v, w))
    (htu : Set.MapsTo (fun w' : W => (v, w')) t u) :
    IsJHolomorphicWithinAt J₂ K (fun w' : W => f (v, w')) t w := by
  simpa [Function.comp_def] using
    IsJHolomorphicWithinAt.comp (J := J₂) (J' := J₁.prod J₂) (J'' := K)
      (f := fun w' : W => (v, w')) (g := f) (s := t) (t := u) (x := w) hf
      (isJHolomorphicWithinAt_prodMk_right J₁ J₂ v t w) htu

end CoordinateRestrictions

section ProductMaps

variable {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}
variable {K₁ : AlmostComplexStructure V'} {K₂ : AlmostComplexStructure W'}

/-- The product map of two pointwise `J`-holomorphic maps is `J`-holomorphic for the
direct-sum almost complex structures. -/
lemma IsJHolomorphicAt.prodMap {f : V → V'} {g : W → W'} {p : V × W}
    (hf : IsJHolomorphicAt J₁ K₁ f p.1) (hg : IsJHolomorphicAt J₂ K₂ g p.2) :
    IsJHolomorphicAt (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) p := by
  simpa [Prod.map] using
    ((hf.comp (isJHolomorphicAt_fst J₁ J₂ p)).prodMk
      (hg.comp (isJHolomorphicAt_snd J₁ J₂ p)))

/-- The product map of two maps `J`-holomorphic within the coordinate images of a product-source
set is `J`-holomorphic within that set. -/
lemma IsJHolomorphicWithinAt.prodMap {f : V → V'} {g : W → W'} {u : Set (V × W)}
    {p : V × W} (hf : IsJHolomorphicWithinAt J₁ K₁ f (Prod.fst '' u) p.1)
    (hg : IsJHolomorphicWithinAt J₂ K₂ g (Prod.snd '' u) p.2) :
    IsJHolomorphicWithinAt (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) u p := by
  simpa [Prod.map] using
    ((hf.comp (isJHolomorphicWithinAt_fst J₁ J₂ u p) (fun q hq => ⟨q, hq, rfl⟩)).prodMk
      (hg.comp (isJHolomorphicWithinAt_snd J₁ J₂ u p) (fun q hq => ⟨q, hq, rfl⟩)))

/-- The product map of two maps `J`-holomorphic within sets is `J`-holomorphic within the
product set. -/
lemma IsJHolomorphicWithinAt.prodMap_prod {f : V → V'} {g : W → W'} {s : Set V} {t : Set W}
    {p : V × W} (hf : IsJHolomorphicWithinAt J₁ K₁ f s p.1)
    (hg : IsJHolomorphicWithinAt J₂ K₂ g t p.2) :
    IsJHolomorphicWithinAt (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) (s ×ˢ t) p := by
  simpa [Prod.map] using
    ((hf.comp (isJHolomorphicWithinAt_fst J₁ J₂ (s ×ˢ t) p) (fun q hq => hq.1)).prodMk
      (hg.comp (isJHolomorphicWithinAt_snd J₁ J₂ (s ×ˢ t) p) (fun q hq => hq.2)))

/-- The product map of two maps `J`-holomorphic on sets is `J`-holomorphic on the product set. -/
lemma IsJHolomorphicOn.prodMap {f : V → V'} {g : W → W'} {s : Set V} {t : Set W}
    (hf : IsJHolomorphicOn J₁ K₁ f s) (hg : IsJHolomorphicOn J₂ K₂ g t) :
    IsJHolomorphicOn (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) (s ×ˢ t) := by
  intro p hp
  simpa [Prod.map] using (hf p.1 hp.1).prodMap_prod (hg p.2 hp.2)

/-- The product map of two globally `J`-holomorphic maps is globally `J`-holomorphic. -/
lemma IsJHolomorphic.prodMap {f : V → V'} {g : W → W'}
    (hf : IsJHolomorphic J₁ K₁ f) (hg : IsJHolomorphic J₂ K₂ g) :
    IsJHolomorphic (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) :=
  fun p => (hf p.1).prodMap (hg p.2)

end ProductMaps

end TauCeti
