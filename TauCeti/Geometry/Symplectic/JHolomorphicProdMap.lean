/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphicProd

/-!
# Product maps of constant-structure `J`-holomorphic maps

This file adds the source-and-target product calculus for the pointwise constant-structure
`J`-holomorphic
predicate used in the analytic Heegaard Floer roadmap. The existing product file handles maps
with a common source and product target. Here the source is also a product: if
`f : V → V'` and `g : W → W'` are constant-structure `J`-holomorphic, then
`Prod.map f g : V × W → V' × W'` is constant-structure `J`-holomorphic for the direct-sum almost
complex
structures, both on arbitrary product-source subsets and on rectangular product sets.

The same API records the affine coordinate inclusions `v ↦ (v, w₀)` and `w ↦ (v₀, w)`,
and restriction of a product-source constant-structure `J`-holomorphic map along either inclusion.
These are the
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

/-- The affine inclusion of the first coordinate into a product is constant-structure
`J`-holomorphic. -/
lemma isConstStructureJHolomorphicAt_prodMk_left (w₀ : W) (v : V) :
    IsConstStructureJHolomorphicAt J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) v :=
  (isConstStructureJHolomorphicAt_id J₁ v).prodMk (isConstStructureJHolomorphicAt_const J₁ J₂ w₀ v)

/-- The affine inclusion of the second coordinate into a product is constant-structure
`J`-holomorphic. -/
lemma isConstStructureJHolomorphicAt_prodMk_right (v₀ : V) (w : W) :
    IsConstStructureJHolomorphicAt J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) w :=
  (isConstStructureJHolomorphicAt_const J₂ J₁ v₀ w).prodMk (isConstStructureJHolomorphicAt_id J₂ w)

/-- The affine inclusion of the first coordinate into a product is constant-structure
`J`-holomorphic within
every set. -/
lemma isConstStructureJHolomorphicWithinAt_prodMk_left (w₀ : W) (s : Set V) (v : V) :
    IsConstStructureJHolomorphicWithinAt J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) s v :=
  (isConstStructureJHolomorphicAt_prodMk_left J₁ J₂ w₀ v).isConstStructureJHolomorphicWithinAt

/-- The affine inclusion of the second coordinate into a product is constant-structure
`J`-holomorphic within
every set. -/
lemma isConstStructureJHolomorphicWithinAt_prodMk_right (v₀ : V) (s : Set W) (w : W) :
    IsConstStructureJHolomorphicWithinAt J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) s w :=
  (isConstStructureJHolomorphicAt_prodMk_right J₁ J₂ v₀ w).isConstStructureJHolomorphicWithinAt

/-- The affine inclusion of the first coordinate into a product is constant-structure
`J`-holomorphic on every
set. -/
lemma isConstStructureJHolomorphicOn_prodMk_left (w₀ : W) (s : Set V) :
    IsConstStructureJHolomorphicOn J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) s :=
  isConstStructureJHolomorphicOn_of_forall fun v _ =>
    isConstStructureJHolomorphicWithinAt_prodMk_left J₁ J₂ w₀ s v

/-- The affine inclusion of the second coordinate into a product is constant-structure
`J`-holomorphic on every
set. -/
lemma isConstStructureJHolomorphicOn_prodMk_right (v₀ : V) (s : Set W) :
    IsConstStructureJHolomorphicOn J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) s :=
  isConstStructureJHolomorphicOn_of_forall fun w _ =>
    isConstStructureJHolomorphicWithinAt_prodMk_right J₁ J₂ v₀ s w

/-- The affine inclusion of the first coordinate into a product is globally
constant-structure `J`-holomorphic. -/
lemma isConstStructureJHolomorphic_prodMk_left (w₀ : W) :
    IsConstStructureJHolomorphic J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) :=
  isConstStructureJHolomorphic_of_forall fun v =>
    isConstStructureJHolomorphicAt_prodMk_left J₁ J₂ w₀ v

/-- The affine inclusion of the second coordinate into a product is globally
constant-structure `J`-holomorphic. -/
lemma isConstStructureJHolomorphic_prodMk_right (v₀ : V) :
    IsConstStructureJHolomorphic J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) :=
  isConstStructureJHolomorphic_of_forall fun w =>
    isConstStructureJHolomorphicAt_prodMk_right J₁ J₂ v₀ w

end CoordinateInclusions

section CoordinateRestrictions

variable {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}
variable {K : AlmostComplexStructure X}

/-- Restricting a product-source constant-structure `J`-holomorphic map to a fixed second coordinate
preserves
constant-structure `J`-holomorphicity. -/
lemma IsConstStructureJHolomorphicAt.comp_prodMk_left {f : V × W → X} {v : V} {w : W}
    (hf : IsConstStructureJHolomorphicAt (J₁.prod J₂) K f (v, w)) :
    IsConstStructureJHolomorphicAt J₁ K (fun v' : V => f (v', w)) v := by
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicAt.comp (J := J₁) (J' := J₁.prod J₂) (J'' := K)
      (f := fun v' : V => (v', w)) (g := f) (x := v) hf
      (isConstStructureJHolomorphicAt_prodMk_left J₁ J₂ w v)

/-- Restricting a product-source constant-structure `J`-holomorphic map to a fixed first coordinate
preserves
constant-structure `J`-holomorphicity. -/
lemma IsConstStructureJHolomorphicAt.comp_prodMk_right {f : V × W → X} {v : V} {w : W}
    (hf : IsConstStructureJHolomorphicAt (J₁.prod J₂) K f (v, w)) :
    IsConstStructureJHolomorphicAt J₂ K (fun w' : W => f (v, w')) w := by
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicAt.comp (J := J₂) (J' := J₁.prod J₂) (J'' := K)
      (f := fun w' : W => (v, w')) (g := f) (x := w) hf
      (isConstStructureJHolomorphicAt_prodMk_right J₁ J₂ v w)

/-- Restricting a product-source map along a fixed second-coordinate inclusion preserves
within-set constant-structure `J`-holomorphicity. -/
lemma IsConstStructureJHolomorphicWithinAt.comp_prodMk_left {f : V × W → X}
    {u : Set (V × W)} {s : Set V} {v : V} {w : W}
    (hf : IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) K f u (v, w))
    (hsu : Set.MapsTo (fun v' : V => (v', w)) s u) :
    IsConstStructureJHolomorphicWithinAt J₁ K (fun v' : V => f (v', w)) s v := by
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicWithinAt.comp (J := J₁) (J' := J₁.prod J₂) (J'' := K)
      (f := fun v' : V => (v', w)) (g := f) (s := s) (t := u) (x := v) hf
      (isConstStructureJHolomorphicWithinAt_prodMk_left J₁ J₂ w s v) hsu

/-- Restricting a product-source map along a fixed first-coordinate inclusion preserves
within-set constant-structure `J`-holomorphicity. -/
lemma IsConstStructureJHolomorphicWithinAt.comp_prodMk_right {f : V × W → X}
    {u : Set (V × W)} {t : Set W} {v : V} {w : W}
    (hf : IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) K f u (v, w))
    (htu : Set.MapsTo (fun w' : W => (v, w')) t u) :
    IsConstStructureJHolomorphicWithinAt J₂ K (fun w' : W => f (v, w')) t w := by
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicWithinAt.comp (J := J₂) (J' := J₁.prod J₂) (J'' := K)
      (f := fun w' : W => (v, w')) (g := f) (s := t) (t := u) (x := w) hf
      (isConstStructureJHolomorphicWithinAt_prodMk_right J₁ J₂ v t w) htu

end CoordinateRestrictions

section ProductMaps

variable {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}
variable {K₁ : AlmostComplexStructure V'} {K₂ : AlmostComplexStructure W'}

/-- The product map of two pointwise constant-structure `J`-holomorphic maps is constant-structure
`J`-holomorphic for the
direct-sum almost complex structures. -/
lemma IsConstStructureJHolomorphicAt.prodMap {f : V → V'} {g : W → W'} {p : V × W}
    (hf : IsConstStructureJHolomorphicAt J₁ K₁ f p.1)
    (hg : IsConstStructureJHolomorphicAt J₂ K₂ g p.2) :
    IsConstStructureJHolomorphicAt (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) p := by
  simpa [Prod.map] using
    ((hf.comp (isConstStructureJHolomorphicAt_fst J₁ J₂ p)).prodMk
      (hg.comp (isConstStructureJHolomorphicAt_snd J₁ J₂ p)))

/-- The product map of two maps constant-structure `J`-holomorphic within the coordinate images of a
product-source
set is constant-structure `J`-holomorphic within that set. -/
lemma IsConstStructureJHolomorphicWithinAt.prodMap {f : V → V'} {g : W → W'} {u : Set (V × W)}
    {p : V × W} (hf : IsConstStructureJHolomorphicWithinAt J₁ K₁ f (Prod.fst '' u) p.1)
    (hg : IsConstStructureJHolomorphicWithinAt J₂ K₂ g (Prod.snd '' u) p.2) :
    IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) u p := by
  simpa [Prod.map] using
    ((hf.comp (isConstStructureJHolomorphicWithinAt_fst J₁ J₂ u p)
      (fun q hq => ⟨q, hq, rfl⟩)).prodMk
      (hg.comp (isConstStructureJHolomorphicWithinAt_snd J₁ J₂ u p) (fun q hq => ⟨q, hq, rfl⟩)))

/-- The product map of two maps constant-structure `J`-holomorphic within sets is constant-structure
`J`-holomorphic within the
product set. -/
lemma IsConstStructureJHolomorphicWithinAt.prodMap_prod
    {f : V → V'} {g : W → W'} {s : Set V} {t : Set W}
    {p : V × W} (hf : IsConstStructureJHolomorphicWithinAt J₁ K₁ f s p.1)
    (hg : IsConstStructureJHolomorphicWithinAt J₂ K₂ g t p.2) :
    IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) (s ×ˢ t) p := by
  simpa [Prod.map] using
    ((hf.comp (isConstStructureJHolomorphicWithinAt_fst J₁ J₂ (s ×ˢ t) p) (fun q hq => hq.1)).prodMk
      (hg.comp (isConstStructureJHolomorphicWithinAt_snd J₁ J₂ (s ×ˢ t) p) (fun q hq => hq.2)))

/-- The product map of two maps constant-structure `J`-holomorphic on sets is constant-structure
`J`-holomorphic on the product set. -/
lemma IsConstStructureJHolomorphicOn.prodMap {f : V → V'} {g : W → W'} {s : Set V} {t : Set W}
    (hf : IsConstStructureJHolomorphicOn J₁ K₁ f s)
    (hg : IsConstStructureJHolomorphicOn J₂ K₂ g t) :
    IsConstStructureJHolomorphicOn (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) (s ×ˢ t) := by
  exact isConstStructureJHolomorphicOn_of_forall fun p hp => by
    simpa [Prod.map] using
      (hf.isConstStructureJHolomorphicWithinAt hp.1).prodMap_prod
        (hg.isConstStructureJHolomorphicWithinAt hp.2)

/-- The product map of two globally constant-structure `J`-holomorphic maps is globally
constant-structure `J`-holomorphic. -/
lemma IsConstStructureJHolomorphic.prodMap {f : V → V'} {g : W → W'}
    (hf : IsConstStructureJHolomorphic J₁ K₁ f) (hg : IsConstStructureJHolomorphic J₂ K₂ g) :
    IsConstStructureJHolomorphic (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) :=
  isConstStructureJHolomorphic_of_forall fun p =>
    (hf.isConstStructureJHolomorphicAt p.1).prodMap
      (hg.isConstStructureJHolomorphicAt p.2)

end ProductMaps

end TauCeti
