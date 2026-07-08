/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Geometry.Symplectic.JHolomorphic
public import TauCeti.Geometry.Symplectic.Prod

/-!
# Product operations for `J`-holomorphic maps

This file adds the product calculus for the map-level `J`-holomorphic predicate used by the
analytic Heegaard Floer roadmap. The target product carries the direct-sum almost complex
structure from `TauCeti.Geometry.Symplectic.Prod`, and a map into that product is
`J`-holomorphic exactly when its two coordinate maps are.

The API is deliberately local and linear: it packages Mathlib's Frechet-derivative product
rules with the existing linear direct-sum almost-complex API. Later strip, disk, product, and
symmetric-product targets can use these lemmas without unfolding the Cauchy--Riemann equation.

## Main declarations

* `TauCeti.IsConstJHolomorphicAt.prodMk`, `IsConstJHolomorphicWithinAt.prodMk`,
  `IsConstJHolomorphicOn.prodMk`, and `IsConstJHolomorphic.prodMk`: product maps of
  `J`-holomorphic maps.
* `TauCeti.isConstJHolomorphicAt_fst` and `isConstJHolomorphicAt_snd`, with within-set, setwise, and
  global variants: the coordinate projections are `J`-holomorphic.
* `TauCeti.isConstJHolomorphicAt_prod_iff`, `isConstJHolomorphicWithinAt_prod_iff`,
  `isConstJHolomorphicOn_prod_iff`, and `isConstJHolomorphic_prod_iff`: coordinatewise
  characterizations of `J`-holomorphic maps into a product.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: product almost complex structures act componentwise.
-/

public section

namespace TauCeti

variable {V W X : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

section Projections

variable (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W)

/-- The first coordinate projection is `J`-holomorphic at every point. -/
@[simp]
lemma isConstJHolomorphicAt_fst (p : V × W) :
    IsConstJHolomorphicAt (J₁.prod J₂) J₁ Prod.fst p :=
  (isConstJHolomorphicAt_continuousLinearMap_iff (ContinuousLinearMap.fst ℝ V W) p).mpr
    (AlmostComplexStructure.isComplexLinearMap_fst J₁ J₂)

/-- The second coordinate projection is `J`-holomorphic at every point. -/
@[simp]
lemma isConstJHolomorphicAt_snd (p : V × W) :
    IsConstJHolomorphicAt (J₁.prod J₂) J₂ Prod.snd p :=
  (isConstJHolomorphicAt_continuousLinearMap_iff (ContinuousLinearMap.snd ℝ V W) p).mpr
    (AlmostComplexStructure.isComplexLinearMap_snd J₁ J₂)

/-- The first coordinate projection is `J`-holomorphic within every set. -/
@[simp]
lemma isConstJHolomorphicWithinAt_fst (s : Set (V × W)) (p : V × W) :
    IsConstJHolomorphicWithinAt (J₁.prod J₂) J₁ Prod.fst s p :=
  (isConstJHolomorphicAt_fst J₁ J₂ p).isConstJHolomorphicWithinAt

/-- The second coordinate projection is `J`-holomorphic within every set. -/
@[simp]
lemma isConstJHolomorphicWithinAt_snd (s : Set (V × W)) (p : V × W) :
    IsConstJHolomorphicWithinAt (J₁.prod J₂) J₂ Prod.snd s p :=
  (isConstJHolomorphicAt_snd J₁ J₂ p).isConstJHolomorphicWithinAt

/-- The first coordinate projection is `J`-holomorphic on every set. -/
@[simp]
lemma isConstJHolomorphicOn_fst (s : Set (V × W)) :
    IsConstJHolomorphicOn (J₁.prod J₂) J₁ Prod.fst s :=
  fun p _ => isConstJHolomorphicWithinAt_fst J₁ J₂ s p

/-- The second coordinate projection is `J`-holomorphic on every set. -/
@[simp]
lemma isConstJHolomorphicOn_snd (s : Set (V × W)) :
    IsConstJHolomorphicOn (J₁.prod J₂) J₂ Prod.snd s :=
  fun p _ => isConstJHolomorphicWithinAt_snd J₁ J₂ s p

/-- The first coordinate projection is globally `J`-holomorphic. -/
@[simp]
lemma isConstJHolomorphic_fst :
    IsConstJHolomorphic (J₁.prod J₂) J₁ Prod.fst :=
  fun p => isConstJHolomorphicAt_fst J₁ J₂ p

/-- The second coordinate projection is globally `J`-holomorphic. -/
@[simp]
lemma isConstJHolomorphic_snd :
    IsConstJHolomorphic (J₁.prod J₂) J₂ Prod.snd :=
  fun p => isConstJHolomorphicAt_snd J₁ J₂ p

end Projections

section ProductMaps

variable {J : AlmostComplexStructure V} {J₁ : AlmostComplexStructure W}
variable {J₂ : AlmostComplexStructure X}

/-- Pairing two pointwise `J`-holomorphic maps gives a `J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstJHolomorphicAt.prodMk {f : V → W} {g : V → X} {x : V}
    (hf : IsConstJHolomorphicAt J J₁ f x) (hg : IsConstJHolomorphicAt J J₂ g x) :
    IsConstJHolomorphicAt J (J₁.prod J₂) (fun y => (f y, g y)) x := by
  refine ⟨hf.choose.prod hg.choose, hf.hasFDerivAt.prodMk hg.hasFDerivAt, ?_⟩
  exact hf.derivative_isComplexLinear.prod hg.derivative_isComplexLinear

/-- Pairing two maps `J`-holomorphic within a set gives a `J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstJHolomorphicWithinAt.prodMk {f : V → W} {g : V → X} {s : Set V} {x : V}
    (hf : IsConstJHolomorphicWithinAt J J₁ f s x)
    (hg : IsConstJHolomorphicWithinAt J J₂ g s x) :
    IsConstJHolomorphicWithinAt J (J₁.prod J₂) (fun y => (f y, g y)) s x := by
  refine ⟨hf.choose.prod hg.choose, hf.hasFDerivWithinAt.prodMk hg.hasFDerivWithinAt, ?_⟩
  exact hf.derivative_isComplexLinear.prod hg.derivative_isComplexLinear

/-- Pairing two maps `J`-holomorphic on a set gives a `J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstJHolomorphicOn.prodMk {f : V → W} {g : V → X} {s : Set V}
    (hf : IsConstJHolomorphicOn J J₁ f s) (hg : IsConstJHolomorphicOn J J₂ g s) :
    IsConstJHolomorphicOn J (J₁.prod J₂) (fun y => (f y, g y)) s :=
  fun x hx => (hf x hx).prodMk (hg x hx)

/-- Pairing two globally `J`-holomorphic maps gives a `J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstJHolomorphic.prodMk {f : V → W} {g : V → X}
    (hf : IsConstJHolomorphic J J₁ f) (hg : IsConstJHolomorphic J J₂ g) :
    IsConstJHolomorphic J (J₁.prod J₂) (fun y => (f y, g y)) :=
  fun x => (hf x).prodMk (hg x)

/-- A map into a direct-sum target is pointwise `J`-holomorphic iff both coordinate maps are. -/
@[simp]
lemma isConstJHolomorphicAt_prod_iff (f : V → W × X) (x : V) :
    IsConstJHolomorphicAt J (J₁.prod J₂) f x ↔
      IsConstJHolomorphicAt J J₁ (fun y => (f y).1) x ∧
        IsConstJHolomorphicAt J J₂ (fun y => (f y).2) x := by
  constructor
  · intro hf
    exact ⟨(isConstJHolomorphicAt_fst J₁ J₂ (f x)).comp hf,
      (isConstJHolomorphicAt_snd J₁ J₂ (f x)).comp hf⟩
  · intro h
    simpa using h.1.prodMk h.2

/-- A map into a direct-sum target is `J`-holomorphic within a set iff both coordinate maps are. -/
@[simp]
lemma isConstJHolomorphicWithinAt_prod_iff (f : V → W × X) (s : Set V) (x : V) :
    IsConstJHolomorphicWithinAt J (J₁.prod J₂) f s x ↔
      IsConstJHolomorphicWithinAt J J₁ (fun y => (f y).1) s x ∧
        IsConstJHolomorphicWithinAt J J₂ (fun y => (f y).2) s x := by
  constructor
  · intro hf
    exact ⟨(isConstJHolomorphicWithinAt_fst J₁ J₂ Set.univ (f x)).comp hf (by simp),
      (isConstJHolomorphicWithinAt_snd J₁ J₂ Set.univ (f x)).comp hf (by simp)⟩
  · intro h
    simpa using h.1.prodMk h.2

/-- A map into a direct-sum target is `J`-holomorphic on a set iff both coordinate maps are. -/
@[simp]
lemma isConstJHolomorphicOn_prod_iff (f : V → W × X) (s : Set V) :
    IsConstJHolomorphicOn J (J₁.prod J₂) f s ↔
      IsConstJHolomorphicOn J J₁ (fun y => (f y).1) s ∧
        IsConstJHolomorphicOn J J₂ (fun y => (f y).2) s := by
  constructor
  · intro hf
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact ((isConstJHolomorphicWithinAt_prod_iff f s x).mp (hf x hx)).1
    · exact ((isConstJHolomorphicWithinAt_prod_iff f s x).mp (hf x hx)).2
  · intro h
    exact h.1.prodMk h.2

/-- A map into a direct-sum target is globally `J`-holomorphic iff both coordinate maps are. -/
@[simp]
lemma isConstJHolomorphic_prod_iff (f : V → W × X) :
    IsConstJHolomorphic J (J₁.prod J₂) f ↔
      IsConstJHolomorphic J J₁ (fun y => (f y).1) ∧
        IsConstJHolomorphic J J₂ (fun y => (f y).2) := by
  constructor
  · intro hf
    refine ⟨fun x => ?_, fun x => ?_⟩
    · exact ((isConstJHolomorphicAt_prod_iff f x).mp (hf x)).1
    · exact ((isConstJHolomorphicAt_prod_iff f x).mp (hf x)).2
  · intro h
    exact h.1.prodMk h.2

end ProductMaps

end TauCeti
