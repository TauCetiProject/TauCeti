/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.FDeriv.Prod
import TauCeti.Geometry.Symplectic.JHolomorphic
import TauCeti.Geometry.Symplectic.Prod

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

* `TauCeti.IsJHolomorphicAt.prodMk`, `IsJHolomorphicWithinAt.prodMk`,
  `IsJHolomorphicOn.prodMk`, and `IsJHolomorphic.prodMk`: product maps of `J`-holomorphic maps.
* `TauCeti.isJHolomorphicAt_fst` and `isJHolomorphicAt_snd`, with within-set, setwise, and
  global variants: the coordinate projections are `J`-holomorphic.
* `TauCeti.isJHolomorphicAt_prod_iff`, `isJHolomorphicWithinAt_prod_iff`,
  `isJHolomorphicOn_prod_iff`, and `isJHolomorphic_prod_iff`: coordinatewise
  characterizations of `J`-holomorphic maps into a product.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: product almost complex structures act componentwise.
-/

namespace TauCeti

variable {V W X : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

section Projections

variable (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W)

/-- The first coordinate projection is `J`-holomorphic at every point. -/
@[simp]
lemma isJHolomorphicAt_fst (p : V × W) :
    IsJHolomorphicAt (J₁.prod J₂) J₁ Prod.fst p :=
  (isJHolomorphicAt_continuousLinearMap_iff (ContinuousLinearMap.fst ℝ V W) p).mpr
    (AlmostComplexStructure.isComplexLinearMap_fst J₁ J₂)

/-- The second coordinate projection is `J`-holomorphic at every point. -/
@[simp]
lemma isJHolomorphicAt_snd (p : V × W) :
    IsJHolomorphicAt (J₁.prod J₂) J₂ Prod.snd p :=
  (isJHolomorphicAt_continuousLinearMap_iff (ContinuousLinearMap.snd ℝ V W) p).mpr
    (AlmostComplexStructure.isComplexLinearMap_snd J₁ J₂)

/-- The first coordinate projection is `J`-holomorphic within every set. -/
@[simp]
lemma isJHolomorphicWithinAt_fst (s : Set (V × W)) (p : V × W) :
    IsJHolomorphicWithinAt (J₁.prod J₂) J₁ Prod.fst s p :=
  (isJHolomorphicAt_fst J₁ J₂ p).isJHolomorphicWithinAt

/-- The second coordinate projection is `J`-holomorphic within every set. -/
@[simp]
lemma isJHolomorphicWithinAt_snd (s : Set (V × W)) (p : V × W) :
    IsJHolomorphicWithinAt (J₁.prod J₂) J₂ Prod.snd s p :=
  (isJHolomorphicAt_snd J₁ J₂ p).isJHolomorphicWithinAt

/-- The first coordinate projection is `J`-holomorphic on every set. -/
@[simp]
lemma isJHolomorphicOn_fst (s : Set (V × W)) :
    IsJHolomorphicOn (J₁.prod J₂) J₁ Prod.fst s :=
  fun p _ => isJHolomorphicWithinAt_fst J₁ J₂ s p

/-- The second coordinate projection is `J`-holomorphic on every set. -/
@[simp]
lemma isJHolomorphicOn_snd (s : Set (V × W)) :
    IsJHolomorphicOn (J₁.prod J₂) J₂ Prod.snd s :=
  fun p _ => isJHolomorphicWithinAt_snd J₁ J₂ s p

/-- The first coordinate projection is globally `J`-holomorphic. -/
@[simp]
lemma isJHolomorphic_fst :
    IsJHolomorphic (J₁.prod J₂) J₁ Prod.fst :=
  fun p => isJHolomorphicAt_fst J₁ J₂ p

/-- The second coordinate projection is globally `J`-holomorphic. -/
@[simp]
lemma isJHolomorphic_snd :
    IsJHolomorphic (J₁.prod J₂) J₂ Prod.snd :=
  fun p => isJHolomorphicAt_snd J₁ J₂ p

end Projections

section ProductMaps

variable {J : AlmostComplexStructure V} {J₁ : AlmostComplexStructure W}
variable {J₂ : AlmostComplexStructure X}

/-- Pairing two pointwise `J`-holomorphic maps gives a `J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsJHolomorphicAt.prodMk {f : V → W} {g : V → X} {x : V}
    (hf : IsJHolomorphicAt J J₁ f x) (hg : IsJHolomorphicAt J J₂ g x) :
    IsJHolomorphicAt J (J₁.prod J₂) (fun y => (f y, g y)) x := by
  refine ⟨hf.choose.prod hg.choose, hf.hasFDerivAt.prodMk hg.hasFDerivAt, ?_⟩
  exact hf.derivative_isComplexLinear.prod hg.derivative_isComplexLinear

/-- Pairing two maps `J`-holomorphic within a set gives a `J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsJHolomorphicWithinAt.prodMk {f : V → W} {g : V → X} {s : Set V} {x : V}
    (hf : IsJHolomorphicWithinAt J J₁ f s x)
    (hg : IsJHolomorphicWithinAt J J₂ g s x) :
    IsJHolomorphicWithinAt J (J₁.prod J₂) (fun y => (f y, g y)) s x := by
  refine ⟨hf.choose.prod hg.choose, hf.hasFDerivWithinAt.prodMk hg.hasFDerivWithinAt, ?_⟩
  exact hf.derivative_isComplexLinear.prod hg.derivative_isComplexLinear

/-- Pairing two maps `J`-holomorphic on a set gives a `J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsJHolomorphicOn.prodMk {f : V → W} {g : V → X} {s : Set V}
    (hf : IsJHolomorphicOn J J₁ f s) (hg : IsJHolomorphicOn J J₂ g s) :
    IsJHolomorphicOn J (J₁.prod J₂) (fun y => (f y, g y)) s :=
  fun x hx => (hf x hx).prodMk (hg x hx)

/-- Pairing two globally `J`-holomorphic maps gives a `J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsJHolomorphic.prodMk {f : V → W} {g : V → X}
    (hf : IsJHolomorphic J J₁ f) (hg : IsJHolomorphic J J₂ g) :
    IsJHolomorphic J (J₁.prod J₂) (fun y => (f y, g y)) :=
  fun x => (hf x).prodMk (hg x)

/-- A map into a direct-sum target is pointwise `J`-holomorphic iff both coordinate maps are. -/
@[simp]
lemma isJHolomorphicAt_prod_iff (f : V → W × X) (x : V) :
    IsJHolomorphicAt J (J₁.prod J₂) f x ↔
      IsJHolomorphicAt J J₁ (fun y => (f y).1) x ∧
        IsJHolomorphicAt J J₂ (fun y => (f y).2) x := by
  constructor
  · intro hf
    exact ⟨(isJHolomorphicAt_fst J₁ J₂ (f x)).comp hf,
      (isJHolomorphicAt_snd J₁ J₂ (f x)).comp hf⟩
  · intro h
    simpa using h.1.prodMk h.2

/-- A map into a direct-sum target is `J`-holomorphic within a set iff both coordinate maps are. -/
@[simp]
lemma isJHolomorphicWithinAt_prod_iff (f : V → W × X) (s : Set V) (x : V) :
    IsJHolomorphicWithinAt J (J₁.prod J₂) f s x ↔
      IsJHolomorphicWithinAt J J₁ (fun y => (f y).1) s x ∧
        IsJHolomorphicWithinAt J J₂ (fun y => (f y).2) s x := by
  constructor
  · intro hf
    exact ⟨(isJHolomorphicWithinAt_fst J₁ J₂ Set.univ (f x)).comp hf (by simp),
      (isJHolomorphicWithinAt_snd J₁ J₂ Set.univ (f x)).comp hf (by simp)⟩
  · intro h
    simpa using h.1.prodMk h.2

/-- A map into a direct-sum target is `J`-holomorphic on a set iff both coordinate maps are. -/
@[simp]
lemma isJHolomorphicOn_prod_iff (f : V → W × X) (s : Set V) :
    IsJHolomorphicOn J (J₁.prod J₂) f s ↔
      IsJHolomorphicOn J J₁ (fun y => (f y).1) s ∧
        IsJHolomorphicOn J J₂ (fun y => (f y).2) s := by
  constructor
  · intro hf
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact ((isJHolomorphicWithinAt_prod_iff f s x).mp (hf x hx)).1
    · exact ((isJHolomorphicWithinAt_prod_iff f s x).mp (hf x hx)).2
  · intro h
    exact h.1.prodMk h.2

/-- A map into a direct-sum target is globally `J`-holomorphic iff both coordinate maps are. -/
@[simp]
lemma isJHolomorphic_prod_iff (f : V → W × X) :
    IsJHolomorphic J (J₁.prod J₂) f ↔
      IsJHolomorphic J J₁ (fun y => (f y).1) ∧
        IsJHolomorphic J J₂ (fun y => (f y).2) := by
  constructor
  · intro hf
    refine ⟨fun x => ?_, fun x => ?_⟩
    · exact ((isJHolomorphicAt_prod_iff f x).mp (hf x)).1
    · exact ((isJHolomorphicAt_prod_iff f x).mp (hf x)).2
  · intro h
    exact h.1.prodMk h.2

end ProductMaps

end TauCeti
