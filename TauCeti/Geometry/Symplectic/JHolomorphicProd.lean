/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Geometry.Symplectic.JHolomorphic
public import TauCeti.Geometry.Symplectic.Prod

/-!
# Product operations for constant-structure `J`-holomorphic maps

This file adds the product calculus for the map-level constant-structure `J`-holomorphic predicate
used by the
analytic Heegaard Floer roadmap. The target product carries the direct-sum almost complex
structure from `TauCeti.Geometry.Symplectic.Prod`, and a map into that product is
constant-structure `J`-holomorphic exactly when its two coordinate maps are.

The API is deliberately local and linear: it packages Mathlib's Frechet-derivative product
rules with the existing linear direct-sum almost-complex API. Later strip, disk, product, and
symmetric-product targets can use these lemmas without unfolding the Cauchy--Riemann equation.

## Main declarations

* `TauCeti.IsConstStructureJHolomorphicAt.prodMk`, `IsConstStructureJHolomorphicWithinAt.prodMk`,
  `IsConstStructureJHolomorphicOn.prodMk`, and `IsConstStructureJHolomorphic.prodMk`: product maps
  of
  constant-structure `J`-holomorphic maps.
* `TauCeti.isConstStructureJHolomorphicAt_fst` and `isConstStructureJHolomorphicAt_snd`, with
within-set, setwise, and
  global variants: the coordinate projections are constant-structure `J`-holomorphic.
* `TauCeti.isConstStructureJHolomorphicAt_prod_iff`,
`isConstStructureJHolomorphicWithinAt_prod_iff`,
  `isConstStructureJHolomorphicOn_prod_iff`, and `isConstStructureJHolomorphic_prod_iff`:
  coordinatewise
  characterizations of constant-structure `J`-holomorphic maps into a product.

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

/-- The first coordinate projection is constant-structure `J`-holomorphic at every point. -/
@[simp]
lemma isConstStructureJHolomorphicAt_fst (p : V × W) :
    IsConstStructureJHolomorphicAt (J₁.prod J₂) J₁ Prod.fst p :=
  (isConstStructureJHolomorphicAt_continuousLinearMap_iff (ContinuousLinearMap.fst ℝ V W) p).mpr
    (AlmostComplexStructure.isComplexLinearMap_fst J₁ J₂)

/-- The second coordinate projection is constant-structure `J`-holomorphic at every point. -/
@[simp]
lemma isConstStructureJHolomorphicAt_snd (p : V × W) :
    IsConstStructureJHolomorphicAt (J₁.prod J₂) J₂ Prod.snd p :=
  (isConstStructureJHolomorphicAt_continuousLinearMap_iff (ContinuousLinearMap.snd ℝ V W) p).mpr
    (AlmostComplexStructure.isComplexLinearMap_snd J₁ J₂)

/-- The first coordinate projection is constant-structure `J`-holomorphic within every set. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_fst (s : Set (V × W)) (p : V × W) :
    IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) J₁ Prod.fst s p :=
  (isConstStructureJHolomorphicAt_fst J₁ J₂ p).isConstStructureJHolomorphicWithinAt

/-- The second coordinate projection is constant-structure `J`-holomorphic within every set. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_snd (s : Set (V × W)) (p : V × W) :
    IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) J₂ Prod.snd s p :=
  (isConstStructureJHolomorphicAt_snd J₁ J₂ p).isConstStructureJHolomorphicWithinAt

/-- The first coordinate projection is constant-structure `J`-holomorphic on every set. -/
@[simp]
lemma isConstStructureJHolomorphicOn_fst (s : Set (V × W)) :
    IsConstStructureJHolomorphicOn (J₁.prod J₂) J₁ Prod.fst s :=
  isConstStructureJHolomorphicOn_of_forall fun p _ =>
    isConstStructureJHolomorphicWithinAt_fst J₁ J₂ s p

/-- The second coordinate projection is constant-structure `J`-holomorphic on every set. -/
@[simp]
lemma isConstStructureJHolomorphicOn_snd (s : Set (V × W)) :
    IsConstStructureJHolomorphicOn (J₁.prod J₂) J₂ Prod.snd s :=
  isConstStructureJHolomorphicOn_of_forall fun p _ =>
    isConstStructureJHolomorphicWithinAt_snd J₁ J₂ s p

/-- The first coordinate projection is globally constant-structure `J`-holomorphic. -/
@[simp]
lemma isConstStructureJHolomorphic_fst :
    IsConstStructureJHolomorphic (J₁.prod J₂) J₁ Prod.fst :=
  isConstStructureJHolomorphic_of_forall fun p =>
    isConstStructureJHolomorphicAt_fst J₁ J₂ p

/-- The second coordinate projection is globally constant-structure `J`-holomorphic. -/
@[simp]
lemma isConstStructureJHolomorphic_snd :
    IsConstStructureJHolomorphic (J₁.prod J₂) J₂ Prod.snd :=
  isConstStructureJHolomorphic_of_forall fun p =>
    isConstStructureJHolomorphicAt_snd J₁ J₂ p

end Projections

section ProductMaps

variable {J : AlmostComplexStructure V} {J₁ : AlmostComplexStructure W}
variable {J₂ : AlmostComplexStructure X}

/-- Pairing two pointwise constant-structure `J`-holomorphic maps gives a constant-structure
`J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstStructureJHolomorphicAt.prodMk {f : V → W} {g : V → X} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J₁ f x) (hg : IsConstStructureJHolomorphicAt J J₂ g x) :
    IsConstStructureJHolomorphicAt J (J₁.prod J₂) (fun y => (f y, g y)) x := by
  refine isConstStructureJHolomorphicAt_of_hasFDerivAt
    (hf.hasFDerivAt.prodMk hg.hasFDerivAt) ?_
  exact hf.derivative_isComplexLinear.prod hg.derivative_isComplexLinear

/-- Pairing two maps constant-structure `J`-holomorphic within a set gives a constant-structure
`J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstStructureJHolomorphicWithinAt.prodMk {f : V → W} {g : V → X} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J₁ f s x)
    (hg : IsConstStructureJHolomorphicWithinAt J J₂ g s x) :
    IsConstStructureJHolomorphicWithinAt J (J₁.prod J₂) (fun y => (f y, g y)) s x := by
  refine isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt
    (hf.hasFDerivWithinAt.prodMk hg.hasFDerivWithinAt) ?_
  exact hf.derivative_isComplexLinear.prod hg.derivative_isComplexLinear

/-- Pairing two maps constant-structure `J`-holomorphic on a set gives a constant-structure
`J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstStructureJHolomorphicOn.prodMk {f : V → W} {g : V → X} {s : Set V}
    (hf : IsConstStructureJHolomorphicOn J J₁ f s) (hg : IsConstStructureJHolomorphicOn J J₂ g s) :
    IsConstStructureJHolomorphicOn J (J₁.prod J₂) (fun y => (f y, g y)) s :=
  isConstStructureJHolomorphicOn_of_forall fun _ hx =>
    (hf.isConstStructureJHolomorphicWithinAt hx).prodMk
      (hg.isConstStructureJHolomorphicWithinAt hx)

/-- Pairing two globally constant-structure `J`-holomorphic maps gives a constant-structure
`J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstStructureJHolomorphic.prodMk {f : V → W} {g : V → X}
    (hf : IsConstStructureJHolomorphic J J₁ f) (hg : IsConstStructureJHolomorphic J J₂ g) :
    IsConstStructureJHolomorphic J (J₁.prod J₂) (fun y => (f y, g y)) :=
  isConstStructureJHolomorphic_of_forall fun x =>
    (hf.isConstStructureJHolomorphicAt x).prodMk (hg.isConstStructureJHolomorphicAt x)

/-- A map into a direct-sum target is pointwise constant-structure `J`-holomorphic iff both
coordinate maps are. -/
@[simp]
lemma isConstStructureJHolomorphicAt_prod_iff (f : V → W × X) (x : V) :
    IsConstStructureJHolomorphicAt J (J₁.prod J₂) f x ↔
      IsConstStructureJHolomorphicAt J J₁ (fun y => (f y).1) x ∧
        IsConstStructureJHolomorphicAt J J₂ (fun y => (f y).2) x := by
  constructor
  · intro hf
    exact ⟨(isConstStructureJHolomorphicAt_fst J₁ J₂ (f x)).comp hf,
      (isConstStructureJHolomorphicAt_snd J₁ J₂ (f x)).comp hf⟩
  · intro h
    simpa using h.1.prodMk h.2

/-- A map into a direct-sum target is constant-structure `J`-holomorphic within a set iff both
coordinate maps are. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_prod_iff (f : V → W × X) (s : Set V) (x : V) :
    IsConstStructureJHolomorphicWithinAt J (J₁.prod J₂) f s x ↔
      IsConstStructureJHolomorphicWithinAt J J₁ (fun y => (f y).1) s x ∧
        IsConstStructureJHolomorphicWithinAt J J₂ (fun y => (f y).2) s x := by
  constructor
  · intro hf
    exact ⟨(isConstStructureJHolomorphicWithinAt_fst J₁ J₂ Set.univ (f x)).comp hf (by simp),
      (isConstStructureJHolomorphicWithinAt_snd J₁ J₂ Set.univ (f x)).comp hf (by simp)⟩
  · intro h
    simpa using h.1.prodMk h.2

/-- A map into a direct-sum target is constant-structure `J`-holomorphic on a set iff both
coordinate maps are. -/
@[simp]
lemma isConstStructureJHolomorphicOn_prod_iff (f : V → W × X) (s : Set V) :
    IsConstStructureJHolomorphicOn J (J₁.prod J₂) f s ↔
      IsConstStructureJHolomorphicOn J J₁ (fun y => (f y).1) s ∧
        IsConstStructureJHolomorphicOn J J₂ (fun y => (f y).2) s := by
  constructor
  · intro hf
    refine ⟨isConstStructureJHolomorphicOn_of_forall fun x hx => ?_,
      isConstStructureJHolomorphicOn_of_forall fun x hx => ?_⟩
    · exact ((isConstStructureJHolomorphicWithinAt_prod_iff f s x).mp
        (hf.isConstStructureJHolomorphicWithinAt hx)).1
    · exact ((isConstStructureJHolomorphicWithinAt_prod_iff f s x).mp
        (hf.isConstStructureJHolomorphicWithinAt hx)).2
  · intro h
    exact h.1.prodMk h.2

/-- A map into a direct-sum target is globally constant-structure `J`-holomorphic iff both
coordinate maps are. -/
@[simp]
lemma isConstStructureJHolomorphic_prod_iff (f : V → W × X) :
    IsConstStructureJHolomorphic J (J₁.prod J₂) f ↔
      IsConstStructureJHolomorphic J J₁ (fun y => (f y).1) ∧
        IsConstStructureJHolomorphic J J₂ (fun y => (f y).2) := by
  constructor
  · intro hf
    refine ⟨isConstStructureJHolomorphic_of_forall fun x => ?_,
      isConstStructureJHolomorphic_of_forall fun x => ?_⟩
    · exact ((isConstStructureJHolomorphicAt_prod_iff f x).mp
        (hf.isConstStructureJHolomorphicAt x)).1
    · exact ((isConstStructureJHolomorphicAt_prod_iff f x).mp
        (hf.isConstStructureJHolomorphicAt x)).2
  · intro h
    exact h.1.prodMk h.2

end ProductMaps

end TauCeti
