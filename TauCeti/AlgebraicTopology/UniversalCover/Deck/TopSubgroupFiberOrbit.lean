/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbit

/-!
# Top-subgroup fibre orbits

This file records the quotient map from fibre orbits by a subgroup `H ≤ Deck p` to the
full deck-orbit quotient, obtained from the inclusion `H ≤ ⊤`. It is the top-subgroup
counterpart to the bottom-subgroup API in
`TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbit`: the bottom quotient
recovers the fibre, while the top quotient recovers the unpointed deck-orbit quotient.

The declarations here are bookkeeping for the universal-covers roadmap. In the pointed and
unpointed cover correspondence, changing a chosen lift by a subgroup action first forms the
`H`-fibre quotient; then forgetting the subgroup and remembering only the full deck orbit is
the passage from pointed fibre data to unpointed fibre data.

## Main declarations

* `TauCeti.Deck.subgroupFiberOrbitMapToFiberOrbit`: the map
  `SubgroupFiberOrbitQuotient H b → FiberOrbitQuotient p b` induced by `H ≤ ⊤`.
* `TauCeti.Deck.subgroupFiberOrbitMapToFiberOrbit_apply`: this map sends an `H`-class to
  the full deck-orbit class of the same fibre point.
* `TauCeti.Deck.subgroupFiberOrbitMapToFiberOrbit_eq_iff`: equality after forgetting to
  full deck orbits is membership in a full deck orbit.
* `TauCeti.Deck.IsRegular.subgroupFiberOrbitMapToFiberOrbit_eq`: for a regular deck action,
  the forgotten full deck-orbit class is independent of the `H`-orbit.

## References

This is a small prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
items 7 and 8: covers associated to subgroups and the pointed/unpointed Galois
correspondence. It builds only on Mathlib's orbit quotients and the existing Tau Ceti
deck-orbit API.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- The map from the quotient of one fibre by `H` to the full deck-orbit quotient, induced
by the subgroup inclusion `H ≤ ⊤`. -/
@[expose] def subgroupFiberOrbitMapToFiberOrbit (H : Subgroup (Deck p)) :
    SubgroupFiberOrbitQuotient H b → FiberOrbitQuotient p b :=
  subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b) ∘
    subgroupFiberOrbitMapOfLE (b := b) (le_top : H ≤ (⊤ : Subgroup (Deck p)))

/-- Forgetting from `H`-orbits to full deck orbits sends a class to the full orbit class of
the same fibre point. -/
@[simp]
lemma subgroupFiberOrbitMapToFiberOrbit_apply (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    subgroupFiberOrbitMapToFiberOrbit H (subgroupFiberOrbitClass H e) =
      fiberOrbitClass e :=
  rfl

/-- For `H = ⊤`, forgetting from `H`-orbits to full deck orbits is the top-subgroup
identification already supplied by `subgroupFiberOrbitQuotientTopEquiv`. -/
@[simp]
lemma subgroupFiberOrbitMapToFiberOrbit_top :
    subgroupFiberOrbitMapToFiberOrbit (p := p) (b := b) (⊤ : Subgroup (Deck p)) =
      subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  rfl

/-- The top-subgroup equivalence identifies equality of top-subgroup classes with equality
of the corresponding full deck-orbit classes. -/
@[simp]
lemma subgroupFiberOrbitClass_top_eq_iff (e e' : p ⁻¹' {b}) :
    subgroupFiberOrbitClass (⊤ : Subgroup (Deck p)) e =
        subgroupFiberOrbitClass (⊤ : Subgroup (Deck p)) e' ↔
      fiberOrbitClass e = fiberOrbitClass e' := by
  constructor
  · intro h
    exact congrArg (subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b)) h
  · intro h
    exact congrArg (subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b)).symm h

/-- Equality of top-subgroup fibre-orbit classes is membership in a full deck orbit. -/
lemma subgroupFiberOrbitClass_top_eq_iff_mem_orbit (e e' : p ⁻¹' {b}) :
    subgroupFiberOrbitClass (⊤ : Subgroup (Deck p)) e =
        subgroupFiberOrbitClass (⊤ : Subgroup (Deck p)) e' ↔
      e ∈ MulAction.orbit (Deck p) e' := by
  rw [subgroupFiberOrbitClass_top_eq_iff, fiberOrbitClass_eq_iff]

/-- The map induced by `H ≤ ⊤`, after identifying the top quotient with the full deck-orbit
quotient, is `subgroupFiberOrbitMapToFiberOrbit`. -/
@[simp]
lemma subgroupFiberOrbitQuotientTopEquiv_mapOfLE (H : Subgroup (Deck p)) :
    subgroupFiberOrbitQuotientTopEquiv (p := p) (b := b) ∘
        subgroupFiberOrbitMapOfLE (b := b) (le_top : H ≤ (⊤ : Subgroup (Deck p))) =
      subgroupFiberOrbitMapToFiberOrbit (p := p) (b := b) H :=
  rfl

/-- Equality after forgetting from `H`-orbits to full deck orbits is exactly membership of
representatives in the same full deck orbit. -/
lemma subgroupFiberOrbitMapToFiberOrbit_apply_eq_iff (H : Subgroup (Deck p))
    (e e' : p ⁻¹' {b}) :
    subgroupFiberOrbitMapToFiberOrbit H (subgroupFiberOrbitClass H e) =
        subgroupFiberOrbitMapToFiberOrbit H (subgroupFiberOrbitClass H e') ↔
      e ∈ MulAction.orbit (Deck p) e' := by
  rw [subgroupFiberOrbitMapToFiberOrbit_apply, subgroupFiberOrbitMapToFiberOrbit_apply,
    fiberOrbitClass_eq_iff]

/-- Equality after forgetting from an `H`-fibre quotient to full deck orbits can be checked
on representatives. -/
lemma subgroupFiberOrbitMapToFiberOrbit_eq_iff (H : Subgroup (Deck p))
    (x y : SubgroupFiberOrbitQuotient H b) :
    subgroupFiberOrbitMapToFiberOrbit H x = subgroupFiberOrbitMapToFiberOrbit H y ↔
      ∃ e e' : p ⁻¹' {b}, x = subgroupFiberOrbitClass H e ∧
        y = subgroupFiberOrbitClass H e' ∧ e ∈ MulAction.orbit (Deck p) e' := by
  refine Quotient.inductionOn' x ?_
  intro e
  refine Quotient.inductionOn' y ?_
  intro e'
  constructor
  · intro hxy
    refine ⟨e, e', rfl, rfl, ?_⟩
    exact (subgroupFiberOrbitMapToFiberOrbit_apply_eq_iff H e e').mp hxy
  · rintro ⟨e, e', hx, hy, hee'⟩
    rw [hx, hy]
    exact (subgroupFiberOrbitMapToFiberOrbit_apply_eq_iff H e e').mpr hee'

/-- If `H ≤ K`, forgetting `H`-orbits to full deck orbits factors through the `K`-orbit
quotient. -/
@[simp]
lemma subgroupFiberOrbitMapToFiberOrbit_mapOfLE {H K : Subgroup (Deck p)} (hHK : H ≤ K)
    (x : SubgroupFiberOrbitQuotient H b) :
    subgroupFiberOrbitMapToFiberOrbit K (subgroupFiberOrbitMapOfLE (b := b) hHK x) =
      subgroupFiberOrbitMapToFiberOrbit H x := by
  refine Quotient.inductionOn' x ?_
  intro e
  rfl

namespace IsRegular

/-- For a regular deck action, every `H`-fibre orbit maps to the same full deck-orbit class
as any chosen point of the fibre. -/
lemma subgroupFiberOrbitMapToFiberOrbit_eq (hreg : IsRegular p) (H : Subgroup (Deck p))
    (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient H b) :
    subgroupFiberOrbitMapToFiberOrbit H x = fiberOrbitClass e := by
  refine Quotient.inductionOn' x ?_
  intro e'
  exact hreg.fiberOrbitClass_eq e' e

/-- For a regular deck action, forgetting any two subgroup fibre-orbit classes to full deck
orbits gives the same result. -/
lemma subgroupFiberOrbitMapToFiberOrbit_eq_subgroupFiberOrbitMapToFiberOrbit
    (hreg : IsRegular p) (H K : Subgroup (Deck p))
    (x : SubgroupFiberOrbitQuotient H b) (y : SubgroupFiberOrbitQuotient K b) :
    subgroupFiberOrbitMapToFiberOrbit H x = subgroupFiberOrbitMapToFiberOrbit K y := by
  obtain ⟨e⟩ := hreg.nonempty_fiber b
  rw [hreg.subgroupFiberOrbitMapToFiberOrbit_eq H e x,
    hreg.subgroupFiberOrbitMapToFiberOrbit_eq K e y]

end IsRegular

end Deck

end TauCeti
