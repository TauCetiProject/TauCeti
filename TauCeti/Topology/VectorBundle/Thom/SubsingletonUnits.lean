/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism

/-!
# The canonical unoriented Thom isomorphism when `Kˣ` is a subsingleton

Let `E → B` be a real vector bundle with finite-dimensional model fibre `F` of rank
`r = finrank ℝ F` and let `K` be a commutative ring whose group of units `Kˣ` is a subsingleton
(for example `K = ZMod 2`). By `TauCeti.isThomClass_thomClassOfSubsingletonUnits`, the canonical
class `TauCeti.thomClassOfSubsingletonUnits F E K ∈ Hʳ(E, E₀; K)` is the unique Thom class of `E`,
requiring no orientation of `E`. Combining it with the Thom isomorphism of
`TauCeti.Topology.VectorBundle.Thom.Isomorphism` yields canonical `K`-linear Thom equivalences
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` (`p + r = m`) over bases admitting a finite trivializing cover and
over compact bases.

## Main definitions and results

* `TauCeti.bijective_thomMap_thomClassOfSubsingletonUnits_of_biUnion_eq_univ`,
  `TauCeti.thomEquivOfSubsingletonUnitsOfBiUnionEqUniv`: the canonical unoriented Thom isomorphism
  over a finite trivializing cover when `Kˣ` is a subsingleton.
* `TauCeti.bijective_thomMap_thomClassOfSubsingletonUnits_of_compactSpace`,
  `TauCeti.thomEquivOfSubsingletonUnitsOfCompactSpace`: the canonical unoriented Thom isomorphism
  over a compact base when `Kˣ` is a subsingleton.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set

universe w

namespace TauCeti

section SubsingletonUnits

variable {B : Type w} [TopologicalSpace B] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K] [Subsingleton Kˣ] (M : ModuleCat.{w} K)

/-- **Canonical unoriented Thom isomorphism over a finite trivializing cover**: when `Kˣ` is a
subsingleton (such as `ZMod 2`) and finitely many sets `W i` contained in linear trivializations
cover `B`, `thomMap` of `thomClassOfSubsingletonUnits F E K` is bijective in every degree. -/
theorem bijective_thomMap_thomClassOfSubsingletonUnits_of_biUnion_eq_univ {ι : Type*}
    (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m) :
    Function.Bijective
      (thomMap F E M (finrank ℝ F) p m h (thomClassOfSubsingletonUnits F E K)) :=
  bijective_thomMap_of_biUnion_eq_univ M s hWe hW p m h
    (isThomClass_thomClassOfSubsingletonUnits F E K)

/-- **Canonical unoriented Thom linear equivalence** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` over a finite
trivializing cover when `Kˣ` is a subsingleton (such as `ZMod 2`). -/
def thomEquivOfSubsingletonUnitsOfBiUnionEqUniv {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  thomEquivOfBiUnionEqUniv M s hWe hW p m h (thomClassOfSubsingletonUnits F E K)
    (isThomClass_thomClassOfSubsingletonUnits F E K)

/-- `TauCeti.thomEquivOfSubsingletonUnitsOfBiUnionEqUniv` applies `TauCeti.thomMap` at
`TauCeti.thomClassOfSubsingletonUnits`. -/
@[simp]
theorem thomEquivOfSubsingletonUnitsOfBiUnionEqUniv_apply {ι : Type*} (s : Finset ι)
    {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfSubsingletonUnitsOfBiUnionEqUniv F E M s hWe hW p m h a =
      thomMap F E M (finrank ℝ F) p m h (thomClassOfSubsingletonUnits F E K) a :=
  thomEquivOfBiUnionEqUniv_apply M s hWe hW p m h _ _ a

/-- **Canonical unoriented Thom isomorphism over a compact base**: when `Kˣ` is a subsingleton
(such as `ZMod 2`) and `B` is compact, `thomMap` of `thomClassOfSubsingletonUnits F E K` is
bijective in every degree. -/
theorem bijective_thomMap_thomClassOfSubsingletonUnits_of_compactSpace [CompactSpace B]
    (p m : ℕ) (h : p + finrank ℝ F = m) :
    Function.Bijective
      (thomMap F E M (finrank ℝ F) p m h (thomClassOfSubsingletonUnits F E K)) :=
  bijective_thomMap_of_compactSpace M p m h (isThomClass_thomClassOfSubsingletonUnits F E K)

/-- **Canonical unoriented Thom linear equivalence** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` over a compact
base when `Kˣ` is a subsingleton (such as `ZMod 2`). -/
def thomEquivOfSubsingletonUnitsOfCompactSpace [CompactSpace B]
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  thomEquivOfCompactSpace F E M p m h (thomClassOfSubsingletonUnits F E K)
    (isThomClass_thomClassOfSubsingletonUnits F E K)

/-- `TauCeti.thomEquivOfSubsingletonUnitsOfCompactSpace` applies `TauCeti.thomMap` at
`TauCeti.thomClassOfSubsingletonUnits`. -/
@[simp]
theorem thomEquivOfSubsingletonUnitsOfCompactSpace_apply [CompactSpace B]
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfSubsingletonUnitsOfCompactSpace F E M p m h a =
      thomMap F E M (finrank ℝ F) p m h (thomClassOfSubsingletonUnits F E K) a :=
  thomEquivOfCompactSpace_apply M p m h _ _ a

end SubsingletonUnits

end TauCeti
