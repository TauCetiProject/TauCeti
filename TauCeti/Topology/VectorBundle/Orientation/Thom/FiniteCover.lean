/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Thom.Class
public import TauCeti.Topology.VectorBundle.Thom.FiniteCover

/-!
# The oriented Thom isomorphism over finite trivializing covers

Let `E → B` be a real vector bundle with finite-dimensional model fibre `F` of rank
`r = finrank ℝ F` and orientation `o : TauCeti.VectorBundleOrientation F E ι`. Given an orientation
`ω` of `F` and a generator `g` of `Hʳ(F, F ∖ {0}; K)` over a commutative ring `K`, the oriented
Thom class `o.thomClassOfModel hι ω g` (`TauCeti.VectorBundleOrientation.thomClassOfModel`) is a
Thom class in the sense of `TauCeti.IsThomClass`
(`TauCeti.VectorBundleOrientation.isThomClass_thomClassOfModel`). Combining this with the
finite-cover Thom isomorphism of `TauCeti.Topology.VectorBundle.Thom.FiniteCover`
(`TauCeti.IsThomClass.bijective_thomMap_of_biUnion_eq_univ`,
`TauCeti.IsThomClass.thomEquivOfBiUnionEqUniv`,
`TauCeti.IsThomClass.bijective_thomMap_of_compactSpace`,
`TauCeti.IsThomClass.thomEquivOfCompactSpace`) yields the oriented Thom isomorphism
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` (`p + r = m`) over any base admitting a finite trivializing cover,
and in particular over any compact base `B`.

## Main definitions and results

* `TauCeti.VectorBundleOrientation.bijective_thomMap_thomClassOfModel_of_biUnion_eq_univ`,
  `TauCeti.VectorBundleOrientation.thomEquivOfModelOfBiUnionEqUniv`: the oriented Thom isomorphism
  for a vector bundle admitting a finite trivializing cover.
* `TauCeti.VectorBundleOrientation.bijective_thomMap_thomClassOfModel_of_compactSpace`,
  `TauCeti.VectorBundleOrientation.thomEquivOfModelOfCompactSpace`: the oriented Thom isomorphism
  over a compact base `B`.

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

namespace TauCeti.VectorBundleOrientation

section ThomIsomorphism

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type*} [Fintype ι]
  {K : Type w} [CommRing K]

/-- **The oriented Thom isomorphism over a finite trivializing cover**: for an oriented real vector
bundle `o : VectorBundleOrientation F E ι` covered by a finite family `s : Finset κ` of sets `W j`
contained in linear trivializations, an orientation `ω` of `F`, and a generator `g` of
`Hʳ(F, F ∖ {0}; K)`, the Thom map of `o.thomClassOfModel hι ω g` is bijective in every degree. -/
theorem bijective_thomMap_thomClassOfModel_of_biUnion_eq_univ
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) (M : ModuleCat.{w} K) {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hW : ⋃ j ∈ s, W j = univ)
    (hWe : ∀ j ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W j ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective
      (thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g)) :=
  (o.isThomClass_thomClassOfModel hι ω hg).bijective_thomMap_of_biUnion_eq_univ M s hW hWe h

/-- **The oriented Thom linear equivalence** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` over a finite
trivializing cover associated to `o.thomClassOfModel hι ω g`. -/
def thomEquivOfModelOfBiUnionEqUniv
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) (M : ModuleCat.{w} K) {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hW : ⋃ j ∈ s, W j = univ)
    (hWe : ∀ j ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W j ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  (o.isThomClass_thomClassOfModel hι ω hg).thomEquivOfBiUnionEqUniv M s hW hWe h

@[simp]
theorem thomEquivOfModelOfBiUnionEqUniv_apply
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) (M : ModuleCat.{w} K) {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hW : ⋃ j ∈ s, W j = univ)
    (hWe : ∀ j ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W j ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    o.thomEquivOfModelOfBiUnionEqUniv hι ω M s hW hWe h hg a =
      thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g) a :=
  (o.isThomClass_thomClassOfModel hι ω hg).thomEquivOfBiUnionEqUniv_apply M s hW hWe h a

/-- **The oriented Thom isomorphism over a compact base**: for an oriented real vector bundle
`o : VectorBundleOrientation F E ι` over a compact space `B`, an orientation `ω` of `F`, and a
generator `g` of `Hʳ(F, F ∖ {0}; K)`, the Thom map of `o.thomClassOfModel hι ω g` is bijective in
every degree. -/
theorem bijective_thomMap_thomClassOfModel_of_compactSpace [CompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective
      (thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g)) :=
  (o.isThomClass_thomClassOfModel hι ω hg).bijective_thomMap_of_compactSpace M h

/-- **The oriented Thom linear equivalence** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` over a compact base `B`
associated to `o.thomClassOfModel hι ω g`. -/
def thomEquivOfModelOfCompactSpace [CompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  (o.isThomClass_thomClassOfModel hι ω hg).thomEquivOfCompactSpace M h

@[simp]
theorem thomEquivOfModelOfCompactSpace_apply [CompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    o.thomEquivOfModelOfCompactSpace hι ω M h hg a =
      thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g) a :=
  (o.isThomClass_thomClassOfModel hι ω hg).thomEquivOfCompactSpace_apply M h a

end ThomIsomorphism

end TauCeti.VectorBundleOrientation
