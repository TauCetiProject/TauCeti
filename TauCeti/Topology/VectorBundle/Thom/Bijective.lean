/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.Homology

/-!
# The homology Thom isomorphism over a finitely trivialized base

Let `E → B` be a real vector bundle with model fibre `F` of rank `r`, and let `u ∈ Hʳ(E, E₀; K)`
be a Thom class (`TauCeti.IsThomClass`) with coefficients in a field `K`, for instance the unique
class with `K = ZMod 2`. If `B` is covered by finitely many open sets, each in
the base set of a linear trivialization, then the cohomology Thom map `a ↦ π^*a ⌣ u` is bijective
(`TauCeti.bijective_thomMap_of_biUnion_eq_univ`). Over a field, the homology Thom map
`x ↦ π_*(x ⌢ u)` is the transpose of the Thom map up to sign
(`TauCeti.bijective_homologyThomMap_iff`), so it is bijective as well:
`Hₚ₊ᵣ(E, E₀; K) ≅ Hₚ(B; K)`
(`TauCeti.IsThomClass.bijective_homologyThomMap_of_biUnion_eq_univ`). Only the finite cover is
used here; for a vector bundle over an arbitrary base see
`TauCeti.bijective_homologyThomMap_of_field`.

Composed with the comparison of the disc-sphere pair with the Thom pair, this is the input for
identifying the relative homology of a disc-bundle attachment, such as the attachment of the
negative disc bundle of a critical submanifold of a Morse–Bott function, with the shifted homology
of the base.

## Main results

* `TauCeti.IsThomClass.bijective_homologyThomMap_of_biUnion_eq_univ`: the Thom isomorphism in
  homology over a finitely trivialized base, with coefficients in a field.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Set Module

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- **The Thom isomorphism in homology over a finitely trivialized base.** Let `E → B` be a real
vector bundle of rank `r` whose base is covered by finitely many open sets, each contained in the
base set of a linear trivialization, and let `u ∈ Hʳ(E, E₀; K)` be a Thom class with coefficients
in a field `K`. Then the homology Thom map `x ↦ π_*(x ⌢ u)` is bijective from `Hₚ₊ᵣ(E, E₀; K)`
onto `Hₚ(B; K)`, for every degree `p`. -/
theorem IsThomClass.bijective_homologyThomMap_of_biUnion_eq_univ {K : Type w} [Field K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : ⋃ i ∈ s, W i = univ) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (bijective_homologyThomMap_iff F E h u).2
    (bijective_thomMap_of_biUnion_eq_univ _ s hWo hWe hW p m (by omega) hu)

end TauCeti
