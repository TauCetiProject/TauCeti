/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Perturbation
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Rational subsets descend along dense maps of Huber rings

**A generalization of the rational half of Wedhorn, *Adic Spaces* (arXiv:1910.05934v1),
Proposition 7.48.** Wedhorn states that for an affinoid ring `A` the canonical map
`Spa Â → Spa A` is a homeomorphism which maps rational subsets to rational subsets. This file
proves the statements about rational subsets, and the inducing property they give, for an
arbitrary continuous ring homomorphism `φ : A → B` with dense image between Huber rings. Neither
ring is assumed complete, and the plus rings `A⁺ ⊆ A` and `B⁺ ⊆ B` are arbitrary subrings with
`φ(A⁺) ⊆ B⁺`.

## Main results

* `TauCeti.ValuationSpectrum.exists_mem_spaRationalFamily_preimage_eq_of_denseRange`: every
  member of the rational family of `Spa(B, B⁺)` is the preimage under `spaComap φ` of a member of
  the rational family of `Spa(A, A⁺)`.
* `TauCeti.ValuationSpectrum.isInducing_spaComap_of_denseRange`: `spaComap φ` is inducing.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.48, proved
  there by reference to R. Huber, *Continuous valuations*, Math. Z. 212 (1993), Proposition 3.9.
* `TauCetiRoadmap/AdicSpaces/README.md`, §3.1: the adic spectrum of the completed rational
  localisation `(A_U, A_U⁺)` is naturally homeomorphic to `U`, with rational subsets identified.

## Provenance

Consulted: AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, files `SpaParameterPerturbation.lean`,
`SpaRationalOpenHomeomorph.lean` and `SpaRationalSubsetCorrespondence.lean` of
`projects/AdicSpaces/Adic spaces/`.
-/

public section

namespace TauCeti.ValuationSpectrum

open Topology TauCeti.Huber

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- Along a continuous dense-range map `φ : A → B` from a Huber ring, a finite set `T ∋ 0` of `B`
is approximated within a neighbourhood `V` of zero, in both directions, by the image of a finite set
of `A` that generates an open ideal, and an element `s` of `B` by the image of an element of `A`. -/
private theorem exists_isOpen_span_forall_sub_mem_of_denseRange [IsHuberRing A] [DecidableEq B]
    {φ : A →+* B} (hφc : Continuous φ) (hφ : DenseRange φ) {V : Set B} (hV : V ∈ 𝓝 0) {T : Finset B}
    (hT : 0 ∈ T) (s : B) :
    ∃ (T' : Finset A) (s' : A), IsOpen (Ideal.span (T' : Set A) : Set A) ∧
      (∀ t ∈ T, ∃ u ∈ T'.image φ, t - u ∈ V) ∧ (∀ u ∈ T'.image φ, ∃ t ∈ T, u - t ∈ V) ∧
      s - φ s' ∈ V := by
  classical
  -- `G ⊆ φ⁻¹(V)` generates an open ideal, and `φ (a b)` lies within `V ∩ -V` of each `b : B`
  obtain ⟨G, hGV, hGopen⟩ := exists_finset_subset_isOpen_span (hφc.tendsto' 0 0 (map_zero φ) hV)
  choose a ha ha' using fun b ↦ by
    simpa using mem_closure_iff_nhds_zero.mp (hφ b) _ (Filter.inter_mem hV (neg_mem_nhds_zero B hV))
  refine ⟨T.image a ∪ G, a s, Ideal.isOpen_of_isOpen_subideal (Ideal.span_mono (by simp)) hGopen,
    fun t ht ↦ ⟨φ (a t), by grind, ha' t⟩, fun u hu ↦ ?_, ha' s⟩
  simp only [Finset.mem_image, Finset.mem_union] at hu
  -- the elements of `φ(G)` lie in `V`, so they are close to `0 ∈ T`
  obtain ⟨x, ⟨t, ht, rfl⟩ | hx, rfl⟩ := hu
  exacts [⟨t, ht, ha t⟩, ⟨0, hT, by simpa using hGV hx⟩]

/-- **Rational subsets descend along a dense map (a generalization of the rational half of
Wedhorn Proposition 7.48).** If `φ : A → B` is a continuous homomorphism of Huber rings with dense
image, every member `R(T/s)` of the rational family of `Spa(B, B⁺)` is the preimage under
`spaComap φ` of a member `R(T'/s')` of the rational family of `Spa(A, A⁺)`; that is,
`R(T/s) = R(φ(T')/φ(s'))` with `T' · A` open.

As the rational family is a basis of `Spa(B, B⁺)`, this makes `spaComap φ` inducing
(`isInducing_spaComap_of_denseRange`). -/
theorem exists_mem_spaRationalFamily_preimage_eq_of_denseRange [IsHuberRing A] [IsHuberRing B]
    {φ : A →+* B} (hφc : Continuous φ) (hφ : DenseRange φ) (Aplus : Subring A) (Bplus : Subring B)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) {U : Set (spa Bplus)} (hU : U ∈ spaRationalFamily Bplus) :
    ∃ W ∈ spaRationalFamily Aplus, spaComap φ hφc Aplus Bplus hplus ⁻¹' W = U := by
  classical
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalFamily_iff.mp hU
  -- padding `T` with `0` keeps `T · B` open, and `R(T/s)` is unchanged by it
  obtain ⟨V, hV, hpert⟩ :=
    exists_mem_nhds_forall_rationalSubset_eq_of_sub_mem Bplus (insert 0 T) (by simpa using hT) s
  obtain ⟨T', s', hT', hTT', hT'T, hs'⟩ :=
    exists_isOpen_span_forall_sub_mem_of_denseRange hφc hφ hV (Finset.mem_insert_self 0 T) s
  refine ⟨_, mem_spaRationalFamily_iff.mpr ⟨T', s', hT', rfl⟩, ?_⟩
  rw [spaComap_preimage_rationalSubset, hpert _ _ hTT' hT'T hs',
    rationalSubset_insert_of_forall_vle Bplus T s 0 fun v _ ↦ v.toValuativeRel.zero_vle s]

/-- **Pullback of adic spectra along a continuous homomorphism of Huber rings with dense image is
inducing.** For the completion `A → Â` this is the inducing part of Wedhorn Proposition 7.48; here
neither ring needs to be complete, and `A⁺`, `B⁺` are arbitrary subrings with `φ(A⁺) ⊆ B⁺`.

Since `spa Bplus` is T0, `Topology.IsInducing.isEmbedding` upgrades this to an embedding. Unlike
`isEmbedding_spaComap`, this assumes no embedding of the full valuation spectra along `comap φ`. -/
theorem isInducing_spaComap_of_denseRange [IsHuberRing A] [IsHuberRing B] {φ : A →+* B}
    (hφc : Continuous φ) (hφ : DenseRange φ) (Aplus : Subring A) (Bplus : Subring B)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) : IsInducing (spaComap φ hφc Aplus Bplus hplus) := by
  refine ⟨le_antisymm (continuous_spaComap φ hφc Aplus Bplus hplus).le_induced ?_⟩
  -- every member of the rational basis of `Spa(B, B⁺)` is the preimage of an open of `Spa(A, A⁺)`
  rw [(isTopologicalBasis_spaRationalFamily Bplus).eq_generateFrom]
  refine le_generateFrom fun U hU ↦ ?_
  obtain ⟨W, hW, rfl⟩ :=
    exists_mem_spaRationalFamily_preimage_eq_of_denseRange hφc hφ Aplus Bplus hplus hU
  exact isOpen_induced ((isTopologicalBasis_spaRationalFamily Aplus).isOpen hW)

end TauCeti.ValuationSpectrum

end
