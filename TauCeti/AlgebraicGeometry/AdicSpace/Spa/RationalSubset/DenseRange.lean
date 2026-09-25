/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Perturbation
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Rational subsets descend along dense maps of Huber rings

**A generalization of the rational half of Wedhorn, *Adic Spaces* (arXiv:1910.05934v1),
Proposition 7.48.** Wedhorn states that for an affinoid ring `A` the canonical map
`Spa Â → Spa A` is a homeomorphism which maps rational subsets to rational subsets. This file
proves the **preimage** direction, and the inducing property it gives, for an arbitrary continuous
ring homomorphism `φ : A → B` with dense image between Huber rings: every rational subset of
`Spa(B, B⁺)` is the preimage under `spaComap φ` of a rational subset of `Spa(A, A⁺)`. Wedhorn's
image statement additionally needs `spaComap φ` to be surjective, which is not proved here.
Neither ring is assumed complete, and the plus rings `A⁺ ⊆ A` and `B⁺ ⊆ B` are arbitrary subrings
with `φ(A⁺) ⊆ B⁺`.

## Main results

* `TauCeti.ValuationSpectrum.exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange`: every
  member of the rational family of `Spa(B, B⁺)` is the preimage under `spaComap φ` of a member of
  the rational family of `Spa(A, A⁺)`.
* `TauCeti.ValuationSpectrum.isInducing_spaComap_of_denseRange`: `spaComap φ` is inducing.
* `TauCeti.Huber.Pair.Hom.exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange` and
  `TauCeti.Huber.Pair.Hom.isInducing_spaComap_of_denseRange`: the same two results for a morphism
  of Huber pairs whose underlying ring homomorphism has dense range.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.48, proved
  there by reference to R. Huber, *Continuous valuations*, Math. Z. 212 (1993), Proposition 3.9.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, Apache-2.0,
  `projects/AdicSpaces/Adic spaces/`.

## Provenance

**Adapted from AINTLIB, not ported** (C. Birkbeck; `github.com/CBirkbeck/AINTLIB`, Apache-2.0,
branch `dev/adic-spaces`, commit `37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`,
`projects/AdicSpaces/Adic spaces/`). AINTLIB proves the corresponding descent only for the
canonical map from a complete Tate ring to a completed rational localisation of it, as part of its
Wedhorn 8.2(2) comparison. The correspondence is:

* `SpaRationalSubsetCorrespondence.lean`, `exists_downstairs_rationalDatum` — AINTLIB's form of
  `exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange`;
* `SpaParameterPerturbation.lean`, `exists_uniform_spanning_bound` and
  `indexedRationalSet_perturb_eq` — its padding and perturbation steps, which correspond to
  `TauCeti.Huber.exists_isOpen_span_forall_sub_mem_of_denseRange` and
  `exists_finset_subset_isOpen_span` in `TauCeti/RingTheory/Huber/OpenIdeal.lean`;
* `SpaRationalOpenHomeomorph.lean`, `exists_A_level_open_presentation` and
  `spaPresheafValueEquivRationalOpen_isOpenMap` — its open-presentation and open-map steps.

What changed: the rings are Huber rather than Tate and neither is complete; the map is any
continuous ring homomorphism with dense range rather than the canonical map to a completed
rational localisation; the plus rings are arbitrary subrings where AINTLIB requires rings of
integral elements; numerator ideals are only open where AINTLIB asks for the unit ideal; the
descended numerators are enlarged by a finite set generating an open ideal of `A` where AINTLIB
pads by a power of a topologically nilpotent unit; and the perturbation step is TauCeti's
Huber-ring form of Proposition 7.34. No code is copied.
-/

public section

namespace TauCeti.ValuationSpectrum

open Topology TauCeti.Huber

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- **Rational subsets descend along a dense map (a generalization of the rational half of
Wedhorn Proposition 7.48).** If `φ : A → B` is a continuous homomorphism of Huber rings with dense
image, every member `R(T/s)` of the rational family of `Spa(B, B⁺)` is the preimage under
`spaComap φ` of a member `R(T'/s')` of the rational family of `Spa(A, A⁺)`; that is,
`R(T/s) = R(φ(T')/φ(s'))` with `T' · A` open.

As the rational family is a basis of `Spa(B, B⁺)`, this makes `spaComap φ` inducing
(`isInducing_spaComap_of_denseRange`). -/
theorem exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange [IsHuberRing A]
    [IsHuberRing B] {φ : A →+* B} (hφc : Continuous φ) (hφ : DenseRange φ) (Aplus : Subring A)
    (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) {U : Set (spa Bplus)}
    (hU : U ∈ spaRationalFamily Bplus) :
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
    exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange hφc hφ Aplus Bplus hplus hU
  exact isOpen_induced ((isTopologicalBasis_spaRationalFamily Aplus).isOpen hW)

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber.Pair.Hom

open Topology TauCeti.ValuationSpectrum

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}

/-- **Rational subsets descend along a morphism of Huber pairs with dense image.** Every member of
the rational family of `Spa(T)` is the preimage under `f.spaComap` of a member of the rational
family of `Spa(S)`. -/
theorem exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange (f : Hom S T)
    (hf : DenseRange f.toRingHom) {U : Set (spa T.plus)} (hU : U ∈ spaRationalFamily T.plus) :
    ∃ W ∈ spaRationalFamily S.plus, f.spaComap ⁻¹' W = U := by
  rw [spaComap_def]
  exact ValuationSpectrum.exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange
    f.continuous_toRingHom hf S.plus T.plus f.map_mem_plus hU

/-- **The map of adic spectra induced by a morphism of Huber pairs with dense image is inducing.**
For the completion morphism this is the inducing part of Wedhorn Proposition 7.48. -/
theorem isInducing_spaComap_of_denseRange (f : Hom S T) (hf : DenseRange f.toRingHom) :
    IsInducing f.spaComap := by
  rw [spaComap_def]
  exact ValuationSpectrum.isInducing_spaComap_of_denseRange f.continuous_toRingHom hf S.plus
    T.plus f.map_mem_plus

end TauCeti.Huber.Pair.Hom

end
