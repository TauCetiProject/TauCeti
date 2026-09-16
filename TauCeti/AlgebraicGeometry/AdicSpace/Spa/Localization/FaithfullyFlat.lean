/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Pi
public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.Huber.StronglyNoetherian

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Proper
import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Flat
import TauCeti.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithful flatness of a rational cover

**Wedhorn's Corollary 8.32**: let `A` be a complete Hausdorff strongly noetherian Tate ring and let
the rational subsets `R(Tᵢ/sᵢ)` of a finite family cover `Spa(A, A⁺)`. Then the map
`A → ∏ᵢ A⟨Tᵢ/sᵢ⟩` into the product of the rational localisations is faithfully flat, and in
particular injective.

Each factor is flat by `TauCeti.Huber.PairOfDefinition.flat_toCompletionLoc`. For faithfulness, a
maximal ideal of `A` is the support of a point of `Spa(A, A⁺)`
(`TauCeti.ValuationSpectrum.exists_mem_spa_supp_eq_of_isMaximal`). That point lies in some
`R(Tᵢ/sᵢ)`, and its support stays proper in `A⟨Tᵢ/sᵢ⟩` by
`TauCeti.ValuationSpectrum.map_supp_toCompletionLoc_ne_top`. These are the two hypotheses of
`RingHom.FaithfullyFlat.pi_of_exists_map_ne_top`, the faithful-flatness criterion for a finite
product of flat ring homomorphisms.

## Main results

* `TauCeti.ValuationSpectrum.faithfullyFlat_pi_toCompletionLoc`: the map into the product over a
  finite rational cover is faithfully flat.
* `TauCeti.ValuationSpectrum.pi_toCompletionLoc_injective`: that map is injective.
* `TauCeti.ValuationSpectrum.faithfullyFlat_rationalLocalizationPiHom_of_span_eq_top` and
  `TauCeti.ValuationSpectrum.rationalLocalizationPiHom_injective_of_span_eq_top`: the same for the
  standard rational cover `(R(T/t))_{t ∈ T}` of a set `T` generating the unit ideal.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Corollary 8.32.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch `dev/adic-spaces` at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, was consulted. Its file
`projects/AdicSpaces/Adic spaces/Cor832.lean` proves the maximal-ideal criterion for a finite
product of flat algebras (`faithfullyFlat_pi_of_maximal_ne_top`) and states the corollary with
chart flatness and prime lifting as hypotheses. `AuditCleanWrappers.lean` (`cor_8_32_clean_proof`)
discharges these for its presheaf values by lifting primes to points of `Spa`, through lemmas
that are still sorried there. The argument here has the same shape, but its inputs are Tau Ceti's
own flatness and support lemmas, and no code is ported.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] [IsStronglyNoetherian A]

/-- **Wedhorn's Corollary 8.32, faithful flatness.** If the rational subsets `R(Tᵢ/sᵢ)` of a finite
family cover `Spa(A, A⁺)`, then the map `A → ∏ᵢ A⟨Tᵢ/sᵢ⟩` into the product of the rational
localisations is faithfully flat. Here `A` is a complete Hausdorff strongly noetherian Tate ring,
and `A⁺` is a ring of integral elements containing the chosen ring of definition. For the standard
rational cover of a set generating the unit ideal, where no `A⁺` has to be chosen, see
`faithfullyFlat_rationalLocalizationPiHom_of_span_eq_top`. -/
theorem faithfullyFlat_pi_toCompletionLoc (P : PairOfDefinition A) (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (hP : P.ringOfDefinition ≤ Aplus) {ι : Type*}
    [Finite ι] (T : ι → Finset A) (s : ι → A) (S : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra A (S i)] [∀ i, IsLocalization.Away (s i) (S i)]
    (hden : ∀ i, HasDenominatorPower P (T i) (s i) (S i))
    (hcov : spa Aplus ⊆ ⋃ i, rationalSubset Aplus (T i) (s i)) :
    letI : ∀ i, UniformSpace (S i) := fun i ↦ locUniformSpace P (T i) (s i) (S i) (hden i)
    letI : ∀ i, IsUniformAddGroup (S i) := fun i ↦
      isUniformAddGroup_locUniformSpace P (T i) (s i) (S i) (hden i)
    letI : ∀ i, IsTopologicalRing (S i) := fun i ↦
      isTopologicalRing_locUniformSpace P (T i) (s i) (S i) (hden i)
    (RingHom.pi fun i ↦ toCompletionLoc P (T i) (s i) (S i) (hden i)).FaithfullyFlat := by
  -- the uniformities are explicit in the goal; the completions need these instances to be rings
  have _ (i : ι) := isUniformAddGroup_locUniformSpace P (T i) (s i) (S i) (hden i)
  have _ (i : ι) := isTopologicalRing_locUniformSpace P (T i) (s i) (S i) (hden i)
  -- every factor is flat, so it remains to keep each maximal ideal proper in some factor
  refine RingHom.FaithfullyFlat.pi_of_exists_map_ne_top
    (fun i ↦ flat_toCompletionLoc P (T i) (s i) (S i) (hden i)) fun m hm ↦ ?_
  -- `m` is the support of a point of `Spa(A, A⁺)`, which lies in some `R(Tᵢ/sᵢ)`
  obtain ⟨v, hv, rfl⟩ := exists_mem_spa_supp_eq_of_isMaximal Aplus hplus m
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hv)
  exact ⟨i, map_supp_toCompletionLoc_ne_top P Aplus hP (T i) (s i) (S i) (hden i) hi⟩

/-- **Wedhorn's Corollary 8.32, injectivity.** If the rational subsets `R(Tᵢ/sᵢ)` of a finite
family cover `Spa(A, A⁺)`, then the map `A → ∏ᵢ A⟨Tᵢ/sᵢ⟩` is injective. It is even faithfully flat
(`faithfullyFlat_pi_toCompletionLoc`); for the standard rational cover of a set generating the unit
ideal, see `rationalLocalizationPiHom_injective_of_span_eq_top`. -/
theorem pi_toCompletionLoc_injective (P : PairOfDefinition A) (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (hP : P.ringOfDefinition ≤ Aplus) {ι : Type*}
    [Finite ι] (T : ι → Finset A) (s : ι → A) (S : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra A (S i)] [∀ i, IsLocalization.Away (s i) (S i)]
    (hden : ∀ i, HasDenominatorPower P (T i) (s i) (S i))
    (hcov : spa Aplus ⊆ ⋃ i, rationalSubset Aplus (T i) (s i)) :
    letI : ∀ i, UniformSpace (S i) := fun i ↦ locUniformSpace P (T i) (s i) (S i) (hden i)
    letI : ∀ i, IsUniformAddGroup (S i) := fun i ↦
      isUniformAddGroup_locUniformSpace P (T i) (s i) (S i) (hden i)
    letI : ∀ i, IsTopologicalRing (S i) := fun i ↦
      isTopologicalRing_locUniformSpace P (T i) (s i) (S i) (hden i)
    Function.Injective (RingHom.pi fun i ↦ toCompletionLoc P (T i) (s i) (S i) (hden i)) := by
  -- the uniformities are explicit in the goal; the completions need these instances to be rings
  have _ (i : ι) := isUniformAddGroup_locUniformSpace P (T i) (s i) (S i) (hden i)
  have _ (i : ι) := isTopologicalRing_locUniformSpace P (T i) (s i) (S i) (hden i)
  exact (faithfullyFlat_pi_toCompletionLoc P Aplus hplus hP T s S hden hcov).injective

/-- **Corollary 8.32 for a standard rational cover.** When `T` generates the unit ideal, the
structure map `A → ∏_{t ∈ T} A⟨T/t⟩` into the family of rational localisations is faithfully flat.
This is `faithfullyFlat_pi_toCompletionLoc` for the family `(R(T/t))_{t ∈ T}`; the unit-ideal
condition on `T` takes the place of its ring of integral elements `A⁺` and covering hypothesis. -/
theorem faithfullyFlat_rationalLocalizationPiHom_of_span_eq_top (P : PairOfDefinition A)
    {T : Finset A} (hT : Ideal.span (T : Set A) = ⊤) (S : ∀ _ : T, Type*) [∀ t : T, CommRing (S t)]
    [∀ t : T, Algebra A (S t)] [∀ t : T, IsLocalization.Away (t : A) (S t)]
    (hden : ∀ t : T, HasDenominatorPower P T (t : A) (S t)) :
    letI : ∀ t : T, UniformSpace (S t) := fun t ↦ locUniformSpace P T (t : A) (S t) (hden t)
    letI : ∀ t : T, IsUniformAddGroup (S t) := fun t ↦
      isUniformAddGroup_locUniformSpace P T (t : A) (S t) (hden t)
    letI : ∀ t : T, IsTopologicalRing (S t) := fun t ↦
      isTopologicalRing_locUniformSpace P T (t : A) (S t) (hden t)
    (rationalLocalizationPiHom P T S hden).FaithfullyFlat := by
  -- take the Huber pair `(A, A°)`: its ring of integral elements contains the ring of definition,
  -- and its rational subsets `R(T/t)` cover `Spa(A, A°)` because `T` generates the unit ideal
  convert faithfullyFlat_pi_toCompletionLoc P _ (Pair.powerBounded A).isRingOfIntegralElements
    (Pair.powerBounded_plus (A := A) ▸ P.le_powerBoundedSubring) (fun _ ↦ T) (↑) S hden
    ((spa_eq_biUnion_rationalSubset_of_span_eq_top _ hT).trans iSup_subtype').le using 1
  exact RingHom.ext fun a ↦ funext (rationalLocalizationPiHom_apply P T S hden a)

/-- **Corollary 8.32 for a standard rational cover, injectivity.** When `T` generates the unit
ideal, the structure map `A → ∏_{t ∈ T} A⟨T/t⟩` is injective. It is even faithfully flat
(`faithfullyFlat_rationalLocalizationPiHom_of_span_eq_top`); for an arbitrary finite rational cover
of `Spa(A, A⁺)`, see `pi_toCompletionLoc_injective`. -/
theorem rationalLocalizationPiHom_injective_of_span_eq_top (P : PairOfDefinition A) {T : Finset A}
    (hT : Ideal.span (T : Set A) = ⊤) (S : ∀ _ : T, Type*) [∀ t : T, CommRing (S t)]
    [∀ t : T, Algebra A (S t)] [∀ t : T, IsLocalization.Away (t : A) (S t)]
    (hden : ∀ t : T, HasDenominatorPower P T (t : A) (S t)) :
    letI : ∀ t : T, UniformSpace (S t) := fun t ↦ locUniformSpace P T (t : A) (S t) (hden t)
    letI : ∀ t : T, IsUniformAddGroup (S t) := fun t ↦
      isUniformAddGroup_locUniformSpace P T (t : A) (S t) (hden t)
    letI : ∀ t : T, IsTopologicalRing (S t) := fun t ↦
      isTopologicalRing_locUniformSpace P T (t : A) (S t) (hden t)
    Function.Injective (rationalLocalizationPiHom P T S hden) := by
  -- the uniformities are explicit in the goal; the completions need these instances to be rings
  have _ (t : T) := isUniformAddGroup_locUniformSpace P T t (S t) (hden t)
  have _ (t : T) := isTopologicalRing_locUniformSpace P T t (S t) (hden t)
  exact (faithfullyFlat_rationalLocalizationPiHom_of_span_eq_top P hT S hden).injective

end TauCeti.ValuationSpectrum

end
