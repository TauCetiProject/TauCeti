/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Localization
public import TauCeti.RingTheory.Huber.StableUniform

/-!
# Stable uniformity and the structure presheaf

Buzzard and Verberkmoes call a Tate pair `(A, A⁺)` stably uniform when `𝒪_X(U)` is uniform for
every rational subset `U` of `X = Spa(A, A⁺)`. This file identifies that condition, for the
presentation-indexed limit `presentationLimit`, with `TauCeti.Huber.IsStablyUniform`, the
uniformity of every rational localization `A⟨T/s⟩`. It deduces that stable uniformity passes to
rational localizations.

## Main results

* `TauCeti.Huber.isStablyUniform_iff_forall_isUniform_presentationLimit`: for a subring `A⁺` of
  power-bounded elements, `A` is stably uniform exactly when `presentationLimit A⁺ V` is uniform
  for every rational open `V` of `Spa(A, A⁺)`.
* `TauCeti.Huber.PairOfDefinition.isStablyUniform_completion_locTopology`: a rational
  localization `A⟨T/s⟩` of a stably uniform Tate ring is stably uniform.

## References

* K. Buzzard, A. Verberkmoes, *Stably uniform affinoids are sheafy*, J. reine angew. Math. 740
  (2018), 25–39, §3 and the proof of Theorem 7.
* D. Hansen, K. S. Kedlaya, *Sheafiness criteria for Huber rings*, Definition 3.13.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2 (2) and
  Remark 8.4.
-/

public section

namespace TauCeti.Huber

open CategoryTheory _root_.TopologicalSpace TauCeti.ValuationSpectrum PairOfDefinition

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- **Stable uniformity of a pair.** Let `P` be a pair of definition of `A` and `A⁺` a subring of
power-bounded elements. Then `A` is stably uniform exactly when `presentationLimit A⁺ V` is uniform
for every rational open `V` of `Spa(A, A⁺)`; on `V = R(T/s)` this limit is `A⟨T/s⟩` by
`presentationLimitRationalIso`. The left side involves neither `P` nor `A⁺`, so the right side
holds for one such choice exactly when it holds for all of them. Unlike
`isStablyUniform_iff_forall_isUniform_completionLocObj`, which ranges over presentations `(T, s)`,
this ranges over the rational opens themselves. -/
theorem isStablyUniform_iff_forall_isUniform_presentationLimit (P : PairOfDefinition A)
    {Aplus : Subring A} (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) : IsStablyUniform A ↔
      ∀ V ∈ spaRationalOpens Aplus, IsUniform (presentationLimit (P := P) Aplus V) := by
  -- on a rational open `R(T/s)`, `presentationLimit` is `A⟨T/s⟩`, so uniformity transfers
  have hrat (T : Finset A) (s : A) (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :=
    Iso.isUniform_iff <| TopCommRingCat.isCompleteSeparated.ι.mapIso <|
      presentationLimitRationalIso Aplus hAplus
        ⟨T, s, hasDenominatorPower_of_isOpen_span P T s _ hT⟩ hT
  rw [isStablyUniform_iff_forall_isUniform_completionLocObj P]
  refine ⟨fun h V hV ↦ ?_, fun h T s hT ↦
    (hrat T s hT).mp (h _ (spaBasicOpen_mem_spaRationalOpens hT))⟩
  -- present the rational open `V` as `R(T/s)` with `T` spanning an open ideal
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hV
  exact (hrat T s hT).mpr (h T s hT)

/-- **A rational localization of a stably uniform Tate ring is stably uniform** (Buzzard and
Verberkmoes, proof of Theorem 7): if `T` spans an open ideal of `A`, then `A⟨T/s⟩` is stably
uniform when `A` is. Here `A⟨T/s⟩` is `UniformSpace.Completion S` for the uniformity
`locUniformSpace P T s S hden`, a Tate ring by `isTateRing_completion_locTopology_of_isTateRing`.
For `hden` one may take `hasDenominatorPower_of_isOpen_span P T s S hT`. -/
theorem PairOfDefinition.isStablyUniform_completion_locTopology [IsStablyUniform A]
    (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type v) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isTateRing_completion_locTopology_of_isTateRing P T s S hden
    IsStablyUniform (UniformSpace.Completion S) := by
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isTateRing_completion_locTopology_of_isTateRing P T s S hden
  have hAplus ⦃a : A⦄ : a ∈ powerBoundedSubring A → IsPowerBounded a := mem_powerBoundedSubring.mp
  -- it suffices to test each rational open `W` of `Spa(A⟨T/s⟩, A_U⁺)`, where `A_U⁺ ⊆ A⟨T/s⟩°`
  refine (isStablyUniform_iff_forall_isUniform_presentationLimit
    (completionLocalization P T s S hden)
    (isPowerBounded_of_mem_completedPlusSubring P _ hAplus T s S hden)).mpr fun W hW ↦ ?_
  -- `W` is the pullback of a rational `V ⊆ R(T/s)` of `Spa(A, A°)` (Wedhorn, Proposition 8.2 (2))
  obtain ⟨V, hV, hVT, rfl⟩ := exists_mem_spaRationalOpens_locOpensComap_eq P _ T s S hden hT W hW
  -- by Wedhorn's Remark 8.4 the presheaf of `A⟨T/s⟩` on `W` is that of `A` on `V`, which is uniform
  exact (Iso.isUniform_iff <| TopCommRingCat.isCompleteSeparated.ι.mapIso <|
    presentationLimitLocIso P _ T s S hden hAplus hT V hV hVT).mp <|
    (isStablyUniform_iff_forall_isUniform_presentationLimit P hAplus).mp ‹_› V hV

end TauCeti.Huber
