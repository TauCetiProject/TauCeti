/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.GDelta.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Zariski.Basic

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedHomeomorph
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Flat
import TauCeti.RingTheory.Huber.LocalizationTopology.RatLoc
import TauCeti.RingTheory.Huber.LocalizationTopology.WeightedEvaluation
import TauCeti.RingTheory.Huber.Restricted.Noetherian
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete
import TauCeti.RingTheory.Ideal.GoingDown
import TauCeti.RingTheory.Ideal.MinimalPrime.Finite

/-!
# Nowhere dense zero loci in rigid affinoids

`TauCeti.ValuationSpectrum.isNowhereDense_spaZeroLocus_iff` characterizes the nowhere dense
zero loci of a rigid affinoid by avoidance of the minimal primes of its coordinate ring.
`TauCeti.ValuationSpectrum.exists_le_minimalPrime_of_nonempty_interior_spaZeroLocus` extracts a
minimal prime containing the defining ideal when the zero locus has nonempty interior.

The main inputs are `Huber.PairOfDefinition.flat_toCompletionLoc`,
`Ideal.under_mem_minimalPrimes` and `spaVanishingIdeal_spaZeroLocus`.

See B. Conrad, *Irreducible components of rigid spaces*, §2.1.
-/

public section

namespace TauCeti.ValuationSpectrum

open Set Topology Huber
open Huber.PairOfDefinition

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] [Algebra K A]

/-- If the zero locus of an ideal in a rigid affinoid has nonempty adic interior,
the ideal is contained in a minimal prime of the coordinate ring.
See B. Conrad, *Irreducible components of rigid spaces*, §2.1. -/
theorem exists_le_minimalPrime_of_nonempty_interior_spaZeroLocus
    (hA : IsTopologicallyFiniteType (algebraMap K A)) {I : Ideal A}
    (h : (interior (spaZeroLocus (powerBoundedSubring A) I)).Nonempty) :
    ∃ p ∈ minimalPrimes A, I ≤ p := by
  classical
  have : IsTateRing A := hA.isTateRing
  let := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace A := hA.completeSpace
  have : T2Space A := hA.t2Space
  have : IsStronglyNoetherian A := hA.isStronglyNoetherian
  obtain ⟨x, hx⟩ := h
  obtain ⟨V, hV, hxV, hVsub⟩ := (isTopologicalBasis_spaRationalFamily
    (powerBoundedSubring A)).exists_subset_of_mem_open hx isOpen_interior
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalFamily_iff.mp hV
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  have hd := P.hasDenominatorPower_of_isOpen_span (T : Set A) s (Localization.Away s) hT
  let B := ratLoc P T s hd
  have hf : algebraMap A B = P.toCompletionLoc T s (Localization.Away s) hd :=
    algebraMap_ratLoc P T s hd
  have : Module.Flat A B := by
    rw [← RingHom.flat_algebraMap_iff, hf]
    exact P.flat_toCompletionLoc T s (Localization.Away s) hd
  let algKB : Algebra K B := ((algebraMap A B).comp (algebraMap K A)).toAlgebra
  have hspan := Ideal.isOpen_of_isOpen_subideal
    (Ideal.span_mono (subset_insert s (T : Set A))) hT
  have hB : IsTopologicallyFiniteType (algebraMap K B) :=
    (hf.symm ▸ P.isTopologicallyFiniteType_toCompletionLoc T s (Localization.Away s) hd
      hspan).comp hA
  have : @ContinuousSMul K B algKB.toSMul _ _ :=
    continuousSMul_of_algebraMap _ _ hB.continuous
  let Aplus := powerBoundedSubring A
  let Bplus := completedPlusSubring P Aplus T s (Localization.Away s) hd
  let e := spaCompletedLocalizationHomeomorph P Aplus
    P.le_powerBoundedSubring T s (Localization.Away s) hd
  have hBplus : Bplus ≤ powerBoundedSubring B :=
    completedPlusSubring_le_powerBoundedSubring P Aplus
      (fun {_} ha ↦ mem_powerBoundedSubring.mp ha) T s (Localization.Away s) hd
  -- Vanishing on the rational open forces the extended ideal into the nilradical.
  have hmap : I.map (algebraMap A B) ≤ (⊥ : Ideal B).radical := by
    rw [← spaVanishingIdeal_spaZeroLocus hB, spaZeroLocus_bot,
      ← subset_spaZeroLocus_iff_le_spaVanishingIdeal]
    intro y _
    let z : spa Bplus := ⟨y.val, spa_antitone hBplus y.property⟩
    have hz := interior_subset (hVsub (e z).property)
    rw [mem_spaZeroLocus, spaCompletedLocalizationHomeomorph_apply,
      spaLocToRationalSubset_val, spaComapLoc_val, supp_comap] at hz
    rw [mem_spaZeroLocus, Ideal.map_le_iff_le_comap]
    rw [hf]
    exact hz
  let y := e.symm ⟨x, hxV⟩
  obtain ⟨q, hq, _⟩ := Ideal.exists_minimalPrimes_le (J := y.val.supp) bot_le
  refine ⟨q.under A, Ideal.under_mem_minimalPrimes hq, ?_⟩
  exact Ideal.map_le_iff_le_comap.mp (hmap.trans (hq.1.1.radical_le_iff.mpr bot_le))

/-- The zero locus of an ideal in a rigid affinoid is nowhere dense in the adic topology
if and only if the ideal is contained in no minimal prime of the coordinate ring.
See B. Conrad, *Irreducible components of rigid spaces*, §2.1. -/
theorem isNowhereDense_spaZeroLocus_iff
    (hA : IsTopologicallyFiniteType (algebraMap K A)) {I : Ideal A} :
    IsNowhereDense (spaZeroLocus (powerBoundedSubring A) I) ↔
      ∀ p ∈ minimalPrimes A, ¬ I ≤ p := by
  classical
  have : ContinuousSMul K A := continuousSMul_of_algebraMap _ _ hA.continuous
  have : IsNoetherianRing A := hA.isNoetherianRing
  have hclosed : @IsClosed _ (spaZariskiTopology (powerBoundedSubring A))
      (spaZeroLocus (powerBoundedSubring A) I) :=
    (isClosed_spaZariskiTopology_iff _).mpr ⟨I, rfl⟩
  rw [(hclosed.mono (le_spaZariskiTopology _)).isNowhereDense_iff]
  refine ⟨?_, fun h ↦ eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_⟩
  · intro h p hp hIp
    obtain ⟨g, hgp, hg⟩ :=
      Ideal.exists_notMem_forall_le_of_mem_minimalPrimes ⊥
        (minimalPrimes.finite_of_isNoetherianRing A) hp
    let U := (suppFun ∘ (Subtype.val : spa (powerBoundedSubring A) → Spv A)) ⁻¹'
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A))
    have hmem (x : spa (powerBoundedSubring A)) : x ∈ U ↔ g ∉ x.val.supp := by
      simp only [U, mem_preimage, Function.comp_apply, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
        suppFun_asIdeal]
    have hU : IsOpen U :=
      (PrimeSpectrum.basicOpen g).isOpen.preimage (continuous_suppFun.comp continuous_subtypeVal)
    have hsub : U ⊆ spaZeroLocus (powerBoundedSubring A) I :=
      fun x hx ↦ (mem_spaZeroLocus _).mpr (hIp.trans (hg _ inferInstance bot_le ((hmem x).mp hx)))
    have hUempty : U = ∅ := eq_empty_of_subset_empty (h ▸ interior_maximal hsub hU)
    have hgzero : g ∈ spaVanishingIdeal (powerBoundedSubring A) univ :=
      (mem_spaVanishingIdeal _).mpr fun x _ ↦ not_not.mp fun hx ↦
        notMem_empty x (hUempty ▸ (hmem x).mpr hx)
    rw [← spaZeroLocus_bot, spaVanishingIdeal_spaZeroLocus hA] at hgzero
    exact hgp (hp.1.1.radical_le_iff.mpr bot_le hgzero)
  · obtain ⟨p, hp, hIp⟩ :=
      exists_le_minimalPrime_of_nonempty_interior_spaZeroLocus hA ⟨x, hx⟩
    exact h p hp hIp

end TauCeti.ValuationSpectrum
