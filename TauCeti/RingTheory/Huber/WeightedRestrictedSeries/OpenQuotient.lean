/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Surjective

import TauCeti.Topology.Algebra.Nonarchimedean.Completion.Surjective

/-!
# Weighted restricted series preserve open quotient maps

An open quotient map `φ : A → B` of nonarchimedean rings, with `𝓝 (0 : A)` countably
generated, induces open quotient maps on weighted restricted series and their separated
completions when each target weight is the image of the corresponding source weight.

Surjectivity is `IsOpenQuotientMap.weightedMap_surjective`. For openness, a target series whose
coefficients lie in the image of a weighted neighbourhood lifts to a series in that
neighbourhood: a restricted lift can be corrected at its finitely many exceptional
coefficients using `IsWeightedRestricted.exists_coeff_mem_weightMul`.
Completion then preserves openness and surjectivity through
`AddMonoidHom.isOpenMap_completion` and `AddMonoidHom.surjective_completion`.

These coefficientwise open quotients let finite-type presentations be transported to
weighted restricted-series algebras in further variables.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §5.6 and Proposition 6.33.
-/

public section

open Filter Topology UniformSpace

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]

variable {B : Type*} [NonarchimedeanRing A] [CommRing B] [TopologicalSpace B]
  [NonarchimedeanRing B]

/-- An open quotient map induces an open quotient map on weighted restricted series when each
source weight maps onto the corresponding target weight. The source neighbourhood filter
must be countably generated. -/
theorem _root_.IsOpenQuotientMap.weightedMap [(𝓝 (0 : A)).IsCountablyGenerated]
    {φ : A →+* B} (hq : IsOpenQuotientMap φ)
    {T : Fin k → Set A} {S : Fin k → Set B} (hT : IsWeightFamily T) (hS : IsWeightFamily S)
    (hTS : ∀ i, φ '' T i = S i) :
    IsOpenQuotientMap (Huber.weightedMap hq.continuous hT hS (fun i ↦ (hTS i).subset)) := by
  set F := Huber.weightedMap hq.continuous hT hS (fun i ↦ (hTS i).subset)
  refine ⟨hq.weightedMap_surjective hT hS hTS, continuous_weightedMap .., ?_⟩
  refine IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr <|
    ((hasBasis_nhds_zero_weightedTopology hT).map F).ge_iff.mpr fun U _ ↦ ?_
  let V : OpenAddSubgroup B :=
    { U.toAddSubgroup.map (φ : A →+ B) with
      isOpen' := hq.isOpenMap _ U.isOpen }
  refine Filter.mem_of_superset
    ((hasBasis_nhds_zero_weightedTopology hS).mem_of_mem (i := V) trivial) fun g hg ↦ ?_
  -- Equality of the weighted subgroup images supplies a preimage for every coefficient.
  have hgU : ∀ ν, ∃ u ∈ weightMul T ν U.toAddSubgroup,
      φ u = MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) B) := by
    intro ν
    apply (Set.mem_image (φ : A → B) (weightMul T ν U.toAddSubgroup : Set A) _).mp
    rw [φ.image_weightMul_of_image_eq hTS]
    exact mem_weightedNhd.mp hg ν
  choose u huU hu using hgU
  obtain ⟨L, hL⟩ := hq.weightedMap_surjective hT hS hTS g
  have hLφ (ν) : φ (MvPowerSeries.coeff ν (L : MvPowerSeries (Fin k) A)) =
      MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) B) := by
    simpa only [coe_weightedMap, MvPowerSeries.coeff_map] using
      congrArg (fun x : weightedRestrictedSubring S hS ↦
        MvPowerSeries.coeff ν (x : MvPowerSeries (Fin k) B)) hL
  -- Correct the restricted lift only at the finitely many coefficients outside the U bound.
  classical
  obtain ⟨L', hL', hL'U, hcoeff⟩ :=
    (mem_weightedRestrictedSubring.mp L.2).exists_coeff_mem_weightMul U u huU
  have hL'φ : ∀ ν, φ (MvPowerSeries.coeff ν L') =
      MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) B) := by
    intro ν
    rw [hcoeff]
    split_ifs
    · exact hLφ ν
    · exact hu ν
  refine ⟨⟨L', mem_weightedRestrictedSubring.mpr hL'⟩,
    mem_weightedNhd.mpr hL'U, Subtype.ext ?_⟩
  ext ν
  simpa only [F, coe_weightedMap, MvPowerSeries.coeff_map] using hL'φ ν

/-- An open quotient map induces an open quotient map on completed weighted restricted-series
algebras with image weights, when the source neighbourhood filter is countably generated. -/
theorem _root_.IsOpenQuotientMap.weightedMapCompletion
    [(𝓝 (0 : A)).IsCountablyGenerated] {φ : A →+* B} (hq : IsOpenQuotientMap φ)
    {T : Fin k → Set A} {S : Fin k → Set B} (hT : IsWeightFamily T) (hS : IsWeightFamily S)
    (hTS : ∀ i, φ '' T i = S i) :
    IsOpenQuotientMap (Huber.weightedMapCompletion hq.continuous hT hS
      (fun i ↦ (hTS i).subset)) := by
  have hF := hq.weightedMap hT hS hTS
  set F := Huber.weightedMap hq.continuous hT hS (fun i ↦ (hTS i).subset)
  -- The completed ring map is the completion of the additive coefficientwise map.
  have heq : ⇑(Huber.weightedMapCompletion hq.continuous hT hS (fun i ↦ (hTS i).subset)) =
      ⇑(F.toAddMonoidHom.completion hF.continuous) :=
    Completion.ext (continuous_weightedMapCompletion ..)
      (AddMonoidHom.continuous_completion _ _) fun a ↦ by simp [F]
  rw [heq]
  exact ⟨F.toAddMonoidHom.surjective_completion hF.continuous hF.surjective hF.isOpenMap,
    AddMonoidHom.continuous_completion _ _,
    F.toAddMonoidHom.isOpenMap_completion hF.continuous hF.isOpenMap⟩

end TauCeti.Huber
