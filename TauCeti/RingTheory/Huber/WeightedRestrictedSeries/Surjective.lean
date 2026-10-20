/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.FirstCountable
import Mathlib.Data.Finsupp.Encodable
import TauCeti.Order.Filter.Cofinite.Lift

/-!
# Weighted restricted series lift along an open surjection

A continuous open surjection `φ : A → B` of nonarchimedean rings whose source has
countably generated `𝓝 0` induces a surjection on weighted restricted series when the target
weights are the images of the source weights.

The coefficients can be lifted subject to their index-dependent weighted neighbourhoods.
`TauCeti.exists_lift_eventually_mem_cofinite` supplies the diagonal choice, so one family of
lifts satisfies every weighted neighbourhood bound eventually. For each bound, the finitely
many coefficients outside the target weighted additive subgroup are lifted arbitrarily.

The kernel of the induced map is coefficientwise (`TauCeti.Huber.mem_ker_weightedMap_iff`), and
every series in the extension `J · A⟨X⟩_T` of an ideal `J` has its coefficients in `J`
(`Ideal.coeff_mem_of_mem_map_weightedC`).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §5.6 and Proposition 6.33.

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`,
`projects/AdicSpaces/Adic spaces/RestrictedModule.lean`, has the corresponding statement for
modules in one variable, `restrictedModule_map_surjective`, with both sides assumed Hausdorff.
This version treats weighted multivariate series. Nothing was copied.

The proof shares `TauCeti.exists_lift_eventually_mem_cofinite` with
`TauCeti.exists_lift_tendsto_cofinite_nhds`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]

/-- A continuous surjection carrying zero neighbourhoods onto zero neighbourhoods induces a
surjection on weighted restricted series when it maps each source weight onto the target weight.
Only the source neighbourhood filter needs to be countably generated. -/
theorem weightedMap_surjective [(𝓝 (0 : A)).IsCountablyGenerated] {φ : A →+* B}
    (hφ : Continuous φ) (hsurj : Function.Surjective φ)
    (hnhds : 𝓝 (0 : B) ≤ Filter.map φ (𝓝 (0 : A)))
    {T : Fin k → Set A} {S : Fin k → Set B} (hT : IsWeightFamily T) (hS : IsWeightFamily S)
    (hTS : ∀ i, φ '' T i = S i) :
    Function.Surjective (weightedMap hφ hT hS (fun i ↦ (hTS i).subset)) := by
  intro g
  have hopen : IsOpenMap φ := IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr hnhds
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup (G := A)
  let W (n : ℕ) : OpenAddSubgroup B :=
    { (V n).toAddSubgroup.map (φ : A →+ B) with
      isOpen' := hopen _ (V n).isOpen }
  have hmap (ν : Fin k →₀ ℕ) (n : ℕ) :
      φ '' (weightMul T ν (V n).toAddSubgroup : Set A) =
        (weightMul S ν (W n).toAddSubgroup : Set B) :=
    φ.image_weightMul_of_image_eq hTS ν (V n).toAddSubgroup
  obtain ⟨L, hL, hbound⟩ := exists_lift_eventually_mem_cofinite φ hsurj
    (fun n ν ↦ (weightMul T ν (V n).toAddSubgroup : Set A))
    (fun ν n m hnm ↦ weightMul_mono T ν (hV.antitone hnm))
    (fun ν ↦ MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) B))
    (fun n ↦ by
      simp only [hmap]
      exact (isWeightedRestricted_iff.mp (mem_weightedRestrictedSubring.mp g.2)) (W n))
  let f : MvPowerSeries (Fin k) A := L
  have hf : IsWeightedRestricted T f := by
    rw [isWeightedRestricted_iff]
    intro U
    obtain ⟨n, -, hn⟩ := hV.toHasBasis.mem_iff.mp (U.isOpen.mem_nhds U.zero_mem)
    filter_upwards [hbound n] with ν hν
    exact weightMul_mono T ν hn hν
  refine ⟨⟨f, mem_weightedRestrictedSubring.mpr hf⟩, Subtype.ext ?_⟩
  ext ν
  rw [coe_weightedMap, MvPowerSeries.coeff_map]
  simpa only [MvPowerSeries.coeff_apply f] using hL ν

/-- An open quotient map induces a surjection on weighted restricted series with image weights.
The source neighbourhood filter is required to be countably generated. -/
theorem _root_.IsOpenQuotientMap.weightedMap_surjective
    [(𝓝 (0 : A)).IsCountablyGenerated] {φ : A →+* B} (hq : IsOpenQuotientMap φ)
    {T : Fin k → Set A} {S : Fin k → Set B} (hT : IsWeightFamily T) (hS : IsWeightFamily S)
    (hTS : ∀ i, φ '' T i = S i) :
    Function.Surjective (weightedMap hq.continuous hT hS (fun i ↦ (hTS i).subset)) :=
  TauCeti.Huber.weightedMap_surjective hq.continuous hq.surjective
    (map_zero φ ▸ hq.isOpenMap.nhds_le 0) hT hS hTS

/-- **The kernel of `weightedMap` is coefficientwise**: a series is killed by the map induced by
`φ` exactly when each of its coefficients is killed by `φ`. -/
theorem mem_ker_weightedMap_iff {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {S : Fin k → Set B} {hT : IsWeightFamily T} {hS : IsWeightFamily S}
    {hTS : ∀ i, φ '' T i ⊆ S i} {f : weightedRestrictedSubring T hT} :
    f ∈ RingHom.ker (weightedMap hφ hT hS hTS) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ RingHom.ker φ := by
  simp only [RingHom.mem_ker]
  refine ⟨fun h ν ↦ ?_, fun h ↦ Subtype.ext <| MvPowerSeries.ext fun ν ↦ ?_⟩
  · simpa using congrArg (fun g : weightedRestrictedSubring S hS ↦
      MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) B)) h
  · simpa using h ν

end TauCeti.Huber

namespace Ideal

open TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **Series in `J · A⟨X⟩_T` have coefficients in `J`**, for any ideal `J` and any weights. -/
theorem coeff_mem_of_mem_map_weightedC {T : Fin k → Set A} {hT : IsWeightFamily T}
    {J : Ideal A} {f : weightedRestrictedSubring T hT} (hf : f ∈ J.map (weightedC T hT))
    (ν : Fin k →₀ ℕ) : MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ J := by
  have hle : J.map (weightedC T hT) ≤ (RingHom.ker
      (MvPowerSeries.map (Quotient.mk J))).comap (weightedRestrictedSubring T hT).subtype :=
    map_le_iff_le_comap.mpr fun a ha ↦ by
      simp [RingHom.mem_ker, Quotient.eq_zero_iff_mem.mpr ha]
  simpa [Quotient.eq_zero_iff_mem] using
    congrArg (MvPowerSeries.coeff ν) (RingHom.mem_ker.mp (hle hf))

end Ideal

end
