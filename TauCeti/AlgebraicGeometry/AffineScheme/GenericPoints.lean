/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import TauCeti.RingTheory.Spectrum.Prime.MinimalPrimes
public import TauCeti.Topology.Sober.GenericPoints

import Mathlib.Tactic.Choose

/-!
# Affine neighbourhoods through generic points

A finite set of generic points in a quasi-separated scheme has pairwise disjoint affine
neighbourhoods. One can also include any prescribed point in an affine open containing
that finite set. A quasi-compact quasi-separated scheme with finitely many irreducible
components therefore has a finite affine cover whose every member contains all generic
points. These covers enter the affine reduction in Chow's lemma.

## References

* The Stacks Project, Tag 0200, Step 1.
-/

public noncomputable section

universe u

open TopologicalSpace Topology
open scoped Function

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A generic point in an affine open corresponds to a minimal prime of its section ring. -/
lemma IsAffineOpen.primeIdealOf_mem_minimalPrimes {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ genericPoints X) (hxU : x ∈ U) :
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∈ minimalPrimes Γ(X, U) := by
  rw [← PrimeSpectrum.mem_genericPoints_iff]
  have hoe : IsOpenEmbedding hU.fromSpec.base := hU.fromSpec.isOpenEmbedding
  have h : hU.fromSpec.base ⁻¹' closure {x} ∈ irreducibleComponents (Spec Γ(X, U)) :=
    preimage_mem_irreducibleComponents hx hoe
      ⟨x, subset_closure rfl, by rw [hU.range_fromSpec]; exact hxU⟩
  rw [hoe.isOpenMap.preimage_closure_eq_closure_preimage hoe.continuous] at h
  have : hU.fromSpec.base ⁻¹' {x} = {hU.primeIdealOf ⟨x, hxU⟩} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hU.fromSpec_primeIdealOf ⟨x, hxU⟩, fun y hy ↦ ?_⟩
    exact hoe.injective (hy.trans (hU.fromSpec_primeIdealOf ⟨x, hxU⟩).symm)
  rwa [this] at h

/-- Let `U` be an affine open of `X` and let `x ∈ U` be the generic point of an irreducible
component
of `X`. Any quasi-compact open `W ⊆ U` not containing `x` can be separated from `x` by a standard
open: there is `f ∈ Γ(X, U)` with `x ∈ D(f)` and `D(f) ∩ W = ∅`. -/
@[stacks 00EV]
lemma IsAffineOpen.exists_mem_basicOpen_and_disjoint {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ genericPoints X) (hxU : x ∈ U) {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W)
    (hWU : W ⊆ (U : Set X)) (hxW : x ∉ W) :
    ∃ f : Γ(X, U), x ∈ X.basicOpen f ∧ Disjoint (X.basicOpen f : Set X) W := by
  have hoe : IsOpenEmbedding hU.fromSpec.base := hU.fromSpec.isOpenEmbedding
  have hrange : Set.range hU.fromSpec.base = (U : Set X) := hU.range_fromSpec
  obtain ⟨f, hf, hdisj⟩ := PrimeSpectrum.exists_notMem_and_disjoint_basicOpen_of_mem_minimalPrimes
    (hU.primeIdealOf_mem_minimalPrimes hx hxU) (hWo.preimage hU.fromSpec.continuous)
    (hoe.isInducing.isCompact_preimage' hWc (hrange ▸ hWU))
    (by
      change hU.fromSpec.base (hU.primeIdealOf ⟨x, hxU⟩) ∉ W
      rw [hU.fromSpec_primeIdealOf]
      exact hxW)
  have hmem (y : Spec Γ(X, U)) :
      hU.fromSpec.base y ∈ X.basicOpen f ↔ y ∈ PrimeSpectrum.basicOpen f :=
    congr(y ∈ $(hU.fromSpec_preimage_basicOpen f)).to_iff
  refine ⟨f, ?_, Set.disjoint_left.mpr fun y hy hyW ↦ ?_⟩
  · have h := (hmem (hU.primeIdealOf ⟨x, hxU⟩)).mpr hf
    rwa [hU.fromSpec_primeIdealOf ⟨x, hxU⟩] at h
  · have hyU : y ∈ Set.range hU.fromSpec.base := by
      rw [hrange]; exact X.basicOpen_le f hy
    obtain ⟨z, rfl⟩ := hyU
    exact Set.disjoint_left.mp hdisj ((hmem z).mp hy) hyW

/-- **Disjoint affine neighbourhoods of generic points.** Let `X` be a quasi-separated scheme and
let
`points` be a finite set of generic points of irreducible components of `X`. Then there is a
family of pairwise disjoint affine opens `U x`, for `x ∈ points`, with `x ∈ U x`. -/
@[stacks 0200]
theorem exists_isAffineOpen_pairwise_disjoint [QuasiSeparatedSpace X] {points : Set X}
    (hsf : points.Finite) (hs : points ⊆ genericPoints X) :
    ∃ U : X → X.Opens, (∀ x ∈ points, IsAffineOpen (U x)) ∧ (∀ x ∈ points, x ∈ U x) ∧
      points.Pairwise (Disjoint on U) := by
  classical
  have hV : ∀ x ∈ points, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ ∀ y ∈ points, y ≠ x → y ∉ V := by
    intro x hx
    have hΩ : IsOpen ((⋃ y ∈ points \ {x}, closure ({y} : Set X))ᶜ) :=
      (hsf.sdiff.isClosed_biUnion fun y _ ↦ isClosed_closure).isOpen_compl
    have hxΩ : x ∈ (⟨_, hΩ⟩ : X.Opens) := by
      intro hmem
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨hys, hyx⟩ := Set.mem_sdiff_singleton.mp hy
      exact genericPoints.notMem_closure_of_ne (hs hx) (hs hys) (Ne.symm hyx) hxy
    obtain ⟨V, hVaff, hxV, hVsub⟩ := exists_isAffineOpen_mem_and_subset hxΩ
    refine ⟨V, hVaff, hxV, fun y hy hyx hyV ↦ hVsub hyV ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨y, Set.mem_sdiff_singleton.mpr ⟨hy, hyx⟩, subset_closure rfl⟩
  choose! V hVaff hVmem hVnot using hV
  have key : ∀ x ∈ points, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ V x ∧
      ∀ y ∈ points, y ≠ x → Disjoint U (V y) := by
    intro x hx
    set W : Set X := ⋃ y ∈ points \ {x}, ((V x : Set X) ∩ (V y : Set X))
    have hWo : IsOpen W := isOpen_biUnion fun y _ ↦ (V x).isOpen.inter (V y).isOpen
    have hWc : IsCompact W := hsf.sdiff.isCompact_biUnion fun y hy ↦
      QuasiSeparatedSpace.inter_isCompact _ _ (V x).isOpen (hVaff x hx).isCompact
        (V y).isOpen (hVaff y (Set.mem_sdiff_singleton.mp hy).1).isCompact
    have hWU : W ⊆ (V x : Set X) := Set.iUnion₂_subset fun y _ ↦ Set.inter_subset_left
    have hxW : x ∉ W := by
      intro hmem
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨hys, hyx⟩ := Set.mem_sdiff_singleton.mp hy
      exact hVnot y hys x hx (Ne.symm hyx) hxy.2
    obtain ⟨f, hf, hdisj⟩ := (hVaff x hx).exists_mem_basicOpen_and_disjoint (hs hx)
      (hVmem x hx) hWo hWc hWU hxW
    refine ⟨X.basicOpen f, (hVaff x hx).basicOpen f, hf, X.basicOpen_le f, fun y hy hyx ↦ ?_⟩
    rw [← Opens.coe_disjoint]
    refine Set.disjoint_left.mpr fun z hz hzy ↦ Set.disjoint_left.mp hdisj hz ?_
    exact Set.mem_iUnion₂.mpr ⟨y, Set.mem_sdiff_singleton.mpr ⟨hy, hyx⟩,
      ⟨X.basicOpen_le f hz, hzy⟩⟩
  choose! U hUaff hUmem hUle hUdisj using key
  exact ⟨U, hUaff, hUmem, fun x hx y hy hxy ↦
    (hUdisj x hx y hy (Ne.symm hxy)).mono_right (hUle y hy)⟩

/-- A finite set of generic points of irreducible components of a quasi-separated scheme is
contained
in an affine open: the disjoint union of the affine opens provided by
`AlgebraicGeometry.exists_isAffineOpen_pairwise_disjoint` is affine. -/
theorem exists_isAffineOpen_of_subset_genericPoints [QuasiSeparatedSpace X] {points : Set X}
    (hsf : points.Finite) (hs : points ⊆ genericPoints X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ points ⊆ (U : Set X) := by
  obtain ⟨U, hUaff, hUmem, hUdisj⟩ := exists_isAffineOpen_pairwise_disjoint hsf hs
  refine ⟨⨆ x ∈ points, U x, IsAffineOpen.biSup_of_disjoint hsf hUaff hUdisj, fun x hx ↦ ?_⟩
  exact Opens.mem_iSup.mpr ⟨x, Opens.mem_iSup.mpr ⟨hx, hUmem x hx⟩⟩

/-- **An affine open containing a point and all generic points.** Let `X` be a quasi-separated
scheme, let
`points` be a finite set of generic points of irreducible components of `X` and let `x : X`. Then
there is an affine open of `X` containing `x` and all points of `points`. -/
@[stacks 0200]
theorem exists_isAffineOpen_mem_of_subset_genericPoints [QuasiSeparatedSpace X] {points : Set X}
    (hsf : points.Finite) (hs : points ⊆ genericPoints X) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ points ⊆ (U : Set X) := by
  classical
  set t : Set X := {y ∈ points | x ∉ closure ({y} : Set X)}
  have htf : t.Finite := hsf.subset fun y hy ↦ hy.1
  have hts : t ⊆ genericPoints X := fun y hy ↦ hs hy.1
  have hΩ : IsOpen ((⋃ y ∈ t, closure ({y} : Set X))ᶜ) :=
    (htf.isClosed_biUnion fun y _ ↦ isClosed_closure).isOpen_compl
  have hxΩ : x ∈ (⟨_, hΩ⟩ : X.Opens) := by
    intro hmem
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hmem
    exact hy.2 hxy
  obtain ⟨W, hWaff, hxW, hWsub⟩ := exists_isAffineOpen_mem_and_subset hxΩ
  have hWt : ∀ y ∈ t, y ∉ W := fun y hy hyW ↦
    hWsub hyW (Set.mem_iUnion₂.mpr ⟨y, hy, subset_closure rfl⟩)
  have hWs : ∀ y ∈ points, y ∉ t → y ∈ W := by
    intro y hy hyt
    have hxy : x ∈ closure ({y} : Set X) := by
      by_contra h
      exact hyt ⟨hy, h⟩
    exact ((isGenericPoint_closure (x := y)).mem_open_set_iff W.isOpen).mpr ⟨x, hxy, hxW⟩
  obtain ⟨U, hUaff, hUmem, hUdisj⟩ := exists_isAffineOpen_pairwise_disjoint htf hts
  have key : ∀ y ∈ t, ∃ U' : X.Opens, IsAffineOpen U' ∧ y ∈ U' ∧ U' ≤ U y ∧ Disjoint U' W := by
    intro y hy
    obtain ⟨f, hf, hdisj⟩ := (hUaff y hy).exists_mem_basicOpen_and_disjoint (hts hy) (hUmem y hy)
      (W.isOpen.inter (U y).isOpen)
      (QuasiSeparatedSpace.inter_isCompact _ _ W.isOpen hWaff.isCompact (U y).isOpen
        (hUaff y hy).isCompact) Set.inter_subset_right (fun h ↦ hWt y hy h.1)
    refine ⟨X.basicOpen f, (hUaff y hy).basicOpen f, hf, X.basicOpen_le f, ?_⟩
    rw [← Opens.coe_disjoint]
    exact Set.disjoint_left.mpr fun z hz hzW ↦
      Set.disjoint_left.mp hdisj hz ⟨hzW, X.basicOpen_le f hz⟩
  choose! U' hU'aff hU'mem hU'le hU'disj using key
  refine ⟨W ⊔ ⨆ y ∈ t, U' y, ?_, Opens.mem_sup.mpr (.inl hxW), fun y hy ↦ ?_⟩
  · refine hWaff.sup_of_disjoint (IsAffineOpen.biSup_of_disjoint htf hU'aff
      fun y hy z hz hyz ↦ (hUdisj hy hz hyz).mono (hU'le y hy) (hU'le z hz)) ?_
    simp only [disjoint_iSup_iff]
    exact fun y hy ↦ (hU'disj y hy).symm
  · by_cases hyt : y ∈ t
    · exact Opens.mem_sup.mpr (.inr (Opens.mem_iSup.mpr ⟨y,
        Opens.mem_iSup.mpr ⟨hyt, hU'mem y hyt⟩⟩))
    · exact Opens.mem_sup.mpr (.inl (hWs y hy hyt))

/-- **Affine cover through the generic points.** A quasi-compact and quasi-separated scheme with
finitely many irreducible components admits a finite affine open cover each member of which
contains all the generic points of the irreducible components. -/
@[stacks 0200]
theorem exists_isAffineOpen_cover_genericPoints_subset [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : (irreducibleComponents X).Finite) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, genericPoints X ⊆ (U i : Set X)) ∧ ⨆ i, U i = ⊤ := by
  classical
  have h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ genericPoints X ⊆ (U : Set X) :=
    fun x ↦ exists_isAffineOpen_mem_of_subset_genericPoints (genericPoints.finite hX) le_rfl x
  choose U hUaff hUmem hUsub using h
  obtain ⟨s, hc⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ (U x : Set X))
    (fun x ↦ (U x).isOpen) fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hUmem x⟩
  refine ⟨s.card, fun i ↦ U (s.equivFin.symm i), fun i ↦ hUaff _, fun i ↦ hUsub _,
    eq_top_iff.mpr fun x _ ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hc (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨s.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end AlgebraicGeometry
