/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.Module.SpanRank

/-!
# Punctured spectra of local rings

The punctured spectrum is the complement of the closed point of a local spectrum.

## References

* The Stacks Project, Section 58.20 (Tag 0BM7).
* Ported from Taylor Dupuy, Thomas Tucker and Zhuoran Wang, pcfawd-formalization at commit
  `9a20b3f` (Apache 2.0), `Pcf/Stacks/Purity/PuncturedSpectrum.lean`.
-/

public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The complement of the closed point in the spectrum of a local ring. -/
@[stacks 0BM7 "the punctured spectrum"]
def puncturedSpectrum : (Spec (.of R)).Opens :=
  -- `Spec (.of R)` has `PrimeSpectrum R` as its underlying topological space by definition.
  show TopologicalSpace.Opens (PrimeSpectrum R) from
    { carrier := {IsLocalRing.closedPoint R}ᶜ
      is_open' := (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl }

/-- A point lies in the punctured spectrum exactly when it differs from the closed point. -/
@[simp]
theorem mem_puncturedSpectrum_iff (x : PrimeSpectrum R) :
    x ∈ puncturedSpectrum R ↔ x ≠ IsLocalRing.closedPoint R := by
  -- Membership reduces to the complement in the underlying prime spectrum.
  change x ∉ ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) ↔ _
  simp

/-- The deleted closed point lies outside the punctured spectrum. -/
theorem closedPoint_notMem_puncturedSpectrum :
    IsLocalRing.closedPoint R ∉ puncturedSpectrum R := by
  simp

/-- The punctured spectrum is the union of basic opens when their generators have maximal
radical. -/
theorem puncturedSpectrum_eq_iSup_basicOpen {s : Set R}
    (hs : (Ideal.span s).radical = IsLocalRing.maximalIdeal R) :
    puncturedSpectrum R = ⨆ x : s, PrimeSpectrum.basicOpen x.1 := by
  -- Both sides are opens of the definitionally identical spaces `Spec (.of R)` and
  -- `PrimeSpectrum R`; this exposes the latter to use the basic-open API.
  change (show TopologicalSpace.Opens (PrimeSpectrum R) from puncturedSpectrum R) =
    ⨆ x : s, PrimeSpectrum.basicOpen x.1
  apply SetLike.ext'
  rw [TopologicalSpace.Opens.coe_iSup]
  ext p
  simp only [Set.mem_iUnion, SetLike.mem_coe, puncturedSpectrum,
    PrimeSpectrum.mem_basicOpen]
  constructor
  · intro hp
    by_contra h
    push Not at h
    have hs_le : s ⊆ p.asIdeal := fun x hx ↦ h ⟨x, hx⟩
    have hm_le : IsLocalRing.maximalIdeal R ≤ p.asIdeal := by
      rw [← hs]
      exact p.isPrime.radical_le_iff.mpr (Ideal.span_le.mpr hs_le)
    have hp_le : p.asIdeal ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal p.isPrime.ne_top
    apply hp
    apply PrimeSpectrum.ext
    exact le_antisymm hp_le hm_le
  · rintro ⟨x, hx⟩ hp
    have hxm : x.1 ∈ IsLocalRing.maximalIdeal R := by
      rw [← hs]
      exact Ideal.le_radical (Ideal.subset_span x.2)
    apply hx
    rw [hp]
    exact hxm

/-- The punctured spectrum is quasi-compact when the maximal ideal is the radical of a finitely
generated ideal. -/
theorem isCompact_puncturedSpectrum {J : Ideal R} (hfg : J.FG)
    (hrad : J.radical = IsLocalRing.maximalIdeal R) :
    IsCompact (puncturedSpectrum R).1 := by
  obtain ⟨s, _, hs⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have hs' : (Ideal.span (s : Set R)).radical = IsLocalRing.maximalIdeal R :=
    (congrArg Ideal.radical hs).trans hrad
  rw [puncturedSpectrum_eq_iSup_basicOpen R hs']
  -- The open of `Spec (.of R)` is an open of `PrimeSpectrum R` by definition.
  change IsCompact ((⨆ x : (s : Set R), PrimeSpectrum.basicOpen x.1 :
    TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R))
  simpa only [TopologicalSpace.Opens.coe_iSup] using
    (isCompact_iUnion fun x : (s : Set R) ↦ PrimeSpectrum.isCompact_basicOpen x.1)

/-- A finitely generated maximal ideal gives a quasi-compact punctured spectrum, including
the case of a Noetherian local ring. -/
theorem isCompact_puncturedSpectrum_of_fg_maximalIdeal
    (hfg : (IsLocalRing.maximalIdeal R).FG) :
    IsCompact (puncturedSpectrum R).1 :=
  isCompact_puncturedSpectrum R hfg (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical

end IsLocalRing
