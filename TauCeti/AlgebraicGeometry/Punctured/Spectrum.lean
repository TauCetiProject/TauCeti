/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Punctured spectra of local rings

The punctured spectrum is the complement of the closed point of a local spectrum. Studying
finite étale covers of it, as in purity of the branch locus, needs the puncture to be controlled
by finitely many basic opens, so that covers can be described and glued chart by chart.

## Main definitions

* `IsLocalRing.puncturedSpectrum`: the open subscheme `Spec R ∖ {𝔪}`.

## Main results

* `IsLocalRing.zeroLocus_eq_singleton_closedPoint`: a set generating an ideal with maximal radical
  vanishes exactly at the closed point.
* `IsLocalRing.puncturedSpectrum_eq_iSup_basicOpen`: if some set `s` generates an ideal whose
  radical is the maximal ideal, the puncture is the union of the basic opens `D(x)` for `x ∈ s`.
* `IsLocalRing.isCompact_puncturedSpectrum`: the puncture is quasi-compact whenever the maximal
  ideal is the radical of a finitely generated ideal.
* `IsLocalRing.isCompact_puncturedSpectrum_of_fg_maximalIdeal`: the special case of a finitely
  generated maximal ideal, in particular of a Noetherian local ring.

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

/-- The points of the punctured spectrum are those of `Spec R` other than the closed point. -/
theorem coe_puncturedSpectrum :
    (puncturedSpectrum R).1 = ({IsLocalRing.closedPoint R}ᶜ : Set (PrimeSpectrum R)) := by
  unfold puncturedSpectrum
  rfl

/-- A point lies in the punctured spectrum exactly when it differs from the closed point. -/
@[simp]
theorem mem_puncturedSpectrum_iff (x : PrimeSpectrum R) :
    x ∈ puncturedSpectrum R ↔ x ≠ IsLocalRing.closedPoint R := by
  -- Membership reduces to the complement in the underlying prime spectrum.
  change x ∈ ({IsLocalRing.closedPoint R}ᶜ : Set (PrimeSpectrum R)) ↔ _
  simp

/-- The deleted closed point lies outside the punctured spectrum. -/
theorem closedPoint_notMem_puncturedSpectrum :
    IsLocalRing.closedPoint R ∉ puncturedSpectrum R := by
  simp

/-- A set whose generated ideal has maximal radical vanishes exactly at the closed point. -/
theorem zeroLocus_eq_singleton_closedPoint {s : Set R}
    (hs : (Ideal.span s).radical = IsLocalRing.maximalIdeal R) :
    PrimeSpectrum.zeroLocus s = {IsLocalRing.closedPoint R} := by
  rw [← PrimeSpectrum.zeroLocus_span, ← PrimeSpectrum.zeroLocus_radical, hs]
  exact PrimeSpectrum.zeroLocus_eq_singleton (IsLocalRing.maximalIdeal R)

/-- The punctured spectrum is the union of basic opens when their generators have maximal
radical. -/
theorem puncturedSpectrum_eq_iSup_basicOpen {s : Set R}
    (hs : (Ideal.span s).radical = IsLocalRing.maximalIdeal R) :
    puncturedSpectrum R = ⨆ x : s, PrimeSpectrum.basicOpen x.1 := by
  have key : ({IsLocalRing.closedPoint R}ᶜ : Set (PrimeSpectrum R)) =
      ⋃ x : s, (PrimeSpectrum.basicOpen x.1 : Set (PrimeSpectrum R)) := by
    rw [← zeroLocus_eq_singleton_closedPoint R hs]
    ext p
    simp [PrimeSpectrum.mem_zeroLocus, Set.subset_def]
  -- Both sides are opens of the definitionally identical spaces `Spec (.of R)` and
  -- `PrimeSpectrum R`; this exposes the latter to use the basic-open API.
  change (show TopologicalSpace.Opens (PrimeSpectrum R) from puncturedSpectrum R) =
    ⨆ x : s, PrimeSpectrum.basicOpen x.1
  apply SetLike.ext'
  rw [TopologicalSpace.Opens.coe_iSup]
  exact (coe_puncturedSpectrum R).trans key

/-- The punctured spectrum is quasi-compact when the maximal ideal is the radical of a finitely
generated ideal. -/
theorem isCompact_puncturedSpectrum {J : Ideal R} (hfg : J.FG)
    (hrad : J.radical = IsLocalRing.maximalIdeal R) :
    IsCompact (puncturedSpectrum R).1 := by
  have h := (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg hfg).isCompact
  rw [zeroLocus_eq_singleton_closedPoint R (s := (J : Set R)) (by rwa [Ideal.span_eq])] at h
  exact h

/-- A finitely generated maximal ideal gives a quasi-compact punctured spectrum, including
the case of a Noetherian local ring. -/
theorem isCompact_puncturedSpectrum_of_fg_maximalIdeal
    (hfg : (IsLocalRing.maximalIdeal R).FG) :
    IsCompact (puncturedSpectrum R).1 :=
  isCompact_puncturedSpectrum R hfg (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical

end IsLocalRing
