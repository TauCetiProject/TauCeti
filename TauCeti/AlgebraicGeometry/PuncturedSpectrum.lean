/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.RingTheory.LocalRing.Spectrum

/-!
# Punctured spectra of local rings

The punctured spectrum is the complement of the closed point of a local spectrum. Studying
finite étale covers of it, as in purity of the branch locus, needs the puncture to be controlled
by finitely many basic opens, so that covers can be described and glued chart by chart.

## Main definitions

* `TauCeti.IsLocalRing.puncturedSpectrum`: the open subscheme `Spec R ∖ {𝔪}`.

## Main results

* `TauCeti.IsLocalRing.mem_preimage_puncturedSpectrum_iff`: the primes of an `R`-algebra `B` in
  the preimage of the punctured spectrum are those not lying over `𝔪`.
* `TauCeti.IsLocalRing.puncturedSpectrum_eq_iSup_basicOpen`: if some set `s` generates an ideal
  whose radical is the maximal ideal, the puncture is the union of the basic opens `D(x)` for
  `x ∈ s`.
* `TauCeti.IsLocalRing.isCompact_puncturedSpectrum`: the puncture is quasi-compact whenever the
  maximal ideal is the radical of a finitely generated ideal.
* `TauCeti.IsLocalRing.isCompact_puncturedSpectrum_of_fg_maximalIdeal`: the special case of a
  finitely generated maximal ideal, in particular of a Noetherian local ring.
* `TauCeti.IsLocalRing.preimage_puncturedSpectrum`: for an algebra `A'` over `A` whose closed
  point is the only point over the closed point of `Spec A`, the punctured spectrum of `A'` is the
  preimage of that of `A`.

## References

* The Stacks Project, Section 58.20 (Tag 0BM7).
* Ported from Taylor Dupuy, Thomas Tucker and Zhuoran Wang, pcfawd-formalization at commit
  `9a20b3f` (Apache 2.0), `Pcf/Stacks/Purity/PuncturedSpectrum.lean`.
-/

public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace TauCeti.IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The complement of the closed point in the spectrum of a local ring. -/
@[stacks 0BM7 "the punctured spectrum"]
def puncturedSpectrum : (Spec (.of R)).Opens :=
  -- `Spec (.of R)` has `PrimeSpectrum R` as its underlying topological space by definition.
  show TopologicalSpace.Opens (PrimeSpectrum R) from
    { carrier := {IsLocalRing.closedPoint R}ᶜ
      is_open' := (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl }

/-- The points of the punctured spectrum are those of `Spec R` other than the closed point. -/
@[simp]
theorem coe_puncturedSpectrum :
    (SetLike.coe (puncturedSpectrum R) : Set (PrimeSpectrum R)) = {IsLocalRing.closedPoint R}ᶜ := by
  unfold puncturedSpectrum
  rfl

/-- A point lies in the punctured spectrum exactly when it differs from the closed point. -/
@[simp]
theorem mem_puncturedSpectrum_iff (x : PrimeSpectrum R) :
    x ∈ puncturedSpectrum R ↔ x ≠ IsLocalRing.closedPoint R := by
  -- `Spec (.of R)` and `PrimeSpectrum R` are only definitionally equal, so `rw` with
  -- `coe_puncturedSpectrum` cannot see the membership; `change` crosses that boundary.
  change x ∈ ({IsLocalRing.closedPoint R}ᶜ : Set (PrimeSpectrum R)) ↔ _
  simp

/-- A prime of an `R`-algebra `B` lies in the preimage of the punctured spectrum of `R` exactly
when it does not lie over the maximal ideal of `R`. -/
@[simp]
theorem mem_preimage_puncturedSpectrum_iff {B : Type u} [CommRing B] [Algebra R B]
    (q : PrimeSpectrum B) :
    q ∈ Spec.map (CommRingCat.ofHom (algebraMap R B)) ⁻¹ᵁ puncturedSpectrum R ↔
      q.asIdeal.under R ≠ IsLocalRing.maximalIdeal R := by
  -- The base map of `Spec.map` is `PrimeSpectrum.comap`, by definition.
  change PrimeSpectrum.comap (algebraMap R B) q ∈ puncturedSpectrum R ↔ _
  rw [mem_puncturedSpectrum_iff, Ne, Ne, PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal]
  -- The ideal of `closedPoint R` is `maximalIdeal R`, by definition.
  rfl

/-- The deleted closed point lies outside the punctured spectrum. -/
theorem closedPoint_notMem_puncturedSpectrum :
    IsLocalRing.closedPoint R ∉ puncturedSpectrum R := by
  simp

/-- The punctured spectrum is the union of basic opens when their generators have maximal
radical. -/
theorem puncturedSpectrum_eq_iSup_basicOpen {s : Set R}
    (hs : (Ideal.span s).radical = IsLocalRing.maximalIdeal R) :
    puncturedSpectrum R = ⨆ x : s, PrimeSpectrum.basicOpen x.1 := by
  have key : ({IsLocalRing.closedPoint R}ᶜ : Set (PrimeSpectrum R)) =
      ⋃ x : s, (PrimeSpectrum.basicOpen x.1 : Set (PrimeSpectrum R)) := by
    rw [← zeroLocus_eq_singleton_closedPoint hs]
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
    IsCompact (SetLike.coe (puncturedSpectrum R) : Set (PrimeSpectrum R)) := by
  have h := (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg hfg).isCompact
  have hs : (Ideal.span (J : Set R)).radical = IsLocalRing.maximalIdeal R := by
    rwa [Ideal.span_eq]
  rw [zeroLocus_eq_singleton_closedPoint hs] at h
  -- The carrier of the puncture is the complement of the closed point.
  simpa using h

/-- A finitely generated maximal ideal gives a quasi-compact punctured spectrum, including
the case of a Noetherian local ring. -/
theorem isCompact_puncturedSpectrum_of_fg_maximalIdeal
    (hfg : (IsLocalRing.maximalIdeal R).FG) :
    IsCompact (SetLike.coe (puncturedSpectrum R) : Set (PrimeSpectrum R)) :=
  isCompact_puncturedSpectrum R hfg (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical

section

variable {A A' : Type u} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
  [Algebra A A']

/-- If the closed point of `Spec A'` is the only point over the closed point of `Spec A`, the
punctured spectrum of `A'` is the preimage of the punctured spectrum of `A`. -/
theorem preimage_puncturedSpectrum
    (h : ((IsLocalRing.maximalIdeal A).map (algebraMap A A')).radical =
      IsLocalRing.maximalIdeal A') :
    Spec.map (CommRingCat.ofHom (algebraMap A A')) ⁻¹ᵁ puncturedSpectrum A =
      puncturedSpectrum A' := by
  have : IsLocalHom (algebraMap A A') :=
    ((IsLocalRing.local_hom_tfae (algebraMap A A')).out 1 3).mpr (h ▸ Ideal.le_radical)
  -- A point `x` of `Spec A'` maps to the point `PrimeSpectrum.comap (algebraMap A A') x`.
  have key (x : PrimeSpectrum A') : PrimeSpectrum.comap (algebraMap A A') x =
      IsLocalRing.closedPoint A ↔ x = IsLocalRing.closedPoint A' := by
    refine ⟨fun hx ↦ PrimeSpectrum.ext (le_antisymm
      (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)
      (?_ : IsLocalRing.maximalIdeal A' ≤ x.asIdeal)),
      fun hx ↦ hx ▸ IsLocalRing.comap_closedPoint _⟩
    rw [← h, x.isPrime.radical_le_iff, Ideal.map_le_iff_le_comap]
    exact (congrArg PrimeSpectrum.asIdeal hx).ge
  ext x
  exact ((mem_puncturedSpectrum_iff A _).trans (key x).not).trans
    (mem_puncturedSpectrum_iff A' x).symm

end

end TauCeti.IsLocalRing
