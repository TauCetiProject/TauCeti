/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Japanese
public import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Quasi-finite extensions of Japanese domains

A domain that is a quasi-finite, finite-type extension of a Japanese domain is Japanese
(Stacks, Lemma 10.161.5 (032I)). By the algebraic Zariski main theorem, every prime of the
extension `S` avoids some `r` such that `S[1/r]` is the localization at `r` of a subalgebra
`S'` of `S` that is finite over `R`. The finite extension domain `S'` is Japanese, hence so are
its localization and `S[1/r]`, and being Japanese is local on `Spec S`.

The Stacks statement assumes `R` Noetherian; the argument here does not use it, since the finite
case `TauCeti.Ring.IsJapanese.of_finite` and Mathlib's Zariski main theorem need no Noetherian
hypothesis.

## Main results

* `TauCeti.Ring.IsJapanese.of_quasiFinite`: a quasi-finite finite-type extension domain of a
  Japanese domain is Japanese.

## References

* [Stacks Project, Lemma 10.161.5 (032I)](https://stacks.math.columbia.edu/tag/032I)
* [Stacks Project, Theorem 10.123.12 (00Q9)](https://stacks.math.columbia.edu/tag/00Q9), Zariski's
  main theorem.
-/

public section

universe u v

namespace TauCeti.Ring

variable {R : Type u} [CommRing R] [IsDomain R]

variable (R) in
/-- **A quasi-finite extension domain of a Japanese domain is Japanese.** If `R ⊆ S` is an
injective, finite-type and quasi-finite map of domains and `R` is Japanese, then `S` is Japanese.
Stacks, Lemma 10.161.5 (032I), without its Noetherian hypothesis. -/
theorem IsJapanese.of_quasiFinite (S : Type v) [CommRing S] [IsDomain S] [Algebra R S]
    [FaithfulSMul R S] [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] [IsJapanese R] :
    IsJapanese S := by
  -- The elements `r` for which `S[1/r]` is a localization of a finite `R`-subalgebra of `S`.
  let t : Set S := {s | ∃ S' : Subalgebra R S, S'.toSubmodule.FG ∧
    ∃ r : S', S'.val.toRingHom r = s ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r)}
  refine IsJapanese.of_span_eq_top (t := t) ?_ ?_
  · -- Every maximal ideal avoids some element of `t`, by Zariski's main theorem.
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨S', hS', r, hrm, hbij⟩ :=
      Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := R) m
    exact hrm (by simpa using hle (Ideal.subset_span ⟨S', hS', r, rfl, hbij⟩))
  · rintro _ ⟨S', hS', r, rfl, hbij⟩ hdom
    have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
    have : FaithfulSMul R S' := .tower_bot R S' S
    have : IsJapanese S' := of_finite R S'
    let e := RingEquiv.ofBijective _ hbij
    have : IsDomain (Localization.Away r) := e.toMulEquiv.isDomain
    have : IsJapanese (Localization.Away r) :=
      isJapanese_of_isLocalization (Submonoid.powers r) (Localization.Away r)
    exact e.isJapanese

end TauCeti.Ring
