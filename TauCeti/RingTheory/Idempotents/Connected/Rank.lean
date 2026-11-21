/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Rank
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum

import Mathlib.Algebra.Module.FinitePresentation
import TauCeti.RingTheory.Idempotents.Projective
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Connected prime spectra via constant stalk rank

Over a nontrivial commutative ring `R`, `Spec R` is connected if and only if every finitely
generated projective `R`-module has constant stalk rank. In particular, if every finitely generated
projective `R`-module is free, then `Spec R` is connected.

## Main results

* `TauCeti.connectedSpace_primeSpectrum_iff_forall_finite_projective_rankAtStalk_const`: `Spec R`
  is connected iff every finitely generated projective module has constant stalk rank.
* `TauCeti.connectedSpace_primeSpectrum_of_forall_free`: if every finitely generated projective
  module over a nontrivial commutative ring `R` is free, then `Spec R` is connected.
-/

public section

universe u

namespace TauCeti

/-- **Connectedness of `Spec R` via constant rank.** Over a nontrivial commutative ring `R`, the
prime spectrum is connected if and only if every finitely generated projective `R`-module has
constant stalk rank. -/
theorem connectedSpace_primeSpectrum_iff_forall_finite_projective_rankAtStalk_const
    (R : Type u) [CommRing R] [Nontrivial R] :
    ConnectedSpace (PrimeSpectrum R) ↔
      ∀ (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P],
        ∃ n : ℕ, ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) P p = n := by
  refine ⟨fun hconn P _ _ _ _ ↦ ?_, fun hconst ↦ ?_⟩
  · have := Module.finitePresentation_of_projective R P
    obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
    exact ⟨Module.rankAtStalk P p₀, fun p ↦
      (Module.isLocallyConstant_rankAtStalk (R := R) (M := P)).apply_eq_of_preconnectedSpace p p₀⟩
  · refine connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.2 fun e he ↦ ?_
    have : Module.Finite R (Ideal.span {e} : Ideal R) :=
      Module.Finite.iff_fg.2 (Submodule.fg_span_singleton e)
    have : Module.Projective R (Ideal.span {e} : Ideal R) := he.projective_span_singleton
    obtain ⟨n, hn⟩ := hconst (Ideal.span {e} : Ideal R)
    obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
    classical
    have hconst' (p : PrimeSpectrum R) :
        (if e ∈ p.asIdeal then 0 else 1) = (if e ∈ p₀.asIdeal then 0 else 1) := by
      rw [← he.rankAtStalk_span_singleton, ← he.rankAtStalk_span_singleton, hn p, hn p₀]
    by_cases hmem : e ∈ p₀.asIdeal
    · left; refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .zero ?_
      ext p; simpa [hmem] using hconst' p
    · right; refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .one ?_
      ext p; simpa [hmem] using hconst' p

/-- If `R` is nontrivial and every finitely generated projective `R`-module is free, then `Spec R`
is connected. -/
theorem connectedSpace_primeSpectrum_of_forall_free (R : Type u) [CommRing R] [Nontrivial R]
    (hfree : ∀ (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P]
      [Module.Projective R P], Module.Free R P) :
    ConnectedSpace (PrimeSpectrum R) :=
  (connectedSpace_primeSpectrum_iff_forall_finite_projective_rankAtStalk_const R).2
    fun P _ _ _ _ ↦
      have := hfree P
      ⟨Module.finrank R P, fun p ↦
        congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := P)) p⟩

end TauCeti
