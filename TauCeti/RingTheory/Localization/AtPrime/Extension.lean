/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Extension

/-!
# Maximal ideals of the semilocalization over a prime

Let `S` be an `R`-algebra, `p` a prime ideal of `R`, `Rₚ` the localization of `R` at `p` and `Sₚ`
the localization of `S` at the image of `R \ p`. When `Sₚ` is integral over `Rₚ`, the maximal ideals
of `Sₚ` are the primes of `S` over `p`: `m ↦ m ∩ S`, with inverse `q ↦ q Sₚ`
(`IsLocalization.AtPrime.maximalSpectrumEquivPrimesOver`). Mathlib's
`IsDedekindDomain.primesOverEquivPrimesOver` is the same bijection for Dedekind domains, with the
maximal ideals of `Sₚ` described as the primes over the maximal ideal of `Rₚ`.

For `S` finite over `R`, `Sₚ` is the semilocal ring of `S` over `p`, and this is the
correspondence between its maximal ideals and the points of the fibre over `p`.
-/

public section

open Algebra Ideal IsLocalRing

namespace IsLocalization.AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
  [Algebra Rₚ Sₚ] [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
  [Algebra.IsIntegral Rₚ Sₚ]

include Rₚ in
/-- For `Sₚ` integral over `Rₚ`, the maximal ideals of the semilocalization `Sₚ` of `S` over `p`
are the primes of `S` over `p`: `m ↦ m ∩ S`, with inverse `q ↦ q Sₚ`. -/
noncomputable def maximalSpectrumEquivPrimesOver : MaximalSpectrum Sₚ ≃ p.primesOver S where
  toFun m :=
    have : m.asIdeal.LiesOver (maximalIdeal Rₚ) := (mem_primesOver_of_isPrime Rₚ Sₚ).2
    have := liesOver_comap_of_liesOver (S := S) p Rₚ m.asIdeal
    ⟨m.asIdeal.comap (algebraMap S Sₚ), inferInstance, inferInstance⟩
  invFun q :=
    have := q.2.1
    have := q.2.2
    have hd := Ideal.disjoint_primeCompl_of_liesOver q.1 p
    have : (q.1.map (algebraMap S Sₚ)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ Sₚ q.1 inferInstance hd
    -- `q Sₚ` lies over the maximal ideal of `Rₚ`, since both contract to `p` in `R`.
    have hR : ((q.1.map (algebraMap S Sₚ)).under Rₚ).under R = p := by
      rw [Ideal.under_under, ← Ideal.under_under (B := S),
        IsLocalization.under_map_of_isPrime_disjoint _ Sₚ inferInstance hd, ← q.1.over_def p]
    have : (q.1.map (algebraMap S Sₚ)).LiesOver (maximalIdeal Rₚ) := ⟨by
      refine le_antisymm ?_ (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
      rw [← IsLocalization.under_le_under_iff p.primeCompl Rₚ, hR,
        IsLocalization.AtPrime.under_maximalIdeal Rₚ p]⟩
    ⟨q.1.map (algebraMap S Sₚ),
      Ideal.IsMaximal.of_liesOver_isMaximal (q.1.map (algebraMap S Sₚ)) (maximalIdeal Rₚ)⟩
  left_inv m := MaximalSpectrum.ext <|
    IsLocalization.map_under (algebraMapSubmonoid S p.primeCompl) Sₚ m.asIdeal
  right_inv q := Subtype.ext <| by
    have := q.2.1
    have := q.2.2
    exact IsLocalization.under_map_of_isPrime_disjoint _ Sₚ inferInstance
      (Ideal.disjoint_primeCompl_of_liesOver q.1 p)

@[simp]
theorem coe_maximalSpectrumEquivPrimesOver_apply (m : MaximalSpectrum Sₚ) :
    (maximalSpectrumEquivPrimesOver p Rₚ Sₚ m).1 = m.asIdeal.comap (algebraMap S Sₚ) :=
  (rfl)

@[simp]
theorem maximalSpectrumEquivPrimesOver_symm_apply_asIdeal (q : p.primesOver S) :
    ((maximalSpectrumEquivPrimesOver p Rₚ Sₚ).symm q).asIdeal = q.1.map (algebraMap S Sₚ) :=
  (rfl)

end IsLocalization.AtPrime
