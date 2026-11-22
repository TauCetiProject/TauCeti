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
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
  [Algebra Rₚ Sₚ] [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
  [Algebra.IsIntegral Rₚ Sₚ]

include Rₚ in
/-- For `Sₚ` integral over `Rₚ`, the maximal ideals of the semilocalization `Sₚ` of `S` over `p`
are the primes of `S` over `p`: `m ↦ m ∩ S`, with inverse `q ↦ q Sₚ`. -/
noncomputable def maximalSpectrumEquivPrimesOver : MaximalSpectrum Sₚ ≃ p.primesOver S where
  toFun m :=
    have := IsLocalization.AtPrime.isLocalRing Rₚ p
    have : m.asIdeal.LiesOver (maximalIdeal Rₚ) := (mem_primesOver_of_isPrime Rₚ Sₚ).2
    have := liesOver_comap_of_liesOver (S := S) p Rₚ m.asIdeal
    ⟨m.asIdeal.comap (algebraMap S Sₚ), inferInstance, inferInstance⟩
  invFun q :=
    have := IsLocalization.AtPrime.isLocalRing Rₚ p
    have := isPrime_map_of_liesOver S p Sₚ q.val
    have := liesOver_map_of_liesOver p Rₚ Sₚ q.val
    ⟨q.val.map (algebraMap S Sₚ),
      Ideal.IsMaximal.of_liesOver_isMaximal (q.val.map (algebraMap S Sₚ)) (maximalIdeal Rₚ)⟩
  left_inv m := MaximalSpectrum.ext <|
    IsLocalization.map_under (algebraMapSubmonoid S p.primeCompl) Sₚ m.asIdeal
  right_inv q := Subtype.ext <|
    IsLocalization.under_map_of_isPrime_disjoint _ Sₚ inferInstance
      (Ideal.disjoint_primeCompl_of_liesOver q.val p)

@[simp]
theorem coe_maximalSpectrumEquivPrimesOver_apply (m : MaximalSpectrum Sₚ) :
    (maximalSpectrumEquivPrimesOver p Rₚ Sₚ m).val = m.asIdeal.comap (algebraMap S Sₚ) :=
  (rfl)

@[simp]
theorem maximalSpectrumEquivPrimesOver_symm_apply_asIdeal (q : p.primesOver S) :
    ((maximalSpectrumEquivPrimesOver p Rₚ Sₚ).symm q).asIdeal = q.val.map (algebraMap S Sₚ) :=
  (rfl)

end IsLocalization.AtPrime
