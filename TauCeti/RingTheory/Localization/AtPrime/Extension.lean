/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.Localization.BaseChange

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

Suppose that among the ideals of `S` contracting into `p` there is a greatest one `q`, for
instance when `S` is a valuation ring and the kernel of `R → S` lies in `p`
(`Ideal.exists_isGreatest_comap_le`). Then `Sₚ` is the localization of `S` at `q`
(`IsLocalization.isLocalization_atPrime_of_isGreatest_comap_le`); in particular so is
`S ⊗[R] Rₚ` (`IsLocalization.isLocalization_atPrime_tensorProduct_of_isGreatest_comap_le`).
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

namespace IsLocalization

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {p : Ideal R} [p.IsPrime]
  {q : Ideal B} [q.IsPrime]

/-- Let `B` be an algebra over `R`, `p` a prime of `R` and `q` the greatest ideal of `B`
contracting into `p` (which is prime by `Ideal.isPrime_of_isGreatest_comap_le`). Then a
localization of `B` at the image of `R \ p` is a localization of `B` at `q`. -/
theorem isLocalization_atPrime_of_isGreatest_comap_le
    (hq : IsGreatest {J : Ideal B | J.comap (algebraMap R B) ≤ p} q) (S : Type*) [CommRing S]
    [Algebra B S] [IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) S] :
    IsLocalization.AtPrime S q := by
  refine of_le (Algebra.algebraMapSubmonoid B p.primeCompl) _
    (fun t ht htq ↦ Set.disjoint_left.mp (Ideal.disjoint_map_primeCompl_iff_comap_le.mpr hq.1)
      htq ht) fun w hw ↦ ?_
  -- Otherwise `w` lies in a maximal ideal of `S`, whose contraction to `B` is an ideal disjoint
  -- from the image of `R \ p`, hence contained in `q`.
  by_contra hu
  obtain ⟨M, hM, hwM⟩ := exists_max_ideal_of_mem_nonunits hu
  have hdisj := ((isPrime_iff_isPrime_disjoint (Algebra.algebraMapSubmonoid B p.primeCompl) S
    M).mp hM.isPrime).2.symm
  exact hw (hq.2 (Ideal.disjoint_map_primeCompl_iff_comap_le.mp hdisj) hwM)

/-- Let `B` be an algebra over `R`, `p` a prime of `R` and `q` the greatest ideal of `B`
contracting into `p`. Then `B ⊗[R] R_p` is a localization of `B` at `q`. -/
theorem isLocalization_atPrime_tensorProduct_of_isGreatest_comap_le
    (hq : IsGreatest {J : Ideal B | J.comap (algebraMap R B) ≤ p} q) :
    IsLocalization.AtPrime (TensorProduct R B (Localization.AtPrime p)) q :=
  isLocalization_atPrime_of_isGreatest_comap_le hq _

end IsLocalization
