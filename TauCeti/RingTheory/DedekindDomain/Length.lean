/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import TauCeti.RingTheory.Length.Localization
import Mathlib.RingTheory.DedekindDomain.Dvr
import TauCeti.RingTheory.Length

/-!
# Lengths of quotients of Dedekind domains

Let `J` be a nonzero ideal of a Dedekind domain `B`. This file reads the factorization of `J` off
lengths of quotients.

* For a prime `P` of `B`, the localization `B_P` is a discrete valuation ring (or the fraction
  field), and `length_{B_P} (B_P ⧸ J B_P)` is the exponent of `P` in the factorization of `J`.
* If `B` is integral over a local ring `A`, the local length formula of
  `Ideal.length_quotient_eq_finsum_length_localization` becomes
  `length_A (B ⧸ J) = Σ_m v_m(J) · length_A (B ⧸ m)`, the sum over the maximal ideals `m` of `B`,
  where `length_A (B ⧸ m)` is the residue degree `[κ(m) : κ(A)]`.

## Main results

* `Ideal.length_localization_quotient_map_eq_count_normalizedFactors`: for a nonzero ideal `J` and
  a prime `P` of a Dedekind domain, `length_{B_P} (B_P ⧸ J B_P)` is the multiplicity of `P` in the
  factorization of `J`. The proof adapts Mathlib's
  `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count` (the case `J = pB`).
* `Ideal.length_quotient_eq_finsum_count_normalizedFactors_mul`: over a local ring `A`,
  `length_A (B ⧸ J) = Σ_m v_m(J) · length_A (B ⧸ m)`.

## References

* W. Fulton, *Intersection Theory*, Appendix A.3.
-/

public section

namespace Ideal

open UniqueFactorizationMonoid

section Dedekind

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

/-- **The local length of a quotient of a Dedekind domain is a multiplicity.** For a nonzero ideal
`J` and a prime `P` of a Dedekind domain `B`, `B_P ⧸ J B_P` has length over `B_P` equal to the
multiplicity of `P` in the factorization of `J`. The proof adapts the one of Mathlib's
`Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count`, the case `J = pB`. -/
theorem length_localization_quotient_map_eq_count_normalizedFactors {J : Ideal B} (hJ : J ≠ ⊥)
    (P : Ideal B) [P.IsPrime] :
    Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ J.map (algebraMap B (Localization.AtPrime P))) =
      (normalizedFactors J).count P := by
  by_cases hJP : J ≤ P
  · have hP0 : P ≠ ⊥ := ne_bot_of_le_ne_bot hJ hJP
    have : P.IsMaximal := IsPrime.isMaximal ‹_› hP0
    have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0
      (Localization.AtPrime P)
    -- `J = P ^ v * Q` with `Q` prime to `P`, so `J B_P` is the `v`-th power of the maximal ideal.
    obtain ⟨Q, hPQ, hJQ⟩ := eq_prime_pow_mul_coprime hJ P
    have hQP : ¬ Q ≤ P := fun h ↦ IsMaximal.ne_top ‹_› (by rwa [sup_of_le_left h] at hPQ)
    have hmap : J.map (algebraMap B (Localization.AtPrime P)) =
        IsLocalRing.maximalIdeal _ ^ (normalizedFactors J).count P := by
      conv_lhs => rw [hJQ]
      rw [Ideal.map_mul, Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal,
        IsLocalization.AtPrime.map_eq_top_of_not_le _ hQP, mul_top]
    rw [hmap, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  · -- Away from the primes containing `J`, both sides vanish.
    have hcount : (normalizedFactors J).count P = 0 :=
      Multiset.count_eq_zero.2 fun h ↦ hJP (le_of_dvd (dvd_of_mem_normalizedFactors h))
    rw [hcount, Nat.cast_zero, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff]
    exact IsLocalization.AtPrime.map_eq_top_of_not_le _ hJP

/-- **The length of `B ⧸ J` over a local base, for a Dedekind domain `B`.** If the Dedekind domain
`B` is integral over a local ring `A` and `J ≠ ⊥`, then
`length_A (B ⧸ J) = Σ_m v_m(J) · length_A (B ⧸ m)`, the sum over the maximal ideals `m` of `B`,
where `v_m(J)` is the multiplicity of `m` in the factorization of `J` and `length_A (B ⧸ m)` is
the residue degree `[κ(m) : κ(A)]` read as a length. -/
theorem length_quotient_eq_finsum_count_normalizedFactors_mul {A : Type*} [CommRing A]
    [IsLocalRing A] [Algebra A B] [Algebra.IsIntegral A B] {J : Ideal B} (hJ : J ≠ ⊥) :
    Module.length A (B ⧸ J) =
      ∑ᶠ m : MaximalSpectrum B,
        (normalizedFactors J).count m.asIdeal * Module.length A (B ⧸ m.asIdeal) := by
  -- A nonzero ideal of a Dedekind domain has Artinian quotient.
  obtain ⟨x, hxJ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have : IsArtinian B (B ⧸ J) := (isFiniteLength_iff_isNoetherian_isArtinian.1
    (TauCeti.isFiniteLength_quotient_of_nonZeroDivisor_mem J hxJ
      (mem_nonZeroDivisors_of_ne_zero hx0))).2
  have : IsArtinianRing (B ⧸ J) := isArtinian_of_tower B inferInstance
  rw [length_quotient_eq_finsum_length_localization J]
  refine finsum_congr fun m ↦ ?_
  rw [length_localization_quotient_map_eq_count_normalizedFactors hJ,
    MaximalSpectrum.length_residueField_localization_eq]

end Dedekind

end Ideal
