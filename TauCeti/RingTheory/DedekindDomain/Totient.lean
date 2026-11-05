/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Group.Pi.Units
import TauCeti.RingTheory.Ideal.Quotient.Totient

/-!
# Euler's totient for ideals of a Dedekind domain

For an ideal `I` of an infinite Dedekind domain `R` whose quotient `R ⧸ I` is finite, this file
counts the units of `R ⧸ I` in terms of the absolute norm `N = Ideal.absNorm`:
`#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∣ I} (1 - (N 𝔭)⁻¹)`, the product running over the height-one primes
dividing `I`. For `R = ℤ` this is Euler's product formula for the totient.

The set of primes dividing `I` is passed as a `Finset` `S` together with the characterisation
`∀ v, v ∈ S ↔ v.asIdeal ∣ I`, so that any concrete description of the prime divisors of `I` can
be used directly.

The computation is local: by the Chinese remainder theorem `(R ⧸ I)ˣ` splits into the units of the
quotients `R ⧸ 𝔭 ^ e`, which are counted by `Ideal.card_units_quotient_pow_mul_card_quotient`
for a maximal ideal of an arbitrary commutative ring.

## Main results

* `Ideal.card_units_quotient_mul_prod_absNorm`: `#(R ⧸ I)ˣ · ∏_{𝔭 ∈ S} N 𝔭 = N I · ∏_{𝔭 ∈ S}
  (N 𝔭 - 1)` in `ℕ`, the analogue of `Nat.totient_mul_prod_primeFactors`.
* `Ideal.card_units_quotient_eq_absNorm_mul_prod`: `#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∈ S} (1 - (N 𝔭)⁻¹)`
  in any field of characteristic zero, the analogue of `Nat.totient_eq_mul_prod_factors`.
-/

public section

open IsDedekindDomain

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Infinite R]

private theorem card_units_quotient_mul_prod_absNorm_of_prod_eq (I : Ideal R)
    {S : Finset (HeightOneSpectrum R)} {e : HeightOneSpectrum R → ℕ} (he : ∀ v ∈ S, e v ≠ 0)
    (hprod : ∏ v ∈ S, v.asIdeal ^ e v = I) : Nat.card (R ⧸ I)ˣ * ∏ v ∈ S, absNorm v.asIdeal =
      absNorm I * ∏ v ∈ S, (absNorm v.asIdeal - 1) := by
  let φ := HeightOneSpectrum.quotientEquivPiOfProdEq I (fun v : S ↦ (v : HeightOneSpectrum R))
    (fun v ↦ e v) Subtype.coe_injective.pairwise_ne ((Finset.prod_coe_sort S _).trans hprod)
  rw [Nat.card_congr ((Units.mapEquiv φ.toMulEquiv).trans MulEquiv.piUnits).toEquiv, Nat.card_pi,
    Finset.prod_coe_sort S fun v ↦ Nat.card (R ⧸ v.asIdeal ^ e v)ˣ, ← hprod, map_prod,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  simpa only [absNorm_eq_natCard] using
    card_units_quotient_pow_mul_card_quotient v.asIdeal (he v hv)

/-- **Euler's totient for ideals**, multiplicative form: if `S` is the set of height-one primes
dividing `I` and `R ⧸ I` is finite, then `#(R ⧸ I)ˣ · ∏_{𝔭 ∈ S} N 𝔭 = N I · ∏_{𝔭 ∈ S} (N 𝔭 - 1)`.
This is the analogue of `Nat.totient_mul_prod_primeFactors`; for the form with the factors
`1 - (N 𝔭)⁻¹` in a field, see `Ideal.card_units_quotient_eq_absNorm_mul_prod`. -/
theorem card_units_quotient_mul_prod_absNorm (I : Ideal R) [Finite (R ⧸ I)]
    {S : Finset (HeightOneSpectrum R)} (hS : ∀ v, v ∈ S ↔ v.asIdeal ∣ I) :
    Nat.card (R ⧸ I)ˣ * ∏ v ∈ S, absNorm v.asIdeal =
      absNorm I * ∏ v ∈ S, (absNorm v.asIdeal - 1) := by
  have hI : I ≠ 0 := fun h ↦ (absNorm_ne_zero_iff I).mpr ‹_› (by rw [h, map_zero])
  let e : HeightOneSpectrum R → ℕ := fun v ↦
    (Associates.mk v.asIdeal).count (Associates.mk I).factors
  have he (v : HeightOneSpectrum R) : e v ≠ 0 ↔ v ∈ S := by
    rw [hS, Associates.count_ne_zero_iff_dvd hI v.irreducible]
  refine card_units_quotient_mul_prod_absNorm_of_prod_eq I (fun v ↦ (he v).mpr) ?_
  rw [← finprod_eq_finsetProd_of_mulSupport_subset (fun v ↦ v.asIdeal ^ e v) fun v hv ↦
    (he v).mp fun h ↦ hv (by simp [h])]
  exact Ideal.finprod_heightOneSpectrum_factorization hI

/-- **Euler's totient for ideals**: if `S` is the set of height-one primes dividing `I` and
`R ⧸ I` is finite, then `#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∈ S} (1 - (N 𝔭)⁻¹)` in any field of
characteristic zero. This is the analogue of `Nat.totient_eq_mul_prod_factors`, which is stated
over `ℚ` only; the identity in `ℕ`, free of inverses, is
`Ideal.card_units_quotient_mul_prod_absNorm`. -/
theorem card_units_quotient_eq_absNorm_mul_prod {F : Type*} [Field F] [CharZero F] (I : Ideal R)
    [Finite (R ⧸ I)] {S : Finset (HeightOneSpectrum R)} (hS : ∀ v, v ∈ S ↔ v.asIdeal ∣ I) :
    (Nat.card (R ⧸ I)ˣ : F) = absNorm I * ∏ v ∈ S, (1 - (absNorm v.asIdeal : F)⁻¹) := by
  have hN (v) (hv : v ∈ S) : absNorm v.asIdeal ≠ 0 :=
    ne_zero_of_dvd_ne_zero ((absNorm_ne_zero_iff I).mpr ‹_›) (map_dvd absNorm ((hS v).mp hv))
  have hN' (v) (hv : v ∈ S) : (absNorm v.asIdeal : F) ≠ 0 := Nat.cast_ne_zero.mpr (hN v hv)
  have key (v) (hv : v ∈ S) :
      (1 - (absNorm v.asIdeal : F)⁻¹) * absNorm v.asIdeal = (absNorm v.asIdeal - 1 : ℕ) := by
    rw [sub_mul, one_mul, inv_mul_cancel₀ (hN' v hv), Nat.cast_pred (Nat.pos_of_ne_zero (hN v hv))]
  refine mul_right_cancel₀ (Finset.prod_ne_zero_iff.mpr hN') ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_congr rfl key]
  exact_mod_cast card_units_quotient_mul_prod_absNorm I hS

end Ideal
