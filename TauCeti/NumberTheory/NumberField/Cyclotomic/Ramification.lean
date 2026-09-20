/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.NumberTheory.NumberField.RamifiedPrimes
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# The ramified primes of a cyclotomic extension of a number field

Let `M / K` be an `m`-th cyclotomic extension with `K` a number field. The level `m` lies in the
different ideal of `𝓞 M` over `𝓞 K` — equivalently, that different divides `(m)` — so
ramification in `M / K` is confined to the primes above `m`. Read through absolute discriminants,
along the factorisation `|discr M| = 𝔑 𝔡(𝓞 M / 𝓞 K) * |discr K| ^ [M : K]`, the same bound says
that a rational prime dividing `discr M` divides `discr K` or divides `m`: the extension ramifies
only below or at the level.

Neither statement constrains `m` against `K`. In that they differ from the degree identity
`[M : K] = φ m` of `TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank`, which needs `m` coprime
to `discr K` and fails outright when `K` already contains a primitive `m`-th root of unity.

## Main results

* `IsCyclotomicExtension.natCast_mem_differentIdeal`: the level `m` lies in the different ideal
  of `𝓞 M` over `𝓞 K`.
* `IsCyclotomicExtension.prime_dvd_natAbs_discr_or_dvd_of_dvd_natAbs_discr`: a prime dividing
  `discr M` divides `discr K` or divides `m` — the extension ramifies only below or at the level.
* `IsCyclotomicExtension.dvd_level_of_mem_ramifiedPrimes`: every rational prime ramifying in a
  subfield of `ℚ(ζ_m)` divides `m`.
* `IsCyclotomicExtension.four_dvd_level_of_two_mem_ramifiedPrimes`: if `2` ramifies in a
  subfield, then `4` divides the cyclotomic level.

## Implementation notes

`natCast_mem_differentIdeal` reads as a membership rather than as a divisibility of
`Ideal.span {(m : 𝓞 M)}`; `Ideal.span_singleton_le_iff_mem` gives the divisibility form where
that is the one wanted.

Both results ask `M` to be a number field alongside `K`. That is no restriction, since a
cyclotomic extension of a number field is one: `IsCyclotomicExtension.numberField {m} K M`.

-/

public section

namespace IsCyclotomicExtension

-- Source: the ramification bound of `TauCetiRoadmap/Chebotarev/README.md`, §7.4, which asks that
-- the primes ramified in the cyclotomic crossing but not below all lie above the level.
open NumberField Polynomial in
/-- **The level lies in the different ideal.** For `M / K` an `m`-th cyclotomic extension of
number fields, `m` belongs to the different ideal of `𝓞 M` over `𝓞 K`; equivalently that different
divides `(m)`, so only primes dividing `m` can ramify in `M / K`. -/
theorem natCast_mem_differentIdeal (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : ℕ) [IsCyclotomicExtension {m} K M] :
    (m : 𝓞 M) ∈ differentIdeal (𝓞 K) (𝓞 M) := by
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · -- At level `0` the claim reads `0 ∈ differentIdeal`, and every ideal contains `0`.
    simp
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  set z : 𝓞 M := hζ.toInteger
  -- `M = K(ζ)` is generated over `K` by a primitive `m`-th root of unity, so the different
  -- contains the element `aeval ζ (derivative (minpoly (𝓞 K) ζ))`.
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K M z
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ)
  have hzpow : z ^ m = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  -- `ζ` is a root of `X ^ m - 1`, so its minimal polynomial divides that.
  obtain ⟨q, hq⟩ : minpoly (𝓞 K) z ∣ (X ^ m - 1 : (𝓞 K)[X]) :=
    minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral z) (by simp [hzpow])
  -- Differentiating that factorisation at `ζ` makes `m * ζ ^ (m - 1)` a multiple of `hmem`.
  have hder : (m : 𝓞 M) * z ^ (m - 1) =
      aeval z (derivative (minpoly (𝓞 K) z)) * aeval z q := by
    have h : aeval z (derivative (X ^ m - 1 : (𝓞 K)[X])) =
        aeval z (derivative (minpoly (𝓞 K) z * q)) := by rw [hq]
    simpa [derivative_mul, derivative_X_pow, minpoly.aeval] using h
  -- Multiplying by `ζ` and using `ζ ^ m = 1` turns `m * ζ ^ (m - 1)` into `m` itself.
  have hm : (m : 𝓞 M) = aeval z (derivative (minpoly (𝓞 K) z)) * aeval z q * z := by
    rw [← hder, mul_assoc, pow_sub_one_mul (NeZero.ne m) z, hzpow, mul_one]
  rw [hm]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hmem)

open NumberField in
/-- **A prime ramifying in a cyclotomic extension either ramifies below or divides the level.**
For `M / K` an `m`-th cyclotomic extension of number fields, a prime dividing `discr M` divides
`discr K` or divides `m`. -/
theorem prime_dvd_natAbs_discr_or_dvd_of_dvd_natAbs_discr (K M : Type*) [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] (m : ℕ) [IsCyclotomicExtension {m} K M]
    {p : ℕ} (hp : p.Prime) (hpM : p ∣ (NumberField.discr M).natAbs) :
    p ∣ (NumberField.discr K).natAbs ∨ p ∣ m := by
  -- `|discr M|` factors as the norm of `𝔡(𝓞 M / 𝓞 K)` times `|discr K| ^ [M : K]`, so `p`
  -- divides one of those two factors.
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) M (𝓞 M)] at hpM
  rcases hp.dvd_mul.mp hpM with h | h
  · -- That different contains `m`, so its norm divides `Algebra.norm ℤ (m : 𝓞 M) = m ^ [M : ℚ]`.
    refine Or.inr (hp.dvd_of_dvd_pow (n := Module.finrank ℤ (𝓞 M)) (h.trans ?_))
    have hnorm := Ideal.absNorm_dvd_norm_of_mem (natCast_mem_differentIdeal K M m)
    rwa [Algebra.norm_natCast, ← Nat.cast_pow, Int.natCast_dvd_natCast] at hnorm
  · exact Or.inl (hp.dvd_of_dvd_pow h)

/-- **Every prime ramifying in a subfield of a cyclotomic field divides the level.** Let `M` be an
`m`-th cyclotomic extension of `ℚ` and let `F ⊆ M` be an intermediate field. If the rational
prime `p` ramifies in `F`, then `p ∣ m`.

Indeed, the discriminant of `F` divides the discriminant of `M`, while a rational prime dividing
the latter either divides the discriminant of `ℚ` or the cyclotomic level. The first alternative
is impossible because `discr ℚ = 1`. -/
theorem dvd_level_of_mem_ramifiedPrimes (M : Type*) [Field M] [NumberField M] (m : ℕ)
    [IsCyclotomicExtension {m} ℚ M] (F : IntermediateField ℚ M) {p : ℕ}
    (hpF : p ∈ NumberField.ramifiedPrimes F) : p ∣ m := by
  let _ : NumberField F := NumberField.of_intermediateField F
  have hp : p.Prime := NumberField.prime_of_mem_ramifiedPrimes hpF
  have hpM : p ∣ (NumberField.discr M).natAbs := by
    have hpM' : (p : ℤ) ∣ NumberField.discr M :=
      ((NumberField.mem_ramifiedPrimes_iff_dvd_discr hp).mp hpF).trans
        (NumberField.discr_dvd_discr F M)
    simpa using (Int.natAbs_dvd_natAbs.mpr hpM')
  rcases prime_dvd_natAbs_discr_or_dvd_of_dvd_natAbs_discr ℚ M m hp hpM with hpQ | hpm
  · rw [NumberField.discr_rat] at hpQ
    exact (hp.not_dvd_one hpQ).elim
  · exact hpm

/-- **A cyclotomic level containing a field ramified at `2` is divisible by `4`.** Let `M` be an
`m`-th cyclotomic extension of `ℚ` and let `F ⊆ M` be an intermediate field. If `2` ramifies in
`F`, then `4 ∣ m`.

The preceding prime-divisor bound first gives `2 ∣ m`. If exactly one factor of `2` occurred in
`m`, Mathlib's cyclotomic ramification-index formula would give ramification index one above `2`
in `M`; unramifiedness would then descend to `F`, a contradiction. -/
theorem four_dvd_level_of_two_mem_ramifiedPrimes (M : Type*) [Field M] [NumberField M] (m : ℕ)
    [IsCyclotomicExtension {m} ℚ M] (F : IntermediateField ℚ M)
    (hF : 2 ∈ NumberField.ramifiedPrimes F) : 4 ∣ m := by
  by_cases hm : m = 0
  · simp [hm]
  have h2m : 2 ∣ m := dvd_level_of_mem_ramifiedPrimes M m F hF
  by_contra h4m
  obtain ⟨a, rfl⟩ := h2m
  have ha : ¬ 2 ∣ a := by
    intro h2a
    obtain ⟨b, rfl⟩ := h2a
    exact h4m ⟨b, by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsGalois ℚ M := IsCyclotomicExtension.isGalois {2 * a} ℚ M
  have hidx : (Ideal.span {(2 : ℤ)}).ramificationIdxIn (NumberField.RingOfIntegers M) = 1 := by
    simpa using IsCyclotomicExtension.Rat.ramificationIdxIn_eq (2 * a) M
      (p := 2) (k := 0) (m := a) (by simp) ha
  have hur : Algebra.IsUnramifiedIn (NumberField.RingOfIntegers M) (Ideal.span {(2 : ℤ)}) := by
    rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
    intro P _ hP
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(2 : ℤ)}) P Gal(M/ℚ)]
    exact hidx
  have hM : 2 ∈ NumberField.ramifiedPrimes M := by
    apply (NumberField.mem_ramifiedPrimes_iff_dvd_discr Nat.prime_two).mpr
    exact ((NumberField.mem_ramifiedPrimes_iff_dvd_discr Nat.prime_two).mp hF).trans
      (NumberField.discr_dvd_discr F M)
  exact (NumberField.mem_ramifiedPrimes_iff.mp hM).2 hur

end IsCyclotomicExtension
