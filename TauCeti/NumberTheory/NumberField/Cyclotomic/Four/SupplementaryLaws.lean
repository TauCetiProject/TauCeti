/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Primary
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal

/-!
# The supplementary laws for `i` and `-1` in quartic reciprocity

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and let `λ = a + b i` be primary. The quartic residue symbols of the units `i` and
`-1` at the ideal `λ 𝓞 K` are

* `(i / λ)_4 = i ^ (-((a - 1) / 2))`, and
* `(-1 / λ)_4 = (-1) ^ ((a - 1) / 2)`.

In particular, for a rational integer `m ≡ 1 (mod 4)`, `(i / m)_4 = (-1) ^ ((m - 1) / 4)` and
`(-1 / m)_4 = 1`. These are the supplementary laws that complement the law of biquadratic
reciprocity for primary elements.

Both laws follow from the value of the power residue symbol of a root of unity at an ideal,
`(ζ / λ)_4 = ζ ^ ((N λ - 1) / 4)` (`Ideal.powerResidueSymbolIdeal_mk_of_pow_eq_one`), and the
congruences of `(N λ - 1) / 4` for primary `λ`: modulo `4` it is `-((a - 1) / 2)`
(`TauCeti.IsPrimaryGaussian.norm_sub_one_div_four_modEq_four`), and modulo `2` it is `(a - 1) / 2`
(`TauCeti.IsPrimaryGaussian.norm_sub_one_div_four`). The symbols are elements of `𝓞 K`; the laws
are read in `K`, where the integer powers of `i` and `-1` live.

## Main results

* `TauCeti.IsPrimaryGaussian.absNorm_span_singleton_coprime_four`: a primary element generates
  an ideal of norm prime to `4`.
* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_toInteger`:
  `(i / λ)_4 = i ^ (-((a - 1) / 2))`.
* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_neg_one`:
  `(-1 / λ)_4 = (-1) ^ ((a - 1) / 2)`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger`:
  `(i / m)_4 = (-1) ^ ((m - 1) / 4)` for a rational integer `m ≡ 1 (mod 4)`.
* `TauCeti.powerResidueSymbolIdeal_span_intCast_mk_neg_one`: `(-1 / m)_4 = 1` for a rational
  integer `m ≡ 1 (mod 4)`.

## References

* N. Xu, *Reciprocity Laws*, §5, Definition 5.2 and Proposition 5.7.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9.
-/

public section

open NumberField Ideal

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- A primary element of `𝓞 K = ℤ[i]` generates an ideal whose norm is odd, hence prime to `4`. -/
theorem IsPrimaryGaussian.absNorm_span_singleton_coprime_four {x : 𝓞 K}
    (hx : IsPrimaryGaussian x) : (absNorm (span {x})).Coprime 4 := by
  rw [absNorm_span_singleton, show 4 = 2 ^ 2 by rfl]
  exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hx.odd_norm))

variable {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}

/-- For primary `λ = a + b i`, the exponent `(N λ - 1) / 4` of the power residue symbol at `λ` is
the integer `(Algebra.norm ℤ λ - 1) / 4`. -/
private theorem IsPrimaryGaussian.natCast_absNorm_sub_one_div_four
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    (((absNorm (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) - 1) / 4 : ℕ) : ℤ) =
      (Algebra.norm ℤ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) - 1) / 4 := by
  have hcop := hx.absNorm_span_singleton_coprime_four
  have hN : (absNorm (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) : ℤ) =
      Algebra.norm ℤ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) := by
    rw [absNorm_span_singleton, Int.natCast_natAbs, abs_of_nonneg]
    rw [hζ.norm_intCast_add_intCast_mul_toInteger_of_four]
    positivity
  have h₀ : absNorm (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hcop
    exact absurd hcop (by norm_num)
  omega

variable [HasEnoughRootsOfUnity (𝓞 K) 4]

/-- **The supplementary law for `i`.** If `λ = a + b i` is primary, then
`(i / λ)_4 = i ^ (-((a - 1) / 2))`, the symbol being taken at the ideal `λ 𝓞 K` and read in `K`. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_toInteger
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ hζ.toInteger) : 𝓞 K) : K) = ζ ^ (-((a - 1) / 2)) := by
  have h₀ : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hc : ((hζ.toInteger : 𝓞 K) : K) = ζ := hζ.coe_toInteger
  rw [powerResidueSymbolIdeal_mk_of_pow_eq_one hx.absNorm_span_singleton_coprime_four
      hζ.toInteger_isPrimitiveRoot.pow_eq_one, RingOfIntegers.coe_eq_algebraMap, map_pow,
    ← RingOfIntegers.coe_eq_algebraMap, hc, ← zpow_natCast,
    ← div_eq_one_iff_eq (zpow_ne_zero _ h₀), ← zpow_sub₀ h₀, hζ.zpow_eq_one_iff_dvd,
    hx.natCast_absNorm_sub_one_div_four]
  exact_mod_cast hx.norm_sub_one_div_four_modEq_four.symm.dvd

/-- **The supplementary law for `-1`.** If `λ = a + b i` is primary, then
`(-1 / λ)_4 = (-1) ^ ((a - 1) / 2)`, the symbol being taken at the ideal `λ 𝓞 K` and read
in `K`. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_neg_one
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (-1)) : 𝓞 K) : K) = (-1) ^ ((a - 1) / 2) := by
  rw [powerResidueSymbolIdeal_mk_of_pow_eq_one hx.absNorm_span_singleton_coprime_four
      (by norm_num), RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_one,
    ← zpow_natCast, ← div_eq_one_iff_eq (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)),
    ← zpow_sub₀ (neg_ne_zero.mpr one_ne_zero),
    (IsPrimitiveRoot.neg_one_of_two_ne_zero two_ne_zero).zpow_eq_one_iff_dvd,
    hx.natCast_absNorm_sub_one_div_four]
  exact_mod_cast hx.norm_sub_one_div_four.symm.dvd

/-- **The supplementary law for `i` at a rational integer.** If `m ≡ 1 (mod 4)`, then
`(i / m)_4 = (-1) ^ ((m - 1) / 4)`, the symbol being taken at the ideal `m 𝓞 K` and read in `K`. -/
theorem _root_.IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger
    (hζ : IsPrimitiveRoot ζ 4) {m : ℤ} (hm : m ≡ 1 [ZMOD 4]) :
    ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ hζ.toInteger) : 𝓞 K) :
      K) = (-1) ^ ((m - 1) / 4) := by
  -- Write `m` as the Gaussian integer `m + 0 i`.
  have hm₀ : (m : 𝓞 K) = (m : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger := by simp
  have hx : IsPrimaryGaussian ((m : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger) :=
    hm₀ ▸ (isPrimaryGaussian_intCast_iff (K := K)).mpr hm
  obtain ⟨j, hj⟩ := hm.symm.dvd
  rw [hm₀, hx.powerResidueSymbolIdeal_mk_toInteger, show -((m - 1) / 2) = 2 * -j by omega,
    show (m - 1) / 4 = j by omega, zpow_mul, zpow_ofNat, hζ.sq_eq_neg_one, zpow_neg, ← inv_zpow,
    inv_neg_one]

/-- **The supplementary law for `-1` at a rational integer.** If `m ≡ 1 (mod 4)`, then
`(-1 / m)_4 = 1`, the symbol being taken at the ideal `m 𝓞 K`. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_neg_one {m : ℤ} (hm : m ≡ 1 [ZMOD 4]) :
    powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (-1)) = 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  -- Write `m` as the Gaussian integer `m + 0 i`.
  have hm₀ : (m : 𝓞 K) = (m : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger := by simp
  have hx : IsPrimaryGaussian ((m : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger) :=
    hm₀ ▸ (isPrimaryGaussian_intCast_iff (K := K)).mpr hm
  obtain ⟨j, hj⟩ := hm.symm.dvd
  have h := hx.powerResidueSymbolIdeal_mk_neg_one
  rw [Even.neg_one_zpow ⟨j, by omega⟩] at h
  rw [hm₀]
  exact_mod_cast h

section Examples

variable (hζ : IsPrimitiveRoot ζ 4)
include hζ

/- `(i / -3)_4 = (-1) ^ ((-3 - 1) / 4) = -1`, and `(i / (-1 + 2i))_4 = i ^ 1 = i` at the primary
prime `-1 + 2i` of norm `5`. -/
example : ((powerResidueSymbolIdeal (span {((-3 : ℤ) : 𝓞 K)}) 4
    (Ideal.Quotient.mk _ hζ.toInteger) : 𝓞 K) : K) = -1 := by
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger (by decide)]
  norm_num

example : ((powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ hζ.toInteger) : 𝓞 K) : K) = ζ := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  norm_num

/- `(-1 / (3 + 2i))_4 = (-1) ^ ((3 - 1) / 2) = -1` at the primary prime `3 + 2i` of norm `13`. -/
example : ((powerResidueSymbolIdeal (span {((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ (-1)) : 𝓞 K) : K) = -1 := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_neg_one
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  norm_num

end Examples

end TauCeti
