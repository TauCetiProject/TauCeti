/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupWithZero.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Primary
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal

/-!
# The supplementary laws for `i` and `-1` in quartic reciprocity

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and let `λ = a + b i` be primary. The quartic residue symbols of the units `i` and
`-1` at the ideal `λ 𝓞 K` are

* `(i / λ)_4 = i ^ (-((a - 1) / 2))`, and
* `(-1 / λ)_4 = (-1) ^ ((a - 1) / 2)`.

In particular, for a rational integer `m ≡ 1 (mod 4)`, `(i / m)_4 = (-1) ^ ((m - 1) / 4)`, and
`(-1 / m)_4 = 1` for every odd rational integer `m`. These are the supplementary laws that
complement the law of biquadratic reciprocity for primary elements.

Both laws follow from the value of the power residue symbol of a root of unity at an ideal,
`(ζ / λ)_4 = ζ ^ ((N λ - 1) / 4)` (`Ideal.powerResidueSymbolIdeal_mk_of_pow_eq_one`), and the
congruences of `(N λ - 1) / 4` for primary `λ`: modulo `4` it is `-((a - 1) / 2)`
(`TauCeti.IsPrimaryGaussian.norm_sub_one_div_four_modEq_four`), and modulo `2` it is `(a - 1) / 2`
(`TauCeti.IsPrimaryGaussian.norm_sub_one_div_four`). The symbols are elements of `𝓞 K`; the laws
are read in `K`, where the integer powers of `i` and `-1` live.

## Main results

* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_toInteger`:
  `(i / λ)_4 = i ^ (-((a - 1) / 2))`.
* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_neg_one`:
  `(-1 / λ)_4 = (-1) ^ ((a - 1) / 2)`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_toInteger`:
  `(i / m)_4 = (-1) ^ ((m - 1) / 4)` for a rational integer `m ≡ 1 (mod 4)`.
* `TauCeti.powerResidueSymbolIdeal_span_intCast_mk_neg_one`: `(-1 / m)_4 = 1` for an odd
  rational integer `m`.

## References

* N. Xu, *Reciprocity Laws*, §5, Definition 5.2 and Proposition 5.7.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9.
-/

public section

open NumberField Ideal

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

variable {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ} [HasEnoughRootsOfUnity (𝓞 K) 4]

/-- **The supplementary law for `i`.** If `λ = a + b i` is primary, then
`(i / λ)_4 = i ^ (-((a - 1) / 2))`, the symbol being taken at the ideal `λ 𝓞 K` and read in `K`. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_toInteger
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ hζ.toInteger) : 𝓞 K) : K) = ζ ^ (-((a - 1) / 2)) := by
  rw [powerResidueSymbolIdeal_mk_of_pow_eq_one hx.absNorm_span_singleton_coprime_four
      hζ.toInteger_isPrimitiveRoot.pow_eq_one]
  push_cast [hζ.coe_toInteger]
  rw [← zpow_natCast, hx.natCast_absNorm_sub_one_div_four]
  exact zpow_eq_zpow_of_modEq hζ.pow_eq_one hx.norm_sub_one_div_four_modEq_four

/-- **The supplementary law for `-1`.** If `λ = a + b i` is primary, then
`(-1 / λ)_4 = (-1) ^ ((a - 1) / 2)`, the symbol being taken at the ideal `λ 𝓞 K` and read
in `K`. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_neg_one
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (-1)) : 𝓞 K) : K) = (-1) ^ ((a - 1) / 2) := by
  rw [powerResidueSymbolIdeal_mk_of_pow_eq_one hx.absNorm_span_singleton_coprime_four
      (by norm_num)]
  push_cast
  rw [← zpow_natCast, hx.natCast_absNorm_sub_one_div_four]
  exact zpow_eq_zpow_of_modEq (n := 2) (by norm_num) hx.norm_sub_one_div_four

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
  have h₂ : -((m - 1) / 2) = 2 * -j := by omega
  have h₄ : (m - 1) / 4 = j := by omega
  rw [hm₀, hx.powerResidueSymbolIdeal_mk_toInteger, h₂, h₄, zpow_mul, zpow_ofNat,
    hζ.sq_eq_neg_one]
  simp [zpow_neg, ← inv_zpow]

/-- **The supplementary law for `-1` at a rational integer.** If `m` is odd, then
`(-1 / m)_4 = 1`, the symbol being taken at the ideal `m 𝓞 K`. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_neg_one {m : ℤ} (hm : Odd m) :
    powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (-1)) = 1 := by
  -- Since `m` and `-m` generate the same ideal, we may assume `m ≡ 1 (mod 4)`.
  wlog hm₁ : m ≡ 1 [ZMOD 4] generalizing m
  · have h := this hm.neg (by obtain ⟨k, rfl⟩ := hm; simp only [Int.ModEq] at hm₁ ⊢; omega)
    rwa [Int.cast_neg, span_singleton_neg] at h
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  -- Write `m` as the Gaussian integer `m + 0 i`.
  have hm₀ : (m : 𝓞 K) = (m : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger := by simp
  have hx : IsPrimaryGaussian ((m : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger) :=
    hm₀ ▸ (isPrimaryGaussian_intCast_iff (K := K)).mpr hm₁
  obtain ⟨j, hj⟩ := hm₁.symm.dvd
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
