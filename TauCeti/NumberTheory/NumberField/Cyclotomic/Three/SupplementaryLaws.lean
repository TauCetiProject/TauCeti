/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootsOfUnity
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Three.RationalResidue
import TauCeti.Algebra.GroupWithZero.Basic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Three.Primary

/-!
# The cubic residue symbol of `1 - ω` at rational integers

For a primitive cube root of unity `ω` and an integer `t ≡ 2 (mod 3)`, the cubic residue
symbol of `1 - ω` at the principal ideal `(t)` is `ω ^ (2 * ((t + 1) / 3))`
(`IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_one_sub_toInteger`).
The denominator can be negative or composite. This is the rational-denominator part of
Eisenstein's supplement to cubic reciprocity; composite denominators also occur in Williams'
proof for nonrational primary primes.

The calculation uses `(1 - ω)² = -3ω`, the triviality of the cubic residue symbol of coprime
rational integers, and the value of the symbol at a root of unity.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3,
  Williams' proof of equation (4), pp. 66–67.
-/

public section

open NumberField Ideal

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

private theorem rational_supplement_exponent_modEq {t : ℤ} (ht : t ≡ 2 [ZMOD 3]) :
    ((2 * ((absNorm (span {(t : 𝓞 K)}) - 1) / 3) : ℕ) : ℤ) ≡
      2 * ((t + 1) / 3) [ZMOD 3] := by
  let I : Ideal (𝓞 K) := span {(t : 𝓞 K)}
  have hnorm : (absNorm I : ℤ) = t ^ 2 := by
    dsimp [I]
    rw [absNorm_span_singleton]
    have h : Algebra.norm ℤ (t : 𝓞 K) = t ^ 2 := by
      simpa using
        (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_intCast_add_intCast_mul_toInteger_of_three t 0
    rw [h, Int.natCast_natAbs, abs_of_nonneg (sq_nonneg t)]
  have hdiv : ((absNorm I - 1) / 3 : ℕ) = ((t ^ 2 - 1) / 3 : ℤ) := by
    rw [Int.natCast_ediv, Int.natCast_sub (Nat.one_le_iff_ne_zero.mpr ?_), hnorm]
    · norm_num
    · intro h
      rw [h, Nat.cast_zero] at hnorm
      have : t = 0 := by nlinarith [sq_nonneg t]
      subst t
      norm_num [Int.ModEq] at ht
  have hpow : (2 * ((t ^ 2 - 1) / 3)) ≡ 2 * ((t + 1) / 3) [ZMOD 3] := by
    obtain ⟨m, hm⟩ := ht.symm.dvd
    have ht' : t = 3 * (m + 1) - 1 := by omega
    rw [ht']
    have he : (3 * (m + 1) - 1) ^ 2 - 1 = 3 * (3 * (m + 1) ^ 2 - 2 * (m + 1)) := by ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (3 : ℤ) ≠ 0)]
    unfold Int.ModEq
    omega
  have hresult : ((2 * ((absNorm I - 1) / 3) : ℕ) : ℤ) ≡
      2 * ((t + 1) / 3) [ZMOD 3] := by
    rw [Nat.cast_mul, Nat.cast_ofNat, hdiv]
    exact hpow
  exact hresult

/-- **The rational-denominator supplement to cubic reciprocity.** For an integer
`t ≡ 2 (mod 3)`, including negative and composite integers, `((1 - ζ) / t)₃` is
`ζ ^ (2 * ((t + 1) / 3))`. The symbol is read in `K` to allow integer exponents. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_one_sub_toInteger {t : ℤ}
    (ht : t ≡ 2 [ZMOD 3]) :
    ((powerResidueSymbolIdeal (span {(t : 𝓞 K)}) 3
      (Ideal.Quotient.mk _ (1 - hζ.toInteger)) : 𝓞 K) : K) =
        ζ ^ (2 * ((t + 1) / 3)) := by
  -- Squaring uses only the trivial symbol of the rational integer `-3`.
  have ht3 : IsCoprime (-3 : ℤ) t := by
    refine ⟨-((t + 1) / 3), -1, ?_⟩
    unfold Int.ModEq at ht
    omega
  have hprimary : TauCeti.IsPrimaryEisenstein (t : 𝓞 K) :=
    TauCeti.isPrimaryEisenstein_intCast_iff.mpr ht
  let I : Ideal (𝓞 K) := span {(t : 𝓞 K)}
  let χ := powerResidueSymbolIdeal I 3
  let ω := hζ.toInteger
  have hω : ω ^ 3 = 1 := hζ.toInteger_cube_eq_one
  have hsq : (1 - ω) ^ 2 = (-3 : ℤ) * ω := by
    have h := IsCyclotomicExtension.Rat.Three.eta_sq hζ
    rw [IsCyclotomicExtension.Rat.Three.coe_eta] at h
    dsimp [ω]
    push_cast
    linear_combination h
  have hχ3 : χ (Ideal.Quotient.mk I ((-3 : ℤ) : 𝓞 K)) = 1 := by
    simpa only [χ, I, map_intCast] using
      powerResidueSymbolIdeal_intCast_three (K := K) ht3
  have hχ2 : χ (Ideal.Quotient.mk I (1 - ω)) ^ 2 = χ (Ideal.Quotient.mk I ω) := by
    rw [← map_pow, ← map_pow, hsq, map_mul, map_mul, hχ3, one_mul]
  have hχω : χ (Ideal.Quotient.mk I ω) = ω ^ ((absNorm I - 1) / 3) :=
    powerResidueSymbolIdeal_mk_of_pow_eq_one hprimary.absNorm_span_singleton_coprime_three hω
  have hχ0 : χ (Ideal.Quotient.mk I (1 - ω)) ≠ 0 := by
    intro h
    have hw0 : ω ≠ 0 := hζ.toInteger_isPrimitiveRoot.ne_zero (by decide)
    rw [h, zero_pow (by decide), hχω] at hχ2
    exact (pow_ne_zero _ hw0) hχ2.symm
  -- Cubing gives one, so squaring the previous identity recovers the original symbol.
  have hχcube : χ (Ideal.Quotient.mk I (1 - ω)) ^ 3 = 1 :=
    powerResidueSymbolIdeal_pow_eq_one (MulChar.apply_ne_zero_iff.mp hχ0)
  have hχ : χ (Ideal.Quotient.mk I (1 - ω)) =
      ω ^ (2 * ((absNorm I - 1) / 3)) := by
    rw [mul_comm 2, pow_mul]
    linear_combination -χ (Ideal.Quotient.mk I (1 - ω)) * hχcube +
      (χ (Ideal.Quotient.mk I (1 - ω)) ^ 2 + ω ^ ((absNorm I - 1) / 3)) *
        (hχ2.trans hχω)
  -- Read the symbol in the field and reduce its exponent modulo three.
  rw [hχ]
  push_cast [ω, hζ.coe_toInteger]
  rw [← zpow_natCast]
  exact TauCeti.zpow_eq_zpow_of_modEq hζ.pow_eq_one (rational_supplement_exponent_modEq (K := K) ht)

/- The inert prime `2` gives a nontrivial symbol. -/
example : ((powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
    (Ideal.Quotient.mk _ (1 - hζ.toInteger)) : 𝓞 K) : K) = ζ ^ 2 := by
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_sub_toInteger (by decide)]
  norm_num

/- The composite denominator `-10` and the unit denominator `-1` give the trivial symbol. -/
example : ((powerResidueSymbolIdeal (span {((-10 : ℤ) : 𝓞 K)}) 3
    (Ideal.Quotient.mk _ (1 - hζ.toInteger)) : 𝓞 K) : K) = 1 := by
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_sub_toInteger (by decide)]
  exact (hζ.zpow_eq_one_iff_dvd _).2 (by decide)

example : ((powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K)}) 3
    (Ideal.Quotient.mk _ (1 - hζ.toInteger)) : 𝓞 K) : K) = 1 := by
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_sub_toInteger (by decide)]
  norm_num

end IsPrimitiveRoot
