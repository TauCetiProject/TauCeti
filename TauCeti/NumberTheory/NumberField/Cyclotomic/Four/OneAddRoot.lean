/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.ZModChar
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Primary
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal
import Mathlib.Algebra.CharP.Lemmas
import TauCeti.Data.Nat.ModEq
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.QuarticReciprocity.IntCast
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.SupplementaryLaws
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The quartic supplementary laws for `1 + i`, `1 - i`, and `2`

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and let `i` be a primitive fourth root of unity in `𝓞 K`. For every primary Gaussian
integer `λ = a + b i`, the quartic power residue symbol of `1 + i` at `λ 𝓞 K` is

`((1 + i) / λ)₄ = i ^ ((a - b - b² - 1) / 4)`.

In particular, for every rational integer `m ≡ 1 (mod 4)`, including negative and composite
denominators, `((1 + i) / m)₄ = i ^ ((m - 1) / 4)`, and more generally
`((1 + i) / m)₄ = i ^ ((m * χ₄(m) - 1) / 4)` for every odd integer `m`. Applying the law to the
primitive root `-i` and combining with `2 = (1 + i)(1 - i)` gives the conjugate and dyadic laws
`((1 - i) / λ)₄ = i ^ (-((a + b - b² - 1) / 4))` and `(2 / λ)₄ = i ^ (-(b / 2))`; in particular
`(2 / (a + b i))₄ = 1` if and only if `8 ∣ b` whenever `a` is odd.

The proof proceeds in two stages:

1. **Rational denominators**
   (`IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger`): split rational
   primes are evaluated by pairing conjugate factors (following the cancellation argument in
   `TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue`, where the paired
   contribution is the symbol of `i`), inert rational primes by Frobenius in characteristic `q`,
   and composite integers `m ≡ 1 (mod 4)` by multiplicativity.
2. **General primary denominators**
   (`TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger`): for primary
   `π = a + b i` with coprime coordinates and `b = 2 ^ k * b'` (`b'` odd, `k ≥ 1`), the
   congruence `b (1 + i) ≡ b - a (mod π)` and `2 = (-i) (1 + i)²` express
   `((1 + i) / π)₄ ^ (2 k + 1)` in terms of `(i / π)₄`, `(b' / π)₄`, and `((b - a) / π)₄`.
   Odd-integer quartic reciprocity
   (`TauCeti.IsPrimaryGaussian.coe_quartic_reciprocity_intCast_add_mul_of_odd`), triviality of
   rational symbols (`Ideal.powerResidueSymbolIdeal_intCast_four`), and the rational-denominator
   case evaluate every factor; raising to the odd power `2 k + 1` recovers `((1 + i) / π)₄`
   because `(2 k + 1)² ≡ 1 (mod 4)`. Arbitrary primary `λ` then factor as `m · (a₀ + b₀ i)` with
   `m ≡ 1 (mod 4)` and `IsCoprime a₀ b₀`, combining via the multiplicativity modulo `4` of the
   exponent (`TauCeti.IsPrimaryGaussian.sub_sub_sq_sub_one_div_four_mul_modEq_four`).

## Main results

* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger`:
  `((1 + i) / m)₄ = i ^ ((m - 1) / 4)` for rational integers `m ≡ 1 (mod 4)`.
* `TauCeti.IsPrimaryGaussian.four_dvd_sub_sub_sq_sub_one`:
  `4 ∣ a - b - b² - 1` for primary `a + b i`.
* `TauCeti.IsPrimaryGaussian.sub_sub_sq_sub_one_div_four_mul_modEq_four`:
  the exponent `(a - b - b² - 1) / 4` is additive modulo `4` on products of primary elements.
* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger`:
  `((1 + i) / (a + b i))₄ = i ^ ((a - b - b² - 1) / 4)` for every primary `a + b i`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger_of_odd`:
  `((1 + i) / m)₄ = i ^ ((m * χ₄(m) - 1) / 4)` for every odd integer `m`.
* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_sub_toInteger`:
  `((1 - i) / (a + b i))₄ = i ^ (-((a + b - b² - 1) / 4))` for every primary `a + b i`.
* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_two`:
  `(2 / (a + b i))₄ = i ^ (-(b / 2))` for every primary `a + b i`.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_add_mul_mk_two_eq_one_iff`:
  `(2 / (a + b i))₄ = 1 ↔ 8 ∣ b` for odd `a`.

## References

* C. F. Gauss, *Theoria residuorum biquadraticorum, Commentatio secunda*, §§68–76.
* N. Xu, *Reciprocity Laws*, §5, for the primary convention and the rational-denominator
  quartic-symbol calculations.
-/

public section

open NumberField Ideal IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]
  {ζ : K}

private theorem symbol_one_add_pair (hζ : IsPrimitiveRoot ζ 4) (I : Ideal (𝓞 K))
    (hu : IsUnit (Ideal.Quotient.mk I (1 - hζ.toInteger))) :
    powerResidueSymbolIdeal I 4 (Ideal.Quotient.mk I (1 - hζ.toInteger)) ^ 3 *
      powerResidueSymbolIdeal I 4 (Ideal.Quotient.mk I (1 + hζ.toInteger)) =
        powerResidueSymbolIdeal I 4 (Ideal.Quotient.mk I hζ.toInteger) := by
  have hpow := powerResidueSymbolIdeal_pow_eq_one (n := 4) hu
  have hAB : 1 + hζ.toInteger = hζ.toInteger * (1 - hζ.toInteger) := by
    linear_combination hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  rw [hAB, map_mul, map_mul]
  linear_combination powerResidueSymbolIdeal I 4 (Ideal.Quotient.mk I hζ.toInteger) * hpow

private theorem symbol_one_add_split (hζ : IsPrimitiveRoot ζ 4) {q : ℕ}
    (hq : q.Prime) (hq1 : q % 4 = 1) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) = hζ.toInteger ^ ((q - 1) / 4) := by
  -- Factor `q` into conjugate Gaussian integers, each of absolute norm `q`.
  obtain ⟨σ, _, hτ⟩ := TauCeti.exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ
  have hτi : τ hζ.toInteger = -hζ.toInteger := by
    rw [hτ _ hζ.toInteger_isPrimitiveRoot.pow_eq_one, pow_succ,
      hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one, neg_one_mul]
  obtain ⟨β, hβ, hqβ, hN⟩ := TauCeti.exists_natCast_eq_mul_of_mod_four_ne_three
    (σ := (τ : 𝓞 K →+* 𝓞 K)) hτ hq (by omega : q % 4 ≠ 3)
  simp only [RingEquiv.coe_toRingHom] at hqβ
  have hcop : IsCoprime (2 : 𝓞 K) β := by
    have h : IsCoprime (2 : ℤ) q := by
      exact_mod_cast (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega : q % 2 = 1)))
    have h : IsCoprime (2 : 𝓞 K) (q : 𝓞 K) := by
      simpa using h.map (Int.castRingHom (𝓞 K))
    rw [hqβ] at h
    exact h.of_mul_right_right
  have hu : IsUnit (Ideal.Quotient.mk (span {β}) (1 - hζ.toInteger)) := by
    apply Ideal.Quotient.isUnit_mk_iff.mpr
    apply isCoprime_iff_sup_eq.mp
    apply (isCoprime_span_singleton_iff _ _).mpr
    exact hcop.of_isCoprime_of_dvd_left ⟨1 + hζ.toInteger, by
      linear_combination hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one⟩
  -- Pair the symbols of `1 + i` and `1 - i`; their quotient is the symbol of `i`.
  have hpow := powerResidueSymbolIdeal_pow_eq_one (n := 4) hu
  have hmap := map_powerResidueSymbolIdeal (n := 4) (span {β}) τ (1 - hζ.toInteger)
  have hτB : τ (1 - hζ.toInteger) = 1 + hζ.toInteger := by simp [hτi]
  rw [hτ _ hpow, hτB] at hmap
  have hmapβ : (span {β}).map τ = span {τ β} := by
    rw [map_span, Set.image_singleton]
  rw [hqβ, ← span_singleton_mul_span_singleton,
    powerResidueSymbolIdeal_mul_right (by simpa using hβ) (by simpa using hβ),
    ← hmapβ, ← hmap]
  have hodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hcop4 : (absNorm (span {β})).Coprime 4 := by
    simpa only [hN] using hodd.coprime_two_right.pow_right 2
  conv_rhs => rw [← hN, ← powerResidueSymbolIdeal_mk_of_pow_eq_one hcop4
    hζ.toInteger_isPrimitiveRoot.pow_eq_one]
  exact symbol_one_add_pair hζ _ hu

private theorem symbol_one_add_inert (hζ : IsPrimitiveRoot ζ 4) {q : ℕ}
    (hq : q.Prime) (hq3 : q % 4 = 3) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) = (-hζ.toInteger) ^ ((q + 1) / 4) := by
  have := Fact.mk hq
  let P : Ideal (𝓞 K) := span {(q : 𝓞 K)}
  have : P.IsMaximal :=
    ((span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr
      (TauCeti.prime_natCast_of_mod_four_eq_three hq hq3)).isMaximal (by simpa using hq.ne_zero)
  have hq0 : (q : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact mem_span_singleton_self _
  have : CharP (𝓞 K ⧸ P) q := (CharP.charP_iff_prime_eq_zero hq).mpr hq0
  let i := Ideal.Quotient.mk P hζ.toInteger
  have hi2 : i ^ 2 = -1 := by
    rw [← map_pow, hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one, map_neg, map_one]
  have hi4 : i ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hi2, neg_one_sq]
  have hn : 1 + i ≠ 0 := by
    intro he
    have : i = -1 := by linear_combination he
    rw [this] at hi2
    have : (2 : 𝓞 K ⧸ P) = 0 := by linear_combination hi2
    have := (CharP.cast_eq_zero_iff (𝓞 K ⧸ P) q 2).mp this
    have := Nat.le_of_dvd (by decide : 0 < 2) this
    omega
  -- Frobenius is conjugation, so `(1 + i) ^ (q - 1) = -i`.
  have hiq : i ^ q = -i := by
    obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
    rw [hk, pow_add, pow_mul, hi4, one_pow, one_mul, pow_succ, hi2, neg_one_mul]
  have hF : (1 + i) ^ (q - 1) = -i := by
    have h := add_pow_char (1 : 𝓞 K ⧸ P) i q
    rw [one_pow, hiq, ← Nat.sub_add_cancel hq.one_lt.le, pow_succ] at h
    have hm : (1 + i) * (-i) = 1 - i := by linear_combination -hi2
    exact mul_right_cancel₀ hn (h.trans (by simpa [mul_comm, sub_eq_add_neg] using hm.symm))
  have hE : (q ^ 2 - 1) / 4 = (q - 1) * ((q + 1) / 4) := by
    rw [TauCeti.sq_sub_one_eq_four_mul_of_mod_four_eq_three hq3, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  -- Raise the Frobenius identity to `(q + 1) / 4`, then uniquely lift the residue.
  rw [powerResidueSymbolIdeal_of_isMaximal]
  refine (powerResidueSymbol_eq_iff ?_
    (by
      have hneg : (-hζ.toInteger) ^ 4 = 1 := by
        linear_combination hζ.toInteger_isPrimitiveRoot.pow_eq_one
      rw [← pow_mul, Nat.mul_comm, pow_mul, hneg, one_pow])).mpr ?_
  · have hodd : Odd q := Nat.odd_iff.mpr (by omega)
    rw [TauCeti.absNorm_span_natCast_four]
    exact (hodd.coprime_two_right.pow_left 2).pow_right 2
  · rw [TauCeti.absNorm_span_natCast_four, hE, pow_mul, map_pow, map_neg, map_add, map_one]
    exact congrArg (· ^ ((q + 1) / 4)) hF.symm

private def rationalExponent (m : ℤ) : ℤ := (m * ZMod.χ₄ m - 1) / 4

private theorem rationalExponent_neg (m : ℤ) : rationalExponent (-m) = rationalExponent m := by
  simp only [rationalExponent, Int.cast_neg, ZMod.χ₄_neg, neg_mul_neg]

private theorem rationalExponent_mul {m n : ℤ} (hm : Odd m) (hn : Odd n) :
    rationalExponent (m * n) ≡ rationalExponent m + rationalExponent n [ZMOD 4] := by
  have hmn : (m * n) * ZMod.χ₄ ((m * n : ℤ) : ZMod 4) =
      (m * ZMod.χ₄ m) * (n * ZMod.χ₄ n) := by
    rw [Int.cast_mul, map_mul]
    ring
  obtain ⟨a, ha⟩ := (ZMod.int_mul_χ₄_modEq_one hm).symm.dvd
  obtain ⟨b, hb⟩ := (ZMod.int_mul_χ₄_modEq_one hn).symm.dvd
  have ha' : m * ZMod.χ₄ m = 4 * a + 1 := by omega
  have hb' : n * ZMod.χ₄ n = 4 * b + 1 := by omega
  simp only [rationalExponent, hmn, ha', hb']
  rw [show (4 * a + 1) * (4 * b + 1) - 1 = 4 * (a + b + 4 * (a * b)) by ring]
  simp only [Int.mul_ediv_cancel_left _ (by decide : (4 : ℤ) ≠ 0)]
  simp only [Int.ModEq]
  omega

private theorem symbol_one_add_nat_prime (hζ : IsPrimitiveRoot ζ 4) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) :
    ((powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) =
      ζ ^ rationalExponent (q : ℤ) := by
  have hi : algebraMap (𝓞 K) K hζ.toInteger = ζ := hζ.coe_toInteger
  have hodd := hq.odd_of_ne_two hq2
  rcases (show q % 4 = 1 ∨ q % 4 = 3 by
    have := Nat.odd_iff.mp hodd
    omega) with hq1 | hq3
  · rw [symbol_one_add_split hζ hq hq1]
    simp only [map_pow, hi]
    rw [rationalExponent, Int.cast_natCast, ZMod.χ₄_nat_one_mod_four hq1, mul_one,
      ← zpow_natCast]
    congr 1
    omega
  · rw [symbol_one_add_inert hζ hq hq3]
    simp only [map_pow, map_neg, hi]
    have hneg : -ζ = ζ⁻¹ := eq_inv_of_mul_eq_one_left (by
      rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])
    rw [hneg, inv_pow, ← zpow_natCast, ← zpow_neg,
      rationalExponent, Int.cast_natCast, ZMod.χ₄_nat_three_mod_four hq3, mul_neg_one]
    congr 1
    omega

/-- **The rational-denominator supplement for `1 + i` at an odd integer.** For every odd integer
`m`, including negative and composite `m`, the quartic symbol of `1 + i` at `m 𝓞 K` is
`i ^ ((m * χ₄(m) - 1) / 4)`, where `χ₄` is the non-principal Dirichlet character modulo `4`. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger_of_odd
    (hζ : IsPrimitiveRoot ζ 4) {m : ℤ} (hm : Odd m) :
    ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) =
        ζ ^ ((m * ZMod.χ₄ m - 1) / 4) := by
  rw [← rationalExponent]
  induction m using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (Int.not_odd_zero hm).elim
  | h₂ m hunit =>
    have hm' : span {(m : 𝓞 K)} = ⊤ := span_singleton_eq_top.mpr
      (hunit.map (Int.castRingHom (𝓞 K)))
    rw [hm', powerResidueSymbolIdeal_top]
    rcases Int.isUnit_iff.mp hunit with rfl | rfl
    · norm_num [rationalExponent]
    · rw [rationalExponent_neg]
      norm_num [rationalExponent]
  | h₃ m p hm0 hp ih =>
    obtain ⟨hpodd, hmodd⟩ := Int.odd_mul.mp hm
    have hq := Int.prime_iff_natAbs_prime.mp hp
    have hq2 : p.natAbs ≠ 2 := by
      intro he
      have := Int.odd_iff.mp hpodd
      rcases Int.natAbs_eq p with h | h <;> rw [he] at h <;> omega
    have hpval := symbol_one_add_nat_prime hζ hq hq2
    have hpval' : ((powerResidueSymbolIdeal (span {(p : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) =
        ζ ^ rationalExponent p := by
      generalize he : p.natAbs = q at hpval
      rcases Int.natAbs_eq p with h | h <;> rw [he] at h
      · have hcast : (p : 𝓞 K) = (q : 𝓞 K) := by exact_mod_cast h
        rw [hcast, h]
        exact hpval
      · have hcast : (p : 𝓞 K) = -(q : 𝓞 K) := by
          simpa using congrArg (Int.castRingHom (𝓞 K)) h
        rw [hcast, span_singleton_neg, h, rationalExponent_neg]
        exact hpval
    rw [Int.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right (by simpa using hp.ne_zero) (by simpa using hm0)]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at hpval' ih ⊢
    rw [hpval', ih hmodd, ← zpow_add₀ (hζ.ne_zero (by decide))]
    exact TauCeti.zpow_eq_zpow_of_modEq hζ.pow_eq_one (rationalExponent_mul hpodd hmodd).symm

/-- **The rational-denominator supplement for `1 + i`.** For every integer `m ≡ 1 (mod 4)`,
including negative and composite `m`, the quartic symbol at `m 𝓞 K` is `i ^ ((m - 1) / 4)`.
The same primitive fourth root is used in the numerator and in the value. -/
theorem powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger
    (hζ : IsPrimitiveRoot ζ 4) {m : ℤ} (hm : m ≡ 1 [ZMOD 4]) :
    ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = ζ ^ ((m - 1) / 4) := by
  have hodd : Odd m := Int.odd_iff.mpr (by simp only [Int.ModEq] at hm; omega)
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger_of_odd hodd,
    ZMod.χ₄_int_one_mod_four hm, mul_one]

section Examples

variable (hζ : IsPrimitiveRoot ζ 4)
include hζ

/- An inert prime, a split prime, a prime square, and a negative composite denominator. -/
example : ((powerResidueSymbolIdeal (span {((-3 : ℤ) : 𝓞 K)}) 4
    (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -ζ := by
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger (by decide)]
  norm_num
  exact inv_eq_of_mul_eq_one_left (by rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])

example : ((powerResidueSymbolIdeal (span {((5 : ℤ) : 𝓞 K)}) 4
    (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = ζ := by
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger (by decide)]
  norm_num

example : ((powerResidueSymbolIdeal (span {((9 : ℤ) : 𝓞 K)}) 4
    (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -1 := by
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger (by decide)]
  norm_num [hζ.sq_eq_neg_one]

example : ((powerResidueSymbolIdeal (span {((-15 : ℤ) : 𝓞 K)}) 4
    (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = 1 := by
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger (by decide)]
  norm_num [hζ.pow_eq_one]

end Examples

end IsPrimitiveRoot

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]
  {ζ : K} {hζ : IsPrimitiveRoot ζ 4}

/-! ### Integrality and multiplicativity of the exponent -/

/-- **Multiplicativity of the `1 + i` supplement exponent.** For primary `a₁ + b₁ i` and
`a₂ + b₂ i` in `𝓞 K = ℤ[i]`, the exponent `(a - b - b² - 1) / 4` of their product
`(a₁ a₂ - b₁ b₂) + (a₁ b₂ + b₁ a₂) i` is congruent modulo `4` to the sum of their exponents. -/
theorem IsPrimaryGaussian.sub_sub_sq_sub_one_div_four_mul_modEq_four {a₁ b₁ a₂ b₂ : ℤ}
    (hx₁ : IsPrimaryGaussian ((a₁ : 𝓞 K) + (b₁ : 𝓞 K) * hζ.toInteger))
    (hx₂ : IsPrimaryGaussian ((a₂ : 𝓞 K) + (b₂ : 𝓞 K) * hζ.toInteger)) :
    ((a₁ * a₂ - b₁ * b₂) - (a₁ * b₂ + b₁ * a₂) - (a₁ * b₂ + b₁ * a₂) ^ 2 - 1) / 4 ≡
      (a₁ - b₁ - b₁ ^ 2 - 1) / 4 + (a₂ - b₂ - b₂ ^ 2 - 1) / 4 [ZMOD 4] := by
  have hπ₁ := hζ.isPrimaryGaussian_add_mul_iff.mp hx₁
  have hπ₂ := hζ.isPrimaryGaussian_add_mul_iff.mp hx₂
  simp only [Int.ModEq] at hπ₁ hπ₂
  obtain ⟨u₁, rfl⟩ : ∃ u₁, a₁ = 2 * u₁ + 1 := ⟨(a₁ - 1) / 2, by omega⟩
  obtain ⟨r₁, rfl⟩ : ∃ r₁, b₁ = 2 * (u₁ + 2 * r₁) := ⟨(b₁ - 2 * u₁) / 4, by omega⟩
  obtain ⟨u₂, rfl⟩ : ∃ u₂, a₂ = 2 * u₂ + 1 := ⟨(a₂ - 1) / 2, by omega⟩
  obtain ⟨r₂, rfl⟩ : ∃ r₂, b₂ = 2 * (u₂ + 2 * r₂) := ⟨(b₂ - 2 * u₂) / 4, by omega⟩
  set u₃ : ℤ := u₁ + u₂ - 4 * (u₁ * r₂ + r₁ * u₂ + 2 * r₁ * r₂)
  set r₃ : ℤ := r₁ + r₂ + 2 * u₁ * u₂ + 4 * (u₁ * r₂ + r₁ * u₂ + r₁ * r₂)
  have hdiv (u r : ℤ) :
      (2 * u + 1 - 2 * (u + 2 * r) - (2 * (u + 2 * r)) ^ 2 - 1) / 4 = -r - (u + 2 * r) ^ 2 := by
    have h : 2 * u + 1 - 2 * (u + 2 * r) - (2 * (u + 2 * r)) ^ 2 - 1 =
        4 * (-r - (u + 2 * r) ^ 2) := by ring
    rw [h, Int.mul_ediv_cancel_left _ (by decide)]
  have ha₃ : (2 * u₁ + 1) * (2 * u₂ + 1) - 2 * (u₁ + 2 * r₁) * (2 * (u₂ + 2 * r₂)) =
      2 * u₃ + 1 := by simp only [u₃]; ring
  have hb₃ : (2 * u₁ + 1) * (2 * (u₂ + 2 * r₂)) + 2 * (u₁ + 2 * r₁) * (2 * u₂ + 1) =
      2 * (u₃ + 2 * r₃) := by simp only [u₃, r₃]; ring
  rw [ha₃, hb₃, hdiv u₃ r₃, hdiv u₁ r₁, hdiv u₂ r₂]
  have hsq (u r : ℤ) : -r - (u + 2 * r) ^ 2 ≡ -r - u ^ 2 [ZMOD 4] :=
    Int.modEq_iff_dvd.mpr ⟨u * r + r ^ 2, by ring⟩
  refine (hsq u₃ r₃).trans ((Int.ModEq.trans ?_ ((hsq u₁ r₁).add (hsq u₂ r₂)).symm))
  have hu₃ : u₃ ≡ u₁ + u₂ [ZMOD 4] :=
    Int.modEq_iff_dvd.mpr ⟨u₁ * r₂ + r₁ * u₂ + 2 * r₁ * r₂, by simp only [u₃]; ring⟩
  have hr₃ : r₃ ≡ r₁ + r₂ + 2 * u₁ * u₂ [ZMOD 4] :=
    Int.modEq_iff_dvd.mpr ⟨-(u₁ * r₂ + r₁ * u₂ + r₁ * r₂), by simp only [r₃]; ring⟩
  refine (hr₃.neg.sub (hu₃.pow 2)).trans ?_
  exact Int.modEq_iff_dvd.mpr ⟨u₁ * u₂, by ring⟩

/-! ### Primary elements with coprime coordinates -/

/-- Congruence modulo `4` matching the exponent recovered from `((1 + i) / π)₄ ^ (2 k + 1)` to
`(a - b - b² - 1) / 4` when `π = a + b i` is primary and `b = 2 ^ k * b'` with `k ≥ 1` and `b'`
odd. -/
private theorem one_add_exponent_coprime_modEq {a b b' : ℤ} {k : ℕ}
    (hπ : a ≡ 1 [ZMOD 4] ∧ b ≡ 0 [ZMOD 4] ∨ a ≡ 3 [ZMOD 4] ∧ b ≡ 2 [ZMOD 4])
    (hk : 1 ≤ k) (hb' : Odd b') (hb : b = (2 : ℤ) ^ k * b') :
    (2 * (k : ℤ) + 1) *
        ((a - b - 1) / 4 + 2 * (((b - a - 1) / 2) * ((a - 1) / 2)) -
          2 * (((b' - 1) / 2) * ((a - 1) / 2)) - (k : ℤ) * ((a - 1) / 2)) ≡
      (a - b - b ^ 2 - 1) / 4 [ZMOD 4] := by
  simp only [Int.ModEq] at hπ
  rcases eq_or_lt_of_le hk with rfl | hk2
  · obtain ⟨w, rfl⟩ := hb'
    have hb_eq : b = 4 * w + 2 := by rw [hb]; ring
    subst hb_eq
    obtain ⟨s, rfl⟩ : ∃ s, a = 4 * s + 3 := ⟨a / 4, by omega⟩
    have h1 : (4 * s + 3 - (4 * w + 2) - 1) / 4 = s - w := by omega
    have h2 : (4 * w + 2 - (4 * s + 3) - 1) / 2 = 2 * w - 2 * s - 1 := by omega
    have h3 : (4 * s + 3 - 1) / 2 = 2 * s + 1 := by omega
    have h4 : (2 * w + 1 - 1) / 2 = w := by omega
    have h5 : (4 * s + 3 - (4 * w + 2) - (4 * w + 2) ^ 2 - 1) / 4 =
        s - w - 4 * w ^ 2 - 4 * w - 1 := by
      have h : 4 * s + 3 - (4 * w + 2) - (4 * w + 2) ^ 2 - 1 =
          4 * (s - w - 4 * w ^ 2 - 4 * w - 1) := by ring
      rw [h, Int.mul_ediv_cancel_left _ (by decide)]
    rw [h1, h2, h3, h4, h5]
    exact Int.modEq_iff_dvd.mpr ⟨6 * s ^ 2 - 3 * w * s + 7 * s - w ^ 2 - 2 * w + 2, by ring⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
    set c : ℤ := (2 : ℤ) ^ m * b'
    have hb_eq : b = 4 * c := by
      rw [hb, pow_add]; simp only [c]; ring
    subst hb_eq
    obtain ⟨s, rfl⟩ : ∃ s, a = 4 * s + 1 := ⟨a / 4, by omega⟩
    have h1 : (4 * s + 1 - 4 * c - 1) / 4 = s - c := by omega
    have h3 : (4 * s + 1 - 1) / 2 = 2 * s := by omega
    have h5 : (4 * s + 1 - 4 * c - (4 * c) ^ 2 - 1) / 4 = s - c - 4 * c ^ 2 := by
      have h : 4 * s + 1 - 4 * c - (4 * c) ^ 2 - 1 = 4 * (s - c - 4 * c ^ 2) := by ring
      rw [h, Int.mul_ediv_cancel_left _ (by decide)]
    rw [h1, h3, h5]
    set p : ℤ := (4 * c - (4 * s + 1) - 1) / 2
    set q : ℤ := (b' - 1) / 2
    cases m with
    | zero =>
      push_cast
      exact Int.modEq_iff_dvd.mpr
        ⟨4 * s - 5 * p * s + 5 * q * s + c - c ^ 2, by ring⟩
    | succ m' =>
      set c' : ℤ := (2 : ℤ) ^ m' * b'
      have hc : c = 2 * c' := by simp only [c, c', pow_succ]; ring
      rw [hc]
      push_cast
      exact Int.modEq_iff_dvd.mpr
        ⟨(2 + (m' : ℤ) + 1) ^ 2 * s - (2 * (2 + (m' : ℤ) + 1) + 1) * (p - q) * s +
          (2 + (m' : ℤ) + 1) * c' - 4 * c' ^ 2, by ring⟩

/-- For primary `π = a + b i` with `IsCoprime a b` and an odd divisor `b'` of `b`, evaluates
`(b' / π)₄ = i ^ (2 * ((b' - 1) / 2) * ((a - 1) / 2))`. -/
private theorem symbol_odd_part_of_isCoprime {a b b' : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hab' : IsCoprime a b') (hb'_odd : Odd b') (hdvd : b' ∣ b) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (b' : 𝓞 K)) : 𝓞 K) : K) =
      ζ ^ (2 * (((b' - 1) / 2) * ((a - 1) / 2))) := by
  rw [hx.coe_quartic_reciprocity_intCast_add_mul_of_odd hb'_odd]
  have hcong : Ideal.Quotient.mk (span {(b' : 𝓞 K)}) ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) =
      Ideal.Quotient.mk (span {(b' : 𝓞 K)}) (a : 𝓞 K) := by
    rw [Ideal.Quotient.eq, mem_span_singleton]
    obtain ⟨t, rfl⟩ := hdvd
    exact ⟨(t : 𝓞 K) * hζ.toInteger, by push_cast; ring⟩
  have hrat : powerResidueSymbolIdeal (span {(b' : 𝓞 K)}) 4
      (Ideal.Quotient.mk _ (a : 𝓞 K)) = 1 := by
    simpa only [map_intCast] using Ideal.powerResidueSymbolIdeal_intCast_four (K := K) hab'
  rw [hcong, hrat, RingOfIntegers.coe_eq_algebraMap, map_one, one_mul, ← hζ.sq_eq_neg_one,
    ← zpow_ofNat, ← zpow_mul]

/-- For primary `π = a + b i` with `IsCoprime a b`, evaluates
`((b - a) / π)₄ = i ^ ((a - b - 1) / 4 + 2 * ((b - a - 1) / 2) * ((a - 1) / 2))`. -/
private theorem symbol_sub_of_isCoprime {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) (hab : IsCoprime a b) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((b - a : ℤ) : 𝓞 K)) : 𝓞 K) : K) =
      ζ ^ ((a - b - 1) / 4 + 2 * (((b - a - 1) / 2) * ((a - 1) / 2))) := by
  have hπ := hζ.isPrimaryGaussian_add_mul_iff.mp hx
  have hab_mod : a - b ≡ 1 [ZMOD 4] := by simp only [Int.ModEq] at hπ ⊢; omega
  have hba_odd : Odd (b - a) := Int.odd_iff.mpr (by simp only [Int.ModEq] at hab_mod; omega)
  rw [hx.coe_quartic_reciprocity_intCast_add_mul_of_odd hba_odd]
  have hcong : Ideal.Quotient.mk (span {((b - a : ℤ) : 𝓞 K)})
      ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) =
      Ideal.Quotient.mk (span {((b - a : ℤ) : 𝓞 K)}) ((b : 𝓞 K) * (1 + hζ.toInteger)) := by
    rw [Ideal.Quotient.eq, mem_span_singleton]
    exact ⟨-1, by push_cast; ring⟩
  have hb_ba : IsCoprime b (b - a) := by
    obtain ⟨u, v, huv⟩ := hab
    exact ⟨v + u, -u, by linear_combination huv⟩
  have hrat : powerResidueSymbolIdeal (span {((b - a : ℤ) : 𝓞 K)}) 4
      (Ideal.Quotient.mk _ (b : 𝓞 K)) = 1 := by
    simpa only [map_intCast] using Ideal.powerResidueSymbolIdeal_intCast_four (K := K) hb_ba
  have hspan : span {((b - a : ℤ) : 𝓞 K)} = span {((a - b : ℤ) : 𝓞 K)} := by
    have hneg : ((b - a : ℤ) : 𝓞 K) = -((a - b : ℤ) : 𝓞 K) := by push_cast; ring
    rw [hneg, span_singleton_neg]
  rw [hcong, map_mul, map_mul, hrat, one_mul, hspan,
    hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger hab_mod,
    ← hζ.sq_eq_neg_one, ← zpow_ofNat, ← zpow_mul, ← zpow_add₀ (hζ.ne_zero (by decide))]

/-- For any primary element `x` of `𝓞 K = ℤ[i]`, `1 + i` is coprime to `x`, so its quartic
residue symbol at `x 𝓞 K` is a fourth root of unity. -/
private theorem symbol_one_add_pow_four_eq_one {x : 𝓞 K} (hx : IsPrimaryGaussian x) :
    (((powerResidueSymbolIdeal (span {x}) 4
        (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K)) ^ 4 = 1 := by
  obtain ⟨c, hc⟩ := dvd_trans (dvd_pow_self (1 + hζ.toInteger) (by decide : 3 ≠ 0))
    (hζ.isPrimaryGaussian_iff.mp hx)
  have hu : IsUnit (Ideal.Quotient.mk (span {x}) (1 + hζ.toInteger)) :=
    Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp
      ((isCoprime_span_singleton_iff _ _).mpr ⟨-c, 1, by linear_combination hc⟩))
  have h := congrArg (algebraMap (𝓞 K) K) (powerResidueSymbolIdeal_pow_eq_one (n := 4) hu)
  rw [map_pow, map_one, ← RingOfIntegers.coe_eq_algebraMap] at h
  exact h

omit [IsCyclotomicExtension {4} ℚ K] in
/-- Modulo `a + b i` with `b = 2 ^ k * b'`, `b - a ≡ i ^ (3 k) * b' * (1 + i) ^ (2 k + 1)`. -/
private theorem mk_sub_eq_mk_pow_mul {a b b' : ℤ} {k : ℕ} (hb : b = (2 : ℤ) ^ k * b') :
    Ideal.Quotient.mk (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) ((b - a : ℤ) : 𝓞 K) =
      Ideal.Quotient.mk (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger})
        (hζ.toInteger ^ (3 * k) * (b' : 𝓞 K) * (1 + hζ.toInteger) ^ (2 * k + 1)) := by
  have hsq : hζ.toInteger ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have h2 : (2 : 𝓞 K) = hζ.toInteger ^ 3 * (1 + hζ.toInteger) ^ 2 := by
    linear_combination -(hζ.toInteger ^ 3 + 2 * hζ.toInteger ^ 2 - 2) * hsq
  have hb_cast : (b : 𝓞 K) = (2 : 𝓞 K) ^ k * (b' : 𝓞 K) := by exact_mod_cast hb
  have hpow : (2 : 𝓞 K) ^ k * (b' : 𝓞 K) * (1 + hζ.toInteger) =
      hζ.toInteger ^ (3 * k) * (b' : 𝓞 K) * (1 + hζ.toInteger) ^ (2 * k + 1) := by
    rw [h2, mul_pow, ← pow_mul, ← pow_mul, pow_succ]
    ring
  rw [Ideal.Quotient.eq, mem_span_singleton]
  refine ⟨-1, ?_⟩
  push_cast
  linear_combination (1 + hζ.toInteger) * hb_cast + hpow

/-- The supplementary law for `1 + i` at a primary Gaussian integer `a + b i` with coprime
coordinates and `b ≠ 0`. -/
private theorem powerResidueSymbolIdeal_mk_one_add_toInteger_of_isCoprime {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hab : IsCoprime a b) (hb : b ≠ 0) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) =
      ζ ^ ((a - b - b ^ 2 - 1) / 4) := by
  have hπ := hζ.isPrimaryGaussian_add_mul_iff.mp hx
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by decide)
  -- Factor `b = 2 ^ k * b'` with `k ≥ 1` and `b'` odd.
  obtain ⟨k, m, hm_odd, hm_eq⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hb)
  obtain ⟨b', hb'_odd, hb_eq⟩ : ∃ b' : ℤ, Odd b' ∧ b = (2 : ℤ) ^ k * b' := by
    have hm_int : Odd (m : ℤ) := by obtain ⟨t, rfl⟩ := hm_odd; exact ⟨t, by push_cast; ring⟩
    rcases Int.natAbs_eq b with h | h
    · exact ⟨m, hm_int, by rw [h, hm_eq]; push_cast; ring⟩
    · exact ⟨-m, hm_int.neg, by rw [h, hm_eq]; push_cast; ring⟩
  have hk : 1 ≤ k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    rw [hk_eq, pow_zero, one_mul] at hb_eq
    have hb_even : Even b := ⟨b / 2, by simp only [Int.ModEq] at hπ; omega⟩
    exact (Int.not_even_iff_odd.mpr (hb_eq ▸ hb'_odd)) hb_even
  -- Evaluate the quartic symbol on both sides of `b - a ≡ i ^ (3 k) * b' * (1 + i) ^ (2 k + 1)`.
  set I : Ideal (𝓞 K) := span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}
  set s : K := ((powerResidueSymbolIdeal I 4 (Ideal.Quotient.mk I (1 + hζ.toInteger)) : 𝓞 K) : K)
  have hval := congrArg (fun x ↦ ((powerResidueSymbolIdeal I 4 x : 𝓞 K) : K))
    (mk_sub_eq_mk_pow_mul (hζ := hζ) (a := a) hb_eq)
  simp only [map_mul, map_pow, RingOfIntegers.coe_eq_algebraMap] at hval
  simp only [← RingOfIntegers.coe_eq_algebraMap] at hval
  have hab' : IsCoprime a b' := (hb_eq ▸ hab).of_mul_right_right
  rw [symbol_sub_of_isCoprime hx hab, hx.powerResidueSymbolIdeal_mk_toInteger,
    symbol_odd_part_of_isCoprime hx hab' hb'_odd ⟨(2 : ℤ) ^ k, by rw [hb_eq, mul_comm]⟩] at hval
  have hi_pow : (ζ ^ (-((a - 1) / 2))) ^ (3 * k) = ζ ^ ((k : ℤ) * ((a - 1) / 2)) := by
    rw [← zpow_natCast, ← zpow_mul]
    refine zpow_eq_zpow_of_modEq hζ.pow_eq_one (Int.modEq_iff_dvd.mpr ⟨(k : ℤ) * ((a - 1) / 2), ?_⟩)
    push_cast
    ring
  rw [hi_pow] at hval
  -- Isolate `s ^ (2 k + 1)` and raise to the `(2 k + 1)`-st power using `(2 k + 1)² ≡ 1 (mod 4)`.
  set E : ℤ := (a - b - 1) / 4 + 2 * (((b - a - 1) / 2) * ((a - 1) / 2)) -
      2 * (((b' - 1) / 2) * ((a - 1) / 2)) - (k : ℤ) * ((a - 1) / 2)
  have hs_pow : s ^ (2 * k + 1) = ζ ^ E := by
    have hE : (a - b - 1) / 4 + 2 * (((b - a - 1) / 2) * ((a - 1) / 2)) =
        ((k : ℤ) * ((a - 1) / 2) + 2 * (((b' - 1) / 2) * ((a - 1) / 2))) + E := by
      simp only [E]; ring
    have hmul : ζ ^ ((k : ℤ) * ((a - 1) / 2) + 2 * (((b' - 1) / 2) * ((a - 1) / 2))) * ζ ^ E =
        ζ ^ ((k : ℤ) * ((a - 1) / 2) + 2 * (((b' - 1) / 2) * ((a - 1) / 2))) * s ^ (2 * k + 1) := by
      rw [← zpow_add₀ hζ0, ← hE, hval, zpow_add₀ hζ0]
    exact mul_left_cancel₀ (zpow_ne_zero _ hζ0) hmul.symm
  have hs_recover : (s ^ (2 * k + 1)) ^ (2 * k + 1) = s := by
    have hsqk : (2 * k + 1) * (2 * k + 1) = 4 * (k ^ 2 + k) + 1 := by ring
    rw [← pow_mul, hsqk, pow_add, pow_mul, symbol_one_add_pow_four_eq_one (hζ := hζ) hx,
      one_pow, one_mul, pow_one]
  rw [← hs_recover, hs_pow, ← zpow_natCast, ← zpow_mul, mul_comm E]
  push_cast
  exact zpow_eq_zpow_of_modEq hζ.pow_eq_one (one_add_exponent_coprime_modEq hπ hk hb'_odd hb_eq)

/-! ### The general supplementary law for `1 + i` -/

/-- **The supplementary law for `1 + i` in quartic reciprocity.** If `λ = a + b i` is a primary
element of `𝓞 K = ℤ[i]` (possibly composite), then
`((1 + i) / λ)₄ = i ^ ((a - b - b² - 1) / 4)`,
the symbol being taken at the ideal `λ 𝓞 K` and read in `K`. The same primitive fourth root `i`
is used in the numerator, the coordinates of `λ`, and the value. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) =
      ζ ^ ((a - b - b ^ 2 - 1) / 4) := by
  -- Factor `a + b i = m * (a₀ + b₀ i)` with `m ≡ 1 (mod 4)` and `IsCoprime a₀ b₀`.
  obtain ⟨m, a₀, b₀, hm, hab₀, hα₀, hmul⟩ := hx.exists_intCast_mul_add_mul_isCoprime hζ
  have hcoords : a = m * a₀ ∧ b = m * b₀ := by
    have hdiff : ((a - m * a₀ : ℤ) : 𝓞 K) + ((b - m * b₀ : ℤ) : 𝓞 K) * hζ.toInteger = 0 := by
      push_cast
      linear_combination hmul
    have hdvd : ((0 : ℤ) : 𝓞 K) ∣
        ((a - m * a₀ : ℤ) : 𝓞 K) + ((b - m * b₀ : ℤ) : 𝓞 K) * hζ.toInteger :=
      ⟨0, by rw [hdiff, mul_zero]⟩
    rw [hζ.intCast_dvd_intCast_add_intCast_mul_toInteger_iff (by decide), zero_dvd_iff,
      zero_dvd_iff, sub_eq_zero, sub_eq_zero] at hdvd
    exact hdvd
  obtain ⟨rfl, rfl⟩ := hcoords
  have hm0 : span {(m : 𝓞 K)} ≠ ⊥ := by
    simpa using (isPrimaryGaussian_intCast_iff (K := K).mpr hm).ne_zero
  have hα₀0 : span {(a₀ : 𝓞 K) + (b₀ : 𝓞 K) * hζ.toInteger} ≠ ⊥ := by
    simpa using hα₀.ne_zero
  rw [hmul, ← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hm0 hα₀0]
  simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap]
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger hm]
  by_cases hb₀ : b₀ = 0
  · subst hb₀
    have ha₀_unit : IsUnit a₀ := isCoprime_zero_right.mp hab₀
    have ha₀_mod := hζ.isPrimaryGaussian_add_mul_iff.mp hα₀
    have ha₀ : a₀ = 1 := by
      rcases Int.isUnit_iff.mp ha₀_unit with rfl | rfl
      · rfl
      · simp only [Int.ModEq] at ha₀_mod; omega
    subst ha₀
    have h1 : ((1 : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger = 1 := by simp
    rw [h1, span_singleton_one, powerResidueSymbolIdeal_top]
    simp
  · rw [powerResidueSymbolIdeal_mk_one_add_toInteger_of_isCoprime hα₀ hab₀ hb₀,
      ← zpow_add₀ (hζ.ne_zero (by decide))]
    have hm_prim : IsPrimaryGaussian ((m : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger) := by
      simpa using isPrimaryGaussian_intCast_iff (K := K).mpr hm
    have hexp := hm_prim.sub_sub_sq_sub_one_div_four_mul_modEq_four hα₀
    simp only [zero_mul, sub_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] at hexp
    exact zpow_eq_zpow_of_modEq hζ.pow_eq_one hexp.symm

/-- **The supplementary law for `1 - i`.** If `λ = a + b i` is primary in `𝓞 K = ℤ[i]`, then
`((1 - i) / λ)_4 = i ^ (-((a + b - b ^ 2 - 1) / 4))`, the symbol being taken at `λ 𝓞 K` and read
in `K`. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_sub_toInteger {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (1 - hζ.toInteger)) : 𝓞 K) : K) =
        ζ ^ (-((a + b - b ^ 2 - 1) / 4)) := by
  have hneg : -ζ = ζ⁻¹ := eq_inv_of_mul_eq_one_left (by
    rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])
  have hζ' : IsPrimitiveRoot (-ζ) 4 := hneg.symm ▸ hζ.inv
  have hi' : hζ'.toInteger = -hζ.toInteger := by
    apply RingOfIntegers.coe_injective
    rw [map_neg]
    exact hζ'.coe_toInteger.trans (congrArg Neg.neg hζ.coe_toInteger.symm)
  have h1 : 1 - hζ.toInteger = 1 + hζ'.toInteger := by rw [hi', sub_eq_add_neg]
  have h2 : (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger =
      (a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * hζ'.toInteger := by
    rw [hi']; push_cast; ring
  have hx' : IsPrimaryGaussian ((a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * hζ'.toInteger) := h2 ▸ hx
  rw [h1, h2, hx'.powerResidueSymbolIdeal_mk_one_add_toInteger, hneg, inv_zpow,
    ← zpow_neg, sub_neg_eq_add, neg_sq]

/-- **The supplementary law for `2` in quartic reciprocity.** If `λ = a + b i` is primary in
`𝓞 K = ℤ[i]`, then `(2 / λ)_4 = i ^ (-(b / 2))`, the symbol being taken at `λ 𝓞 K` and read in
`K`. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_two {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ 2) : 𝓞 K) : K) = ζ ^ (-(b / 2)) := by
  have htwo : (2 : 𝓞 K) = (1 + hζ.toInteger) * (1 - hζ.toInteger) := by
    linear_combination hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  rw [htwo, map_mul, map_mul]
  simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap]
  rw [hx.powerResidueSymbolIdeal_mk_one_add_toInteger,
    hx.powerResidueSymbolIdeal_mk_one_sub_toInteger,
    ← zpow_add₀ (hζ.ne_zero (by decide))]
  congr 1
  obtain ⟨q, hq⟩ := hx.four_dvd_sub_sub_sq_sub_one
  have hx' := (hζ.isPrimaryGaussian_add_mul_iff (a := a) (b := b)).mp hx
  obtain ⟨m, rfl⟩ : ∃ m, b = 2 * m := ⟨b / 2, by simp only [Int.ModEq] at hx'; omega⟩
  omega

/-- **Gauss's criterion for `2` in quartic reciprocity.** For integers `a` and `b` with `a` odd,
the quartic residue symbol `(2 / (a + b i))_4` in `𝓞 K = ℤ[i]` equals `1` if and only if
`8 ∣ b`. -/
theorem _root_.IsPrimitiveRoot.powerResidueSymbolIdeal_span_add_mul_mk_two_eq_one_iff {ζ : K}
    (hζ : IsPrimitiveRoot ζ 4) {a b : ℤ} (ha : Odd a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ 2) = 1 ↔ 8 ∣ b := by
  rcases Int.even_or_odd b with hb | hb
  · wlog hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) generalizing a b
    · have hx' : IsPrimaryGaussian (((-a : ℤ) : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * hζ.toInteger) := by
        rw [hζ.isPrimaryGaussian_add_mul_iff] at hx ⊢
        obtain ⟨k, rfl⟩ := ha
        obtain ⟨l, rfl⟩ := hb
        simp only [Int.ModEq] at hx ⊢
        omega
      have h := this ha.neg hb.neg hx'
      have heq : ((-a : ℤ) : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * hζ.toInteger =
          -((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger) := by push_cast; ring
      rwa [heq, span_singleton_neg, dvd_neg] at h
    have hcoe : (((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ 2) : 𝓞 K) : K) = 1) ↔
        powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
          (Ideal.Quotient.mk _ 2) = 1 := by exact_mod_cast Iff.rfl
    rw [← hcoe, hx.powerResidueSymbolIdeal_mk_two, hζ.zpow_eq_one_iff_dvd, dvd_neg]
    obtain ⟨l, rfl⟩ := hb
    omega
  · set i := hζ.toInteger
    have hsq : i ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
    have hnu : ¬ IsUnit (1 + i) := by
      simpa using hζ.isUnit_intCast_add_intCast_mul_toInteger_iff_of_four (a := 1) (b := 1)
    obtain ⟨k, hk⟩ : ∃ k, a - b = 2 * k :=
      ⟨(a - b) / 2, by obtain ⟨u, rfl⟩ := ha; obtain ⟨v, rfl⟩ := hb; omega⟩
    have hdvd2 : 1 + i ∣ (2 : 𝓞 K) := ⟨1 - i, by linear_combination hsq⟩
    have hdvdx : 1 + i ∣ (a : 𝓞 K) + (b : 𝓞 K) * i := by
      refine ⟨(k : 𝓞 K) * (1 - i) + b, ?_⟩
      have hk' : (a : 𝓞 K) - b = 2 * k := by exact_mod_cast hk
      linear_combination hk' + (k : 𝓞 K) * hsq
    have hncop : ¬ IsCoprime (span {(2 : 𝓞 K)}) (span {(a : 𝓞 K) + (b : 𝓞 K) * i}) := by
      rw [isCoprime_span_singleton_iff]
      exact fun hcop ↦ hnu (hcop.isUnit_of_dvd' hdvd2 hdvdx)
    rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hncop]
    exact iff_of_false zero_ne_one (by obtain ⟨l, rfl⟩ := hb; omega)

section Examples

variable (hζ : IsPrimitiveRoot ζ 4)
include hζ

/- `((1 + i) / (-1 + 2i))₄ = i ^ ((-1 - 2 - 4 - 1) / 4) = i ^ (-2) = -1` at the primary prime
`-1 + 2i` of norm `5`. -/
example : ((powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -1 := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  norm_num [hζ.sq_eq_neg_one]

/- `((1 + i) / (3 + 2i))₄ = i ^ ((3 - 2 - 4 - 1) / 4) = i ^ (-1) = -i` at the primary prime
`3 + 2i` of norm `13`. -/
example : ((powerResidueSymbolIdeal (span {((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -ζ := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  norm_num
  exact inv_eq_of_mul_eq_one_left (by rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])

/- At the composite primary element `3 - 6i = (-3) * (-1 + 2i)`, the symbol is
`(-i) * (-1) = i = i ^ (-7)`. -/
example : ((powerResidueSymbolIdeal (span {((3 : ℤ) : 𝓞 K) + ((-6 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = ζ := by
  rw [IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger
    (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide)]
  have hmod : ((3 - (-6) - (-6) ^ 2 - 1 : ℤ) / 4) ≡ 1 [ZMOD 4] := by decide
  rw [zpow_eq_zpow_of_modEq hζ.pow_eq_one hmod, zpow_one]

/- `(2 / (-1 + 2i))_4 = -i`, `(2 / (1 + 4i))_4 = -1`, and `(2 / (-3 + 8i))_4 = 1` at the primary
primes above `5`, `17`, and `73`. -/
example : ((powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ 2) : 𝓞 K) : K) = -ζ := by
  have hx : IsPrimaryGaussian (((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger) := by
    rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  rw [hx.powerResidueSymbolIdeal_mk_two]
  norm_num
  exact inv_eq_of_mul_eq_one_left (by rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])

example : ((powerResidueSymbolIdeal (span {((1 : ℤ) : 𝓞 K) + ((4 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ 2) : 𝓞 K) : K) = -1 := by
  have hx : IsPrimaryGaussian (((1 : ℤ) : 𝓞 K) + ((4 : ℤ) : 𝓞 K) * hζ.toInteger) := by
    rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  rw [hx.powerResidueSymbolIdeal_mk_two]
  norm_num [hζ.sq_eq_neg_one]

example : powerResidueSymbolIdeal (span {((-3 : ℤ) : 𝓞 K) + ((8 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ 2) = 1 :=
  (hζ.powerResidueSymbolIdeal_span_add_mul_mk_two_eq_one_iff (by decide)).mpr (by decide)

end Examples

end TauCeti
