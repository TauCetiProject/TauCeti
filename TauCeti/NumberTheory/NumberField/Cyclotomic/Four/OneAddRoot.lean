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
import TauCeti.Algebra.GroupWithZero.Basic
import TauCeti.Data.Nat.ModEq
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.QuarticReciprocity.IntCast
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.SupplementaryLaws
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The supplementary laws for `1 + i`, `1 - i`, and `2` in quartic reciprocity

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and let `λ = a + b i` be primary (possibly composite). The quartic residue symbols
of the ramified prime `1 + i`, its conjugate `1 - i`, and `2 = (1 + i)(1 - i)` at the ideal
`λ 𝓞 K` are

* `((1 + i) / λ)_4 = i ^ ((a - b - b² - 1) / 4)`,
* `((1 - i) / λ)_4 = i ^ (-((a + b - b² - 1) / 4))`, and
* `(2 / λ)_4 = i ^ (-(b / 2))`; moreover, `(2 / (a + b i))_4 = 1` if and only if `8 ∣ b` whenever
  `a` is odd.

In particular, for a rational integer `m ≡ 1 (mod 4)`, `((1 + i) / m)_4 = i ^ ((m - 1) / 4)`, and
more generally `((1 + i) / m)_4 = i ^ ((m * χ₄(m) - 1) / 4)` for every odd integer `m`. Together
with the unit supplements in `TauCeti.NumberTheory.NumberField.Cyclotomic.Four.SupplementaryLaws`
and biquadratic reciprocity in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Four.QuarticReciprocity.Primary`, these evaluate any
quartic residue symbol `(α / λ)_4` in `ℤ[i]`.

We first establish the rational-denominator evaluation by pairing conjugate factors at split primes
(following the rational-integer cancellation argument in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue`, where here the paired
contribution is the symbol of `i` rather than `1`) and applying Frobenius at inert primes. For
primary `λ = a + b i` with coprime coordinates, the congruences `a (1 + i) ≡ a + b (mod λ)` and
`λ ≡ b i (1 + i) (mod a + b)` together with `a + b ≡ 1 (mod 4)` and rational-denominator quartic
reciprocity reduce `((1 + i) / λ)_4` to the rational-denominator laws. Factoring out a signed
integer `m ≡ 1 (mod 4)` extends the formula to all primary elements via the additivity of
`(a - b - b² - 1) / 4` modulo `4`.

## Main results

* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger`:
  `((1 + i) / λ)_4 = i ^ ((a - b - b² - 1) / 4)` for primary `λ = a + b i`.
* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_sub_toInteger`:
  `((1 - i) / λ)_4 = i ^ (-((a + b - b² - 1) / 4))` for primary `λ = a + b i`.
* `TauCeti.IsPrimaryGaussian.powerResidueSymbolIdeal_mk_two`,
  `IsPrimitiveRoot.powerResidueSymbolIdeal_span_add_mul_mk_two_eq_one_iff`:
  `(2 / λ)_4 = i ^ (-(b / 2))` for primary `λ = a + b i`, and `(2 / (a + b i))_4 = 1 ↔ 8 ∣ b`
  for any integers `a` and `b` with `a` odd.
* `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger`,
  `IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger_of_odd`:
  `((1 + i) / m)_4 = i ^ ((m - 1) / 4)` for `m ≡ 1 (mod 4)` and
  `i ^ ((m * χ₄(m) - 1) / 4)` for odd `m`.

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

/-! ### The supplementary laws at primary Gaussian integers -/

/-- For primary coordinates `(a, b)`, the combined exponent from `(a / λ)_4` and `(λ / (a + b))_4`
is congruent modulo `4` to `(a - b - b ^ 2 - 1) / 4`. -/
private theorem one_add_exponent_modEq {a b : ℤ}
    (h : a ≡ 1 [ZMOD 4] ∧ b ≡ 0 [ZMOD 4] ∨ a ≡ 3 [ZMOD 4] ∧ b ≡ 2 [ZMOD 4]) :
    2 * ((a ^ 2 - 1) / 8 + ((a - 1) / 2) * ((a - 1) / 2)) - (a + b - 1) / 4 ≡
      (a - b - b ^ 2 - 1) / 4 [ZMOD 4] := by
  simp only [Int.ModEq] at h
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨k, rfl⟩ : ∃ k, a = 4 * k + 1 := ⟨a / 4, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l, b = 4 * l := ⟨b / 4, by omega⟩
    have h8 : ((4 * k + 1) ^ 2 - 1) / 8 = 2 * k ^ 2 + k := by
      have hsq : (4 * k + 1) ^ 2 - 1 = 8 * (2 * k ^ 2 + k) := by ring
      rw [hsq, Int.mul_ediv_cancel_left _ (by decide)]
    have h2 : (4 * k + 1 - 1) / 2 = 2 * k := by omega
    have hsum : (4 * k + 1 + 4 * l - 1) / 4 = k + l := by omega
    have hrhs : (4 * k + 1 - 4 * l - (4 * l) ^ 2 - 1) / 4 = k - l - 4 * l ^ 2 := by
      have h4 : 4 * k + 1 - 4 * l - (4 * l) ^ 2 - 1 = 4 * (k - l - 4 * l ^ 2) := by ring
      rw [h4, Int.mul_ediv_cancel_left _ (by decide)]
    rw [h8, h2, hsum, hrhs]
    exact Int.modEq_iff_dvd.mpr ⟨-(3 * k ^ 2 + l ^ 2), by ring⟩
  · obtain ⟨k, rfl⟩ : ∃ k, a = 4 * k + 3 := ⟨a / 4, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l, b = 4 * l + 2 := ⟨b / 4, by omega⟩
    have h8 : ((4 * k + 3) ^ 2 - 1) / 8 = 2 * k ^ 2 + 3 * k + 1 := by
      have hsq : (4 * k + 3) ^ 2 - 1 = 8 * (2 * k ^ 2 + 3 * k + 1) := by ring
      rw [hsq, Int.mul_ediv_cancel_left _ (by decide)]
    have h2 : (4 * k + 3 - 1) / 2 = 2 * k + 1 := by omega
    have hsum : (4 * k + 3 + (4 * l + 2) - 1) / 4 = k + l + 1 := by omega
    have hrhs : (4 * k + 3 - (4 * l + 2) - (4 * l + 2) ^ 2 - 1) / 4 =
        k - 5 * l - 4 * l ^ 2 - 1 := by
      have h4 : 4 * k + 3 - (4 * l + 2) - (4 * l + 2) ^ 2 - 1 =
          4 * (k - 5 * l - 4 * l ^ 2 - 1) := by ring
      rw [h4, Int.mul_ediv_cancel_left _ (by decide)]
    rw [h8, h2, hsum, hrhs]
    exact Int.modEq_iff_dvd.mpr ⟨-(3 * k ^ 2 + 3 * k + l + l ^ 2 + 1), by ring⟩

/-- The supplementary law for `1 + i` at a primary element `a + b i` with coprime coordinates. -/
private theorem powerResidueSymbolIdeal_mk_one_add_toInteger_of_isCoprime
    {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) (hab : IsCoprime a b) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) =
        ζ ^ ((a - b - b ^ 2 - 1) / 4) := by
  set i := hζ.toInteger
  set x : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * i
  have hsq : i ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hn : a + b ≡ 1 [ZMOD 4] := hx.add_modEq_one
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by decide)
  -- Relate `a (1 + i) ≡ a + b (mod x)` via rational-denominator reciprocity.
  have hmk_x : Ideal.Quotient.mk (span {x}) ((a : 𝓞 K) * (1 + i)) =
      Ideal.Quotient.mk (span {x}) ((a + b : ℤ) : 𝓞 K) :=
    Ideal.Quotient.eq.mpr (mem_span_singleton.mpr
      ⟨i, by simp only [x]; push_cast; linear_combination -(b : 𝓞 K) * hsq⟩)
  have hrel : ((powerResidueSymbolIdeal (span {x}) 4 (Ideal.Quotient.mk _ (a : 𝓞 K)) : 𝓞 K) : K) *
      ((powerResidueSymbolIdeal (span {x}) 4 (Ideal.Quotient.mk _ (1 + i)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {((a + b : ℤ) : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ x) : 𝓞 K) : K) := by
    have h := congrArg (algebraMap (𝓞 K) K)
      (congrArg (powerResidueSymbolIdeal (span {x}) 4) hmk_x)
    rw [map_mul, map_mul, map_mul, hx.quartic_reciprocity_intCast hn] at h
    simpa only [RingOfIntegers.coe_eq_algebraMap] using h
  -- Evaluate `(x / (a + b))_4` using `x ≡ b i (1 + i) (mod a + b)`.
  have hrhs : ((powerResidueSymbolIdeal (span {((a + b : ℤ) : 𝓞 K)}) 4
      (Ideal.Quotient.mk _ x) : 𝓞 K) : K) = ζ ^ (-((a + b - 1) / 4)) := by
    have hcop_bn : IsCoprime b (a + b) := by
      obtain ⟨u, v, huv⟩ := hab
      exact ⟨v - u, u, by linear_combination huv⟩
    have hmk_n : Ideal.Quotient.mk (span {((a + b : ℤ) : 𝓞 K)}) x =
        Ideal.Quotient.mk (span {((a + b : ℤ) : 𝓞 K)}) ((b : 𝓞 K) * (i * (1 + i))) :=
      Ideal.Quotient.eq.mpr (mem_span_singleton.mpr
        ⟨1, by simp only [x]; push_cast; linear_combination -(b : 𝓞 K) * hsq⟩)
    rw [hmk_n, map_mul, map_mul, map_mul, map_mul, map_intCast,
      powerResidueSymbolIdeal_intCast_four hcop_bn, one_mul]
    simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap]
    rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger hn,
      hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger hn,
      ← hζ.sq_eq_neg_one, ← zpow_ofNat, ← zpow_mul, ← zpow_add₀ hζ0]
    exact TauCeti.zpow_eq_zpow_of_modEq hζ.pow_eq_one
      (Int.modEq_iff_dvd.mpr ⟨-((a + b - 1) / 4), by ring⟩)
  set ea : ℤ := (a ^ 2 - 1) / 8 + ((a - 1) / 2) * ((a - 1) / 2)
  rw [hx.powerResidueSymbolIdeal_add_mul_mk_intCast_of_isCoprime hab, hrhs] at hrel
  have hsq_sign : (-1 : K) ^ ea * (-1 : K) ^ ea = 1 := by
    rw [← zpow_add₀ (by norm_num)]
    exact Even.neg_one_zpow ⟨ea, by ring⟩
  calc ((powerResidueSymbolIdeal (span {x}) 4 (Ideal.Quotient.mk _ (1 + i)) : 𝓞 K) : K)
      = (-1 : K) ^ ea * ((-1 : K) ^ ea *
          ((powerResidueSymbolIdeal (span {x}) 4 (Ideal.Quotient.mk _ (1 + i)) : 𝓞 K) : K)) := by
        rw [← mul_assoc, hsq_sign, one_mul]
    _ = ζ ^ (2 * ea - (a + b - 1) / 4) := by
        rw [hrel, ← hζ.sq_eq_neg_one, ← zpow_ofNat, ← zpow_mul, ← zpow_add₀ hζ0, ← sub_eq_add_neg]
    _ = ζ ^ ((a - b - b ^ 2 - 1) / 4) :=
        TauCeti.zpow_eq_zpow_of_modEq hζ.pow_eq_one
          (one_add_exponent_modEq ((hζ.isPrimaryGaussian_add_mul_iff (a := a) (b := b)).mp hx))

section

variable {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {a b : ℤ}

/-- **The supplementary law for `1 + i`.** If `λ = a + b i` is primary in `𝓞 K = ℤ[i]`, including
composite `λ`, then `((1 + i) / λ)_4 = i ^ ((a - b - b ^ 2 - 1) / 4)`, the symbol being taken at
the ideal `λ 𝓞 K` and read in `K`. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_add_toInteger
    (hx : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) =
        ζ ^ ((a - b - b ^ 2 - 1) / 4) := by
  obtain ⟨m, a₁, b₁, hm, hab, hα, hmul⟩ := hx.exists_intCast_mul_add_mul_isCoprime hζ
  have hcoords : a = m * a₁ ∧ b = m * b₁ := by
    have hdvd : ((0 : ℤ) : 𝓞 K) ∣
        ((a - m * a₁ : ℤ) : 𝓞 K) + ((b - m * b₁ : ℤ) : 𝓞 K) * hζ.toInteger := by
      rw [Int.cast_zero, zero_dvd_iff]
      push_cast
      linear_combination hmul
    obtain ⟨ha, hb⟩ :=
      (hζ.intCast_dvd_intCast_add_intCast_mul_toInteger_iff (by decide)).mp hdvd
    rw [zero_dvd_iff, sub_eq_zero] at ha hb
    exact ⟨ha, hb⟩
  have hm0 : span {(m : 𝓞 K)} ≠ ⊥ := by
    have hm_ne : m ≠ 0 := by simp only [Int.ModEq] at hm; omega
    simpa using hm_ne
  have hα0 : span {(a₁ : 𝓞 K) + (b₁ : 𝓞 K) * hζ.toInteger} ≠ ⊥ := by
    simpa using hα.ne_zero
  have hm_prim : IsPrimaryGaussian ((m : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * hζ.toInteger) := by
    simpa using (isPrimaryGaussian_intCast_iff (K := K)).mpr hm
  rw [hmul, ← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hm0 hα0]
  simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap]
  rw [hζ.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger hm,
    powerResidueSymbolIdeal_mk_one_add_toInteger_of_isCoprime hα hab,
    ← zpow_add₀ (hζ.ne_zero (by decide))]
  have hexp := hm_prim.sub_sub_sq_sub_one_div_four_modEq_add hα
  simp only [zero_mul, sub_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at hexp
  rw [hcoords.1, hcoords.2]
  exact TauCeti.zpow_eq_zpow_of_modEq hζ.pow_eq_one hexp.symm

/-- **The supplementary law for `1 - i`.** If `λ = a + b i` is primary in `𝓞 K = ℤ[i]`, then
`((1 - i) / λ)_4 = i ^ (-((a + b - b ^ 2 - 1) / 4))`, the symbol being taken at `λ 𝓞 K` and read
in `K`. -/
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_one_sub_toInteger
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
theorem IsPrimaryGaussian.powerResidueSymbolIdeal_mk_two
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

end

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

/-! ### Examples -/

section PrimaryExamples

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
include hζ

/- `((1 + i) / (-1 + 2i))_4 = i ^ ((-1 - 2 - 4 - 1) / 4) = i ^ (-2) = -1` at the primary prime
`-1 + 2i` of norm `5`. -/
example : ((powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -1 := by
  have hx : IsPrimaryGaussian (((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger) := by
    rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  rw [hx.powerResidueSymbolIdeal_mk_one_add_toInteger]
  norm_num [hζ.sq_eq_neg_one]

/- `((1 + i) / (3 + 2i))_4 = i ^ ((3 - 2 - 4 - 1) / 4) = i ^ (-1) = -i` at the primary prime
`3 + 2i` of norm `13`. -/
example : ((powerResidueSymbolIdeal (span {((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = -ζ := by
  have hx : IsPrimaryGaussian (((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger) := by
    rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  rw [hx.powerResidueSymbolIdeal_mk_one_add_toInteger]
  norm_num
  exact inv_eq_of_mul_eq_one_left (by rw [neg_mul, ← pow_two, hζ.sq_eq_neg_one, neg_neg])

/- At the composite primary element `3 - 6i = (-3)(-1 + 2i)` with `gcd(3, -6) = 3 ≠ 1`,
`((1 + i) / (3 - 6i))_4 = i ^ ((3 + 6 - 36 - 1) / 4) = i ^ (-7) = i`, matching `(-i) * (-1)`. -/
example : ((powerResidueSymbolIdeal (span {((3 : ℤ) : 𝓞 K) + ((-6 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = ζ := by
  have hx : IsPrimaryGaussian (((3 : ℤ) : 𝓞 K) + ((-6 : ℤ) : 𝓞 K) * hζ.toInteger) := by
    rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  rw [hx.powerResidueSymbolIdeal_mk_one_add_toInteger]
  have h : ζ ^ ((-7 : ℤ)) = ζ ^ (1 : ℤ) :=
    TauCeti.zpow_eq_zpow_of_modEq hζ.pow_eq_one (by decide)
  simpa using h

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

end PrimaryExamples

end TauCeti
