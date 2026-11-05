/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal
import TauCeti.Algebra.GroupWithZero.Basic
import TauCeti.Data.Nat.ModEq
import Mathlib.Algebra.CharP.Lemmas
import TauCeti.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The quartic symbol of `1 + i` at rational denominators

The rational-denominator case of the supplementary law for `1 + i` is an input to
its evaluation at general primary Gaussian integers. We compute it by pairing conjugate
factors at split primes and by Frobenius at inert primes. For every rational integer
`m ≡ 1 (mod 4)`, including negative and composite denominators,
`IsPrimitiveRoot.powerResidueSymbolIdeal_span_intCast_mk_one_add_toInteger` proves
`((1 + i) / m)₄ = i ^ ((m - 1) / 4)`.

The conjugate-factor construction follows the rational-integer cancellation argument in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue`, but the numerator here is
not fixed by conjugation: the paired contribution is the symbol of `i`, rather than `1`.

## References

* C. F. Gauss, *Theoria residuorum biquadraticorum, Commentatio secunda*, §§68–76.
* N. Xu, *Reciprocity Laws*, §5, for the primary convention and the rational-denominator
  quartic-symbol calculations.
-/

public section

open NumberField Ideal IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]
  [HasEnoughRootsOfUnity (𝓞 K) 4] {ζ : K}

omit [IsCyclotomicExtension {4} ℚ K] in
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
  refine (powerResidueSymbol_eq_iff ?_ (by simpa only [map_add, map_one] using hn)
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

private theorem symbol_one_add_int (hζ : IsPrimitiveRoot ζ 4) {m : ℤ} (hm : Odd m) :
    ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4
      (Ideal.Quotient.mk _ (1 + hζ.toInteger)) : 𝓞 K) : K) = ζ ^ rationalExponent m := by
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
  rw [symbol_one_add_int hζ hodd, rationalExponent,
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
