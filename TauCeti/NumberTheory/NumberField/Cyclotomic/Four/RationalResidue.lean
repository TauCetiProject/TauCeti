/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Cyclotomic
import Mathlib.NumberTheory.SumTwoSquares
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# Quartic residue symbols of rational integers

In the fourth cyclotomic field `K = ℚ(i)`, the quartic residue symbol `(n / m)₄` is `1` for
coprime rational integers `n` and `m`, where the denominator means the ideal `m 𝓞 K`. This is the
rational-denominator lemma used throughout quartic reciprocity, where it removes the symbols
whose numerator and denominator are both rational integers.

By multiplicativity in the denominator it suffices to treat a rational prime `q`:

* if `q ≢ 3 (mod 4)`, then `q = x² + y² = β β'` with `β = x + y i` and `β' = x - y i`;
  complex conjugation inverts the symbol of `n` at `β`
  (`Ideal.powerResidueSymbolIdeal_map_intCast_mul_eq_one`), so the symbols at `β` and at `β'`
  cancel. This covers `q = 2 = (1 + i) (1 - i)` as well;
* if `q ≡ 3 (mod 4)`, then `q 𝓞 K` is prime of norm `q²`
  (`TauCeti.prime_natCast_of_mod_four_eq_three`), and
  `(n / q)₄ ≡ n ^ ((q² - 1) / 4) = (n ^ (q - 1)) ^ ((q + 1) / 4) ≡ 1 (mod q)` by Fermat's little
  theorem (`Ideal.powerResidueSymbol_intCast_eq_one`).

The individual symbols at the conjugate primes over a split prime need not be trivial: for
instance `(3 / (-1 + 2i))₄ = i`.

## Main results

* `Ideal.powerResidueSymbolIdeal_intCast_four`: `(n / m)₄ = 1` for coprime integers `n` and `m`.

## References

* N. Xu, *Reciprocity Laws*, §5, Proposition 5.10 and its proof.
-/

public section

open NumberField IsCyclotomicExtension.Rat

namespace Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

variable [HasEnoughRootsOfUnity (𝓞 K) 4]

/-- The split and ramified case: if the rational prime `q` is a sum of two squares
`x² + y² = (x + y i) (x - y i)`, the symbols of `n` at the two conjugate factors cancel. -/
private theorem powerResidueSymbolIdeal_natCast_four_of_mod_four_ne_three {n : ℤ} {q : ℕ}
    (hq : q.Prime) (hq3 : q % 4 ≠ 3) (h : IsCoprime n q) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 n = 1 := by
  have := Fact.mk hq
  obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq hq3
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  set ζ := hζ.toInteger
  let σ := (galEquivZMod 4 K).symm (-1)
  set τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ
  have hσ : galEquivZMod 4 K σ = -1 := MulEquiv.apply_symm_apply _ _
  -- Conjugation sends `i` to `i ^ 3 = -i`, so `q = β (τ β)` for `β = x + y i`.
  have hτζ : τ ζ = ζ ^ 3 := by
    have h := galEquivZMod_smul_of_pow_eq 4 K σ hζ.toInteger_isPrimitiveRoot.pow_eq_one
    rw [hσ] at h
    exact h
  set β : 𝓞 K := x + y * ζ
  have hqβ : (q : 𝓞 K) = τ β * β := by
    have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
    rw [← hxy, map_add, map_mul, map_natCast, map_natCast, hτζ]
    push_cast
    linear_combination (-((x : 𝓞 K) * y * ζ) - (y : 𝓞 K) ^ 2 * (ζ ^ 2 - 1)) * hsq
  have hβ : β ≠ 0 := by
    rintro hβ
    rw [hβ, mul_zero, Nat.cast_eq_zero] at hqβ
    exact hq.ne_zero hqβ
  have hcop : IsCoprime (n : 𝓞 K) (τ β * β) := by
    rw [← hqβ, ← Int.cast_natCast]
    exact h.map (Int.castRingHom (𝓞 K))
  have hmapβ : (span {β}).map τ = span {τ β} := by
    rw [map_span, Set.image_singleton]
  rw [hqβ, ← span_singleton_mul_span_singleton,
    powerResidueSymbolIdeal_mul_right_intCast (by simpa using hβ) (by simpa using hβ), ← hmapβ]
  refine powerResidueSymbolIdeal_map_intCast_mul_eq_one hσ _ ?_
  rw [← map_intCast (Quotient.mk (span {β}))]
  exact Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp
    ((isCoprime_span_singleton_iff _ _).mpr hcop.of_mul_right_right))

/-- The inert case: if `q ≡ 3 (mod 4)`, then `q 𝓞 K` is a prime of norm `q²`, and `n` is a
fourth power residue modulo it by Fermat's little theorem. -/
private theorem powerResidueSymbolIdeal_natCast_four_of_mod_four_eq_three {n : ℤ} {q : ℕ}
    (hq : q.Prime) (hq3 : q % 4 = 3) (h : IsCoprime n q) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) 4 n = 1 := by
  have hN := TauCeti.absNorm_span_natCast_four (K := K) q
  have : (span {(q : 𝓞 K)}).IsMaximal :=
    ((span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr
      (TauCeti.prime_natCast_of_mod_four_eq_three hq hq3)).isMaximal (by simpa using hq.ne_zero)
  -- `4 (q - 1) ∣ q² - 1 = (q - 1) (q + 1)` since `4 ∣ q + 1`.
  have hdvd : 4 * (q - 1) ∣ absNorm (span {(q : 𝓞 K)}) - 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
    refine ⟨k + 1, ?_⟩
    rw [hN, show 4 * k + 3 - 1 = 4 * k + 2 by omega,
      show (4 * k + 3) ^ 2 = 4 * (4 * k + 2) * (k + 1) + 1 by ring, Nat.add_sub_cancel]
  rw [powerResidueSymbolIdeal_of_isMaximal]
  exact powerResidueSymbol_intCast_eq_one hq (mem_span_singleton_self _) hdvd h

/-- **The quartic residue symbol of coprime rational integers is trivial** in the fourth
cyclotomic field `ℚ(i)`: `(n / m)₄ = 1` for coprime integers `n` and `m`, the denominator being
the principal ideal `m 𝓞 K`. No sign, parity or primality condition is needed. -/
@[simp]
theorem powerResidueSymbolIdeal_intCast_four {m n : ℤ} (h : IsCoprime n m) :
    powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 n = 1 := by
  induction m using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    -- The symbol at the zero ideal is the trivial character, and `n = ±1`.
    have hn : IsUnit (n : 𝓞 K ⧸ span {((0 : ℤ) : 𝓞 K)}) :=
      (isCoprime_zero_right.mp h).map (Int.castRingHom _)
    revert hn
    rw [Int.cast_zero, span_singleton_eq_bot.mpr rfl, powerResidueSymbolIdeal_bot]
    exact MulChar.one_apply
  | h₂ m hm =>
    have hm' : IsUnit (m : 𝓞 K) := hm.map (Int.castRingHom (𝓞 K))
    rw [span_singleton_eq_top.mpr hm', powerResidueSymbolIdeal_top]
  | h₃ m p hm hp ih =>
    obtain ⟨hnp, hnm⟩ := IsCoprime.mul_right_iff.mp h
    have hp0 : span {(p : 𝓞 K)} ≠ ⊥ := by simpa using hp.ne_zero
    have hm0 : span {(m : 𝓞 K)} ≠ ⊥ := by simpa using hm
    rw [Int.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right_intCast hp0 hm0, ih hnm, mul_one]
    -- Reduce to the rational prime `q = |p|`.
    have hq := Int.prime_iff_natAbs_prime.mp hp
    have hpq : span {(p : 𝓞 K)} = span {(p.natAbs : 𝓞 K)} := by
      rcases Int.natAbs_eq p with hp' | hp' <;> rw [hp'] <;> simp
    have hnq : IsCoprime n p.natAbs := by
      rcases Int.natAbs_eq p with hp' | hp' <;> rw [hp'] at hnp
      · exact hnp
      · exact (IsCoprime.neg_right_iff _ _).mp hnp
    rw [hpq]
    by_cases hq3 : p.natAbs % 4 = 3
    · exact powerResidueSymbolIdeal_natCast_four_of_mod_four_eq_three hq hq3 hnq
    · exact powerResidueSymbolIdeal_natCast_four_of_mod_four_ne_three hq hq3 hnq

/- `(2 / 3)₄ = 1` at the inert prime `3`, where `2 ^ ((9 - 1) / 4) = 4 ≡ 1 (mod 3)`, and
`(3 / 5)₄ = 1` at the split prime `5`. -/
example : powerResidueSymbolIdeal (span {((3 : ℤ) : 𝓞 K)}) 4 (2 : ℤ) = 1 :=
  powerResidueSymbolIdeal_intCast_four (by decide)

example : powerResidueSymbolIdeal (span {((5 : ℤ) : 𝓞 K)}) 4 (3 : ℤ) = 1 :=
  powerResidueSymbolIdeal_intCast_four (by decide)

omit [IsCyclotomicExtension {4} ℚ K] in
/-- At an element `π` of norm `5`, the symbol of `3` is the fourth root of unity `μ ≡ 3 (mod π)`.
This computes the symbols at the two conjugate factors of `5` in the examples below. -/
private theorem powerResidueSymbolIdeal_three_of_absNorm_eq_five {π μ : 𝓞 K}
    (hN : absNorm (span {π}) = 5) (hμ : μ ^ 4 = 1) (hπ : π ∣ μ - 3) :
    powerResidueSymbolIdeal (span {π}) 4 (3 : ℤ) = μ := by
  have hprime : (span {π}).IsPrime :=
    isPrime_of_irreducible_absNorm (by rw [hN]; exact Nat.prime_five)
  have : (span {π}).IsMaximal :=
    hprime.isMaximal fun h ↦ by rw [h, absNorm_bot] at hN; exact absurd hN (by norm_num)
  have hcop : (absNorm (span {π})).Coprime 4 := by rw [hN]; norm_num
  have h3 : ((3 : ℤ) : 𝓞 K ⧸ span {π}) ≠ 0 := by
    -- Otherwise `π ∣ 3` and `π ∣ μ - 3`, so `π` divides the unit `μ`.
    intro h
    rw [← map_intCast (Quotient.mk (span {π})), Quotient.eq_zero_iff_mem,
      mem_span_singleton] at h
    have hu : IsUnit π := isUnit_of_dvd_unit (by simpa using dvd_add hπ h)
      (IsUnit.of_pow_eq_one hμ (by norm_num))
    rw [span_singleton_eq_top.mpr hu, absNorm_top] at hN
    exact absurd hN (by norm_num)
  rw [powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbol_eq_iff hcop h3 hμ, hN,
    ← map_intCast (Quotient.mk (span {π})), pow_one, Quotient.eq, mem_span_singleton]
  simpa using hπ

section Examples

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
include hζ

/- The symbols of `3` at the conjugate primary primes `-1 + 2i` and `-1 - 2i` over `5` are `i`
and `-i = i ^ 3`: only their product `(3 / 5)₄` is trivial. -/
example : powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (3 : ℤ) = hζ.toInteger := by
  have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  refine powerResidueSymbolIdeal_three_of_absNorm_eq_five ?_
    hζ.toInteger_isPrimitiveRoot.pow_eq_one ⟨1 + hζ.toInteger, ?_⟩
  · rw [absNorm_span_singleton, hζ.norm_intCast_add_intCast_mul_toInteger_of_four]
    rfl
  · push_cast
    linear_combination (-2 : 𝓞 K) * hsq

example : powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K) + ((-2 : ℤ) : 𝓞 K) * hζ.toInteger}) 4
    (3 : ℤ) = hζ.toInteger ^ 3 := by
  have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  refine powerResidueSymbolIdeal_three_of_absNorm_eq_five ?_
    (by rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow])
    ⟨1 - hζ.toInteger, ?_⟩
  · rw [absNorm_span_singleton, hζ.norm_intCast_add_intCast_mul_toInteger_of_four]
    rfl
  · push_cast
    linear_combination (hζ.toInteger - 2) * hsq

end Examples

end Ideal
