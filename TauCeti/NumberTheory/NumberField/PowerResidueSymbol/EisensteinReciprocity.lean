/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Primary
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import TauCeti.NumberTheory.NumberField.Ideal.Norm
import TauCeti.NumberTheory.NumberField.PrimeIdeal
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Ideal.Pointwise
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The Eisenstein reciprocity law

Let `p` be an odd prime, `K = ℚ(ζ_p)` the `p`-th cyclotomic field, and `ζ ∈ 𝓞 K` a primitive
`p`-th root of unity. The **Eisenstein reciprocity law** states that for every primary algebraic
integer `α ∈ 𝓞 K` (`TauCeti.IsEisensteinPrimary ζ α`) and every rational integer `a : ℤ` not
divisible by `p`,

  `(α / a)_p = (a / α)_p`,

where the two sides are the `p`-th power residue symbols at the principal ideals `a 𝓞 K` and
`α 𝓞 K` (`TauCeti.IsEisensteinPrimary.eisenstein_reciprocity`). No coprimality between `α` and `a`
is required (when they are not coprime, both symbols vanish), and `α` may be a unit and `a` may be
`±1` (in which case both sides equal `1`).

The proof proceeds in three steps:

1. **The symbol of the Stickelberger product (`m ≥ 2` arbitrary).** For any integer `m ≥ 2`, any
   `α ∈ 𝓞 K` in the `m`-th cyclotomic field `K = ℚ(ζ_m)`, and any ideal `A` of `𝓞 K`, Galois
   equivariance of the power residue symbol and the ideal-norm product formula
   `∏ σ : Gal(K/ℚ), σ • P = N(P) 𝓞 K` (`Ideal.prod_smul_eq_span_absNorm`) give
   `(α ^ γ / A)_m = (α / N A)_m` (`Ideal.powerResidueSymbol_stickelbergerProduct`,
   `Ideal.powerResidueSymbolIdeal_stickelbergerProduct`), where `α ^ γ = stickelbergerProduct m α`.
2. **Eisenstein reciprocity at the norm of an ideal.** When `p` is an odd prime, `α` is primary,
   and `P` is a maximal ideal of norm prime to `p`, Stickelberger's relation for primary integers
   (`IsPrimitiveRoot.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct`) gives
   `Φ((α)) = ±α ^ γ`, and `(-1 / P)_p = 1` for odd `p`. Combining Step 1 with the residue symbol
   identity `(Φ((α)) / P)_p = (N P / α)_p` (`Ideal.powerResidueSymbol_stickelbergerPhi`) yields
   `(α / N P)_p = (N P / α)_p`, and multiplicativity extends this to every ideal `𝔅` whose norm is
   prime to `p` (`TauCeti.IsEisensteinPrimary.eisenstein_reciprocity_absNorm`).
3. **Reduction to rational integers.** For a rational prime `q ≠ p`, pick a prime `P` of `𝓞 K`
   above `q`. Its norm is `q ^ f` where `f` is the order of `q` modulo `p`, so `f ∣ p - 1` and
   hence `f` is coprime to `p`. Step 2 gives `(α / q)_p ^ f = (q / α)_p ^ f` between `p`-th roots
   of unity (or `0 = 0`), whence `(α / q)_p = (q / α)_p`. Multiplicativity and `(-1 / ·)_p = 1`
   extend the identity to all `n : ℕ` with `¬ p ∣ n` and all `a : ℤ` with `¬ (p : ℤ) ∣ a`.

## Main results

* `Ideal.powerResidueSymbol_stickelbergerProduct`: `(α ^ γ / P)_m = (α / N P)_m` for `m ≥ 2` and
  any maximal ideal `P` of the `m`-th cyclotomic field.
* `Ideal.powerResidueSymbolIdeal_stickelbergerProduct`: `(α ^ γ / A)_m = (α / N A)_m` for `m ≥ 2`
  and any ideal `A` of the `m`-th cyclotomic field.
* `TauCeti.IsEisensteinPrimary.eisenstein_reciprocity_absNorm`: `(α / N 𝔅)_p = (N 𝔅 / α)_p` for
  primary `α` and any ideal `𝔅` of norm prime to `p`.
* `TauCeti.IsEisensteinPrimary.eisenstein_reciprocity_natCast`: `(α / n)_p = (n / α)_p` for
  primary `α` and any natural number `n` not divisible by `p`.
* `TauCeti.IsEisensteinPrimary.eisenstein_reciprocity`: **the Eisenstein reciprocity law**,
  `(α / a)_p = (a / α)_p` for primary `α` and any rational integer `a` not divisible by `p`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Theorem 4.1 and (25),
  pp. 69–73.
* N. Xu, *Reciprocity Laws*, §6, Theorem 6.9 and Corollary 6.13, pp. 21–24.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §2.
-/

public section

open NumberField UniqueFactorizationMonoid IsCyclotomicExtension.Rat
open scoped Pointwise

namespace Ideal

section StickelbergerProduct

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} [NeZero m]
  [IsCyclotomicExtension {m} ℚ K]

/-- **The power residue symbol of the Stickelberger product at a prime.** In the `m`-th cyclotomic
field (`m ≥ 2`), for any algebraic integer `α` and any maximal ideal `P`,
`(α ^ γ / P)_m = (α / N P)_m`, where `α ^ γ = TauCeti.stickelbergerProduct m α`. No coprimality
or primality hypothesis on `m`, `P`, or `α` is needed. -/
theorem powerResidueSymbol_stickelbergerProduct (P : Ideal (𝓞 K)) [P.IsMaximal] (hm : 2 ≤ m)
    (α : 𝓞 K) :
    powerResidueSymbol P m (Quotient.mk P (TauCeti.stickelbergerProduct m α)) =
      powerResidueSymbolIdeal (span {(absNorm P : 𝓞 K)}) m (Quotient.mk _ α) := by
  classical
  have : Fact (1 < m) := ⟨hm⟩
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have hc (σ : Gal(K/ℚ)) : (galEquivZMod m K σ : ZMod m).val ≠ 0 := fun h ↦
    Units.ne_zero (galEquivZMod m K σ) ((ZMod.val_eq_zero _).mp h)
  -- Each factor `(σ⁻¹ α / P)_m ^ c(σ)` equals `σ ((σ⁻¹ α / P)_m) = (α / σ P)_m`.
  have hfactor (σ : Gal(K/ℚ)) :
      powerResidueSymbol P m (Quotient.mk P (σ⁻¹ • α)) ^ (galEquivZMod m K σ : ZMod m).val =
        powerResidueSymbolIdeal (σ • P) m (Quotient.mk (σ • P) α) := by
    rw [powerResidueSymbolIdeal_of_isMaximal (σ • P)]
    by_cases h0 : Quotient.mk P (σ⁻¹ • α) = 0
    · rw [h0, MulChar.map_zero, zero_pow (hc σ)]
      have hmem : α ∈ σ • P :=
        mem_pointwise_smul_iff_inv_smul_mem.mpr (Quotient.eq_zero_iff_mem.mp h0)
      rw [Quotient.eq_zero_iff_mem.mpr hmem, MulChar.map_zero]
    · have hpow : powerResidueSymbol P m (Quotient.mk P (σ⁻¹ • α)) ^ m = 1 :=
        powerResidueSymbol_pow_eq_one h0
      rw [← galEquivZMod_smul_of_pow_eq m K σ hpow,
        ← MulSemiringAction.toRingEquiv_apply_apply (G := Gal(K/ℚ)),
        map_powerResidueSymbol P (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ)]
      have hsmul : MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ (σ⁻¹ • α) = α := by
        rw [MulSemiringAction.toRingEquiv_apply_apply, smul_inv_smul]
      rw [hsmul]
      -- `σ • P` is definitionally `P.map (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ)`.
      rfl
  have hne : ∀ σ ∈ (Finset.univ : Finset Gal(K/ℚ)), σ • P ≠ ⊥ := fun σ _ ↦
    Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (RingOfIntegers.not_isField K)
  rw [TauCeti.stickelbergerProduct_def, map_prod, map_prod]
  simp_rw [map_pow, hfactor]
  rw [← powerResidueSymbolIdeal_prod_right hne α, prod_smul_eq_span_absNorm P]

/-- **The power residue symbol of the Stickelberger product at an arbitrary ideal.** In the `m`-th
cyclotomic field (`m ≥ 2`), for any algebraic integer `α` and any ideal `A` of `𝓞 K`,
`(α ^ γ / A)_m = (α / N A)_m`. -/
theorem powerResidueSymbolIdeal_stickelbergerProduct (A : Ideal (𝓞 K)) (hm : 2 ≤ m) (α : 𝓞 K) :
    powerResidueSymbolIdeal A m (Quotient.mk A (TauCeti.stickelbergerProduct m α)) =
      powerResidueSymbolIdeal (span {(absNorm A : 𝓞 K)}) m (Quotient.mk _ α) := by
  have : Fact (1 < m) := ⟨hm⟩
  induction A using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.cast_zero, span_singleton_zero, powerResidueSymbolIdeal_bot]
    -- At `⊥` the trivial character tests whether the argument is a unit; `α ^ γ` is a unit iff
    -- `α` is.
    have hunit : IsUnit (Quotient.mk (⊥ : Ideal (𝓞 K)) (TauCeti.stickelbergerProduct m α)) ↔
        IsUnit (Quotient.mk (⊥ : Ideal (𝓞 K)) α) := by
      simp only [Quotient.isUnit_mk_iff, sup_bot_eq, span_singleton_eq_top]
      constructor
      · intro hu
        rw [TauCeti.stickelbergerProduct_def, IsUnit.prod_iff] at hu
        have hc1 : (galEquivZMod m K 1 : ZMod m).val ≠ 0 := fun h ↦
          Units.ne_zero (galEquivZMod m K 1) ((ZMod.val_eq_zero _).mp h)
        simpa using (isUnit_pow_iff hc1).mp (hu 1 (Finset.mem_univ 1))
      · intro hu
        rw [TauCeti.stickelbergerProduct_def, IsUnit.prod_iff]
        intro σ _
        exact (hu.map (MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K) σ⁻¹)).pow _
    by_cases hu : IsUnit (Quotient.mk (⊥ : Ideal (𝓞 K)) α)
    · rw [MulChar.one_apply (hunit.mpr hu), MulChar.one_apply hu]
    · rw [MulChar.map_nonunit _ (hunit.not.mpr hu), MulChar.map_nonunit _ hu]
  | h₂ A hA =>
    rw [isUnit_iff.mp hA, absNorm_top, Nat.cast_one, span_singleton_one,
      powerResidueSymbolIdeal_top, powerResidueSymbolIdeal_top]
  | h₃ A P hA₀ hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    have hNP : span {(absNorm P : 𝓞 K)} ≠ ⊥ := by
      simpa [span_singleton_eq_bot] using absNorm_eq_zero_iff.not.mpr hP.ne_zero
    have hNA : span {(absNorm A : 𝓞 K)} ≠ ⊥ := by
      simpa [span_singleton_eq_bot] using absNorm_eq_zero_iff.not.mpr hA₀
    rw [powerResidueSymbolIdeal_mul_right hP.ne_zero hA₀, powerResidueSymbolIdeal_of_isMaximal,
      P.powerResidueSymbol_stickelbergerProduct hm α, ih,
      ← powerResidueSymbolIdeal_mul_right hNP hNA, span_singleton_mul_span_singleton,
      ← Nat.cast_mul, ← map_mul absNorm]

end StickelbergerProduct

end Ideal

namespace TauCeti

open Ideal

/-- If `x ^ n = 1` and `y ^ n = 1` in a monoid and `x ^ k = y ^ k` for an exponent `k` coprime to
`n`, then `x = y`. -/
private theorem eq_of_pow_eq_of_coprime {M : Type*} [Monoid M] {x y : M} {n k : ℕ}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (hxy : x ^ k = y ^ k) (hcop : k.Coprime n) : x = y := by
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [Nat.coprime_zero_right] at hcop
    simpa [hcop] using hxy
  have : NeZero n := ⟨hn0⟩
  let m : ℕ := (((ZMod.unitOfCoprime k hcop)⁻¹ : (ZMod n)ˣ) : ZMod n).val
  have hmod : k * m ≡ 1 [MOD n] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp [m]
  calc x = x ^ 1 := (pow_one x).symm
    _ = x ^ (k * m) := (pow_eq_pow_of_modEq hmod hx).symm
    _ = (x ^ k) ^ m := pow_mul x k m
    _ = (y ^ k) ^ m := congrArg (· ^ m) hxy
    _ = y ^ (k * m) := (pow_mul y k m).symm
    _ = y ^ 1 := pow_eq_pow_of_modEq hmod hy
    _ = y := pow_one y

section Reciprocity

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- Eisenstein reciprocity at the norm of a maximal ideal `P` with `(N P).Coprime p`. -/
private theorem eisenstein_reciprocity_absNorm_of_isMaximal {ζ α : 𝓞 K}
    (hα : IsEisensteinPrimary ζ α) (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) (P : Ideal (𝓞 K))
    [P.IsMaximal] (hP : (absNorm P).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm P : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm P : 𝓞 K)) := by
  by_cases hcop : IsCoprime (span {α}) (span {(absNorm P : 𝓞 K)})
  · have hN : (absNorm (span {α})).Coprime (absNorm P) :=
      absNorm_coprime_of_isCoprime_span_natCast hcop
    have hp : p.Prime := Fact.out
    have hstick := powerResidueSymbol_stickelbergerPhi (span {α}) P hP hN hp.two_le
    have hζK : IsPrimitiveRoot (ζ : K) p :=
      hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
    have hα' : IsEisensteinPrimary hζK.toInteger α := by
      have heq : hζK.toInteger = ζ := RingOfIntegers.coe_injective hζK.coe_toInteger
      rwa [heq]
    have hodd : Odd p := hp.odd_of_ne_two hp2
    rcases hζK.stickelbergerPhi_eq_or_eq_neg_stickelbergerProduct hp2 hα' with hΦ | hΦ
    · rw [hΦ, P.powerResidueSymbol_stickelbergerProduct hp.two_le α] at hstick
      exact hstick
    · rw [hΦ, map_neg, ← powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbolIdeal_neg hodd,
        powerResidueSymbolIdeal_of_isMaximal,
        P.powerResidueSymbol_stickelbergerProduct hp.two_le α] at hstick
      exact hstick
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]

/-- **Eisenstein reciprocity at the norm of an ideal.** Let `p` be an odd prime, `K = ℚ(ζ_p)`,
`α ∈ 𝓞 K` a primary algebraic integer, and `𝔅` an ideal of `𝓞 K` whose norm is prime to `p`. Then
`(α / N 𝔅)_p = (N 𝔅 / α)_p`. If `α` and `N 𝔅` are not coprime, both symbols vanish. -/
theorem IsEisensteinPrimary.eisenstein_reciprocity_absNorm {ζ α : 𝓞 K}
    (hα : IsEisensteinPrimary ζ α) (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) {𝔅 : Ideal (𝓞 K)}
    (h𝔅 : (absNorm 𝔅).Coprime p) :
    powerResidueSymbolIdeal (span {(absNorm 𝔅 : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (absNorm 𝔅 : 𝓞 K)) := by
  induction 𝔅 using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left] at h𝔅
    exact absurd h𝔅 (Fact.out : p.Prime).ne_one
  | h₂ 𝔅 h =>
    rw [isUnit_iff.mp h, absNorm_top, Nat.cast_one, span_singleton_one,
      powerResidueSymbolIdeal_top, map_one, MulChar.map_one]
  | h₃ 𝔅 P h𝔅₀ hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    rw [map_mul, Nat.coprime_mul_iff_left] at h𝔅
    have hNP : span {(absNorm P : 𝓞 K)} ≠ ⊥ := by
      simpa [span_singleton_eq_bot] using absNorm_eq_zero_iff.not.mpr hP.ne_zero
    have hN𝔅 : span {(absNorm 𝔅 : 𝓞 K)} ≠ ⊥ := by
      simpa [span_singleton_eq_bot] using absNorm_eq_zero_iff.not.mpr h𝔅₀
    rw [map_mul absNorm, Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hNP hN𝔅, map_mul, map_mul,
      eisenstein_reciprocity_absNorm_of_isMaximal hα hζ hp2 P h𝔅.1, ih h𝔅.2]

/-- Eisenstein reciprocity at a rational prime `q ≠ p`. -/
private theorem eisenstein_reciprocity_prime {ζ α : 𝓞 K} (hα : IsEisensteinPrimary ζ α)
    (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) := by
  have hp : p.Prime := Fact.out
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hPprime, hP0, hPover⟩ := _root_.NumberField.exists_prime_ne_zero_liesOver (K := K) q hq
  have : P.IsMaximal := hPprime.isMaximal (by simpa [zero_eq_bot] using hP0)
  have hqcop : q.Coprime p := (Nat.coprime_primes hq hp).mpr hqp
  have hq_not_dvd : ¬ q ∣ p := fun h ↦ hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h)
  have hNP : absNorm P = q ^ P.inertiaDeg ℤ := (pow_inertiaDeg q P).symm
  -- The residue degree `f = orderOf (q : ZMod p)` divides `φ(p) = p - 1`, so `f` is coprime to `p`.
  have hf_dvd : P.inertiaDeg ℤ ∣ p - 1 := by
    rw [inertiaDeg_eq_of_not_dvd q K P hq_not_dvd]
    have hord : orderOf (q : ZMod p) = orderOf (ZMod.unitOfCoprime q hqcop) := by
      simpa using orderOf_injective (Units.coeHom (ZMod p)) Units.val_injective
        (ZMod.unitOfCoprime q hqcop)
    rw [hord, ← Nat.totient_prime hp, ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have hfcop : (P.inertiaDeg ℤ).Coprime p :=
    ((Nat.coprime_self_sub_left hp.one_le).mpr (Nat.coprime_one_left p)).coprime_dvd_left hf_dvd
  -- Reciprocity at `N P = q ^ f` gives `(α / q)_p ^ f = (q / α)_p ^ f`.
  have hrec := hα.eisenstein_reciprocity_absNorm hζ hp2 (hNP ▸ hqcop.pow_left _)
  rw [hNP, Nat.cast_pow, ← span_singleton_pow, powerResidueSymbolIdeal_pow_right,
    map_pow, map_pow] at hrec
  by_cases hcop : IsCoprime (span {α}) (span {(q : 𝓞 K)})
  · exact eq_of_pow_eq_of_coprime
      (powerResidueSymbolIdeal_pow_eq_one
        (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop)))
      (powerResidueSymbolIdeal_pow_eq_one
        (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop.symm)))
      hrec hfcop
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]

/-- **Eisenstein reciprocity for natural numbers.** Let `p` be an odd prime, `K = ℚ(ζ_p)`,
`α ∈ 𝓞 K` primary, and `n : ℕ` not divisible by `p`. Then `(α / n)_p = (n / α)_p`. -/
theorem IsEisensteinPrimary.eisenstein_reciprocity_natCast {ζ α : 𝓞 K}
    (hα : IsEisensteinPrimary ζ α) (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) {n : ℕ}
    (hn : ¬ p ∣ n) :
    powerResidueSymbolIdeal (span {(n : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (n : 𝓞 K)) := by
  induction n using induction_on_prime with
  | h₁ => exact absurd (dvd_zero p) hn
  | h₂ n hu =>
    obtain rfl := Nat.isUnit_iff.mp hu
    rw [Nat.cast_one, span_singleton_one, powerResidueSymbolIdeal_top, map_one, MulChar.map_one]
  | h₃ n q hn₀ hq ih =>
    have hqp : q.Prime := Nat.prime_iff.mpr hq
    have hqne : q ≠ p := fun h ↦ hn (h ▸ dvd_mul_right q n)
    have hndvd : ¬ p ∣ n := fun h ↦ hn (dvd_mul_of_dvd_right h q)
    have hq0 : span {(q : 𝓞 K)} ≠ ⊥ := by simpa [span_singleton_eq_bot] using hqp.ne_zero
    have hn0 : span {(n : 𝓞 K)} ≠ ⊥ := by simpa [span_singleton_eq_bot] using hn₀
    rw [Nat.cast_mul, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right hq0 hn0, map_mul, map_mul,
      eisenstein_reciprocity_prime hα hζ hp2 hqp hqne, ih hndvd]

/-- **The Eisenstein reciprocity law.** Let `p` be an odd prime, `K = ℚ(ζ_p)`, `ζ ∈ 𝓞 K` a
primitive `p`-th root of unity, `α ∈ 𝓞 K` a primary algebraic integer, and `a : ℤ` a rational
integer not divisible by `p`. Then `(α / a)_p = (a / α)_p`, the `p`-th power residue symbols at the
principal ideals `a 𝓞 K` and `α 𝓞 K`. The integer `a` may be negative, composite, or `±1`, and `α`
may be a unit or share a factor with `a` (in which case both sides vanish). -/
theorem IsEisensteinPrimary.eisenstein_reciprocity {ζ α : 𝓞 K} (hα : IsEisensteinPrimary ζ α)
    (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    powerResidueSymbolIdeal (span {(a : 𝓞 K)}) p (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
  have hnat : ¬ p ∣ a.natAbs := fun h ↦ ha (Int.natCast_dvd.mpr h)
  have hrec := hα.eisenstein_reciprocity_natCast hζ hp2 hnat
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  rcases Int.natAbs_eq a with h | h
  · have heq : (a : 𝓞 K) = (a.natAbs : 𝓞 K) := by
      simpa using congrArg (Int.cast : ℤ → 𝓞 K) h
    rw [heq]
    exact hrec
  · have hneg : (a : 𝓞 K) = -(a.natAbs : 𝓞 K) := by
      simpa using congrArg (Int.cast : ℤ → 𝓞 K) h
    rw [hneg, span_singleton_neg, map_neg, powerResidueSymbolIdeal_neg hodd]
    exact hrec

end Reciprocity

end TauCeti

section Examples

open Ideal TauCeti

/- For `p = 3`, `α = -1 - 3ω` is primary (of norm `7`). At the ideal `𝔅 = (2)` of norm `4`,
Eisenstein reciprocity at the norm of an ideal gives `(α / 4)_3 = (4 / α)_3`, i.e.,
`(α / 2)_3 ^ 2 = (2 / α)_3 ^ 2`, and Eisenstein reciprocity at `a = 2` gives
`(α / 2)_3 = (2 / α)_3`. -/
example {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] {ω : 𝓞 K}
    (hω : IsPrimitiveRoot ω 3) :
    let α : 𝓞 K := -1 - 3 * ω
    powerResidueSymbolIdeal (span {(4 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) 3 (Ideal.Quotient.mk _ (4 : 𝓞 K)) ∧
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ α) ^ 2 =
      powerResidueSymbolIdeal (span {α}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) ^ 2 ∧
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ α) =
      powerResidueSymbolIdeal (span {α}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
  intro α
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have h := hω.pow_eq_one
    have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr (hω.ne_one (by decide))
    exact (mul_eq_zero.mp (by linear_combination h)).resolve_left hne
  have hα : IsEisensteinPrimary ω α := by
    rw [isEisensteinPrimary_iff]
    refine ⟨⟨-1, ω - 1, by linear_combination hω2⟩, -1, 1, ?_⟩
    push_cast
    linear_combination -hω2
  have hN2 : absNorm (span {(2 : 𝓞 K)}) = 4 := by
    rw [← Nat.cast_ofNat (n := 2), absNorm_span_natCast, RingOfIntegers.rank,
      IsCyclotomicExtension.Rat.finrank 3 K]
    decide
  have h4 := hα.eisenstein_reciprocity_absNorm hω (by decide) (𝔅 := span {(2 : 𝓞 K)})
    (by rw [hN2]; decide)
  rw [hN2, Nat.cast_ofNat] at h4
  have h2 := hα.eisenstein_reciprocity hω (by decide) (a := 2) (by decide)
  rw [Int.cast_ofNat] at h2
  refine ⟨h4, ?_, h2⟩
  have h4eq : span {(4 : 𝓞 K)} = span {(2 : 𝓞 K)} ^ 2 := by
    rw [span_singleton_pow]
    norm_num
  have h4cast : (4 : 𝓞 K) = (2 : 𝓞 K) ^ 2 := by norm_num
  rw [h4eq, powerResidueSymbolIdeal_pow_right, h4cast, map_pow, map_pow] at h4
  exact h4

/- At `a = 1` and `a = -1`, both sides of Eisenstein reciprocity are `1` trivially. -/
example {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (hp2 : p ≠ 2) (α : 𝓞 K) :
    powerResidueSymbolIdeal (span {(1 : 𝓞 K)}) p (Ideal.Quotient.mk _ α) = 1 ∧
    powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (1 : 𝓞 K)) = 1 ∧
    powerResidueSymbolIdeal (span {((-1 : ℤ) : 𝓞 K)}) p (Ideal.Quotient.mk _ α) = 1 ∧
    powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ ((-1 : ℤ) : 𝓞 K)) = 1 := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  refine ⟨?_, by simp, ?_, by simp [powerResidueSymbolIdeal_neg hodd]⟩
  · rw [span_singleton_one, powerResidueSymbolIdeal_top]
  · rw [Int.cast_neg, Int.cast_one, span_singleton_neg, span_singleton_one,
      powerResidueSymbolIdeal_top]

/- The primary hypothesis cannot be dropped: multiplying `α` by `ζ` leaves `(q / α)_p` unchanged
while multiplying `(α / q)_p` by `(ζ / q)_p = ζ ^ ((q ^ (p - 1) - 1) / p)` for any rational prime
`q ≠ p`. In particular, for `p = 3`, `q = 2`, and `α = -1 - 3ω` (nonunit of norm `7`), the
non-primary associate `ω * α` violates reciprocity: `(ω α / 2)_3 ≠ (2 / ω α)_3`. -/
example {p q : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hq : q.Prime)
    (hqp : q ≠ p) (α : 𝓞 K) :
    powerResidueSymbolIdeal (span {ζ * α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) =
      powerResidueSymbolIdeal (span {α}) p (Ideal.Quotient.mk _ (q : 𝓞 K)) ∧
    powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ (ζ * α)) =
      ζ ^ ((q ^ (p - 1) - 1) / p) *
        powerResidueSymbolIdeal (span {(q : 𝓞 K)}) p (Ideal.Quotient.mk _ α) := by
  have hp : p.Prime := Fact.out
  have hunit : IsUnit ζ := hζ.isUnit hp.ne_zero
  have hspan : span {ζ * α} = span {α} :=
    span_singleton_eq_span_singleton.mpr (associated_unit_mul_left α ζ hunit)
  have hNq : absNorm (span {(q : 𝓞 K)}) = q ^ (p - 1) := by
    rw [absNorm_span_natCast, RingOfIntegers.rank, IsCyclotomicExtension.Rat.finrank p K,
      Nat.totient_prime hp]
  have hcop : (absNorm (span {(q : 𝓞 K)})).Coprime p :=
    hNq ▸ ((Nat.coprime_primes hq hp).mpr hqp).pow_left _
  refine ⟨by rw [hspan], ?_⟩
  rw [map_mul, map_mul, powerResidueSymbolIdeal_mk_of_pow_eq_one hcop hζ.pow_eq_one, hNq]

example {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] {ω : 𝓞 K}
    (hω : IsPrimitiveRoot ω 3) :
    let α : 𝓞 K := -1 - 3 * ω
    powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ (ω * α)) ≠
      powerResidueSymbolIdeal (span {ω * α}) 3 (Ideal.Quotient.mk _ (2 : 𝓞 K)) := by
  intro α
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have h := hω.pow_eq_one
    have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr (hω.ne_one (by decide))
    exact (mul_eq_zero.mp (by linear_combination h)).resolve_left hne
  have hα : IsEisensteinPrimary ω α := by
    rw [isEisensteinPrimary_iff]
    refine ⟨⟨-1, ω - 1, by linear_combination hω2⟩, -1, 1, ?_⟩
    push_cast
    linear_combination -hω2
  have hcop : IsCoprime (span {α}) (span {(2 : 𝓞 K)}) := by
    rw [isCoprime_span_singleton_iff]
    exact ⟨2 + 3 * ω, -3, by linear_combination -9 * hω2⟩
  have hne0 : powerResidueSymbolIdeal (span {(2 : 𝓞 K)}) 3 (Ideal.Quotient.mk _ α) ≠ 0 :=
    powerResidueSymbolIdeal_mk_eq_zero_iff.not.mpr (not_not.mpr hcop)
  have hunit : IsUnit ω := hω.isUnit (by decide)
  have hspan : span {ω * α} = span {α} :=
    span_singleton_eq_span_singleton.mpr (associated_unit_mul_left α ω hunit)
  have hN2 : absNorm (span {(2 : 𝓞 K)}) = 4 := by
    rw [← Nat.cast_ofNat (n := 2), absNorm_span_natCast, RingOfIntegers.rank,
      IsCyclotomicExtension.Rat.finrank 3 K]
    decide
  have hrec := hα.eisenstein_reciprocity hω (by decide) (a := 2) (by decide)
  rw [Int.cast_ofNat] at hrec
  rw [hspan, map_mul, map_mul,
    powerResidueSymbolIdeal_mk_of_pow_eq_one (by rw [hN2]; decide) hω.pow_eq_one, hN2]
  norm_num only
  rw [pow_one, ← hrec]
  intro h
  have h1 : ω = 1 := mul_right_cancel₀ hne0 (h.trans (one_mul _).symm)
  exact hω.ne_one (by decide) h1

end Examples
