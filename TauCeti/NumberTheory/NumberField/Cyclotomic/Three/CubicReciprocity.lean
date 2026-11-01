/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Three.JacobiSum
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.NumberTheory.NumberField.PrimeIdeal
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# The law of cubic reciprocity

Let `K = ℚ(ζ₃)`, so that `𝓞 K = ℤ[ω]`, and write `(α / π)_3` for the cubic residue symbol at the
ideal `π 𝓞 K`. The law of cubic reciprocity states that `(π₂ / π₁)_3 = (π₁ / π₂)_3` for primary
primes `π₁` and `π₂` of `ℤ[ω]` with different norms
(`TauCeti.IsPrimaryEisenstein.cubic_reciprocity`). It covers the three classical cases at once:
two rational primes `q₁ ≠ q₂ ≡ 2 (mod 3)`, a rational prime and a prime of norm `p ≡ 1 (mod 3)`,
and two primes of different norms `p₁, p₂ ≡ 1 (mod 3)`.

For a primary prime `π` of norm `p` and `P = π 𝓞 K`, let `χ = (· / P)_3` and let `ψ` be a primitive
additive character of `𝓞 K ⧸ P`. Since `J(χ, χ) = π`, the cube of the Gauss sum is
`g(χ, ψ) ^ 3 = p π` (`Ideal.gaussSum_powerResidueSymbol_three_pow_three_eq`). Dually, the Gauss
sum power `Φ(P) = g(χ⁻¹, ψ) ^ 3` of Stickelberger's relation is `p` times the conjugate of `π`,
which we record as `π Φ(P) = p ^ 2` (`Ideal.mul_stickelbergerPhi_three_eq_absNorm_sq`). The
residue symbol of `Φ(P)` at a second prime `P'` of norm prime to `3 p` is
`(Φ(P) / P')_3 = (N P' / P)_3`
(`Ideal.powerResidueSymbol_stickelbergerPhi`), so

`(π / P')_3 (N P' / P)_3 = (p / P')_3 ^ 2`.

Applying this to `(P, P') = (π₁ 𝓞 K, π₂ 𝓞 K)` and to `(π₂ 𝓞 K, π₁ 𝓞 K)` and eliminating the
values `(p₁ / π₂)_3` and `(p₂ / π₁)_3`, which are cube roots of unity, gives the reciprocity law.
Primes with different norms have coprime norms, since `K` is quadratic
(`TauCeti.NumberField.coprime_absNorm_of_absNorm_ne`), and a primary element has norm prime to `3`
(`TauCeti.IsPrimaryEisenstein.absNorm_span_singleton_coprime_three`).

## Main results

* `Ideal.gaussSum_powerResidueSymbol_three_pow_three_eq`: `g(χ, ψ) ^ 3 = p π` for the cubic residue
  symbol `χ` at a primary prime `π` of norm `p`.
* `Ideal.mul_stickelbergerPhi_three_eq_absNorm_sq`: `π Φ(π 𝓞 K) = p ^ 2`.
* `TauCeti.IsPrimaryEisenstein.cubic_reciprocity`: the law of cubic reciprocity.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3, Theorem 3.1 and
  its proof, Proposition 3.3 and (11).
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §3,
  Theorem 1, and Chapter 14, §5.
* N. Xu, *Reciprocity Laws*, §4, Theorem 4.6.
-/

public section

open NumberField

namespace Ideal

open TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
  {P : Ideal (𝓞 K)} [P.IsMaximal]

/-- **The cube of the cubic Gauss sum.** Let `K = ℚ(ζ₃)` and let `P = π 𝓞 K` be a prime with `π`
primary. For every injective ring homomorphism `f` from `𝓞 K` to a domain `R` and every primitive
additive character `ψ` of `𝓞 K ⧸ P` with values in `R`, the Gauss sum of the cubic residue
symbol `χ = (· / P)_3`, pushed to `R` along `f`, satisfies `g(χ, ψ) ^ 3 = N P · f π`. -/
theorem gaussSum_powerResidueSymbol_three_pow_three_eq [Fintype (𝓞 K ⧸ P)] {π : 𝓞 K}
    (hπ : P = span {π}) (hπ' : IsPrimaryEisenstein π) {R : Type*} [CommRing R] [IsDomain R]
    {f : 𝓞 K →+* R} (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R}
    (hψ : ψ.IsPrimitive) :
    gaussSum ((powerResidueSymbol P 3).ringHomComp f) ψ ^ 3 = absNorm P * f π := by
  let _ := Ideal.Quotient.field P
  have hP : (absNorm P).Coprime 3 := hπ ▸ hπ'.absNorm_span_singleton_coprime_three
  have hχ : orderOf ((powerResidueSymbol P 3).ringHomComp f) = 3 := by
    rw [← MulChar.ringHomCompHom_apply, orderOf_injective _ (MulChar.injective_ringHomComp hf),
      orderOf_powerResidueSymbol hP]
  rw [gaussSum_pow_three_eq_card_mul_jacobiSum hχ hψ, jacobiSum_ringHomComp,
    jacobiSum_powerResidueSymbol_three_eq hP hπ hπ', ← Nat.card_eq_fintype_card,
    ← absNorm_eq_natCard]

/-- **The Gauss sum power `Φ(P)` of a primary prime of `ℤ[ω]`.** If `K = ℚ(ζ₃)` and `P = π 𝓞 K`
is a prime with `π` primary, then `π Φ(P) = N P ^ 2`, where `Φ(P) = g(χ⁻¹, ψ) ^ 3` is the cube of
the Gauss sum of the inverse of the cubic residue symbol `χ = (· / P)_3`. Equivalently, `Φ(P)` is
`N P` times the conjugate of `π`. -/
theorem mul_stickelbergerPhi_three_eq_absNorm_sq {π : 𝓞 K} (hπ : P = span {π})
    (hπ' : IsPrimaryEisenstein π) :
    π * stickelbergerPhi P 3 = absNorm P ^ 2 := by
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hP : (absNorm P).Coprime 3 := hπ ▸ hπ'.absNorm_span_singleton_coprime_three
  -- `Φ(P) = χ⁻¹(-1) N P J(χ⁻¹, χ⁻¹)`, and `χ⁻¹(-1) = 1` since `χ⁻¹` has odd order.
  have h1 : (powerResidueSymbol P 3)⁻¹ (-1) = 1 := by
    have h3 : powerResidueSymbol P 3 ^ 3 = 1 := by
      simpa only [orderOf_powerResidueSymbol hP] using pow_orderOf_eq_one (powerResidueSymbol P 3)
    exact MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3)
      (by rw [inv_pow, h3, inv_one])
  rw [stickelbergerPhi_eq_mul_prod_jacobiSum P hP, h1, one_mul,
    (by decide : Finset.Ico 1 (3 - 1) = {1}), Finset.prod_singleton, pow_one,
    ← jacobiSum_powerResidueSymbol_three_eq hP hπ hπ', mul_left_comm,
    jacobiSum_powerResidueSymbol_mul_jacobiSum_inv hP le_rfl, sq]

end Ideal

namespace TauCeti

open Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- The relation `(π₁ / P₂)_3 (N P₂ / π₁)_3 = (N(π₁) / P₂)_3 ^ 2` for a primary prime `π₁` and a
maximal ideal `P₂` whose norm is prime to that of `π₁`, obtained from `π₁ Φ(π₁) = N(π₁) ^ 2` and
the residue symbol of `Φ(π₁)` at `P₂`. -/
private theorem powerResidueSymbol_mul_powerResidueSymbol_absNorm {π₁ : 𝓞 K}
    [(span {π₁}).IsMaximal] (hπ₁ : IsPrimaryEisenstein π₁) (P₂ : Ideal (𝓞 K)) [P₂.IsMaximal]
    (hP₂ : (absNorm P₂).Coprime 3) (h : (absNorm (span {π₁})).Coprime (absNorm P₂)) :
    powerResidueSymbol P₂ 3 (Ideal.Quotient.mk P₂ π₁) *
        powerResidueSymbol (span {π₁}) 3 (Ideal.Quotient.mk _ (absNorm P₂ : 𝓞 K)) =
      powerResidueSymbol P₂ 3 (Ideal.Quotient.mk P₂ (absNorm (span {π₁}) : 𝓞 K)) ^ 2 := by
  rw [← powerResidueSymbolIdeal_of_isMaximal (span {π₁}),
    ← powerResidueSymbol_stickelbergerPhi _ _ hP₂ h (by norm_num), ← map_mul, ← map_mul,
    mul_stickelbergerPhi_three_eq_absNorm_sq rfl hπ₁, map_pow, map_pow]

/-- **The law of cubic reciprocity.** Let `K = ℚ(ζ₃)`, so that `𝓞 K = ℤ[ω]`, and let `π₁` and `π₂`
be primary primes of `𝓞 K` with different norms. Then `(π₂ / π₁)_3 = (π₁ / π₂)_3`, the cubic
residue symbols being taken at the ideals `π₁ 𝓞 K` and `π₂ 𝓞 K`. A primary element is prime to
`3`, so neither symbol is taken at the prime above `3`. -/
theorem IsPrimaryEisenstein.cubic_reciprocity {π₁ π₂ : 𝓞 K} (hπ₁ : IsPrimaryEisenstein π₁)
    (hπ₂ : IsPrimaryEisenstein π₂) (hp₁ : Prime π₁) (hp₂ : Prime π₂)
    (hN : Algebra.norm ℤ π₁ ≠ Algebra.norm ℤ π₂) :
    powerResidueSymbolIdeal (span {π₁}) 3 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 3 (Ideal.Quotient.mk _ π₁) := by
  have hmax {π : 𝓞 K} (hp : Prime π) : (span {π}).IsMaximal :=
    ((span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  have := hmax hp₁
  have := hmax hp₂
  -- The norms of `π₁` and `π₂` are nonnegative, so their ideal norms differ and are coprime.
  have hnorm (π : 𝓞 K) : 0 ≤ Algebra.norm ℤ π := by
    have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
    obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) π
    rw [hζ.norm_intCast_add_intCast_mul_toInteger_of_three]
    nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]
  have h₁₂ : (absNorm (span {π₁})).Coprime (absNorm (span {π₂})) := by
    refine NumberField.coprime_absNorm_of_absNorm_ne (IsCyclotomicExtension.finrank (n := 3) K
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))) fun h ↦ hN ?_
    rw [absNorm_span_singleton, absNorm_span_singleton] at h
    rw [← Int.natAbs_of_nonneg (hnorm π₁), ← Int.natAbs_of_nonneg (hnorm π₂), h]
  have hc₁ := hπ₁.absNorm_span_singleton_coprime_three
  have hc₂ := hπ₂.absNorm_span_singleton_coprime_three
  -- With `x = (π₂ / π₁)_3`, `y = (π₁ / π₂)_3`, `a = (N(π₁) / π₂)_3` and `b = (N(π₂) / π₁)_3`, the
  -- two relations read `y b = a ^ 2` and `x a = b ^ 2`, while `a ^ 3 = b ^ 3 = 1`.
  have hy := powerResidueSymbol_mul_powerResidueSymbol_absNorm hπ₁ _ hc₂ h₁₂
  have hx := powerResidueSymbol_mul_powerResidueSymbol_absNorm hπ₂ _ hc₁ h₁₂.symm
  have ha := powerResidueSymbol_pow_eq_one hc₂ (x := Ideal.Quotient.mk (span {π₂})
    (absNorm (span {π₁}) : 𝓞 K)) (by
      rw [Ne, Quotient.eq_zero_iff_mem]
      exact natCast_notMem_of_coprime_absNorm IsPrime.ne_top' h₁₂)
  have hb := powerResidueSymbol_pow_eq_one hc₁ (x := Ideal.Quotient.mk (span {π₁})
    (absNorm (span {π₂}) : 𝓞 K)) (by
      rw [Ne, Quotient.eq_zero_iff_mem]
      exact natCast_notMem_of_coprime_absNorm IsPrime.ne_top' h₁₂.symm)
  rw [powerResidueSymbolIdeal_of_isMaximal, powerResidueSymbolIdeal_of_isMaximal]
  set x := powerResidueSymbol (span {π₁}) 3 (Ideal.Quotient.mk _ π₂)
  set y := powerResidueSymbol (span {π₂}) 3 (Ideal.Quotient.mk _ π₁)
  set a := powerResidueSymbol (span {π₂}) 3 (Ideal.Quotient.mk _ (absNorm (span {π₁}) : 𝓞 K))
  set b := powerResidueSymbol (span {π₁}) 3 (Ideal.Quotient.mk _ (absNorm (span {π₂}) : 𝓞 K))
  linear_combination y * hb - b ^ 2 * hy - x * ha + a ^ 2 * hx

end TauCeti

section Examples

open Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/- For the primary prime `π = -1 - 3ω` of norm `7`, the cube of the cubic Gauss sum is `7 π`. -/
example {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {P : Ideal (𝓞 K)} [P.IsMaximal] [Fintype (𝓞 K ⧸ P)]
    (hP : P = span {((-1 : ℤ) : 𝓞 K) + (-3 : ℤ) * hζ.toInteger}) {R : Type*} [CommRing R]
    [IsDomain R] {f : 𝓞 K →+* R} (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R}
    (hψ : ψ.IsPrimitive) :
    gaussSum ((powerResidueSymbol P 3).ringHomComp f) ψ ^ 3 =
      7 * f (((-1 : ℤ) : 𝓞 K) + (-3 : ℤ) * hζ.toInteger) := by
  rw [gaussSum_powerResidueSymbol_three_pow_three_eq hP
    (by rw [hζ.isPrimaryEisenstein_add_mul_iff]; decide) hf hψ, hP, absNorm_span_singleton,
    hζ.norm_intCast_add_intCast_mul_toInteger_of_three]
  norm_num

end Examples
