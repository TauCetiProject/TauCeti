/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Three.JacobiSum
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
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

The law extends multiplicatively to a rational integer `A` prime to `3`, which may be negative or
composite: `(A / π)_3 = (π / A)_3` for every primary prime `π`, the right side being the symbol at
the ideal `A 𝓞 K` (`TauCeti.IsPrimaryEisenstein.cubic_reciprocity_intCast`). One of `±A` is
primary, and `(-1 / 𝔞)_3 = 1`. A primary divisor of `A` factors as `-(ρ δ)` with `ρ` a primary
prime and `δ` primary, and `ρ` has a norm different from that of `π` unless `π` divides `A`, in
which case both symbols vanish.

## Main results

* `Ideal.gaussSum_powerResidueSymbol_three_pow_three_eq`: `g(χ, ψ) ^ 3 = p π` for the cubic residue
  symbol `χ` at a primary prime `π` of norm `p`.
* `Ideal.mul_stickelbergerPhi_three_eq_absNorm_sq`: `π Φ(π 𝓞 K) = p ^ 2`.
* `TauCeti.IsPrimaryEisenstein.cubic_reciprocity`: the law of cubic reciprocity.
* `TauCeti.IsPrimaryEisenstein.cubic_reciprocity_intCast`: cubic reciprocity between a primary
  prime and a rational integer prime to `3`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3, Theorem 3.1 and
  its proof, Proposition 3.3 and (11).
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §3,
  Theorem 1, and Chapter 14, §5.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3, Williams' proof of
  the supplement to cubic reciprocity, for the extension to rational integers.
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

/-- Cubic reciprocity between a primary prime `π` and a primary divisor `γ` of a rational integer
`A` prime to `3` and to `π`: `(γ / π)_3 = (π / γ)_3`. -/
private theorem cubic_reciprocity_of_dvd_intCast {π : 𝓞 K} (hπ : IsPrimaryEisenstein π)
    (hp : Prime π) {A : ℤ} (hA : ¬ (3 : ℤ) ∣ A) (hπA : ¬ π ∣ (A : 𝓞 K)) {γ : 𝓞 K}
    (hγ : IsPrimaryEisenstein γ) (hγA : γ ∣ (A : 𝓞 K)) :
    powerResidueSymbolIdeal (span {π}) 3 (Ideal.Quotient.mk _ γ) =
      powerResidueSymbolIdeal (span {γ}) 3 (Ideal.Quotient.mk _ π) := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have := IsCyclotomicExtension.Rat.three_pid K
  -- The norm of a divisor of `A` divides `N(A) = A ^ 2`, and `π` divides its own norm.
  have hnorm {ρ : 𝓞 K} (h : ρ ∣ (A : 𝓞 K)) : Algebra.norm ℤ ρ ∣ A ^ 2 := by
    have h' := map_dvd (Algebra.norm ℤ) h
    rwa [← eq_intCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap,
      finrank_ringOfIntegers_three] at h'
  have hπN : π ∣ ((Algebra.norm ℤ π).natAbs : 𝓞 K) := by
    rw [← absNorm_span_singleton, ← mem_span_singleton]
    exact absNorm_mem _
  -- Induct on a factorisation of an associate `β` of `γ` into primes.
  suffices ∀ β γ : 𝓞 K, Associated β γ → IsPrimaryEisenstein γ → γ ∣ (A : 𝓞 K) →
      powerResidueSymbolIdeal (span {π}) 3 (Ideal.Quotient.mk _ γ) =
        powerResidueSymbolIdeal (span {γ}) 3 (Ideal.Quotient.mk _ π) from
    this γ γ (Associated.refl γ) hγ hγA
  intro β
  induction β using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro γ hβγ _ hγA
    rw [hβγ.eq_zero_iff.mp rfl, zero_dvd_iff, Int.cast_eq_zero] at hγA
    exact absurd (hγA ▸ dvd_zero 3) hA
  | h₂ β hβ =>
    -- A primary unit is `-1`, since `1` has a unique primary multiple by a unit.
    intro γ hβγ hγ _
    have hu : IsUnit γ := hβγ.isUnit hβ
    have h1 : ¬ hζ.toInteger - 1 ∣ 1 := fun h ↦
      hζ.zeta_sub_one_prime'.not_isUnit (isUnit_of_dvd_one h)
    have hγ' : γ = -1 := by
      have := (hζ.existsUnique_isPrimaryEisenstein_unit_mul h1).unique
        (y₁ := hu.unit) (y₂ := -1) (by simpa using hγ)
        (by simpa using (isPrimaryEisenstein_intCast_iff (K := K) (a := -1)).mpr (by decide))
      simpa using congrArg Units.val this
    rw [span_singleton_eq_top.mpr hu, powerResidueSymbolIdeal_top, hγ', map_neg,
      powerResidueSymbolIdeal_neg (by decide), map_one, MulChar.map_one]
  | h₃ β ρ _ hρ ih =>
    intro γ hβγ hγ hγA
    obtain ⟨u, rfl⟩ := hβγ
    -- Replace `ρ` by its primary associate `ρ'`, and write `γ = -(ρ' δ)` with `δ` primary.
    have hρ3 : Algebra.norm ℤ ρ ≠ 3 := fun h ↦ hA <| Int.prime_three.dvd_of_dvd_pow <|
      h ▸ hnorm ((dvd_mul_right _ _).trans ((dvd_mul_right _ _).trans hγA))
    obtain ⟨ρ', ⟨⟨w, rfl⟩, hρ'⟩, -⟩ := hρ.existsUnique_associated_isPrimaryEisenstein hρ3
    set δ : 𝓞 K := ((-(w⁻¹ * u) : (𝓞 K)ˣ) : 𝓞 K) * β with hδ
    have hγδ : ρ * β * u = -(ρ * w * δ) := by
      simp only [hδ, Units.val_neg, Units.val_mul]
      linear_combination (ρ * β * u) * (Units.mul_inv w).symm
    rw [hγδ] at hγ hγA ⊢
    have hδ' : IsPrimaryEisenstein δ := by
      have h := hρ'.three_dvd_sub_one_of_mul (w := -δ) (by simpa [mul_comm] using hγ)
      rw [isPrimaryEisenstein_iff, show δ - 2 = -(-δ - 1) - 3 by ring]
      exact (dvd_neg.mpr h).sub dvd_rfl
    have hρ'p : Prime (ρ * w) := Associated.prime ⟨w, rfl⟩ hρ
    rw [neg_dvd] at hγA
    have hδA : δ ∣ (A : 𝓞 K) := (dvd_mul_left δ _).trans hγA
    have hρ'A : ρ * w ∣ (A : 𝓞 K) := (dvd_mul_right _ δ).trans hγA
    -- `ρ'` and `π` have different norms, since otherwise `π ∣ N(π) = N(ρ') ∣ A ^ 2`.
    have hN : Algebra.norm ℤ π ≠ Algebra.norm ℤ (ρ * w) := fun h ↦ hπA <|
      hp.dvd_of_dvd_pow (n := 2) <| hπN.trans <| by
        rw [← Int.cast_natCast, ← Int.cast_pow]
        exact Int.cast_dvd_cast _ _ (Int.natAbs_dvd.mpr (h ▸ hnorm hρ'A))
    have hδ0 : δ ≠ 0 := by
      intro h
      rw [h, mul_zero, zero_dvd_iff, Int.cast_eq_zero] at hγA
      exact hA (hγA ▸ dvd_zero 3)
    rw [span_singleton_neg, ← span_singleton_mul_span_singleton,
      powerResidueSymbolIdeal_mul_right (by simpa using hρ'p.ne_zero) (by simpa using hδ0),
      ← hπ.cubic_reciprocity hρ' hp hρ'p hN,
      ← ih δ ⟨-(w⁻¹ * u), by rw [hδ, mul_comm]⟩ hδ' hδA, map_neg,
      powerResidueSymbolIdeal_neg (by decide), map_mul, map_mul]

/-- **Cubic reciprocity between a primary prime and a rational integer.** Let `K = ℚ(ζ₃)`, so that
`𝓞 K = ℤ[ω]`, let `π` be a primary prime of `𝓞 K` and let `A` be a rational integer prime to `3`.
Then `(A / π)_3 = (π / A)_3`, the cubic residue symbols being taken at the ideals `π 𝓞 K` and
`A 𝓞 K`. The integer `A` may be negative or composite; if it is not prime to `π`, both sides
vanish. -/
theorem IsPrimaryEisenstein.cubic_reciprocity_intCast {π : 𝓞 K} (hπ : IsPrimaryEisenstein π)
    (hp : Prime π) {A : ℤ} (hA : ¬ (3 : ℤ) ∣ A) :
    powerResidueSymbolIdeal (span {π}) 3 (Ideal.Quotient.mk _ (A : 𝓞 K)) =
      powerResidueSymbolIdeal (span {(A : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) := by
  by_cases hπA : π ∣ (A : 𝓞 K)
  · -- Both residue classes are nonunits.
    have h : ¬IsCoprime (span {π}) (span {(A : 𝓞 K)}) := by
      rw [isCoprime_iff_sup_eq, sup_eq_left.mpr (span_singleton_le_span_singleton.mpr hπA)]
      exact ((span_singleton_prime hp.ne_zero).mpr hp).ne_top
    rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm h),
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr h]
  -- One of `A` and `-A` is primary, and both have the same symbols.
  rcases (by unfold Int.ModEq; omega : A ≡ 2 [ZMOD 3] ∨ -A ≡ 2 [ZMOD 3]) with h | h
  · exact cubic_reciprocity_of_dvd_intCast hπ hp hA hπA
      (isPrimaryEisenstein_intCast_iff.mpr h) dvd_rfl
  · have h' := cubic_reciprocity_of_dvd_intCast hπ hp hA hπA (γ := ((-A : ℤ) : 𝓞 K))
      (isPrimaryEisenstein_intCast_iff.mpr h) (by simp)
    rwa [Int.cast_neg, span_singleton_neg, map_neg, powerResidueSymbolIdeal_neg (by decide)] at h'

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

/- Cubic reciprocity against the negative composite integer `-10 = -2 · 5`: the symbol at
`-10 𝓞 K = 10 𝓞 K` is read at the product of the inert prime `2` and the split prime `5`. -/
example {π : 𝓞 K} (hπ : TauCeti.IsPrimaryEisenstein π) (hp : Prime π) :
    powerResidueSymbolIdeal (span {π}) 3 (Ideal.Quotient.mk _ ((-10 : ℤ) : 𝓞 K)) =
      powerResidueSymbolIdeal (span {((10 : ℤ) : 𝓞 K)}) 3 (Ideal.Quotient.mk _ π) := by
  rw [hπ.cubic_reciprocity_intCast hp (by decide), Int.cast_neg, span_singleton_neg]

end Examples
