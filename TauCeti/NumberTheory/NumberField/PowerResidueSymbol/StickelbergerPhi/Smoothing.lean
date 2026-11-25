/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Relation
import Mathlib.NumberTheory.LegendreSymbol.Complex
import TauCeti.Data.Nat.GCD
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.NumberTheory.NumberField.NarrowClassGroup.CoprimeRepresentative
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Embeddings

/-!
# Positive smoothing of Gauss sums and Stickelberger annihilation

Let `K` be a number field whose ring of integers contains a primitive `m`-th root of unity,
`m ≥ 2`, let `P` be a prime of `𝓞 K` whose norm is prime to `m`, and let `g = g(χ_P, ψ)` be the
Gauss sum of `χ_P = (· / P)_m⁻¹`, so that `Φ(P) = g ^ m` (`Ideal.stickelbergerPhi`). For `b` not
divisible by `m`, the quotient `g(χ_P) ^ b / g(χ_P ^ b)` is a product of Jacobi sums of
characters with values in `𝓞 K`, so it lies in `𝓞 K` even though `g` does not:

  `Ψ_b(P) = Φ(P) ^ (b / m) · ∏_{1 ≤ i < b % m} J(χ_P, χ_P ^ i)`

(`gaussSum_pow_eq_prod_jacobiSum_aux`). Extended multiplicatively to ideals this is
`Ideal.stickelbergerSmoothing`. If `σ` is an automorphism of `𝓞 K` raising the `m`-th roots of
unity to the power `b`, then `σ(Φ(P)) = g(χ_P ^ b) ^ m`, hence `Ψ_b(P) ^ m · σ(Φ(P)) = Φ(P) ^ b`.
Thus `Ψ_b` is the element `g ^ (b - σ_b)` of the descent of Gauss sums along the positive
smoothing `b - σ_b` of the Stickelberger element.

In the `m`-th cyclotomic field `K`, write `c(σ) ∈ [1, m)` for the representative of the class of
`σ ∈ Gal(K/ℚ)` in `(ZMod m)ˣ`, and `θ = ∑_σ (c(σ) / m) σ⁻¹` for the Stickelberger element. For `b`
prime to `m`, the positive smoothing `(b - σ_b) θ = ∑_σ ⌊b c(σ) / m⌋ σ⁻¹` has integral
coefficients. Comparing the `m`-th power of `(Ψ_b(A))` with Stickelberger's relation
`(Φ(A)) = ∏_σ (σ⁻¹ A) ^ c(σ)` (`Ideal.span_stickelbergerPhi`) gives

  `(Ψ_b(A)) = ∏_σ (σ⁻¹ A) ^ ⌊b c(σ) / m⌋`

for every ideal `A` whose norm is prime to `m`. Since every ideal class contains an ideal prime to
`m`, the positive smoothing of the Stickelberger element annihilates the ideal class group: the
ideal `∏_σ (σ⁻¹ I) ^ ⌊b c(σ) / m⌋` is principal for every ideal `I` of `𝓞 K`. As `b` runs over
the integers prime to `m`, the smoothings `(b - σ_b) θ` generate the integral Stickelberger ideal
`ℤ[G] θ ∩ ℤ[G]` as an ideal of `ℤ[G]`, `G = Gal(K/ℚ)` (`b = m + 1` gives `m θ`), so this is the
arithmetic content of Stickelberger's theorem. The proof uses only Gauss sums at primes prime to
`m` and the approximation theorem for ideals, rather than a density theorem for primes in ideal
classes.

## Main definitions and results

* `Ideal.stickelbergerSmoothing A m b`: the smoothed Gauss sum `Ψ_b(A) ∈ 𝓞 K`.
* `Ideal.stickelbergerSmoothing_eq_mul_prod_jacobiSum`: the Jacobi-sum expression of `Ψ_b(P)`.
* `Ideal.stickelbergerSmoothing_add_self`: `Ψ_(b + m)(A) = Φ(A) · Ψ_b(A)`.
* `Ideal.stickelbergerSmoothing_mul_gaussSum`: `Ψ_b(P) · g(χ_P ^ b, ψ) = g(χ_P, ψ) ^ b`.
* `Ideal.stickelbergerSmoothing_pow_mul_apply`: `Ψ_b(A) ^ m · σ(Φ(A)) = Φ(A) ^ b` for an
  automorphism `σ` raising the `m`-th roots of unity to the power `b`.
* `Ideal.span_stickelbergerSmoothing`: `(Ψ_b(A)) = ∏_σ (σ⁻¹ A) ^ ⌊b c(σ) / m⌋` in the `m`-th
  cyclotomic field.
* `Ideal.isPrincipal_prod_inv_smul_pow_mul_div`: for `b` prime to `m`, the ideal
  `∏_σ (σ⁻¹ I) ^ ⌊b c(σ) / m⌋` is principal for every ideal `I`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §6.2, Theorem 6.10 and its
  proof.
* R. Sharifi, *Iwasawa Theory*, Lemma 4.5.2, Lemma 4.5.4 and Theorem 4.5.6.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §5.
-/

public section

open NumberField UniqueFactorizationMonoid

namespace Ideal

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} [NeZero m] [HasEnoughRootsOfUnity (𝓞 K) m]

open scoped Classical in
variable (m) in
/-- The value of `Ψ_b` at a maximal ideal `P` whose norm is prime to `m`, written through
`Φ(P)` and Jacobi sums of `χ_P = (· / P)_m⁻¹`; `1` at every other ideal. -/
private noncomputable def stickelbergerSmoothingAt (b : ℕ) (P : Ideal (𝓞 K)) : 𝓞 K :=
  if h : P.IsMaximal ∧ (absNorm P).Coprime m then
    letI := h.1
    letI := Fintype.ofFinite (𝓞 K ⧸ P)
    stickelbergerPhi P m ^ (b / m) *
      ∏ i ∈ Finset.Ico 1 (b % m),
        jacobiSum (powerResidueSymbol P m)⁻¹ ((powerResidueSymbol P m)⁻¹ ^ i)
  else 1

/-- **The smoothed Gauss sum** `Ψ_b(A) ∈ 𝓞 K` of an ideal `A` of `𝓞 K`. At a maximal ideal `P`
whose norm is prime to `m` it is `Φ(P) ^ (b / m) · ∏_{1 ≤ i < b % m} J(χ_P, χ_P ^ i)`, with
`χ_P = (· / P)_m⁻¹`; if `m ∤ b`, this is the quotient `g(χ_P, ψ) ^ b / g(χ_P ^ b, ψ)`
of Gauss sums (`Ideal.stickelbergerSmoothing_mul_gaussSum`). For an ideal `A = P₁ ⋯ Pᵣ` factored
into primes, `Ψ_b(A) = ∏ᵢ Ψ_b(Pᵢ)`, the primes whose norm is not prime to `m` contributing `1`. -/
noncomputable def stickelbergerSmoothing (A : Ideal (𝓞 K)) (m : ℕ) [NeZero m]
    [HasEnoughRootsOfUnity (𝓞 K) m] (b : ℕ) : 𝓞 K :=
  ((normalizedFactors A).map (stickelbergerSmoothingAt m b)).prod

/-- At a maximal ideal, `Ψ_b` is its local factor. -/
private theorem stickelbergerSmoothing_of_isMaximal (P : Ideal (𝓞 K)) [P.IsMaximal] (b : ℕ) :
    stickelbergerSmoothing P m b = stickelbergerSmoothingAt m b P := by
  have hP : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField K)
  rw [stickelbergerSmoothing, normalizedFactors_irreducible
    (prime_of_isPrime hP inferInstance).irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- **The Jacobi-sum expression of `Ψ_b(P)`.** If the norm of the maximal ideal `P` is prime to
`m`, then `Ψ_b(P) = Φ(P) ^ (b / m) · ∏_{1 ≤ i < b % m} J(χ_P, χ_P ^ i)` with
`χ_P = (· / P)_m⁻¹`. -/
theorem stickelbergerSmoothing_eq_mul_prod_jacobiSum (P : Ideal (𝓞 K)) [P.IsMaximal]
    [Fintype (𝓞 K ⧸ P)] (hP : (absNorm P).Coprime m) (b : ℕ) :
    stickelbergerSmoothing P m b = stickelbergerPhi P m ^ (b / m) *
      ∏ i ∈ Finset.Ico 1 (b % m),
        jacobiSum (powerResidueSymbol P m)⁻¹ ((powerResidueSymbol P m)⁻¹ ^ i) := by
  rw [stickelbergerSmoothing_of_isMaximal, stickelbergerSmoothingAt, dite_eq_left ⟨‹_›, hP⟩]
  -- The local factor sums over `Fintype.ofFinite`; identify it with the given instance.
  congr!

/-- At a maximal ideal whose norm is not prime to `m`, `Ψ_b` is `1` by convention. -/
theorem stickelbergerSmoothing_of_not_coprime (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hP : ¬(absNorm P).Coprime m) (b : ℕ) : stickelbergerSmoothing P m b = 1 := by
  rw [stickelbergerSmoothing_of_isMaximal, stickelbergerSmoothingAt,
    dite_eq_right (not_and_of_not_right _ hP)]

/-- **Multiplicativity of `Ψ_b`.** `Ψ_b(A B) = Ψ_b(A) Ψ_b(B)` for nonzero ideals `A` and `B`. -/
theorem stickelbergerSmoothing_mul {A B : Ideal (𝓞 K)} (hA : A ≠ ⊥) (hB : B ≠ ⊥) (b : ℕ) :
    stickelbergerSmoothing (A * B) m b =
      stickelbergerSmoothing A m b * stickelbergerSmoothing B m b := by
  rw [stickelbergerSmoothing, normalizedFactors_mul hA hB, Multiset.map_add, Multiset.prod_add,
    stickelbergerSmoothing, stickelbergerSmoothing]

/-- `Ψ_b(𝓞 K) = 1`. -/
@[simp]
theorem stickelbergerSmoothing_top (b : ℕ) : stickelbergerSmoothing (⊤ : Ideal (𝓞 K)) m b = 1 := by
  rw [stickelbergerSmoothing, ← one_eq_top, normalizedFactors_one, Multiset.map_zero,
    Multiset.prod_zero]

/-- The zero ideal has no prime factors, so `Ψ_b(0) = 1` by convention. -/
@[simp]
theorem stickelbergerSmoothing_bot (b : ℕ) : stickelbergerSmoothing (⊥ : Ideal (𝓞 K)) m b = 1 := by
  rw [stickelbergerSmoothing, ← zero_eq_bot, normalizedFactors_zero, Multiset.map_zero,
    Multiset.prod_zero]

/-- `Ψ_0(A) = 1`. -/
@[simp]
theorem stickelbergerSmoothing_zero (A : Ideal (𝓞 K)) : stickelbergerSmoothing A m 0 = 1 := by
  have : stickelbergerSmoothingAt m 0 = fun _ : Ideal (𝓞 K) ↦ (1 : 𝓞 K) := by
    funext P
    rw [stickelbergerSmoothingAt]
    split_ifs <;> simp
  rw [stickelbergerSmoothing, this, Multiset.map_const', Multiset.prod_replicate, one_pow]

/-- `Ψ_1(A) = 1` for `m ≥ 2`. -/
@[simp]
theorem stickelbergerSmoothing_one (hm : 2 ≤ m) (A : Ideal (𝓞 K)) :
    stickelbergerSmoothing A m 1 = 1 := by
  have : stickelbergerSmoothingAt m 1 = fun _ : Ideal (𝓞 K) ↦ (1 : 𝓞 K) := by
    funext P
    rw [stickelbergerSmoothingAt]
    split_ifs <;> simp [Nat.div_eq_of_lt (by lia : 1 < m), Nat.mod_eq_of_lt (by lia : 1 < m)]
  rw [stickelbergerSmoothing, this, Multiset.map_const', Multiset.prod_replicate, one_pow]

/-- **Shifting `b` by `m`.** `Ψ_(b + m)(A) = Φ(A) · Ψ_b(A)`; with `Ψ_0(A) = 1`, this gives
`Ψ_(m k)(A) = Φ(A) ^ k`. -/
theorem stickelbergerSmoothing_add_self (A : Ideal (𝓞 K)) (b : ℕ) :
    stickelbergerSmoothing A m (b + m) = stickelbergerPhi A m * stickelbergerSmoothing A m b := by
  induction A using induction_on_prime with
  | h₁ => simp only [zero_eq_bot, stickelbergerSmoothing_bot, stickelbergerPhi_bot, one_mul]
  | h₂ A hA =>
    simp only [isUnit_iff.mp hA, stickelbergerSmoothing_top, stickelbergerPhi_top, one_mul]
  | h₃ A P hA₀ hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    rw [stickelbergerSmoothing_mul hP.ne_zero hA₀, stickelbergerSmoothing_mul hP.ne_zero hA₀,
      stickelbergerPhi_mul hP.ne_zero hA₀, ih]
    by_cases hPm : (absNorm P).Coprime m
    · let _ := Fintype.ofFinite (𝓞 K ⧸ P)
      rw [stickelbergerSmoothing_eq_mul_prod_jacobiSum P hPm,
        stickelbergerSmoothing_eq_mul_prod_jacobiSum P hPm, Nat.add_mod_right,
        Nat.add_div_right _ (NeZero.pos m), pow_succ]
      ring
    · rw [stickelbergerSmoothing_of_not_coprime P hPm, stickelbergerSmoothing_of_not_coprime P hPm,
        stickelbergerPhi_of_not_coprime P hPm]
      ring

/-- **`Ψ_b(P)` is a quotient of Gauss sums.** Let `m ∤ b`, and let `P` be a maximal ideal
whose norm is prime to `m`. For every injective ring homomorphism `f` from `𝓞 K` to a domain `R`
and every primitive additive character `ψ` of `𝓞 K ⧸ P` with values in `R`,
`f (Ψ_b(P)) · g(χ_P ^ b, ψ) = g(χ_P, ψ) ^ b`, the characters being pushed to `R` along `f`. -/
theorem stickelbergerSmoothing_mul_gaussSum (P : Ideal (𝓞 K)) [P.IsMaximal] [Fintype (𝓞 K ⧸ P)]
    (hP : (absNorm P).Coprime m) {b : ℕ} (hb : ¬m ∣ b) {R : Type*} [CommRing R] [IsDomain R]
    {f : 𝓞 K →+* R} (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R}
    (hψ : ψ.IsPrimitive) :
    f (stickelbergerSmoothing P m b) *
        gaussSum (((powerResidueSymbol P m)⁻¹ ^ b).ringHomComp f) ψ =
      gaussSum ((powerResidueSymbol P m)⁻¹.ringHomComp f) ψ ^ b := by
  have hm := Nat.two_le_of_not_dvd hb
  let _ := Ideal.Quotient.field P
  set χ := (powerResidueSymbol P m)⁻¹.ringHomComp f with hχdef
  have hχ : orderOf χ = m := by
    rw [MulChar.orderOf_ringHomComp hf, orderOf_inv, orderOf_powerResidueSymbol hP]
  -- Write `b = m (b / m) + r` with `0 < r < m`; then `χ ^ b = χ ^ r`.
  have hr : 0 < b % m := Nat.pos_of_ne_zero fun h ↦ hb (Nat.dvd_of_mod_eq_zero h)
  have hrm : b % m < orderOf χ := by
    rw [hχ]
    exact Nat.mod_lt _ (NeZero.pos m)
  have hχb : χ ^ b = χ ^ (b % m) := by rw [← pow_mod_orderOf, hχ]
  have haux := gaussSum_pow_eq_prod_jacobiSum_aux χ ψ hr hrm
  rw [stickelbergerSmoothing_eq_mul_prod_jacobiSum P hP, map_mul, map_pow,
    stickelbergerPhi_prime P hP hm hf hψ, map_prod, ← MulChar.ringHomComp_pow, hχb]
  simp only [← jacobiSum_ringHomComp, ← MulChar.ringHomComp_pow, ← hχdef]
  rw [mul_assoc, mul_comm (∏ _ ∈ _, _), ← haux, ← pow_mul, ← pow_add, Nat.div_add_mod]

/-- `Ψ_b(A)` is nonzero when `m ∤ b` and the norm of `A` is prime to `m`. -/
theorem stickelbergerSmoothing_ne_zero {A : Ideal (𝓞 K)} (hA : (absNorm A).Coprime m) {b : ℕ}
    (hb : ¬m ∣ b) : stickelbergerSmoothing A m b ≠ 0 := by
  have hm := Nat.two_le_of_not_dvd hb
  induction A using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left] at hA
    lia
  | h₂ A hA' =>
    rw [isUnit_iff.mp hA', stickelbergerSmoothing_top]
    exact one_ne_zero
  | h₃ A P hA₀ hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    rw [map_mul, Nat.coprime_mul_iff_left] at hA
    rw [stickelbergerSmoothing_mul hP.ne_zero hA₀]
    refine mul_ne_zero ?_ (ih hA.2)
    -- Read `Ψ_b(P)` in `ℂ`, where it divides the nonzero `g(χ_P, ψ) ^ b`.
    let _ := Ideal.Quotient.field P
    let _ := Fintype.ofFinite (𝓞 K ⧸ P)
    obtain ⟨f, hf⟩ := RingOfIntegers.exists_injective_ringHom_complex K
    have hψ := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (𝓞 K ⧸ P)
    have hχ : (powerResidueSymbol P m)⁻¹.ringHomComp f ≠ 1 := by
      rw [MulChar.ringHomComp_ne_one_iff hf, Ne, inv_eq_one, ← orderOf_eq_one_iff,
        orderOf_powerResidueSymbol hA.1]
      lia
    have hg := pow_ne_zero b (gaussSum_ne_zero_of_nontrivial
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hχ hψ)
    rw [← stickelbergerSmoothing_mul_gaussSum P hA.1 hb hf hψ] at hg
    exact fun h ↦ hg (by rw [h, map_zero, zero_mul])

/-- The case of a maximal ideal in `Ideal.stickelbergerSmoothing_pow_mul_apply`. -/
private theorem stickelbergerSmoothing_pow_mul_apply_of_isMaximal (P : Ideal (𝓞 K))
    [P.IsMaximal] (hP : (absNorm P).Coprime m) {b : ℕ} (hb : ¬m ∣ b) (σ : 𝓞 K ≃+* 𝓞 K)
    (hσ : ∀ ζ : 𝓞 K, ζ ^ m = 1 → σ ζ = ζ ^ b) :
    stickelbergerSmoothing P m b ^ m * σ (stickelbergerPhi P m) = stickelbergerPhi P m ^ b := by
  have hm := Nat.two_le_of_not_dvd hb
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  -- Read all three factors as Gauss sum expressions in `ℂ`.
  obtain ⟨f, hf⟩ := RingOfIntegers.exists_injective_ringHom_complex K
  have hψ := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (𝓞 K ⧸ P)
  apply hf
  rw [map_mul, map_pow, map_pow, apply_stickelbergerPhi_eq_gaussSum_pow P hP hm σ hσ hf hψ,
    stickelbergerPhi_prime P hP hm hf hψ, ← mul_pow,
    stickelbergerSmoothing_mul_gaussSum P hP hb hf hψ, ← pow_mul, ← pow_mul, mul_comm]

/-- **The `m`-th power of `Ψ_b(A)`.** Let `σ` be a ring automorphism of `𝓞 K` raising every
`m`-th root of unity to the power `b`, such as the element `σ_b` of the Galois group of a
cyclotomic field. If `m ∤ b` and the norm of the ideal `A` is prime to `m`, then
`Ψ_b(A) ^ m · σ(Φ(A)) = Φ(A) ^ b`. -/
theorem stickelbergerSmoothing_pow_mul_apply {A : Ideal (𝓞 K)} (hA : (absNorm A).Coprime m)
    {b : ℕ} (hb : ¬m ∣ b) (σ : 𝓞 K ≃+* 𝓞 K) (hσ : ∀ ζ : 𝓞 K, ζ ^ m = 1 → σ ζ = ζ ^ b) :
    stickelbergerSmoothing A m b ^ m * σ (stickelbergerPhi A m) = stickelbergerPhi A m ^ b := by
  have hm := Nat.two_le_of_not_dvd hb
  induction A using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left] at hA
    lia
  | h₂ A hA' =>
    rw [isUnit_iff.mp hA', stickelbergerPhi_top, stickelbergerSmoothing_top]
    simp
  | h₃ A P hA₀ hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    rw [map_mul, Nat.coprime_mul_iff_left] at hA
    rw [stickelbergerPhi_mul hP.ne_zero hA₀, stickelbergerSmoothing_mul hP.ne_zero hA₀, map_mul,
      mul_pow, mul_pow, ← stickelbergerSmoothing_pow_mul_apply_of_isMaximal P hA.1 hb σ hσ,
      ← ih hA.2]
    ring

section Cyclotomic

open IsCyclotomicExtension.Rat
open scoped Pointwise

variable [IsCyclotomicExtension {m} ℚ K]

/-- **The smoothed Gauss descent.** Let `K` be the `m`-th cyclotomic field, `m ≥ 2`, let `b` be
prime to `m`, and let `A` be an ideal of `𝓞 K` whose norm is prime to `m`. Then the principal
ideal generated by `Ψ_b(A)` is `A ^ ((b - σ_b) θ) = ∏_σ (σ⁻¹ A) ^ ⌊b c(σ) / m⌋`, the product over
`σ ∈ Gal(K/ℚ)` with `c(σ)` the representative in `[1, m)` of the class of `σ` in `(ZMod m)ˣ`. -/
theorem span_stickelbergerSmoothing (hm : 2 ≤ m) {b : ℕ} (hb : b.Coprime m) {A : Ideal (𝓞 K)}
    (hA : (absNorm A).Coprime m) :
    span {stickelbergerSmoothing A m b} =
      ∏ σ : Gal(K/ℚ), (σ⁻¹ • A) ^ (b * (galEquivZMod m K σ : ZMod m).val / m) := by
  have hbm := hb.not_dvd_of_two_le hm
  have hA0 : A ≠ ⊥ := by
    rintro rfl
    rw [absNorm_bot, Nat.coprime_zero_left] at hA
    lia
  set c : Gal(K/ℚ) → ℕ := fun σ ↦ (galEquivZMod m K σ : ZMod m).val with hc
  -- The automorphism `τ = σ_b`, with `c(ρ τ) = b c(ρ) mod m`.
  set τ := (galEquivZMod m K).symm (ZMod.unitOfCoprime b hb)
  have hτ : (galEquivZMod m K τ : ZMod m) = b := by simp [τ]
  have hcτ (ρ : Gal(K/ℚ)) : c (ρ * τ) = b * c ρ % m := by
    simp only [hc, map_mul, Units.val_mul, hτ, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod,
      mul_comm]
  have hkey := stickelbergerSmoothing_pow_mul_apply hA hbm
    (MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) τ) fun ζ hζ ↦ by
      rw [MulSemiringAction.toRingEquiv_apply_apply, galEquivZMod_smul_of_pow_eq m K τ hζ, hτ,
        ZMod.val_natCast]
      conv_rhs => rw [← Nat.div_add_mod b m, pow_add, pow_mul, hζ, one_pow, one_mul]
  -- In ideals: `(Ψ_b(A)) ^ m · τ (Φ(A)) = (Φ(A)) ^ b`, with `(Φ(A)) = ∏_σ (σ⁻¹ A) ^ c(σ)`.
  have hspan := congrArg (fun x ↦ span {x}) hkey
  simp only [← span_singleton_mul_span_singleton, ← span_singleton_pow,
    MulSemiringAction.toRingEquiv_apply_apply] at hspan
  rw [← Set.smul_set_singleton, ← smul_closure, span_stickelbergerPhi hm hA] at hspan
  -- Applying `τ` multiplies the exponents by `b` modulo `m`.
  have hτΦ : τ • ∏ σ : Gal(K/ℚ), (σ⁻¹ • A) ^ c σ =
      ∏ σ : Gal(K/ℚ), (σ⁻¹ • A) ^ (b * c σ % m) := by
    rw [Finset.smul_prod']
    refine (Fintype.prod_equiv (Equiv.mulRight τ) _ _ fun ρ ↦ ?_).symm
    rw [Equiv.coe_mulRight, hcτ, smul_pow', smul_smul, mul_inv_rev, mul_inv_cancel_left]
  have hpow : (∏ σ : Gal(K/ℚ), (σ⁻¹ • A) ^ c σ) ^ b =
      (∏ σ : Gal(K/ℚ), (σ⁻¹ • A) ^ (b * c σ / m)) ^ m *
        ∏ σ : Gal(K/ℚ), (σ⁻¹ • A) ^ (b * c σ % m) := by
    rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun σ _ ↦ ?_
    rw [← pow_mul, ← pow_mul, ← pow_add, mul_comm (b * c σ / m) m, Nat.div_add_mod, mul_comm]
  rw [hτΦ, hpow] at hspan
  -- Cancel the nonzero factor and take `m`-th roots of ideals.
  have hne : ∏ σ : Gal(K/ℚ), (σ⁻¹ • A) ^ (b * c σ % m) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun σ _ ↦ pow_ne_zero _ fun h ↦ hA0 ?_
    rw [← smul_inv_smul σ A, ← zero_eq_bot, h, zero_eq_bot, smul_bot]
  have h := mul_right_cancel₀ hne hspan
  exact dvd_antisymm ((pow_dvd_pow_iff_dvd (NeZero.ne m)).1 h.dvd)
    ((pow_dvd_pow_iff_dvd (NeZero.ne m)).1 h.symm.dvd)

/-- **Positive smoothings of the Stickelberger element annihilate the class group.** Let `K` be the
`m`-th cyclotomic field, `m ≥ 2`, and let `b` be prime to `m`. For every ideal `I` of `𝓞 K`, the
ideal `I ^ ((b - σ_b) θ) = ∏_σ (σ⁻¹ I) ^ ⌊b c(σ) / m⌋` is principal, the product over
`σ ∈ Gal(K/ℚ)` with `c(σ)` the representative in `[1, m)` of the class of `σ` in `(ZMod m)ˣ`. -/
theorem isPrincipal_prod_inv_smul_pow_mul_div (hm : 2 ≤ m) {b : ℕ} (hb : b.Coprime m)
    (I : Ideal (𝓞 K)) :
    (∏ σ : Gal(K/ℚ), (σ⁻¹ • I) ^ (b * (galEquivZMod m K σ : ZMod m).val / m)).IsPrincipal := by
  obtain rfl | hI := eq_or_ne I ⊥
  · simp only [smul_bot, Finset.prod_pow_eq_pow_sum]
    rcases Nat.eq_zero_or_pos (∑ σ : Gal(K/ℚ), b * (galEquivZMod m K σ : ZMod m).val / m) with
      h | h
    · rw [h, pow_zero, one_eq_top]
      infer_instance
    · rw [← zero_eq_bot, zero_pow h.ne', zero_eq_bot]
      infer_instance
  -- Choose `a ≠ 0` and `J` with `(a) = I J` and `N J` prime to `m`.
  have hm0 : (m : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  obtain ⟨a, J, -, -, haIJ, hJ⟩ := NumberField.exists_isTotallyPositive_span_eq_mul_isCoprime
    ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩
    ⟨span {(m : 𝓞 K)}, span_singleton_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero hm0)⟩
  have hJm : (absNorm (J : Ideal (𝓞 K))).Coprime m := absNorm_coprime_of_isCoprime_span_natCast hJ
  -- The product for `I J = (a)` is generated by `∏_σ (σ⁻¹ a) ^ ⌊b c(σ) / m⌋`, and the one for `J`
  -- by `Ψ_b(J)`.
  have h : (∏ σ : Gal(K/ℚ), (σ⁻¹ • I) ^ (b * (galEquivZMod m K σ : ZMod m).val / m)) *
      span {stickelbergerSmoothing (J : Ideal (𝓞 K)) m b} =
      span {∏ σ : Gal(K/ℚ), (σ⁻¹ • a) ^ (b * (galEquivZMod m K σ : ZMod m).val / m)} := by
    rw [span_stickelbergerSmoothing hm hb hJm, ← Finset.prod_mul_distrib, ← prod_span_singleton]
    simp only [← mul_pow, ← smul_mul', ← haIJ, smul_closure, Set.smul_set_singleton,
      span_singleton_pow]
  -- Cancel the nonzero principal ideal `(Ψ_b(J))`.
  have hΨ : stickelbergerSmoothing (J : Ideal (𝓞 K)) m b ≠ 0 :=
    stickelbergerSmoothing_ne_zero hJm (hb.not_dvd_of_two_le hm)
  obtain ⟨w, hw⟩ := mem_span_singleton'.mp (mul_le_right (h.symm ▸ mem_span_singleton_self _))
  refine ⟨w, mul_right_cancel₀ (span_singleton_eq_bot.not.mpr hΨ) ?_⟩
  rw [h, ← hw, span_singleton_mul_span_singleton]

end Cyclotomic

end Ideal
