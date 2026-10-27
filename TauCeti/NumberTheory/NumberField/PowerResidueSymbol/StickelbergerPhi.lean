/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.SModEq.Basic
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Basic
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import TauCeti.NumberTheory.GaussSum

/-!
# The Gauss sum power `Φ(P) = g(P)^m`

Let `K` be a number field whose ring of integers contains a primitive `m`-th root of unity, with
`m ≥ 2`, and let `P` be a prime of `𝓞 K` whose norm `N P` is prime to `m`. On the residue field
`F = 𝓞 K ⧸ P` let `χ_P = (· / P)_m⁻¹` be the inverse of the `m`-th power residue character, and
let `ψ` be a nontrivial additive character of `F`, such as `t ↦ ζ_p ^ Tr(t)`. The Gauss sum
`g(P) = g(χ_P, ψ)` lives in a field containing `K` and the `p`-th roots of unity, but its `m`-th
power `Φ(P) = g(P)^m` lies in `𝓞 K` and does not depend on `ψ`. Extended multiplicatively to
ideals, `Φ` is the element whose principal ideal Stickelberger's relation factors, and from which
the Eisenstein reciprocity law is deduced. For `m = l` prime, `Φ(P) ≡ -1 (mod l)`, hence
`Φ(A) ≡ ±1 (mod l)` for every ideal `A` whose norm is prime to `l`.

We define `Φ(P)` directly in `𝓞 K` by Mathlib's expansion of the `m`-th power of a Gauss sum of
a character of order `m` into Jacobi sums (`gaussSum_pow_eq_prod_jacobiSum`):
`Φ(P) = χ_P(-1) · N P · ∏_{1 ≤ i < m - 1} J(χ_P, χ_P ^ i)`.
The defining property, that `Φ(P)` is `g(χ_P, ψ)^m` in every domain into which `𝓞 K` embeds and
for every primitive `ψ`, is `Ideal.stickelbergerPhi_prime`. For an ideal `A = P₁ ⋯ Pᵣ` factored
into primes, `Φ(A) = ∏ᵢ Φ(Pᵢ)`; the primes whose norm is not prime to `m` contribute `1`, so that
`Φ(A)` is the value at the part of `A` prime to `m`.

## Main definitions and results

* `Ideal.stickelbergerPhi A m`: the Gauss sum power `Φ(A) ∈ 𝓞 K`.
* `Ideal.stickelbergerPhi_eq_mul_prod_jacobiSum`: the Jacobi-sum expression of `Φ(P)` at a prime
  `P` whose norm is prime to `m`.
* `Ideal.stickelbergerPhi_prime`: `Φ(P) = g(χ_P, ψ)^m`, read in any domain containing `𝓞 K`.
* `Ideal.stickelbergerPhi_mul`: `Φ(A B) = Φ(A) Φ(B)` for nonzero `A` and `B`.
* `Ideal.stickelbergerPhi_top`: `Φ(𝓞 K) = 1`.
* `Ideal.stickelbergerPhi_norm_sq`: `|σ(Φ(A))|² = N(A)^m` for every complex embedding `σ` of `K`
  and every ideal `A` whose norm is prime to `m`.
* `Ideal.stickelbergerPhi_modEq`: `Φ(P) ≡ -1 (mod m)` for `m` prime.
* `Ideal.stickelbergerPhi_modEq_neg_one_pow`: `Φ(A) ≡ (-1)^r (mod m)` for `m` prime, where `r` is
  the number of prime factors of `A`, counted with multiplicity.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Proposition 4.2.
* S. A. Katre, *Gauss–Jacobi sums and Stickelberger's theorem*, §1, Proposition 1.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 14, §5.
-/

public section

open NumberField UniqueFactorizationMonoid

namespace Ideal

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} [NeZero m] [HasEnoughRootsOfUnity (𝓞 K) m]

open scoped Classical in
variable (m) in
/-- The value of `Φ` at a maximal ideal `P` whose norm is prime to `m`, written through Jacobi
sums of `χ_P = (· / P)_m⁻¹`; `1` at every other ideal. -/
private noncomputable def stickelbergerPhiAt (P : Ideal (𝓞 K)) : 𝓞 K :=
  if h : P.IsMaximal ∧ (absNorm P).Coprime m then
    letI := h.1
    letI := Fintype.ofFinite (𝓞 K ⧸ P)
    (powerResidueSymbol P m)⁻¹ (-1) * absNorm P *
      ∏ i ∈ Finset.Ico 1 (m - 1),
        jacobiSum (powerResidueSymbol P m)⁻¹ ((powerResidueSymbol P m)⁻¹ ^ i)
  else 1

/-- **The Gauss sum power** `Φ(A) ∈ 𝓞 K` of an ideal `A` of `𝓞 K`. If `A = P₁ ⋯ Pᵣ` is the
factorisation of `A` into maximal ideals, `Φ(A)` is the product of the `Φ(Pᵢ)` over the factors
whose norm is prime to `m`. For `m ≥ 2`, `Φ(P) = g(χ_P, ψ)^m` is the `m`-th power of the Gauss
sum of `χ_P = (· / P)_m⁻¹` with any primitive additive character `ψ`
(`Ideal.stickelbergerPhi_prime`); for `m = 1`, `Φ(P)` is just the Jacobi-sum expression of
`Ideal.stickelbergerPhi_eq_mul_prod_jacobiSum`. -/
noncomputable def stickelbergerPhi (A : Ideal (𝓞 K)) (m : ℕ) [NeZero m]
    [HasEnoughRootsOfUnity (𝓞 K) m] : 𝓞 K :=
  ((normalizedFactors A).map (stickelbergerPhiAt m)).prod

/-- At a maximal ideal, `Φ` is its local factor. -/
private theorem stickelbergerPhi_of_isMaximal (P : Ideal (𝓞 K)) [P.IsMaximal] :
    stickelbergerPhi P m = stickelbergerPhiAt m P := by
  have hP : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField K)
  rw [stickelbergerPhi, normalizedFactors_irreducible
    (prime_of_isPrime hP inferInstance).irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- **The Jacobi-sum expression of `Φ(P)`.** If the norm of the maximal ideal `P` is prime to
`m`, then `Φ(P) = χ_P(-1) · N P · ∏_{1 ≤ i < m - 1} J(χ_P, χ_P ^ i)` with `χ_P = (· / P)_m⁻¹`. -/
theorem stickelbergerPhi_eq_mul_prod_jacobiSum (P : Ideal (𝓞 K)) [P.IsMaximal]
    [Fintype (𝓞 K ⧸ P)] (hP : (absNorm P).Coprime m) :
    stickelbergerPhi P m = (powerResidueSymbol P m)⁻¹ (-1) * absNorm P *
      ∏ i ∈ Finset.Ico 1 (m - 1),
        jacobiSum (powerResidueSymbol P m)⁻¹ ((powerResidueSymbol P m)⁻¹ ^ i) := by
  rw [stickelbergerPhi_of_isMaximal, stickelbergerPhiAt, dite_eq_left ⟨‹_›, hP⟩]
  -- The local factor sums over `Fintype.ofFinite`; identify it with the given instance.
  congr!

/-- At a maximal ideal whose norm is not prime to `m`, `Φ` is `1` by convention. -/
theorem stickelbergerPhi_of_not_coprime (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hP : ¬(absNorm P).Coprime m) : stickelbergerPhi P m = 1 := by
  rw [stickelbergerPhi_of_isMaximal, stickelbergerPhiAt, dite_eq_right (not_and_of_not_right _ hP)]

/-- **`Φ(P)` is the `m`-th power of the Gauss sum of `χ_P = (· / P)_m⁻¹`.** Let `m ≥ 2` and let
`P` be a maximal ideal whose norm is prime to `m`. For every injective ring homomorphism `f` from
`𝓞 K` to a domain `R` and every primitive additive character `ψ` of `𝓞 K ⧸ P` with values in `R`,
`f (Φ(P)) = g(χ_P, ψ)^m`, the character `χ_P` being pushed to `R` along `f`. -/
theorem stickelbergerPhi_prime (P : Ideal (𝓞 K)) [P.IsMaximal] [Fintype (𝓞 K ⧸ P)]
    (hP : (absNorm P).Coprime m) (hm : 2 ≤ m) {R : Type*} [CommRing R] [IsDomain R]
    {f : 𝓞 K →+* R} (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R}
    (hψ : ψ.IsPrimitive) :
    f (stickelbergerPhi P m) = gaussSum ((powerResidueSymbol P m)⁻¹.ringHomComp f) ψ ^ m := by
  let _ := Ideal.Quotient.field P
  have hχ : orderOf ((powerResidueSymbol P m)⁻¹.ringHomComp f) = m := by
    rw [← MulChar.ringHomCompHom_apply, orderOf_injective _ (MulChar.injective_ringHomComp hf),
      orderOf_inv, orderOf_powerResidueSymbol hP]
  have h := gaussSum_pow_eq_prod_jacobiSum (hχ ▸ hm) hψ
  rw [hχ] at h
  rw [h, stickelbergerPhi_eq_mul_prod_jacobiSum P hP]
  simp [MulChar.ringHomComp_pow, jacobiSum_ringHomComp, absNorm_eq_natCard]

/-- **Multiplicativity of `Φ`.** `Φ(A B) = Φ(A) Φ(B)` for nonzero ideals `A` and `B`. -/
theorem stickelbergerPhi_mul {A B : Ideal (𝓞 K)} (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    stickelbergerPhi (A * B) m = stickelbergerPhi A m * stickelbergerPhi B m := by
  rw [stickelbergerPhi, normalizedFactors_mul hA hB, Multiset.map_add, Multiset.prod_add,
    stickelbergerPhi, stickelbergerPhi]

/-- `Φ(𝓞 K) = 1`. -/
@[simp]
theorem stickelbergerPhi_top : stickelbergerPhi (⊤ : Ideal (𝓞 K)) m = 1 := by
  rw [stickelbergerPhi, ← one_eq_top, normalizedFactors_one, Multiset.map_zero,
    Multiset.prod_zero]

/-- The zero ideal has no prime factors, so `Φ(0) = 1` by convention. -/
@[simp]
theorem stickelbergerPhi_bot : stickelbergerPhi (⊥ : Ideal (𝓞 K)) m = 1 := by
  rw [stickelbergerPhi, ← zero_eq_bot, normalizedFactors_zero, Multiset.map_zero,
    Multiset.prod_zero]

/-- `|σ(Φ(P))|² = N(P)^m` at a maximal ideal `P` whose norm is prime to `m`. -/
private theorem stickelbergerPhi_norm_sq_of_isMaximal (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hP : (absNorm P).Coprime m) (hm : 2 ≤ m) (σ : K →+* ℂ) :
    ‖σ (stickelbergerPhi P m)‖ ^ 2 = (absNorm P : ℝ) ^ m := by
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  let f := σ.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := σ.injective.comp (FaithfulSMul.algebraMap_injective _ _)
  have hχ : (powerResidueSymbol P m)⁻¹.ringHomComp f ≠ 1 := by
    rw [MulChar.ringHomComp_ne_one_iff hf, Ne, inv_eq_one, ← orderOf_eq_one_iff,
      orderOf_powerResidueSymbol hP]
    lia
  have hψ := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (𝓞 K ⧸ P)
  -- `f` is `σ` precomposed with the coercion, so `stickelbergerPhi_prime` computes `σ (Φ(P))`.
  have h : σ (stickelbergerPhi P m) = gaussSum ((powerResidueSymbol P m)⁻¹.ringHomComp f)
      (AddChar.FiniteField.primitiveChar_to_Complex (𝓞 K ⧸ P)) ^ m :=
    stickelbergerPhi_prime P hP hm hf hψ
  calc ‖σ (stickelbergerPhi P m)‖ ^ 2
      = (‖gaussSum ((powerResidueSymbol P m)⁻¹.ringHomComp f)
          (AddChar.FiniteField.primitiveChar_to_Complex (𝓞 K ⧸ P))‖ ^ 2) ^ m := by
        rw [h, norm_pow]
        ring
    _ = (absNorm P : ℝ) ^ m := by
        rw [TauCeti.norm_gaussSum hχ hψ, Real.sq_sqrt (Nat.cast_nonneg _)]
        simp [absNorm_eq_natCard]

/-- **The absolute value of `Φ(A)`.** If `m ≥ 2` and the norm of `A` is prime to `m`, then
`|σ(Φ(A))|² = N(A)^m` for every complex embedding `σ` of `K`. -/
theorem stickelbergerPhi_norm_sq {A : Ideal (𝓞 K)} (hA : (absNorm A).Coprime m) (hm : 2 ≤ m)
    (σ : K →+* ℂ) : ‖σ (stickelbergerPhi A m)‖ ^ 2 = (absNorm A : ℝ) ^ m := by
  induction A using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left] at hA
    lia
  | h₂ A hA' =>
    rw [isUnit_iff.mp hA', stickelbergerPhi_top, absNorm_top]
    simp
  | h₃ A P hA₀ hP ih =>
    have : P.IsMaximal := ((isPrime_of_prime hP).isMaximal hP.ne_zero)
    rw [map_mul, Nat.coprime_mul_iff_left] at hA
    simp only [stickelbergerPhi_mul hP.ne_zero hA₀, map_mul, norm_mul, mul_pow, Nat.cast_mul]
    rw [ih hA.2, stickelbergerPhi_norm_sq_of_isMaximal P hA.1 hm]

/-- `Φ(A)` is nonzero when `m ≥ 2` and the norm of `A` is prime to `m`. -/
theorem stickelbergerPhi_ne_zero {A : Ideal (𝓞 K)} (hA : (absNorm A).Coprime m) (hm : 2 ≤ m) :
    stickelbergerPhi A m ≠ 0 := by
  have hA₀ : absNorm A ≠ 0 := by
    rintro h
    rw [h, Nat.coprime_zero_left] at hA
    lia
  intro h
  have := stickelbergerPhi_norm_sq hA hm (Classical.arbitrary (K →+* ℂ))
  simp only [h, map_zero, norm_zero, zero_pow two_ne_zero] at this
  exact pow_ne_zero m (Nat.cast_ne_zero.mpr hA₀) this.symm

/-- **`Φ(P)` is `-1` modulo `m`.** If `m` is prime and `P` is a maximal ideal whose norm is prime
to `m`, then `Φ(P) ≡ -1` modulo `m 𝓞 K`. -/
theorem stickelbergerPhi_modEq [Fact m.Prime] (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hP : (absNorm P).Coprime m) :
    stickelbergerPhi P m ≡ -1 [SMOD Ideal.span {(m : 𝓞 K)}] := by
  have hm : m.Prime := Fact.out
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  -- We read `Φ(P)` as a Gauss sum power in the ring `R` of algebraic integers of `ℂ`, through an
  -- embedding `f : 𝓞 K → R` and a primitive additive character `ψ` with values in `R`.
  let R := integralClosure ℤ ℂ
  let σ : K →+* ℂ := Classical.arbitrary _
  let f : 𝓞 K →+* R := (σ.comp (algebraMap (𝓞 K) K)).codRestrict R.toSubring
    fun x => (x.isIntegral_coe.map σ.toIntAlgHom :)
  have hf : Function.Injective f := fun x y h =>
    (σ.injective.comp (FaithfulSMul.algebraMap_injective _ _)) (congrArg Subtype.val h)
  let ψ₀ := AddChar.FiniteField.primitiveChar_to_Complex (𝓞 K ⧸ P)
  -- The values of `ψ₀` are roots of unity, hence algebraic integers.
  let ψ : AddChar (𝓞 K ⧸ P) R :=
    { toFun t := ⟨ψ₀ t, IsIntegral.of_pow (Fintype.card_pos (α := 𝓞 K ⧸ P)) <| by
        rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
        exact isIntegral_one⟩
      map_zero_eq_one' := Subtype.ext ψ₀.map_zero_eq_one
      map_add_eq_mul' a b := Subtype.ext (ψ₀.map_add_eq_mul a b) }
  have hψ : ψ.IsPrimitive := fun a ha h =>
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive _ ha <|
      DFunLike.ext _ _ fun t => congrArg Subtype.val (DFunLike.congr_fun h t)
  -- `m` is invertible in the residue field, since it does not divide `N P`.
  have hmF : (m : 𝓞 K ⧸ P) ≠ 0 := by
    refine IsUnit.ne_zero ((isUnit_iff_not_dvd_char _ m).mpr fun h => hm.one_lt.ne' ?_)
    rw [prime_dvd_char_iff_dvd_card, ← Nat.card_eq_fintype_card, ← absNorm_eq_natCard] at h
    exact Nat.eq_one_of_dvd_coprimes hP h dvd_rfl
  have hχ : powerResidueSymbol P m ^ m = 1 := by
    have := pow_orderOf_eq_one (powerResidueSymbol P m)
    rwa [orderOf_powerResidueSymbol hP] at this
  -- In `R`, `f (Φ(P)) + 1 = y * m` by the congruence for Gauss sums.
  have h := TauCeti.gaussSum_pow_modEq_neg_one (l := m)
    (χ := (powerResidueSymbol P m)⁻¹.ringHomComp f)
    (by rw [MulChar.ringHomComp_pow, inv_pow, hχ, inv_one, MulChar.ringHomComp_one])
    (by rw [AddChar.pow_mulShift]; exact hψ hmF)
  rw [← stickelbergerPhi_prime P hP hm.two_le hf hψ, SModEq.sub_mem, sub_neg_eq_add,
    mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  -- Hence `(Φ(P) + 1) / m ∈ K` maps to the algebraic integer `y`, so it lies in `𝓞 K`.
  have hz : σ (((stickelbergerPhi P m + 1 : 𝓞 K) : K) / m) = y := by
    rw [map_div₀, map_natCast, div_eq_iff (Nat.cast_ne_zero.mpr hm.ne_zero)]
    -- `f` is the corestriction of `σ` to `R`, so its values are those of `σ`.
    have hfx : ∀ x, (f x : ℂ) = σ x := fun _ => rfl
    simpa [hfx] using (congrArg Subtype.val hy).symm
  obtain ⟨z, hz'⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 K) |>.mp <|
    (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).mp (hz ▸ y.2)
  rw [SModEq.sub_mem, sub_neg_eq_add, mem_span_singleton']
  refine ⟨z, RingOfIntegers.coe_injective ?_⟩
  rw [map_mul, hz', map_natCast, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hm.ne_zero)]

/-- **`Φ(A)` is `±1` modulo `m`.** If `m` is prime and the norm of `A` is prime to `m`, then
`Φ(A) ≡ (-1)^r` modulo `m 𝓞 K`, where `r` is the number of prime factors of `A` counted with
multiplicity. -/
theorem stickelbergerPhi_modEq_neg_one_pow [Fact m.Prime] {A : Ideal (𝓞 K)}
    (hA : (absNorm A).Coprime m) :
    stickelbergerPhi A m ≡ (-1) ^ (normalizedFactors A).card [SMOD Ideal.span {(m : 𝓞 K)}] := by
  induction A using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left] at hA
    exact absurd hA (Fact.out : m.Prime).ne_one
  | h₂ A hA' =>
    rw [isUnit_iff.mp hA', stickelbergerPhi_top, ← one_eq_top, normalizedFactors_one,
      Multiset.card_zero, pow_zero]
  | h₃ A P hA₀ hP ih =>
    have : P.IsMaximal := ((isPrime_of_prime hP).isMaximal hP.ne_zero)
    rw [map_mul, Nat.coprime_mul_iff_left] at hA
    rw [stickelbergerPhi_mul hP.ne_zero hA₀, normalizedFactors_mul hP.ne_zero hA₀,
      normalizedFactors_irreducible hP.irreducible, Multiset.card_add, Multiset.card_singleton,
      pow_add, pow_one]
    exact (stickelbergerPhi_modEq P hA.1).mul (ih hA.2)

end Ideal
