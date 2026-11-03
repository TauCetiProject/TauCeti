/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.SModEq.Basic
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.NumberTheory.JacobiSum.Basic
import TauCeti.NumberTheory.LegendreSymbol.Complex
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.IntegralClosure.Map

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

The residue symbol of `Φ(A)` at a second prime `P'`, with `N P'` prime to `m` and to `N A`, is
`(Φ(A) / P')_m = (N P' / A)_m`. At a prime `A = P`, with `q = N P'`, the `q`-th power of the
Gauss sum is computed in two ways modulo a prime over `P'`: it is `g(P) ^ q = (q / P)_m g(P)`
because the `q`-th power map is additive in characteristic `p'`, and
`g(P) ^ (q - 1) = Φ(P) ^ ((q - 1) / m) ≡ (Φ(P) / P')_m`. This identity is the input from `Φ` to
the Eisenstein reciprocity law.

## Main definitions and results

* `Ideal.stickelbergerPhi A m`: the Gauss sum power `Φ(A) ∈ 𝓞 K`.
* `Ideal.stickelbergerPhi_eq_mul_prod_jacobiSum`: the Jacobi-sum expression of `Φ(P)` at a prime
  `P` whose norm is prime to `m`.
* `Ideal.stickelbergerPhi_prime`: `Φ(P) = g(χ_P, ψ)^m`, read in any domain containing `𝓞 K`.
* `Ideal.stickelbergerPhi_mul`: `Φ(A B) = Φ(A) Φ(B)` for nonzero `A` and `B`.
* `Ideal.stickelbergerPhi_top`: `Φ(𝓞 K) = 1`.
* `Ideal.stickelbergerPhi_norm_sq`: `|σ(Φ(A))|² = N(A)^m` for every complex embedding `σ` of `K`
  and every ideal `A` whose norm is prime to `m`.
* `Ideal.map_stickelbergerPhi`: `σ (Φ(A)) = Φ(σ A)` for every ring isomorphism `σ` of rings of
  integers, in particular for every automorphism of `K`.
* `Ideal.stickelbergerPhi_modEq`: `Φ(P) ≡ -1 (mod m)` for `m` prime and every maximal ideal `P`
  whose norm is prime to `m`.
* `Ideal.stickelbergerPhi_modEq_neg_one_pow`: `Φ(A) ≡ (-1)^r (mod m)` for `m` prime and every ideal
  `A` whose norm is prime to `m`, where `r` is the number of prime factors of `A`, counted with
  multiplicity.
* `Ideal.powerResidueSymbol_stickelbergerPhi`: `(Φ(A) / P')_m = (N P' / A)_m` for `m ≥ 2`, a
  maximal ideal `P'` whose norm is prime to `m`, and an ideal `A` whose norm is prime to `N P'`.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4, Proposition 4.2, and
  the relation `(Φ(P) / P')_l = (N P' / P)_l` before (25).
* N. Xu, *Reciprocity Laws*, §6, Proposition 6.12.
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

section Galois

variable {L : Type*} [Field L] [NumberField L] [HasEnoughRootsOfUnity (𝓞 L) m]

/-- `σ (Φ(P)) = Φ(σ P)` at a maximal ideal `P`. -/
private theorem map_stickelbergerPhi_of_isMaximal (P : Ideal (𝓞 K)) [P.IsMaximal]
    (σ : 𝓞 K ≃+* 𝓞 L) : σ (stickelbergerPhi P m) = stickelbergerPhi (P.map σ) m := by
  have hN : absNorm (P.map σ) = absNorm P := absNorm_map_of_ringEquiv σ P
  by_cases hP : (absNorm P).Coprime m
  · let _ := Fintype.ofFinite (𝓞 K ⧸ P)
    let _ := Fintype.ofFinite (𝓞 L ⧸ P.map σ)
    -- `σ` carries `χ_P` to `χ_{σ P}` along the induced isomorphism `τ` of residue fields.
    let τ := quotientEquiv P (P.map σ) σ rfl
    have hχ (x : 𝓞 K ⧸ P) :
        σ (powerResidueSymbol P m x) = powerResidueSymbol (P.map σ) m (τ x) := by
      obtain ⟨α, rfl⟩ := Quotient.mk_surjective x
      rw [map_powerResidueSymbol P σ α, ← quotientEquiv_mk P (P.map σ) σ rfl]
    have hχ' := MulChar.map_inv_apply_of_map_apply hχ
    rw [stickelbergerPhi_eq_mul_prod_jacobiSum P hP,
      stickelbergerPhi_eq_mul_prod_jacobiSum (P.map σ) (hN ▸ hP), map_mul, map_mul, map_natCast,
      map_prod, hχ', map_neg, map_one, hN]
    exact congrArg _ <| Finset.prod_congr rfl fun i _ =>
      TauCeti.map_jacobiSum hχ' (MulChar.map_pow_apply_of_map_apply hχ' i)
  · rw [stickelbergerPhi_of_not_coprime P hP, stickelbergerPhi_of_not_coprime (P.map σ) (hN ▸ hP),
      map_one]

/-- **Galois equivariance of `Φ`.** A ring isomorphism `σ : 𝓞 K ≃+* 𝓞 L` carries `Φ(A)` to
`Φ(σ A)`. Taking `L = K`, this applies to every ring automorphism of `𝓞 K`, in particular to the
restriction of every automorphism of `K`. No hypothesis on `A` is needed: `σ` preserves norms, so
the primes whose norm is not prime to `m` contribute `1` on both sides. -/
theorem map_stickelbergerPhi (A : Ideal (𝓞 K)) (σ : 𝓞 K ≃+* 𝓞 L) :
    σ (stickelbergerPhi A m) = stickelbergerPhi (A.map σ) m := by
  have hσ {B : Ideal (𝓞 K)} (hB : B ≠ ⊥) : B.map σ ≠ ⊥ :=
    (map_eq_bot_iff_of_injective σ.injective).not.mpr hB
  induction A using induction_on_prime with
  | h₁ => rw [zero_eq_bot, map_bot, stickelbergerPhi_bot, stickelbergerPhi_bot, map_one]
  | h₂ A hA => rw [isUnit_iff.mp hA, map_top, stickelbergerPhi_top, stickelbergerPhi_top, map_one]
  | h₃ A P hA hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    rw [Ideal.map_mul, stickelbergerPhi_mul hP.ne_zero hA,
      stickelbergerPhi_mul (hσ hP.ne_zero) (hσ hA), map_mul, ih, map_stickelbergerPhi_of_isMaximal]

end Galois

/-- **`Φ(P)` is `-1` modulo `m`.** If `m` is prime and `P` is a maximal ideal whose norm is prime
to `m`, then `Φ(P) ≡ -1` modulo `m 𝓞 K`. -/
theorem stickelbergerPhi_modEq [Fact m.Prime] (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hP : (absNorm P).Coprime m) :
    stickelbergerPhi P m ≡ -1 [SMOD Ideal.span {(m : 𝓞 K)}] := by
  have hm : m.Prime := Fact.out
  let _ := Ideal.Quotient.field P
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  -- We read `Φ(P)` as a Gauss sum power in the ring of algebraic integers of `ℂ`, through an
  -- embedding `f` of `𝓞 K` and a primitive additive character `ψ` with values there.
  let σ : K →+* ℂ := Classical.arbitrary _
  let f : 𝓞 K →+* integralClosure ℤ ℂ := σ.toIntAlgHom.mapIntegralClosure.toRingHom
  have hf : Function.Injective f :=
    AlgHom.mapIntegralClosure_injective (f := σ.toIntAlgHom) σ.injective
  obtain ⟨ψ, hψ⟩ := TauCeti.exists_primitive_addChar_integralClosure (𝓞 K ⧸ P)
  -- `m` is invertible in the residue field, since it does not divide `N P`.
  have hmF : (m : 𝓞 K ⧸ P) ≠ 0 := by
    rw [← map_natCast (Quotient.mk P), Ne, Quotient.eq_zero_iff_mem]
    exact natCast_notMem_of_coprime_absNorm IsPrime.ne_top' hP.symm
  have hχ : powerResidueSymbol P m ^ m = 1 := by
    have := pow_orderOf_eq_one (powerResidueSymbol P m)
    rwa [orderOf_powerResidueSymbol hP] at this
  -- There, `f (Φ(P)) + 1 = y * m` by the congruence for Gauss sums.
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
    -- `f` is the restriction of `σ`, so its values are those of `σ`.
    have hfσ (x : 𝓞 K) : (f x : ℂ) = σ x := rfl
    simpa [hfσ] using (congrArg Subtype.val hy).symm
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

section SecondPrime

/-- The case of a maximal ideal `P` in `powerResidueSymbol_stickelbergerPhi`, read through a domain
`R` containing `𝓞 K` and the values of a primitive additive character of `𝓞 K ⧸ P`, and through a
prime `I` of `R` over `P'`. -/
private theorem powerResidueSymbol_stickelbergerPhi_of_comap (P P' : Ideal (𝓞 K)) [P.IsMaximal]
    [P'.IsMaximal] (hP' : (absNorm P').Coprime m) (hPP' : (absNorm P).Coprime (absNorm P'))
    (hm : 2 ≤ m) {R : Type*} [CommRing R] [IsDomain R] {f : 𝓞 K →+* R}
    (hf : Function.Injective f) {ψ : AddChar (𝓞 K ⧸ P) R} (hψ : ψ.IsPrimitive) (I : Ideal R)
    [I.IsPrime] (hI : I.comap f = P') :
    powerResidueSymbol P' m (Quotient.mk P' (stickelbergerPhi P m)) =
      powerResidueSymbol P m (Quotient.mk P (absNorm P' : 𝓞 K)) := by
  let _ := Ideal.Quotient.field P
  let _ := Ideal.Quotient.field P'
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  let _ := Fintype.ofFinite (𝓞 K ⧸ P')
  have hq : (Quotient.mk P (absNorm P' : 𝓞 K)) ≠ 0 := by
    rw [Ne, Quotient.eq_zero_iff_mem]
    exact natCast_notMem_of_coprime_absNorm IsPrime.ne_top' hPP'.symm
  by_cases hP : (absNorm P).Coprime m
  swap
  · rw [stickelbergerPhi_of_not_coprime P hP, powerResidueSymbol_of_not_coprime hP, map_one,
      MulChar.map_one, MulChar.one_apply hq.isUnit]
  -- The residue field `F'` of `P'` embeds in the domain `S = R ⧸ I` through `ρ`, so `S` has the
  -- characteristic `p` of `F'`, and `N P' = q = p ^ n`.
  have hle : P' ≤ I.comap f := hI.ge
  let ρ := quotientMap I f hle
  have hρ : Function.Injective ρ := quotientMap_injective' hI.le
  set p := ringChar (𝓞 K ⧸ P')
  have hp : p.Prime := CharP.char_is_prime (𝓞 K ⧸ P') p
  have := Fact.mk hp
  have := CharP.of_ringHom_of_ne_zero ρ p hp.ne_zero
  obtain ⟨n, -, hcard⟩ := FiniteField.card (𝓞 K ⧸ P') p
  have hqn : absNorm P' = p ^ (n : ℕ) := by
    rw [absNorm_eq_natCard, Nat.card_eq_fintype_card, hcard]
  have hmq := dvd_absNorm_sub_one hP'
  have hq₀ : 0 < absNorm P' := hqn ▸ pow_pos hp.pos _
  -- The Gauss sum `g = g(χ_P, ψ)` and its image `gbar` in `S`.
  let χ := (powerResidueSymbol P m)⁻¹.ringHomComp f
  let π := Quotient.mk I
  let g := gaussSum χ ψ
  have hg : π g = gaussSum (χ.ringHomComp π) (π.toMonoidHom.compAddChar ψ) := by
    simp only [g, gaussSum, map_sum, map_mul, MulChar.ringHomComp_apply,
      MonoidHom.coe_compAddChar, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass]
  -- `gbar ≠ 0`, because `g g(χ⁻¹, ψ⁻¹) = N P` and `N P` is prime to `p`.
  have hχ : χ ≠ 1 := by
    rw [MulChar.ringHomComp_ne_one_iff hf, Ne, inv_eq_one, ← orderOf_eq_one_iff,
      orderOf_powerResidueSymbol hP]
    lia
  have hg₀ : π g ≠ 0 := by
    intro h
    have h' := congrArg π (gaussSum_mul_gaussSum_eq_card hχ hψ)
    rw [map_mul, h, zero_mul, ← Nat.card_eq_fintype_card, ← absNorm_eq_natCard,
      ← map_natCast f, eq_comm, Quotient.eq_zero_iff_mem, ← mem_comap, hI] at h'
    exact natCast_notMem_of_coprime_absNorm IsPrime.ne_top' hPP' h'
  -- The Frobenius: `gbar ^ q = (q / P)_m gbar`, so `gbar ^ (q - 1) = (q / P)_m` in `S`.
  have hχq : χ.ringHomComp π ^ p ^ (n : ℕ) = χ.ringHomComp π := by
    have h0 : powerResidueSymbol P m ^ m = 1 := by
      simpa [orderOf_powerResidueSymbol hP] using pow_orderOf_eq_one (powerResidueSymbol P m)
    have h1 : χ.ringHomComp π ^ m = 1 := by
      rw [MulChar.ringHomComp_pow, MulChar.ringHomComp_pow, inv_pow, h0, inv_one,
        MulChar.ringHomComp_one, MulChar.ringHomComp_one]
    obtain ⟨k, hk⟩ := hmq
    rw [← hqn, ← Nat.sub_add_cancel hq₀, hk, pow_succ, pow_mul, h1, one_pow, one_mul]
  have hval : (χ.ringHomComp π)⁻¹ ((p : 𝓞 K ⧸ P) ^ (n : ℕ)) =
      π (f (powerResidueSymbol P m (Quotient.mk P (absNorm P' : 𝓞 K)))) := by
    rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_inv, inv_inv, MulChar.ringHomComp_apply,
      MulChar.ringHomComp_apply, map_natCast, ← Nat.cast_pow, ← hqn]
  have hfrob := TauCeti.gaussSum_pow_char_pow hχq (π.toMonoidHom.compAddChar ψ)
    (by rw [← Nat.cast_pow, ← hqn, ← map_natCast (Quotient.mk P)]; exact hq.isUnit)
  rw [hval, ← hg, ← hqn, ← pow_sub_one_mul hq₀.ne'] at hfrob
  have hgq := mul_right_cancel₀ hg₀ hfrob
  -- `f (Φ(P)) = g ^ m`, so `Φ(P) ∉ P'` and `ρ ((Φ(P) / P')_m) = gbar ^ (q - 1)`.
  have hΦ : f (stickelbergerPhi P m) = g ^ m := stickelbergerPhi_prime P hP hm hf hψ
  have hΦP' : Quotient.mk P' (stickelbergerPhi P m) ≠ 0 := by
    rw [Ne, Quotient.eq_zero_iff_mem, ← hI, mem_comap, ← Quotient.eq_zero_iff_mem, hΦ,
      map_pow]
    exact pow_ne_zero m hg₀
  refine eq_of_pow_eq_one_of_mk_eq IsPrime.ne_top' hP' (powerResidueSymbol_pow_eq_one hP' hΦP')
    (powerResidueSymbol_pow_eq_one hP hq) (hρ ?_)
  rw [mk_powerResidueSymbol hP' hΦP', map_pow, quotientMap_mk, quotientMap_mk, hΦ, map_pow,
    ← pow_mul, Nat.mul_div_cancel' hmq, hgq]

/-- `(Φ(P) / P')_m = (N P' / P)_m` at a maximal ideal `P`. -/
private theorem powerResidueSymbol_stickelbergerPhi_of_isMaximal (P P' : Ideal (𝓞 K)) [P.IsMaximal]
    [P'.IsMaximal]
    (hP' : (absNorm P').Coprime m) (hPP' : (absNorm P).Coprime (absNorm P')) (hm : 2 ≤ m) :
    powerResidueSymbol P' m (Quotient.mk P' (stickelbergerPhi P m)) =
      powerResidueSymbol P m (Quotient.mk P (absNorm P' : 𝓞 K)) := by
  -- Work in the ring of algebraic integers of `ℂ`, which is integral over `𝓞 K` through `f`, and
  -- in a prime of it over `P'`.
  let _ := Ideal.Quotient.field P
  let f : 𝓞 K →+* integralClosure ℤ ℂ :=
    (Classical.arbitrary (K →+* ℂ)).toIntAlgHom.mapIntegralClosure.toRingHom
  have hf : Function.Injective f := AlgHom.mapIntegralClosure_injective
    (f := (Classical.arbitrary (K →+* ℂ)).toIntAlgHom) (RingHom.injective _)
  obtain ⟨ψ, hψ⟩ := TauCeti.exists_primitive_addChar_integralClosure (𝓞 K ⧸ P)
  let _ := f.toAlgebra
  have : IsScalarTower ℤ (𝓞 K) (integralClosure ℤ ℂ) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have : Algebra.IsIntegral (𝓞 K) (integralClosure ℤ ℂ) :=
    ⟨fun x ↦ (integralClosure.isIntegral x).tower_top⟩
  obtain ⟨I, hI, hIP'⟩ := exists_ideal_over_maximal_of_isIntegral P'
    (((RingHom.injective_iff_ker_eq_bot _).mp hf).trans_le bot_le)
  exact powerResidueSymbol_stickelbergerPhi_of_comap P P' hP' hPP' hm hf hψ I hIP'

/-- **The residue symbol of `Φ(A)` at a second prime.** Let `m ≥ 2`, let `P'` be a maximal ideal of
`𝓞 K` whose norm is prime to `m`, and let `A` be an ideal whose norm is prime to that of `P'`.
Then `(Φ(A) / P')_m = (N P' / A)_m`, the right side being the symbol at the ideal `A`. For a
maximal ideal `A = P` this is `(Φ(P) / P')_m = (N P' / P)_m`
(`Ideal.powerResidueSymbolIdeal_of_isMaximal`). -/
theorem powerResidueSymbol_stickelbergerPhi (A P' : Ideal (𝓞 K)) [P'.IsMaximal]
    (hP' : (absNorm P').Coprime m) (hAP' : (absNorm A).Coprime (absNorm P')) (hm : 2 ≤ m) :
    powerResidueSymbol P' m (Quotient.mk P' (stickelbergerPhi A m)) =
      powerResidueSymbolIdeal A m (Quotient.mk A (absNorm P' : 𝓞 K)) := by
  induction A using induction_on_prime with
  | h₁ =>
    rw [zero_eq_bot, absNorm_bot, Nat.coprime_zero_left, absNorm_eq_one_iff] at hAP'
    exact absurd hAP' IsPrime.ne_top'
  | h₂ A hA =>
    rw [isUnit_iff.mp hA, stickelbergerPhi_top, powerResidueSymbolIdeal_top, map_one,
      MulChar.map_one]
  | h₃ A P hA₀ hP ih =>
    have : P.IsMaximal := (isPrime_of_prime hP).isMaximal hP.ne_zero
    rw [map_mul, Nat.coprime_mul_iff_left] at hAP'
    rw [stickelbergerPhi_mul hP.ne_zero hA₀, map_mul, map_mul,
      powerResidueSymbolIdeal_mul_right hP.ne_zero hA₀, powerResidueSymbolIdeal_of_isMaximal,
      powerResidueSymbol_stickelbergerPhi_of_isMaximal P P' hP' hAP'.1 hm, ih hAP'.2]

end SecondPrime

end Ideal
