/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.JacobiSum.Quartic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Primary
public import TauCeti.NumberTheory.NumberField.Cyclotomic.RootsOfUnity
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.JacobiSum

/-!
# The Jacobi and Gauss sums of a quartic character

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and let `χ` be a multiplicative character on a finite field `F` with `q` elements,
with values in `𝓞 K`. This file shows that the normalised Jacobi sum `-χ (-1) J(χ, χ)` is
primary, that `J(χ, χ)` has norm `q`, and that `-χ (-1) J(χ, χ)` equals every primary divisor
`π` of `J(χ, χ)` of norm `q`. For the quartic residue symbol `χ = (· / P)_4` at a prime
`P = π 𝓞 K` with `π` primary, this gives the identification `J(χ, χ) = -χ (-1) π`, and with it
the fourth power `g(χ, ψ) ^ 4 = N P · π ^ 2 = π ^ 3 π̄` of the Gauss sum, on which the proof of
biquadratic reciprocity rests.

* If `χ ^ 4 = 1` and `q ≡ 1 (mod 4)`, then `-χ (-1) J(χ, χ)` is primary: it is congruent to `1`
  modulo `(1 + i) ^ 3`. This applies to the quartic residue symbol `χ = (· / P)_4` at a prime `P`
  of `𝓞 K` of odd norm, a character of order `4` (`Ideal.orderOf_powerResidueSymbol`) on a
  residue field with `N P ≡ 1 (mod 4)` elements (`NumberField.dvd_absNorm_sub_one`).
* If `χ` has order `4`, then complex conjugation inverts the values of `χ`, so it maps `J(χ, χ)`
  to `J(χ⁻¹, χ⁻¹)`, and `J(χ, χ) J(χ⁻¹, χ⁻¹) = q` (`jacobiSum_mul_jacobiSum_inv`) says that
  `J(χ, χ)` has norm `q`.
* Consequently, if `χ` has order `4` and `J(χ, χ)` is divisible by a primary element `π` of
  norm `q`, then `-χ (-1) J(χ, χ)` is an associate of `π` that is primary, so it is `π`
  (`TauCeti.existsUnique_unit_mul_isPrimaryGaussian`).
* For `χ = (· / P)_4` with `P = π 𝓞 K` the divisibility holds because `χ (t) ≡ t ^ ((q - 1) / 4)`
  modulo `π`, which makes `J(χ, χ)` a combination of power sums `∑ t, t ^ j` with
  `0 < j < q - 1` modulo `π` (`Ideal.jacobiSum_powerResidueSymbol_pow_mem`). This holds for every
  primary prime `π`, of norm `p ≡ 1 (mod 4)` or a rational prime `-q` with `q ≡ 3 (mod 4)`.
* Since `χ (-1) ^ 2 = 1`, the relation `g(χ, ψ) ^ 4 = q J(χ, χ) ^ 2`
  (`TauCeti.gaussSum_pow_four_eq_card_mul_jacobiSum_sq`) becomes `g(χ, ψ) ^ 4 = N P · π ^ 2`, and
  `N P = π π̄` gives the form `π ^ 3 π̄`. Complex conjugation is described, as in
  `TauCeti.intCast_norm_eq_mul_of_four`, as a ring endomorphism `σ` of `𝓞 K` cubing the fourth
  roots of unity.

## Main results

* `TauCeti.isPrimaryGaussian_neg_apply_neg_one_mul_jacobiSum`: `-χ (-1) J(χ, χ)` is primary for
  every character `χ` with `χ ^ 4 = 1` on a finite field with `q ≡ 1 (mod 4)` elements, with values
  in `𝓞 K`.
* `TauCeti.norm_jacobiSum_eq_card_of_orderOf_eq_four`: `J(χ, χ)` has norm `q` for every character
  `χ` of order `4` with values in `𝓞 K`.
* `TauCeti.neg_apply_neg_one_mul_jacobiSum_eq_of_dvd`: `-χ (-1) J(χ, χ) = π` for every character
  `χ` of order `4` with values in `𝓞 K` and every primary `π` of norm `q` dividing `J(χ, χ)`.
* `Ideal.jacobiSum_powerResidueSymbol_four_eq`: `J(χ, χ) = -χ (-1) π` for the quartic residue
  symbol `χ = (· / P)_4` at a prime `P = π 𝓞 K` with `π` primary.
* `Ideal.gaussSum_powerResidueSymbol_four_pow_four_eq`: `g(χ, ψ) ^ 4 = N P · π ^ 2` for this `χ`
  and a primitive additive character `ψ`, the values pushed to a domain along an injective ring
  homomorphism.
* `Ideal.gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul`: `g(χ, ψ) ^ 4 = π ^ 3 π̄`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §9.
* N. Xu, *Reciprocity Laws*, §5, Proposition 5.9, and the proof of Proposition 4.8.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3, proof of Lemma 3.2.
* The proof of `TauCeti.norm_jacobiSum_eq_card_of_orderOf_eq_four` by complex conjugation follows
  the formal proof of the norm of the cubic Jacobi sum in
  [TauCetiProject/TauCeti#21047](https://github.com/TauCetiProject/TauCeti/pull/21047).
-/

public section

open NumberField IsCyclotomicExtension.Rat

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]
  {F : Type*} [Field F] [Fintype F]

/-- **The Jacobi sum of a quartic character is primary up to sign.** If `χ` is a multiplicative
character with `χ ^ 4 = 1` on a finite field `F` with `#F ≡ 1 (mod 4)`, such as a character of
order `4`, with values in `𝓞 K = ℤ[i]`, then `-χ (-1) J(χ, χ)` is primary. -/
theorem isPrimaryGaussian_neg_apply_neg_one_mul_jacobiSum {χ : MulChar F (𝓞 K)}
    (hχ : χ ^ 4 = 1) (hq : 4 ∣ Fintype.card F - 1) :
    IsPrimaryGaussian (-χ (-1) * jacobiSum χ χ) := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  rw [hζ.isPrimaryGaussian_iff,
    show -χ (-1) * jacobiSum χ χ - 1 = -(χ (-1) * jacobiSum χ χ + 1) by ring, dvd_neg]
  exact one_add_pow_three_dvd_apply_neg_one_mul_jacobiSum_add_one hχ hq
    hζ.toInteger_isPrimitiveRoot

/-- **The norm of the quartic Jacobi sum.** If `χ` is a multiplicative character of order `4` on
a finite field `F`, with values in `𝓞 K = ℤ[i]`, then `J(χ, χ)` has norm `#F`. -/
theorem norm_jacobiSum_eq_card_of_orderOf_eq_four {χ : MulChar F (𝓞 K)} (hχ : orderOf χ = 4) :
    Algebra.norm ℤ (jacobiSum χ χ) = Fintype.card F := by
  obtain ⟨σ, hσ⟩ := exists_ringHom_apply_eq_pow_three_of_four (K := K)
  have h4 : χ ^ 4 = 1 := hχ ▸ pow_orderOf_eq_one χ
  -- `σ` inverts the values of `χ`, so it maps `J(χ, χ)` to `J(χ⁻¹, χ⁻¹)`.
  have hinv : χ⁻¹ = χ.ringHomComp σ := by
    refine MulChar.ext fun u ↦ ?_
    rw [MulChar.ringHomComp_apply,
      hσ _ (by rw [← MulChar.pow_apply_coe, h4, MulChar.one_apply_coe]),
      inv_eq_of_mul_eq_one_right (b := χ ^ 3) (by rw [← pow_succ', h4]), MulChar.pow_apply_coe]
  -- Mathlib's `jacobiSum_mul_jacobiSum_inv`, applied in `K`, gives `J(χ, χ) J(χ⁻¹, χ⁻¹) = #F`.
  let f := algebraMap (𝓞 K) K
  have hf : Function.Injective f := RingOfIntegers.coe_injective
  have h1 : χ.ringHomComp f ≠ 1 := by
    rw [MulChar.ringHomComp_ne_one_iff hf]
    rintro rfl
    simp at hχ
  have h2 : χ.ringHomComp f * χ.ringHomComp f ≠ 1 := by
    rw [← MulChar.ringHomComp_mul, MulChar.ringHomComp_ne_one_iff hf, ← sq]
    intro h
    have := Nat.le_of_dvd two_pos (hχ ▸ orderOf_dvd_of_pow_eq_one h)
    omega
  have hchar : ringChar K ≠ ringChar F := by
    simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm
  have hprod := jacobiSum_mul_jacobiSum_inv hchar h1 h1 h2
  rw [MulChar.ringHomComp_inv, jacobiSum_ringHomComp, jacobiSum_ringHomComp, ← map_mul,
    ← map_natCast f, hinv, jacobiSum_ringHomComp] at hprod
  apply Int.cast_injective (α := 𝓞 K)
  rw [intCast_norm_eq_mul_of_four (σ := σ) hσ, Int.cast_natCast]
  exact hf hprod

/-- **The normalised quartic Jacobi sum is its primary divisor of norm `#F`.** Let `χ` be a
multiplicative character of order `4` on a finite field `F`, with values in `𝓞 K = ℤ[i]`, and let
`π` be a primary element of norm `#F` dividing `J(χ, χ)`. Then `-χ (-1) J(χ, χ) = π`. This applies
to the quartic residue symbol `χ = (· / P)_4` at a prime `P = π 𝓞 K` with `π` primary, where the
divisibility holds (`Ideal.jacobiSum_powerResidueSymbol_four_eq`). -/
theorem neg_apply_neg_one_mul_jacobiSum_eq_of_dvd {χ : MulChar F (𝓞 K)} (hχ : orderOf χ = 4)
    {π : 𝓞 K} (hπ : IsPrimaryGaussian π) (hN : Algebra.norm ℤ π = Fintype.card F)
    (hdvd : π ∣ jacobiSum χ χ) : -χ (-1) * jacobiSum χ χ = π := by
  have hprim := isPrimaryGaussian_neg_apply_neg_one_mul_jacobiSum (hχ ▸ pow_orderOf_eq_one χ)
    (hχ ▸ χ.orderOf_dvd_card_sub_one)
  obtain ⟨y, hy⟩ := dvd_mul_of_dvd_right hdvd (-χ (-1))
  -- Comparing norms, the cofactor `y` has norm `±1`, so it is a unit.
  have hu : (Algebra.norm ℤ (-χ (-1))).natAbs = 1 :=
    Int.isUnit_iff_natAbs_eq.mp (((IsUnit.map χ isUnit_one.neg).neg).map _)
  have hπ0 : (Algebra.norm ℤ π).natAbs ≠ 0 := (Int.natAbs_odd.mpr hπ.odd_norm).pos.ne'
  have hy1 : (Algebra.norm ℤ y).natAbs = 1 := by
    have h := congrArg (fun x ↦ (Algebra.norm ℤ x).natAbs) hy
    simp only [map_mul, Int.natAbs_mul, hu, norm_jacobiSum_eq_card_of_orderOf_eq_four hχ, ← hN,
      one_mul] at h
    exact (Nat.mul_eq_left hπ0).mp h.symm
  have hyu : IsUnit y := by
    rw [← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, Ideal.absNorm_span_singleton,
      hy1]
  -- Both `π` and `y π` are primary, so the unit `y` is `1`.
  obtain ⟨u, -, huniq⟩ := existsUnique_unit_mul_isPrimaryGaussian hπ.odd_norm
  have h1 := huniq 1 (by simpa only [Units.val_one, one_mul] using hπ)
  have hy' := huniq hyu.unit (by simpa only [IsUnit.unit_spec, mul_comm y, ← hy] using hprim)
  rw [hy, ← hyu.unit_spec, hy'.trans h1.symm, Units.val_one, mul_one]

end TauCeti

namespace Ideal

open TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]
  {P : Ideal (𝓞 K)} [P.IsMaximal] [Fintype (𝓞 K ⧸ P)] {π : 𝓞 K}

/-- **The Jacobi sum of the quartic residue symbol.** If `K = ℚ(i)`, `P = π 𝓞 K` is a prime with
`π` primary, and `χ = (· / P)_4`, then `J(χ, χ) = -χ (-1) π`. Equivalently, since
`χ (-1) ^ 2 = 1`, the normalised Jacobi sum `-χ (-1) J(χ, χ)` is `π`. -/
theorem jacobiSum_powerResidueSymbol_four_eq (hπ : P = span {π}) (hπ' : IsPrimaryGaussian π) :
    jacobiSum (powerResidueSymbol P 4) (powerResidueSymbol P 4) =
      -powerResidueSymbol P 4 (-1) * π := by
  let _ := Ideal.Quotient.field P
  have hP : (absNorm P).Coprime 4 := hπ ▸ hπ'.absNorm_span_singleton_coprime_four
  have hN : Algebra.norm ℤ π = Fintype.card (𝓞 K ⧸ P) := by
    rw [← natCast_absNorm_span_singleton_of_four, ← hπ, absNorm_eq_natCard,
      Nat.card_eq_fintype_card]
  have hdvd : π ∣ jacobiSum (powerResidueSymbol P 4) (powerResidueSymbol P 4) := by
    rw [← mem_span_singleton, ← hπ]
    simpa only [pow_one] using
      jacobiSum_powerResidueSymbol_pow_mem hP one_ne_zero one_ne_zero (by norm_num)
  have hneg : powerResidueSymbol P 4 (-1) * powerResidueSymbol P 4 (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [← neg_apply_neg_one_mul_jacobiSum_eq_of_dvd (orderOf_powerResidueSymbol hP) hπ' hN hdvd]
  linear_combination -jacobiSum (powerResidueSymbol P 4) (powerResidueSymbol P 4) * hneg

variable {R : Type*} [CommRing R] [IsDomain R] {f : 𝓞 K →+* R}
  {ψ : AddChar (𝓞 K ⧸ P) R}

/-- **The fourth power of the quartic Gauss sum.** Let `K = ℚ(i)` and let `P = π 𝓞 K` be a prime
with `π` primary. For every injective ring homomorphism `f` from `𝓞 K` to a domain `R` and every
primitive additive character `ψ` of `𝓞 K ⧸ P` with values in `R`, the Gauss sum of the quartic
residue symbol `χ = (· / P)_4`, pushed to `R` along `f`, satisfies `g(χ, ψ) ^ 4 = N P · f π ^ 2`. -/
theorem gaussSum_powerResidueSymbol_four_pow_four_eq (hπ : P = span {π})
    (hπ' : IsPrimaryGaussian π) (hf : Function.Injective f) (hψ : ψ.IsPrimitive) :
    gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ ^ 4 = absNorm P * f π ^ 2 := by
  let _ := Ideal.Quotient.field P
  have hP : (absNorm P).Coprime 4 := hπ ▸ hπ'.absNorm_span_singleton_coprime_four
  have hχ : orderOf ((powerResidueSymbol P 4).ringHomComp f) = 4 := by
    rw [← MulChar.ringHomCompHom_apply, orderOf_injective _ (MulChar.injective_ringHomComp hf),
      orderOf_powerResidueSymbol hP]
  have hneg : f (powerResidueSymbol P 4 (-1)) * f (powerResidueSymbol P 4 (-1)) = 1 := by
    rw [← map_mul, ← map_mul, neg_one_mul, neg_neg, map_one, map_one]
  rw [gaussSum_pow_four_eq_card_mul_jacobiSum_sq hχ hψ, jacobiSum_ringHomComp,
    jacobiSum_powerResidueSymbol_four_eq hπ hπ', ← Nat.card_eq_fintype_card,
    ← absNorm_eq_natCard, map_mul, map_neg]
  linear_combination (absNorm P : R) * f π ^ 2 * hneg

/-- **The fourth power of the quartic Gauss sum, as `π ^ 3 π̄`.** Under the hypotheses of
`Ideal.gaussSum_powerResidueSymbol_four_pow_four_eq`, let `σ` be complex conjugation of
`𝓞 K = ℤ[i]`, given as a ring endomorphism cubing every fourth root of unity
(`TauCeti.exists_ringHom_apply_eq_pow_three_of_four`). Then `g(χ, ψ) ^ 4 = f π ^ 3 · f (σ π)`. -/
theorem gaussSum_powerResidueSymbol_four_pow_four_eq_pow_three_mul (hπ : P = span {π})
    (hπ' : IsPrimaryGaussian π) (hf : Function.Injective f) (hψ : ψ.IsPrimitive)
    {σ : 𝓞 K →+* 𝓞 K} (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) :
    gaussSum ((powerResidueSymbol P 4).ringHomComp f) ψ ^ 4 = f π ^ 3 * f (σ π) := by
  have hN : (absNorm P : 𝓞 K) = π * σ π := by
    rw [← intCast_norm_eq_mul_of_four hσ, ← natCast_absNorm_span_singleton_of_four, ← hπ,
      Int.cast_natCast]
  rw [gaussSum_powerResidueSymbol_four_pow_four_eq hπ hπ' hf hψ, ← map_natCast f, hN, map_mul]
  ring

end Ideal

section Examples

open Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ 4) {P : Ideal (𝓞 K)} [P.IsMaximal] [Fintype (𝓞 K ⧸ P)]
  (hP : P = span {((-1 : ℤ) : 𝓞 K) + (2 : ℤ) * hζ.toInteger})
include hP

/- The primary element `π = -1 + 2i` generates a prime of norm `5`. The quartic residue symbol at
that prime takes the value `(-1) ^ ((5 - 1) / 4) = -1` at `-1`, so the Jacobi sum is `π`
itself. -/
example : jacobiSum (powerResidueSymbol P 4) (powerResidueSymbol P 4) =
    ((-1 : ℤ) : 𝓞 K) + (2 : ℤ) * hζ.toInteger := by
  have hN : absNorm P = 5 := by
    rw [hP, absNorm_span_singleton, hζ.norm_intCast_add_intCast_mul_toInteger_of_four]
    rfl
  have h : powerResidueSymbol P 4 (-1) = -1 := by
    rw [← map_one (Ideal.Quotient.mk P), ← map_neg,
      powerResidueSymbol_mk_of_pow_eq_one (by rw [hN]; decide) (by norm_num), hN]
    norm_num
  rw [jacobiSum_powerResidueSymbol_four_eq hP (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide),
    h, neg_neg, one_mul]

/- For a primitive additive character `ψ` with values in `𝓞 K`, the fourth power of the Gauss sum
at the same prime is `5 (-1 + 2i) ^ 2 = -15 - 20i`. -/
example {ψ : AddChar (𝓞 K ⧸ P) (𝓞 K)} (hψ : ψ.IsPrimitive) :
    gaussSum ((powerResidueSymbol P 4).ringHomComp (RingHom.id _)) ψ ^ 4 =
      ((-15 : ℤ) : 𝓞 K) + (-20 : ℤ) * hζ.toInteger := by
  rw [gaussSum_powerResidueSymbol_four_pow_four_eq hP
      (by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide) Function.injective_id hψ,
    hP, absNorm_span_singleton, hζ.norm_intCast_add_intCast_mul_toInteger_of_four,
    RingHom.id_apply]
  linear_combination (20 : 𝓞 K) * hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one

end Examples
