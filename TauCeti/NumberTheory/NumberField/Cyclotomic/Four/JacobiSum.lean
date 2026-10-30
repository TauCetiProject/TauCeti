/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.JacobiSum.Quartic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Primary

/-!
# The Jacobi sum of a quartic character

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and let `χ` be a multiplicative character on a finite field `F` with `q` elements,
with values in `𝓞 K`. This file shows that the normalised Jacobi sum `-χ (-1) J(χ, χ)` is
primary, that `J(χ, χ)` has norm `q`, and that `-χ (-1) J(χ, χ)` equals every primary divisor
`π` of `J(χ, χ)` of norm `q`. For the quartic residue symbol `χ = (· / π)_4` of a primary prime
`π`, this gives the identification `-χ (-1) J(χ, χ) = π` on which the proof of biquadratic
reciprocity rests, once `π ∣ J(χ, χ)` is known; that divisibility is not proved in this file.

* If `χ ^ 4 = 1` and `q ≡ 1 (mod 4)`, then `-χ (-1) J(χ, χ)` is primary: it is congruent to `1`
  modulo `(1 + i) ^ 3`. This applies to the quartic residue symbol `χ = (· / P)_4` at a prime `P`
  of `𝓞 K` of odd norm, a character of order `4` (`Ideal.orderOf_powerResidueSymbol`) on a
  residue field with `N P ≡ 1 (mod 4)` elements (`NumberField.dvd_absNorm_sub_one`).
* If `χ` has order `4`, then complex conjugation inverts the values of `χ`, so it maps `J(χ, χ)`
  to `J(χ⁻¹, χ⁻¹)`, and `J(χ, χ) J(χ⁻¹, χ⁻¹) = q` (`jacobiSum_mul_jacobiSum_inv`) says that
  `J(χ, χ)` has norm `q`.
* Consequently, if `χ` has order `4` and `J(χ, χ)` is divisible by a primary element `π` of
  norm `q`, then `-χ (-1) J(χ, χ)` is an associate of `π` that is primary, so it is `π`
  (`TauCeti.existsUnique_unit_mul_isPrimaryGaussian`). This file takes the divisibility as a
  hypothesis. For `χ = (· / π)_4` it holds because `χ (t) ≡ t ^ ((q - 1) / 4)` modulo `π`,
  which makes `J(χ, χ)` a combination of power sums `∑ t, t ^ j` with `0 < j < q - 1` modulo `π`.

## Main results

* `TauCeti.isPrimaryGaussian_neg_apply_neg_one_mul_jacobiSum`: `-χ (-1) J(χ, χ)` is primary for
  every character `χ` with `χ ^ 4 = 1` on a finite field with `q ≡ 1 (mod 4)` elements, with values
  in `𝓞 K`.
* `TauCeti.norm_jacobiSum_eq_card_of_orderOf_eq_four`: `J(χ, χ)` has norm `q` for every character
  `χ` of order `4` with values in `𝓞 K`.
* `TauCeti.neg_apply_neg_one_mul_jacobiSum_eq_of_dvd`: `-χ (-1) J(χ, χ) = π` for every character
  `χ` of order `4` with values in `𝓞 K` and every primary `π` of norm `q` dividing `J(χ, χ)`.

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
to the quartic residue symbol `χ = (· / π)_4` at a primary prime `π` of norm `p ≡ 1 (mod 4)`, once
the divisibility `π ∣ J(χ, χ)`, which is not proved here, is supplied. -/
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
