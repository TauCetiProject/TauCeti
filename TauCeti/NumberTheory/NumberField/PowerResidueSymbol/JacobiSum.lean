/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Basic

/-!
# Jacobi sums of power residue symbols

Let `K` be a number field whose ring of integers contains a primitive `n`-th root of unity, let
`P` be a maximal ideal of `𝓞 K` whose absolute norm `q = N P` is prime to `n`, and let
`χ = (· / P)_n` be the `n`-th power residue symbol at `P`, a character of order `n` of the
residue field `𝓞 K ⧸ P` with values in `𝓞 K`. This file records two properties of the Jacobi
sums of powers of `χ`, which are elements of `𝓞 K`.

* Modulo `P`, `χ(x) ≡ x ^ k` with `k = (q - 1) / n`, so `J(χ ^ a, χ ^ b)` is congruent to
  `∑ x, x ^ (a k) (1 - x) ^ (b k)`. When `a, b ≥ 1` and `a + b < n` this is a combination of
  power sums `∑ x, x ^ j` with `0 < j < q - 1`, all of which vanish over the residue field.
  Hence `J(χ ^ a, χ ^ b) ∈ P`.
* For `n ≥ 3`, the characters `χ` and `χ ^ 2` are nontrivial, and Mathlib's
  `jacobiSum_mul_jacobiSum_inv` gives `J(χ, χ) J(χ⁻¹, χ⁻¹) = q`.

For `n = 3` and `K = ℚ(ζ₃)` these are the two facts identifying `J(χ, χ)` with the primary
generator of `P`, the input to the proof of cubic reciprocity.

## Main results

* `Ideal.jacobiSum_powerResidueSymbol_pow_mem`: `J(χ ^ a, χ ^ b) ∈ P` for `a, b ≠ 0` with
  `a + b < n`.
* `Ideal.jacobiSum_powerResidueSymbol_mul_jacobiSum_inv`: `J(χ, χ) J(χ⁻¹, χ⁻¹) = N P` for
  `n ≥ 3`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 8, §3,
  and Chapter 9, §4.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3, proof of Lemma 3.2.
* N. Xu, *Reciprocity Laws*, proof of Proposition 4.8.
-/

public section

open NumberField

namespace Ideal

variable {K : Type*} [Field K] [NumberField K] {P : Ideal (𝓞 K)} [P.IsMaximal]
  [Fintype (𝓞 K ⧸ P)] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity (𝓞 K) n]

/-- **Jacobi sums of power residue symbols lie in the prime.** If `N P` is prime to `n` and
`χ = (· / P)_n`, then `J(χ ^ a, χ ^ b) ≡ 0 (mod P)` whenever `a` and `b` are positive with
`a + b < n`. -/
theorem jacobiSum_powerResidueSymbol_pow_mem (hP : (absNorm P).Coprime n) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b < n) :
    jacobiSum (powerResidueSymbol P n ^ a) (powerResidueSymbol P n ^ b) ∈ P := by
  let _ := Ideal.Quotient.field P
  set k := (absNorm P - 1) / n with hk_def
  have hN : absNorm P - 1 ≠ 0 := by
    rw [absNorm_eq_natCard, ← Nat.card_units]
    exact Nat.card_pos.ne'
  have hk : k ≠ 0 := Nat.div_ne_zero_iff_of_dvd (dvd_absNorm_sub_one hP) |>.mpr ⟨hN, NeZero.ne n⟩
  have hcard : Fintype.card (𝓞 K ⧸ P) - 1 = n * k := by
    rw [← Nat.card_eq_fintype_card, ← absNorm_eq_natCard,
      Nat.mul_div_cancel' (dvd_absNorm_sub_one hP)]
  -- Modulo `P`, the value `(χ ^ c) x` is `x ^ (c k)`, including at `x = 0`.
  have hval (c : ℕ) (hc : c ≠ 0) (x : 𝓞 K ⧸ P) :
      Ideal.Quotient.mk P ((powerResidueSymbol P n ^ c) x) = x ^ (c * k) := by
    rw [MulChar.pow_apply' _ hc, map_pow]
    obtain rfl | hx := eq_or_ne x 0
    · rw [MulChar.map_zero, map_zero, zero_pow hc, zero_pow (mul_ne_zero hc hk)]
    · rw [mk_powerResidueSymbol hP hx, ← pow_mul, mul_comm]
  rw [← Ideal.Quotient.eq_zero_iff_mem, jacobiSum, map_sum]
  simp_rw [map_mul, hval a ha, hval b hb]
  -- Expand `(1 - x) ^ (b k)` and sum the power sums `∑ x, x ^ (a k + j)` with `j ≤ b k`.
  simp_rw [sub_eq_neg_add, add_pow, one_pow, mul_one, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  have hlt : a * k + j < Fintype.card (𝓞 K ⧸ P) - 1 := by
    rw [hcard]
    have hj' : j ≤ b * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    nlinarith [Nat.pos_of_ne_zero hk]
  calc ∑ x : 𝓞 K ⧸ P, x ^ (a * k) * ((-x) ^ j * ((b * k).choose j : 𝓞 K ⧸ P))
      = (-1) ^ j * ((b * k).choose j : 𝓞 K ⧸ P) * ∑ x : 𝓞 K ⧸ P, x ^ (a * k + j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [neg_pow, pow_add]
        ring
    _ = 0 := by rw [FiniteField.sum_pow_lt_card_sub_one _ _ hlt, mul_zero]

/-- **The product of conjugate Jacobi sums is the norm.** If `n ≥ 3`, `N P` is prime to `n` and
`χ = (· / P)_n`, then `J(χ, χ) J(χ⁻¹, χ⁻¹) = N P` in `𝓞 K`. -/
theorem jacobiSum_powerResidueSymbol_mul_jacobiSum_inv (hP : (absNorm P).Coprime n)
    (hn : 3 ≤ n) :
    jacobiSum (powerResidueSymbol P n) (powerResidueSymbol P n) *
      jacobiSum (powerResidueSymbol P n)⁻¹ (powerResidueSymbol P n)⁻¹ = absNorm P := by
  classical
  let _ := Ideal.Quotient.field P
  have hord := orderOf_powerResidueSymbol hP
  have h1 : powerResidueSymbol P n ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have h2 : powerResidueSymbol P n * powerResidueSymbol P n ≠ 1 := by
    intro h
    have := Nat.le_of_dvd two_pos (hord ▸ orderOf_dvd_of_pow_eq_one (by rwa [sq]))
    omega
  -- The residue field is finite, while `K` has characteristic zero.
  have hchar : ringChar K ≠ ringChar (𝓞 K ⧸ P) := by
    simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite (𝓞 K ⧸ P)).symm
  -- Transport the nontriviality hypotheses along the embedding `𝓞 K → K`.
  have hinj := RingOfIntegers.coe_injective (K := K)
  have h1K : (powerResidueSymbol P n).ringHomComp (algebraMap (𝓞 K) K) ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff hinj).mpr h1
  have h2K : (powerResidueSymbol P n).ringHomComp (algebraMap (𝓞 K) K) *
      (powerResidueSymbol P n).ringHomComp (algebraMap (𝓞 K) K) ≠ 1 := by
    rwa [← MulChar.ringHomComp_mul, MulChar.ringHomComp_ne_one_iff hinj]
  have key := jacobiSum_mul_jacobiSum_inv hchar h1K h1K h2K
  apply hinj
  simpa [MulChar.ringHomComp_inv, jacobiSum_ringHomComp, ← Nat.card_eq_fintype_card,
    ← absNorm_eq_natCard] using key

end Ideal
