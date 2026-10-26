/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.MulChar.Lemmas
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The Jacobi sum of a quartic character

Let `χ` be a multiplicative character with `χ ^ 4 = 1` on a finite field `F` with `q ≡ 1 (mod 4)`
elements, such as a character of order `4`, with values in an integral domain `R`, and let
`ι ∈ R` be a primitive fourth root of unity. Then `χ (-1) J(χ, χ) ≡ -1` modulo `(1 + ι) ^ 3`. For
the quartic residue symbol `χ = (· / π)_4` of a prime `π` of `ℤ[i]` this says that
`-χ (-1) J(χ, χ)` is *primary*, the normalisation that identifies `-χ (-1) J(χ, χ)` with the
primary generator `π`.

The proof evaluates `J(χ, χ) = ∑ t, χ (t) χ (1 - t)` term by term.

* The terms `t = 0` and `t = 1` vanish.
* Since `q ≡ 1 (mod 4)`, the field `F` contains a square root `j` of `-1`, and `-4 = (1 + j) ^ 4`
  is a fourth power. Hence the term `t = 1 / 2` is `χ (1 / 4) = χ (-1)`.
* The remaining `q - 3` terms are fourth roots of unity, each congruent to `1` modulo `1 + ι`,
  and the terms at `t` and `1 - t` agree. So they contribute `q - 3` modulo `2 (1 + ι)`, an
  associate of `(1 + ι) ^ 3`.

So `J(χ, χ) ≡ χ (-1) + q - 3`, and `q ≡ 1 (mod 4)` with `4 ∈ ((1 + ι) ^ 3)` gives the claim.

## Main results

* `TauCeti.one_add_pow_three_dvd_apply_neg_one_mul_jacobiSum_add_one`:
  `(1 + ι) ^ 3 ∣ χ (-1) J(χ, χ) + 1`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §9.
* N. Xu, *Reciprocity Laws*, §5, Proposition 5.9, and the proof of Proposition 4.8.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3, proof of Lemma 3.2.
-/

public section

open Finset

namespace TauCeti

variable {F R : Type*} [Field F] [Fintype F] [CommRing R] [IsDomain R]

omit [Fintype F] [IsDomain R] in
/-- The middle term `t = 1 / 2` of `J(χ, χ)`: if `χ ^ 4 = 1` and `-1` is a square in `F`, then
`-4 = (1 + j) ^ 4` for a square root `j` of `-1`, so `χ (1 / 4) = χ (-4)⁻¹ χ (-1) = χ (-1)`. -/
private theorem apply_inv_two_mul_apply_one_sub_inv_two {χ : MulChar F R} (hχ : χ ^ 4 = 1)
    (h2 : (2 : F) ≠ 0) (hF : IsSquare (-1 : F)) : χ 2⁻¹ * χ (1 - 2⁻¹) = χ (-1) := by
  obtain ⟨j, hj⟩ := hF
  have hj4 : (1 + j) ^ 4 = -4 := by linear_combination (j ^ 2 + 4 * j + 5) * hj.symm
  have hj0 : 1 + j ≠ 0 := by
    intro h
    rw [h] at hj4
    exact h2 (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination hj4))
  have hχ' : χ (-4) = 1 := by
    rw [← hj4, map_pow, ← MulChar.pow_apply' χ (by norm_num), hχ, MulChar.one_apply hj0.isUnit]
  rw [show (1 : F) - 2⁻¹ = 2⁻¹ by linear_combination -(mul_inv_cancel₀ h2), ← map_mul,
    ← mul_one (χ _), ← hχ', ← map_mul]
  congr 1
  linear_combination (-1 - 2⁻¹ * 2) * mul_inv_cancel₀ h2

/-- The terms of `J(χ, χ)` off `t ∈ {0, 1, 1 / 2}`: the terms at `t` and `1 - t` agree and are
fourth roots of unity, hence `1` modulo `1 + ι`, so each pair contributes `2` modulo
`2 (1 + ι)`, an associate of `(1 + ι) ^ 3`. -/
private theorem one_add_pow_three_dvd_sum_erase_inv_two [DecidableEq F] {χ : MulChar F R}
    (hχ : χ ^ 4 = 1) {ι : R} (hι : IsPrimitiveRoot ι 4) (h2 : (2 : F) ≠ 0) :
    (1 + ι) ^ 3 ∣ ∑ t ∈ (univ \ {0, 1}).erase 2⁻¹, (χ t * χ (1 - t) - 1) := by
  have hsq := hι.sq_eq_neg_one
  have hS (t : F) : t ∈ (univ \ {0, 1}).erase 2⁻¹ ↔ t ≠ 2⁻¹ ∧ t ≠ 0 ∧ t ≠ 1 := by
    simp [not_or]
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
  refine sum_involution (fun t _ ↦ 1 - t) (fun t ht ↦ ?_) (fun t ht _ h ↦ ?_)
    (fun t ht ↦ ?_) (fun t _ ↦ sub_sub_cancel 1 t)
  · obtain ⟨-, ht0, ht1⟩ := (hS t).mp ht
    -- `χ t χ (1 - t) = ι ^ m` is `1` modulo `ι - 1 = ι (1 + ι)`.
    obtain ⟨m, -, hm⟩ :=
      χ.exists_apply_eq_pow hχ hι (mul_ne_zero ht0 (sub_ne_zero.mpr (Ne.symm ht1)))
    obtain ⟨c, hc⟩ : 1 + ι ∣ χ t * χ (1 - t) - 1 := by
      rw [← map_mul, hm]
      refine (Dvd.intro ι (by linear_combination hsq) : 1 + ι ∣ ι - 1).trans ?_
      simpa using sub_dvd_pow_sub_pow ι 1 m
    rw [← map_add, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, sub_sub_cancel,
      mul_comm (χ (1 - t))]
    exact ⟨-ι * c, by linear_combination 2 * hc + c * (1 + ι) * (ι + 2) * hsq⟩
  · exact ((hS t).mp ht).1 (eq_inv_of_mul_eq_one_left (by linear_combination -h))
  · obtain ⟨hth, ht0, ht1⟩ := (hS t).mp ht
    refine (hS _).mpr ⟨fun h ↦ hth ?_, sub_ne_zero.mpr (Ne.symm ht1), fun h ↦ ht0 ?_⟩
    · linear_combination -h - mul_inv_cancel₀ h2
    · linear_combination -h

/-- **The Jacobi sum of a quartic character.** Let `χ` be a multiplicative character with
`χ ^ 4 = 1` on a finite field `F` with `#F ≡ 1 (mod 4)`, such as a character of order `4`, with
values in an integral domain `R`. If `ι ∈ R` is a primitive fourth root of unity, then
`χ (-1) J(χ, χ) ≡ -1` modulo `(1 + ι) ^ 3`. -/
theorem one_add_pow_three_dvd_apply_neg_one_mul_jacobiSum_add_one {χ : MulChar F R}
    (hχ : χ ^ 4 = 1) (hq : 4 ∣ Fintype.card F - 1) {ι : R} (hι : IsPrimitiveRoot ι 4) :
    (1 + ι) ^ 3 ∣ χ (-1) * jacobiSum χ χ + 1 := by
  classical
  -- `q = 4 k + 5`, since `4 ∣ q - 1` and `q > 1`.
  have hlt := Fintype.one_lt_card (α := F)
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 4 * k + 5 :=
    ⟨(Fintype.card F - 5) / 4, by omega⟩
  have h2 : (2 : F) ≠ 0 :=
    Ring.two_ne_zero (by rw [ne_eq, FiniteField.even_card_iff_char_two]; omega)
  have hF : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.mpr (by omega)
  -- Split `J(χ, χ) = ∑ t ∈ F \ {0, 1}, χ t χ (1 - t)` into the middle term `t = 1 / 2` and the
  -- remaining `q - 3` terms.
  have hmem : (2 : F)⁻¹ ∈ (univ \ {0, 1} : Finset F) := by
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, inv_eq_zero, inv_eq_one, h2,
      true_and, false_or]
    exact fun h ↦ one_ne_zero (by linear_combination h : (1 : F) = 0)
  have hJ : jacobiSum χ χ = χ (-1) + ∑ t ∈ (univ \ {0, 1}).erase 2⁻¹, (χ t * χ (1 - t) - 1) +
      (4 * k + 2 : ℕ) := by
    rw [jacobiSum_eq_sum_sdiff, ← add_sum_erase _ _ hmem,
      apply_inv_two_mul_apply_one_sub_inv_two hχ h2 hF, sum_sub_distrib, sum_const,
      card_erase_of_mem hmem, card_univ_sdiff, card_pair zero_ne_one, hk, nsmul_one,
      show 4 * k + 5 - 2 - 1 = 4 * k + 2 by omega]
    ring
  -- Conclude from `χ (-1) = ± 1` and `(1 + ι) ^ 3 ∣ 4`.
  have hsq := hι.sq_eq_neg_one
  obtain ⟨c, hc⟩ := one_add_pow_three_dvd_sum_erase_inv_two hχ hι h2
  obtain ⟨d, hd⟩ : (1 + ι) ^ 3 ∣ (4 : R) :=
    Dvd.intro (-(1 + ι)) (by linear_combination -(ι ^ 2 + 4 * ι + 5) * hsq)
  have hneg : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [hJ, hc]
  push_cast
  rcases mul_self_eq_one_iff.mp hneg with h | h <;> rw [h]
  · exact ⟨c + d * (k + 1), by linear_combination ((k : R) + 1) * hd⟩
  · exact ⟨-c - d * k, by linear_combination -(k : R) * hd⟩

end TauCeti
