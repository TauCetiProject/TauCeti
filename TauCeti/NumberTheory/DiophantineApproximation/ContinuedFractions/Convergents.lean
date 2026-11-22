/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.ContinuedFractions.Basic

/-!
# Integer convergents and their signed errors

Write `ξ.convergent n = pₙ / qₙ` in lowest terms, with `q₀ = 1`. This file names the integers
`pₙ = ξ.convNum n` and `qₙ = ξ.convDen n` and the signed error `ξ.convErr n = qₙ ξ - pₙ`, and
proves the classical facts about them that the theory of best approximations and the three-gap
theorem are built from.

The integer data satisfy the recurrences `qₙ₊₂ = aₙ₊₂ qₙ₊₁ + qₙ` and `pₙ₊₂ = aₙ₊₂ pₙ₊₁ + pₙ`,
where `aₙ₊₂` is a natural number (Mathlib's partial denominator
`(GenContFract.of ξ).partDens.get? (n + 1)`), and the determinant identity
`pₙ qₙ₊₁ - pₙ₊₁ qₙ = (-1) ^ (n + 1)`.

The errors alternate in sign: before the expansion terminates, `qₙ ξ - pₙ` is positive exactly
for even `n`. From the alternation and the determinant identity, every error is controlled by its
neighbours:

* `|qₙ ξ - pₙ| qₙ₊₁ + |qₙ₊₁ ξ - pₙ₊₁| qₙ = 1`, hence `|qₙ ξ - pₙ| < 1 / qₙ₊₁`;
* `|qₙ ξ - pₙ| = aₙ₊₂ |qₙ₊₁ ξ - pₙ₊₁| + |qₙ₊₂ ξ - pₙ₊₂|`, hence the errors strictly decrease in
  absolute value.

Mathlib's `GenContFract.abs_sub_convs_le` gives the bound `|qₙ ξ - pₙ| ≤ 1 / qₙ₊₁` only
non-strictly; the strict bound needs the next error to be nonzero.

## Main definitions

* `Real.convNum`, `Real.convDen`: the numerator and denominator of `ξ.convergent n`.
* `Real.convErr`: the signed error `qₙ ξ - pₙ`.

## Main statements

* `Real.convDen_add_two`, `Real.convNum_add_two`: the recurrences.
* `Real.convNum_mul_convDen_succ_sub_convNum_succ_mul_convDen`: the determinant identity.
* `Real.convErr_pos_iff`: the errors alternate in sign.
* `Real.abs_convErr_lt_inv_convDen_succ`: `|qₙ ξ - pₙ| < 1 / qₙ₊₁`.
* `Real.abs_convErr_succ_lt`, `Real.strictAnti_abs_convErr`: the errors strictly decrease in
  absolute value.

## References

* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 6th ed., ch. X,
  §§10.2, 10.4, 10.7 and 10.8.
* A. Ya. Khinchin, *Continued Fractions*, ch. I, §§2–4.
-/

public section

open GenContFract
open GenContFract (of)

namespace Real

variable {ξ : ℝ} {n : ℕ}

/-! ### Integer data -/

/-- The numerator `pₙ` of the `n`-th convergent `ξ.convergent n = pₙ / qₙ` of `ξ`, in lowest
terms. -/
noncomputable def convNum (ξ : ℝ) (n : ℕ) : ℤ := (ξ.convergent n).num

/-- The denominator `qₙ` of the `n`-th convergent `ξ.convergent n = pₙ / qₙ` of `ξ`, in lowest
terms. -/
noncomputable def convDen (ξ : ℝ) (n : ℕ) : ℕ := (ξ.convergent n).den

theorem convNum_def (ξ : ℝ) (n : ℕ) : ξ.convNum n = (ξ.convergent n).num := (rfl)

theorem convDen_def (ξ : ℝ) (n : ℕ) : ξ.convDen n = (ξ.convergent n).den := (rfl)

/-- The convergent is the reduced fraction `pₙ / qₙ`. -/
theorem convergent_eq_convNum_div_convDen (ξ : ℝ) (n : ℕ) :
    ξ.convergent n = ξ.convNum n / ξ.convDen n :=
  (Rat.num_div_den _).symm

/-- `pₙ` is the numerator continuant `Aₙ` of the continued fraction of `ξ`. -/
theorem cast_convNum (ξ : ℝ) (n : ℕ) : (ξ.convNum n : ℝ) = (of ξ).nums n :=
  num_convergent ξ n

/-- `qₙ` is the denominator continuant `Bₙ` of the continued fraction of `ξ`. -/
theorem cast_convDen (ξ : ℝ) (n : ℕ) : (ξ.convDen n : ℝ) = (of ξ).dens n :=
  den_convergent ξ n

theorem convDen_pos (ξ : ℝ) (n : ℕ) : 0 < ξ.convDen n :=
  (ξ.convergent n).pos

theorem isCoprime_convNum_convDen (ξ : ℝ) (n : ℕ) : IsCoprime (ξ.convNum n) (ξ.convDen n : ℤ) :=
  Rat.isCoprime_num_den _

@[simp]
theorem convNum_zero (ξ : ℝ) : ξ.convNum 0 = ⌊ξ⌋ := by
  simp [convNum, convergent_zero]

@[simp]
theorem convDen_zero (ξ : ℝ) : ξ.convDen 0 = 1 := by
  simp [convDen, convergent_zero]

theorem monotone_convDen (ξ : ℝ) : Monotone ξ.convDen :=
  monotone_den_convergent ξ

/-- `q₁ = a₁`, where `a₁` is the first partial denominator. -/
theorem convDen_one {a : ℕ} (ha : (of ξ).partDens.get? 0 = some (a : ℝ)) : ξ.convDen 1 = a := by
  obtain ⟨gp, hs, hb⟩ := exists_s_b_of_partDen ha
  have h := first_den_eq hs
  rw [← cast_convDen, hb] at h
  exact_mod_cast h

/-- `p₁ = a₁ ⌊ξ⌋ + 1`, where `a₁` is the first partial denominator. -/
theorem convNum_one {a : ℕ} (ha : (of ξ).partDens.get? 0 = some (a : ℝ)) :
    ξ.convNum 1 = a * ⌊ξ⌋ + 1 := by
  obtain ⟨gp, hs, hb⟩ := exists_s_b_of_partDen ha
  have h := first_num_eq hs
  rw [← cast_convNum, hb, of_partNum_eq_one (partNum_eq_s_a hs), of_h_eq_floor] at h
  exact_mod_cast h

/-- The recurrence `qₙ₊₂ = aₙ₊₂ qₙ₊₁ + qₙ`, where `aₙ₊₂` is the partial denominator
`(of ξ).partDens.get? (n + 1)`. -/
theorem convDen_add_two {a : ℕ} (ha : (of ξ).partDens.get? (n + 1) = some (a : ℝ)) :
    ξ.convDen (n + 2) = a * ξ.convDen (n + 1) + ξ.convDen n := by
  obtain ⟨gp, hs, hb⟩ := exists_s_b_of_partDen ha
  have h := dens_recurrence hs rfl rfl
  rw [of_partNum_eq_one (partNum_eq_s_a hs), hb, one_mul, ← cast_convDen, ← cast_convDen,
    ← cast_convDen] at h
  exact_mod_cast h

/-- The recurrence `pₙ₊₂ = aₙ₊₂ pₙ₊₁ + pₙ`, where `aₙ₊₂` is the partial denominator
`(of ξ).partDens.get? (n + 1)`. -/
theorem convNum_add_two {a : ℕ} (ha : (of ξ).partDens.get? (n + 1) = some (a : ℝ)) :
    ξ.convNum (n + 2) = a * ξ.convNum (n + 1) + ξ.convNum n := by
  obtain ⟨gp, hs, hb⟩ := exists_s_b_of_partDen ha
  have h := nums_recurrence hs rfl rfl
  rw [of_partNum_eq_one (partNum_eq_s_a hs), hb, one_mul, ← cast_convNum, ← cast_convNum,
    ← cast_convNum] at h
  exact_mod_cast h

/-- The denominators strictly increase from index `1` on, as long as the expansion continues. -/
theorem convDen_succ_lt_convDen_add_two (h : ¬(of ξ).TerminatedAt (n + 1)) :
    ξ.convDen (n + 1) < ξ.convDen (n + 2) := by
  obtain ⟨a, ha⟩ := exists_nat_partDens_get?_eq h
  have ha1 : 1 ≤ a := by exact_mod_cast of_one_le_get?_partDen ha
  rw [convDen_add_two ha]
  nlinarith [convDen_pos ξ n]

/-- The denominators of the convergents of an irrational number strictly increase from index `1`
on. -/
theorem strictMono_convDen_succ (hξ : Irrational ξ) : StrictMono fun n ↦ ξ.convDen (n + 1) :=
  strictMono_nat_of_lt_succ fun _ ↦ convDen_succ_lt_convDen_add_two (hξ.not_of_terminatedAt _)

/-- The determinant identity `pₙ qₙ₊₁ - pₙ₊₁ qₙ = (-1) ^ (n + 1)`, as long as the expansion has
not terminated at `n`. -/
theorem convNum_mul_convDen_succ_sub_convNum_succ_mul_convDen (h : ¬(of ξ).TerminatedAt n) :
    ξ.convNum n * ξ.convDen (n + 1) - ξ.convNum (n + 1) * ξ.convDen n = (-1) ^ (n + 1) := by
  -- `SimpContFract.of ξ` is `of ξ` bundled with its simplicity proof, so its determinant
  -- formula applies to `of ξ`.
  have hdet : (of ξ).nums n * (of ξ).dens (n + 1) - (of ξ).dens n * (of ξ).nums (n + 1) =
      (-1) ^ (n + 1) := (SimpContFract.of ξ).determinant h
  rw [← cast_convNum, ← cast_convNum, ← cast_convDen, ← cast_convDen] at hdet
  exact_mod_cast (by linear_combination hdet : (ξ.convNum n * ξ.convDen (n + 1) -
    ξ.convNum (n + 1) * ξ.convDen n : ℝ) = (-1) ^ (n + 1))

/-! ### The signed error -/

/-- The signed error `qₙ ξ - pₙ` of the `n`-th convergent `pₙ / qₙ` of `ξ`. -/
noncomputable def convErr (ξ : ℝ) (n : ℕ) : ℝ := ξ.convDen n * ξ - ξ.convNum n

theorem convErr_def (ξ : ℝ) (n : ℕ) : ξ.convErr n = ξ.convDen n * ξ - ξ.convNum n := (rfl)

theorem convErr_eq_convDen_mul_sub_convergent (ξ : ℝ) (n : ℕ) :
    ξ.convErr n = ξ.convDen n * (ξ - ξ.convergent n) := by
  have hq : (ξ.convDen n : ℝ) ≠ 0 := by exact_mod_cast (convDen_pos ξ n).ne'
  rw [convErr_def, convergent_eq_convNum_div_convDen, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_natCast, mul_sub, mul_div_cancel₀ _ hq]

/-- The zeroth error is the fractional part: `q₀ ξ - p₀ = ξ - ⌊ξ⌋`. -/
@[simp]
theorem convErr_zero (ξ : ℝ) : ξ.convErr 0 = Int.fract ξ := by
  rw [convErr_def, convDen_zero, convNum_zero, Nat.cast_one, one_mul, Int.self_sub_floor]

/-- The errors satisfy the same recurrence as the integer data:
`qₙ₊₂ ξ - pₙ₊₂ = aₙ₊₂ (qₙ₊₁ ξ - pₙ₊₁) + (qₙ ξ - pₙ)`. -/
theorem convErr_add_two {a : ℕ} (ha : (of ξ).partDens.get? (n + 1) = some (a : ℝ)) :
    ξ.convErr (n + 2) = a * ξ.convErr (n + 1) + ξ.convErr n := by
  simp only [convErr_def, convDen_add_two ha, convNum_add_two ha]
  push_cast
  ring

/-- The determinant identity for the errors:
`(qₙ ξ - pₙ) qₙ₊₁ - (qₙ₊₁ ξ - pₙ₊₁) qₙ = (-1) ^ n`. -/
theorem convErr_mul_convDen_succ_sub_convErr_succ_mul_convDen (h : ¬(of ξ).TerminatedAt n) :
    ξ.convErr n * ξ.convDen (n + 1) - ξ.convErr (n + 1) * ξ.convDen n = (-1) ^ n := by
  have hdet : (ξ.convNum n * ξ.convDen (n + 1) - ξ.convNum (n + 1) * ξ.convDen n : ℝ) =
      (-1) ^ (n + 1) := by
    exact_mod_cast convNum_mul_convDen_succ_sub_convNum_succ_mul_convDen h
  rw [convErr_def, convErr_def]
  linear_combination -hdet

/-- Before termination, the error `qₙ ξ - pₙ` is nonzero and has the sign of `(-1) ^ n`. -/
theorem neg_one_pow_mul_convErr_pos (h : ¬(of ξ).TerminatedAt n) :
    0 < (-1) ^ n * ξ.convErr n := by
  rw [convErr_eq_convDen_mul_sub_convergent, ← convs_eq_convergent, mul_left_comm]
  exact mul_pos (by exact_mod_cast convDen_pos ξ n) (neg_one_pow_mul_sub_convs_pos h)

/-- The error vanishes exactly when the expansion has terminated. -/
theorem convErr_eq_zero_iff : ξ.convErr n = 0 ↔ (of ξ).TerminatedAt n := by
  refine ⟨fun h ↦ by_contra fun ht ↦ (neg_one_pow_mul_convErr_pos ht).ne' (by rw [h, mul_zero]),
    fun h ↦ ?_⟩
  rw [convErr_eq_convDen_mul_sub_convergent, ← convs_eq_convergent,
    ← of_correctness_of_terminatedAt h, sub_self, mul_zero]

/-- The absolute error is `(-1) ^ n (qₙ ξ - pₙ)`; this holds after termination too, where both
sides vanish. -/
theorem abs_convErr (ξ : ℝ) (n : ℕ) : |ξ.convErr n| = (-1) ^ n * ξ.convErr n := by
  have hnonneg : 0 ≤ (-1) ^ n * ξ.convErr n := by
    by_cases h : (of ξ).TerminatedAt n
    · rw [convErr_eq_zero_iff.2 h, mul_zero]
    · exact (neg_one_pow_mul_convErr_pos h).le
  rw [← abs_of_nonneg hnonneg, abs_mul, abs_neg_one_pow, one_mul]

/-- **Alternation of the convergents.** Before termination, the error `qₙ ξ - pₙ` is positive
exactly for even `n`: the even convergents lie below `ξ` and the odd ones above. -/
theorem convErr_pos_iff (h : ¬(of ξ).TerminatedAt n) : 0 < ξ.convErr n ↔ Even n := by
  have hpos := neg_one_pow_mul_convErr_pos h
  rcases n.even_or_odd with he | ho
  · rw [he.neg_one_pow, one_mul] at hpos
    exact iff_of_true hpos he
  · rw [ho.neg_one_pow, neg_one_mul, neg_pos] at hpos
    exact iff_of_false hpos.not_gt (Nat.not_even_iff_odd.2 ho)

/-- Before termination, the error `qₙ ξ - pₙ` is negative exactly for odd `n`. -/
theorem convErr_neg_iff (h : ¬(of ξ).TerminatedAt n) : ξ.convErr n < 0 ↔ Odd n := by
  rw [← Nat.not_even_iff_odd, ← convErr_pos_iff h]
  exact ⟨fun h' ↦ h'.not_gt, fun h' ↦ (not_lt.1 h').lt_of_ne (mt convErr_eq_zero_iff.1 h)⟩

/-- `|qₙ ξ - pₙ| qₙ₊₁ + |qₙ₊₁ ξ - pₙ₊₁| qₙ = 1`, as long as the expansion has not terminated
at `n`. -/
theorem abs_convErr_mul_convDen_succ_add_abs_convErr_succ_mul_convDen
    (h : ¬(of ξ).TerminatedAt n) :
    |ξ.convErr n| * ξ.convDen (n + 1) + |ξ.convErr (n + 1)| * ξ.convDen n = 1 := by
  have hsq : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  rw [abs_convErr, abs_convErr, pow_succ]
  linear_combination (-1) ^ n * convErr_mul_convDen_succ_sub_convErr_succ_mul_convDen h + hsq

/-- `|qₙ ξ - pₙ| < 1 / qₙ₊₁`, as long as the expansion has not terminated at `n + 1`. -/
theorem abs_convErr_lt_inv_convDen_succ (h : ¬(of ξ).TerminatedAt (n + 1)) :
    |ξ.convErr n| < 1 / ξ.convDen (n + 1) := by
  have key := abs_convErr_mul_convDen_succ_add_abs_convErr_succ_mul_convDen
    (mt (terminated_stable n.le_succ) h)
  have hpos : 0 < |ξ.convErr (n + 1)| * ξ.convDen n :=
    mul_pos (abs_pos.2 (mt convErr_eq_zero_iff.1 h)) (by exact_mod_cast convDen_pos ξ n)
  rw [lt_div_iff₀ (by exact_mod_cast convDen_pos ξ (n + 1))]
  linarith

/-- `|qₙ ξ - pₙ| = aₙ₊₂ |qₙ₊₁ ξ - pₙ₊₁| + |qₙ₊₂ ξ - pₙ₊₂|`, where `aₙ₊₂` is the partial
denominator `(of ξ).partDens.get? (n + 1)`. -/
theorem abs_convErr_eq_mul_abs_convErr_succ_add {a : ℕ}
    (ha : (of ξ).partDens.get? (n + 1) = some (a : ℝ)) :
    |ξ.convErr n| = a * |ξ.convErr (n + 1)| + |ξ.convErr (n + 2)| := by
  rw [abs_convErr, abs_convErr, abs_convErr, convErr_add_two ha]
  ring

/-- The errors strictly decrease in absolute value, `|qₙ₊₁ ξ - pₙ₊₁| < |qₙ ξ - pₙ|`, as long as
the expansion has not terminated at `n`. -/
theorem abs_convErr_succ_lt (h : ¬(of ξ).TerminatedAt n) :
    |ξ.convErr (n + 1)| < |ξ.convErr n| := by
  have hn := abs_pos.2 (mt convErr_eq_zero_iff.1 h)
  by_cases h₁ : (of ξ).TerminatedAt (n + 1)
  · rwa [convErr_eq_zero_iff.2 h₁, abs_zero]
  obtain ⟨a, ha⟩ := exists_nat_partDens_get?_eq h₁
  have hn₁ := abs_pos.2 (mt convErr_eq_zero_iff.1 h₁)
  rw [abs_convErr_eq_mul_abs_convErr_succ_add ha]
  by_cases h₂ : (of ξ).TerminatedAt (n + 2)
  · -- The last partial denominator is at least `2`.
    have ha₂ : (2 : ℝ) ≤ a := two_le_of_partDen_of_terminatedAt_succ ha h₂
    rw [convErr_eq_zero_iff.2 h₂, abs_zero, add_zero]
    nlinarith
  · have ha₁ : (1 : ℝ) ≤ a := of_one_le_get?_partDen ha
    nlinarith [abs_pos.2 (mt convErr_eq_zero_iff.1 h₂)]

/-- The errors of the convergents of an irrational number strictly decrease in absolute value. -/
theorem strictAnti_abs_convErr (hξ : Irrational ξ) : StrictAnti fun n ↦ |ξ.convErr n| :=
  strictAnti_nat_of_succ_lt fun n ↦ abs_convErr_succ_lt (hξ.not_of_terminatedAt n)

end Real
