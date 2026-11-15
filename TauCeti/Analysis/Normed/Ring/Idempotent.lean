/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Norm gap for idempotent elements in normed rings

Submultiplicativity of the norm forces every idempotent `e` of positive norm in a nonunital
seminormed ring to satisfy `1 ≤ ‖e‖`: from `‖e‖ = ‖e * e‖ ≤ ‖e‖ * ‖e‖` one divides by `‖e‖ > 0`.
Consequently, an idempotent of norm strictly less than `1` vanishes
(`IsIdempotentElem.eq_zero_of_norm_lt_one`).

More generally, if two idempotents `e` and `f` in a nonunital normed ring commute, their difference
`d = e - f` satisfies `d * d * d = d`, so `d * d` is itself an idempotent that vanishes iff
`e = f`; hence `e ≠ f` forces `1 ≤ ‖e - f‖` (`IsIdempotentElem.one_le_norm_sub_of_commute`), and
`‖e - f‖ < 1` forces `e = f` (`IsIdempotentElem.eq_of_norm_sub_lt_one_of_commute`). Commutativity
is sharp: in `M₂(ℂ)`, orthogonal projections onto lines at a small positive angle are noncommuting
idempotents at arbitrarily small nonzero distance. Specializing to `f = 1` in a unital normed ring
shows that `1` is isolated at distance `1` among all idempotents
(`IsIdempotentElem.eq_one_of_norm_sub_one_lt_one`).

## Main results

* `IsIdempotentElem.one_le_norm_of_norm_pos` and `IsIdempotentElem.one_le_norm`: any nonzero
  idempotent in a nonunital normed ring has norm at least `1`.
* `IsIdempotentElem.eq_zero_of_norm_lt_one`: an idempotent with `‖e‖ < 1` is `0`.
* `IsIdempotentElem.one_le_norm_sub_of_commute` and
  `IsIdempotentElem.eq_of_norm_sub_lt_one_of_commute`: distinct commuting idempotents sit at norm
  distance at least `1`.
* `IsIdempotentElem.eq_one_of_norm_sub_one_lt_one` and
  `IsIdempotentElem.eq_one_of_norm_one_sub_lt_one`: an idempotent within norm `< 1` of `1`
  equals `1`.
-/

public section

namespace IsIdempotentElem

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R] {e f : R}

/-- The difference `e - f` of two commuting idempotents is tripotent: `(e - f) ^ 3 = e - f`. -/
theorem sub_mul_sub_mul_sub_of_commute (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hcomm : Commute e f) : (e - f) * (e - f) * (e - f) = e - f := by
  have hef_e : e * f * e = e * f := by rw [mul_assoc, ← hcomm.eq, ← mul_assoc, he.eq]
  have hef_f : e * f * f = e * f := by rw [mul_assoc, hf.eq]
  have hsq : (e - f) * (e - f) = e - e * f - e * f + f := by
    rw [mul_sub, sub_mul, sub_mul, he.eq, hf.eq, hcomm.symm.eq]
    abel
  rw [hsq, add_mul, sub_mul, sub_mul, mul_sub, mul_sub, mul_sub,
    he.eq, hf.eq, hcomm.symm.eq, hef_e, hef_f]
  abel

/-- For commuting idempotents `e` and `f`, `(e - f) * (e - f)` is idempotent. -/
theorem sub_mul_sub_of_commute (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hcomm : Commute e f) : IsIdempotentElem ((e - f) * (e - f)) := by
  rw [IsIdempotentElem, ← mul_assoc, he.sub_mul_sub_mul_sub_of_commute hf hcomm]

end NonUnitalRing

section NonUnitalSeminormedRing

variable {E : Type*} [NonUnitalSeminormedRing E] {e f : E}

/-- An idempotent of positive seminorm in a nonunital seminormed ring has seminorm at least `1`. -/
theorem one_le_norm_of_norm_pos (he : IsIdempotentElem e) (h : 0 < ‖e‖) : 1 ≤ ‖e‖ := by
  have hle : ‖e‖ * 1 ≤ ‖e‖ * ‖e‖ := by
    calc
      ‖e‖ * 1 = ‖e * e‖ := by rw [mul_one, he.eq]
      _ ≤ ‖e‖ * ‖e‖ := norm_mul_le e e
  exact le_of_mul_le_mul_left hle h

/-- An idempotent of seminorm strictly less than `1` has seminorm `0`. -/
theorem norm_eq_zero_of_norm_lt_one (he : IsIdempotentElem e) (h : ‖e‖ < 1) : ‖e‖ = 0 :=
  le_antisymm (le_of_not_gt fun hpos ↦ (he.one_le_norm_of_norm_pos hpos).not_gt h) (norm_nonneg e)

/-- If two commuting idempotents have `0 < ‖e - f‖`, then `1 ≤ ‖e - f‖`. -/
theorem one_le_norm_sub_of_norm_sub_pos_of_commute (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (hcomm : Commute e f) (hpos : 0 < ‖e - f‖) : 1 ≤ ‖e - f‖ := by
  by_contra! hlt
  have hsq_lt : ‖(e - f) * (e - f)‖ < 1 :=
    (norm_mul_le _ _).trans_lt (by nlinarith [norm_nonneg (e - f)])
  have hsq_zero : ‖(e - f) * (e - f)‖ = 0 :=
    (he.sub_mul_sub_of_commute hf hcomm).norm_eq_zero_of_norm_lt_one hsq_lt
  have hle : ‖e - f‖ ≤ 0 := by
    calc
      ‖e - f‖ = ‖(e - f) * (e - f) * (e - f)‖ := by
        rw [he.sub_mul_sub_mul_sub_of_commute hf hcomm]
      _ ≤ ‖(e - f) * (e - f)‖ * ‖e - f‖ := norm_mul_le _ _
      _ = 0 := by rw [hsq_zero, zero_mul]
  exact hpos.not_ge hle

end NonUnitalSeminormedRing

section NonUnitalNormedRing

variable {E : Type*} [NonUnitalNormedRing E] {e f : E}

/-- Every nonzero idempotent in a nonunital normed ring has norm at least `1`. -/
theorem one_le_norm (he : IsIdempotentElem e) (he₀ : e ≠ 0) : 1 ≤ ‖e‖ :=
  he.one_le_norm_of_norm_pos (norm_pos_iff.mpr he₀)

/-- An idempotent of norm strictly less than `1` in a nonunital normed ring is `0`. -/
theorem eq_zero_of_norm_lt_one (he : IsIdempotentElem e) (h : ‖e‖ < 1) : e = 0 :=
  norm_eq_zero.mp (he.norm_eq_zero_of_norm_lt_one h)

/-- Distinct commuting idempotents in a nonunital normed ring have norm distance at least `1`. -/
theorem one_le_norm_sub_of_commute (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hcomm : Commute e f) (hne : e ≠ f) : 1 ≤ ‖e - f‖ :=
  he.one_le_norm_sub_of_norm_sub_pos_of_commute hf hcomm (norm_sub_pos_iff.mpr hne)

/-- Commuting idempotents within norm distance `< 1` in a nonunital normed ring are equal. -/
theorem eq_of_norm_sub_lt_one_of_commute (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hcomm : Commute e f) (h : ‖e - f‖ < 1) : e = f := by
  by_contra hne
  exact (he.one_le_norm_sub_of_commute hf hcomm hne).not_gt h

end NonUnitalNormedRing

section NormedRing

variable {E : Type*} [NormedRing E] {e : E}

/-- An idempotent within norm `< 1` of `1` in a normed ring equals `1`. -/
theorem eq_one_of_norm_sub_one_lt_one (he : IsIdempotentElem e) (h : ‖e - 1‖ < 1) : e = 1 :=
  he.eq_of_norm_sub_lt_one_of_commute .one (Commute.one_right e) h

/-- Symmetric form of `IsIdempotentElem.eq_one_of_norm_sub_one_lt_one` for `‖1 - e‖ < 1`. -/
theorem eq_one_of_norm_one_sub_lt_one (he : IsIdempotentElem e) (h : ‖1 - e‖ < 1) : e = 1 :=
  he.eq_one_of_norm_sub_one_lt_one (by rwa [norm_sub_rev] at h)

end NormedRing

end IsIdempotentElem
