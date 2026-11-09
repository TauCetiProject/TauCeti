/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Basic
public import TauCeti.NumberTheory.Height.FundamentalInequality
import Mathlib.Algebra.Order.AbsoluteValue.Int

/-!
# Local Liouville bounds for linear forms

For a nonzero value `z = ∑ i, a i * x i`, the local product of the sup norms of `a` and `x`
is at most `card ι ^ [K : ℚ] * H(a) * H(x)` times the local absolute value of `z`.
At an infinite place both local quantities are raised to its multiplicity. The same global
constant is necessary even at a finite place: the triangle inequalities at the infinite places
still contribute to the height.

The underlying height estimate bounds the height of `a i * x j / z` by the projective heights
of the two tuples. Unlike the height of `z` itself, this quotient is invariant under scaling
either tuple. These bounds compare the local factors of Plücker coordinates with their
projective height in height estimates for subspaces.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §7.5,
  the local value estimates used in Lemma 7.5.21.
-/

public section

open Finset Height

namespace Height

variable {K ι : Type*} [Field K] [AdmissibleAbsValues K] [Fintype ι]

/-- The height of a product of two coordinates divided by the value of the corresponding
linear form is at most `card ι ^ totalWeight K` times the product of the projective heights.
The denominator may vanish, with division interpreted as totalized division. -/
theorem mulHeight₁_mul_div_sum_mul_le (a x : ι → K) (i j : ι) :
    mulHeight₁ (a i * x j / ∑ k, a k * x k) ≤
      (Fintype.card ι : ℝ) ^ totalWeight K * (mulHeight a * mulHeight x) := by
  classical
  have : Nonempty ι := ⟨i⟩
  have hcard : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using one_le_mul_of_one_le_of_one_le (one_le_pow₀ hcard) (one_le_mulHeight x)
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using one_le_mul_of_one_le_of_one_le (one_le_pow₀ hcard) (one_le_mulHeight a)
  -- Append the value of the form to the multiplication table. Its local sup norm grows
  -- by at most `card ι` at archimedean places, and not at all at nonarchimedean places.
  let t : ι × ι → K := fun p ↦ a p.1 * x p.2
  let y : Option (ι × ι) → K := fun o ↦ o.elim (∑ k, a k * x k) t
  have ht : t ≠ 0 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp ha
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hx
    exact Function.ne_iff.mpr ⟨(k, l), mul_ne_zero hk hl⟩
  have hdiag (v : AbsoluteValue K ℝ) (k : ι) :
      v (a k * x k) ≤ ⨆ p, v (t p) :=
    Finite.le_ciSup (fun p ↦ v (t p)) (k, k)
  have hheight : mulHeight y ≤ (Fintype.card ι : ℝ) ^ totalWeight K * mulHeight t := by
    refine (mulHeight_le_of_forall_iSup_le ht y hcard (p := 1) ?_ ?_).trans_eq
      (by rw [pow_one])
    · intro v _
      simp only [pow_one]
      refine Real.iSup_le (fun o ↦ ?_)
        (mul_nonneg (Nat.cast_nonneg _) (Real.iSup_nonneg fun p ↦ v.nonneg (t p)))
      cases o with
      | none =>
        exact (v.sum_le _ _).trans (by
          simpa only [sum_const, card_univ, nsmul_eq_mul] using
            Finset.sum_le_sum (s := univ) fun k _ ↦ hdiag v k)
      | some p =>
        exact (Finite.le_ciSup (fun p ↦ v (t p)) p).trans
          (le_mul_of_one_le_left (Real.iSup_nonneg fun p ↦ v.nonneg _) hcard)
    · intro v hv
      simp only [pow_one]
      refine Real.iSup_le (fun o ↦ ?_) (Real.iSup_nonneg fun p ↦ v.nonneg _)
      cases o with
      | none => exact ((AdmissibleAbsValues.isNonarchimedean v hv).apply_sum_le_sup
          univ_nonempty).trans (Finset.sup'_le _ _ fun k _ ↦ hdiag v k)
      | some p => exact Finite.le_ciSup (fun p ↦ v (t p)) p
  calc
    _ ≤ mulHeight y := mulHeight₁_div_le_mulHeight y (some (i, j)) none
    _ ≤ _ := by simpa only [t, mulHeight_fun_mul_eq ha hx] using hheight

end Height

namespace NumberField

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι]

/-- **Local Liouville inequality for a linear form at an infinite place.** The product of
the two local sup norms, raised to the place's multiplicity, is bounded by the local value
of the form times the product of the projective heights and the triangle-inequality constant. -/
theorem InfinitePlace.iSup_mul_iSup_pow_mult_le (v : InfinitePlace K) (a x : ι → K)
    (hz : ∑ i, a i * x i ≠ 0) :
    ((⨆ i, v (a i)) * ⨆ i, v (x i)) ^ v.mult ≤
      (Fintype.card ι : ℝ) ^ Module.finrank ℚ K * (mulHeight a * mulHeight x) *
        v (∑ i, a i * x i) ^ v.mult := by
  classical
  have : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp at hz
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v (a i))
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j ↦ v (x j))
  have h := (v.max_apply_one_pow_mult_le_mulHeight₁
    (a i * x j / ∑ k, a k * x k)).trans (mulHeight₁_mul_div_sum_mul_le a x i j)
  rw [NumberField.totalWeight_eq_finrank] at h
  have hlocal : (v (a i) * v (x j) / v (∑ k, a k * x k)) ^ v.mult ≤
      (Fintype.card ι : ℝ) ^ Module.finrank ℚ K * (mulHeight a * mulHeight x) := by
    exact (pow_le_pow_left₀ (by positivity) (le_max_left _ _) _).trans (by
      simpa only [map_div₀, map_mul] using h)
  rw [← hi, ← hj]
  rw [div_pow] at hlocal
  exact (div_le_iff₀ (pow_pos (v.1.pos hz) _)).mp hlocal

/-- **Local Liouville inequality for a linear form at a finite place.** The constant
`card ι ^ [K : ℚ]` remains present, since the global height still uses the infinite places. -/
theorem FinitePlace.iSup_mul_iSup_le (v : FinitePlace K) (a x : ι → K)
    (hz : ∑ i, a i * x i ≠ 0) :
    (⨆ i, v (a i)) * ⨆ i, v (x i) ≤
      (Fintype.card ι : ℝ) ^ Module.finrank ℚ K * (mulHeight a * mulHeight x) *
        v (∑ i, a i * x i) := by
  classical
  have : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp at hz
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v (a i))
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j ↦ v (x j))
  have h := (le_max_left _ _).trans ((v.max_apply_one_le_mulHeight₁
    (a i * x j / ∑ k, a k * x k)).trans (mulHeight₁_mul_div_sum_mul_le a x i j))
  rw [NumberField.totalWeight_eq_finrank, map_div₀, map_mul] at h
  rw [← hi, ← hj]
  exact (div_le_iff₀ (v.1.pos hz)).mp h

end NumberField
