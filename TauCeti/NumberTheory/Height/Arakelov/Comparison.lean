/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Basic
public import TauCeti.NumberTheory.Height.ProjectiveTuple

/-!
# Comparison of Euclidean and sup heights

The relative Euclidean height `arakelovMulHeight` and the projective height `Height.mulHeight`
of a tuple over a number field `K` have the same local factors at the finite places. At an
infinite place one uses the Euclidean norm of the embedded tuple and the other its maximum norm,
and for a tuple indexed by `ι` these satisfy `max ≤ ℓ² ≤ √#ι · max`. Taking the product over the
places gives `H_K(x) ≤ arakelovMulHeight x ≤ √#ι ^ [K : ℚ] · H_K(x)` for the relative heights.
For a nonzero tuple the absolute Euclidean height `height2` is the `[K : ℚ]`-th root of
`arakelovMulHeight`, so `H(x) ≤ height2 x ≤ √#ι · H(x)`, where `H` is
`absoluteProjectiveTupleHeight`.

These comparisons transfer bounds between the two normalizations. For instance, a bound for the
sup height of the Plücker coordinates of a subspace bounds its Euclidean height, at the cost of a
power of the number of coordinates.

## Main results

* `TauCeti.mulHeight_le_arakelovMulHeight`: the sup height is at most the Arakelov height.
* `TauCeti.arakelovMulHeight_le_sqrt_natCard_pow_mul_mulHeight`: the Arakelov height is at most
  `√#ι ^ [K : ℚ]` times the sup height.
* `TauCeti.absoluteProjectiveTupleHeight_le_height2` and
  `TauCeti.height2_le_sqrt_natCard_mul_absoluteProjectiveTupleHeight`: the absolute forms.
* `TauCeti.logHeight_le_arakelovLogHeight` and
  `TauCeti.arakelovLogHeight_le_mul_log_natCard_add_logHeight`: the logarithmic forms.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §6.1, (6.1)–(6.4).
-/

public noncomputable section

open Height Module NumberField

namespace TauCeti

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]

-- The two local estimates below are the comparison of the sup and Euclidean norms on `ℂ^ι`,
-- stated directly for the embedded tuple and the place, as they enter the height formulas.

/-- At an infinite place, the maximum norm of an embedded tuple is at most its Euclidean
norm. -/
private theorem iSup_le_sqrt_sum_sq (w : InfinitePlace K) (y : ι → K) :
    letI := Fintype.ofFinite ι
    ⨆ i, w (y i) ≤ √(∑ i, ‖w.embedding (y i)‖ ^ 2) := by
  let _ := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  refine ciSup_le fun i ↦ ?_
  rw [← InfinitePlace.norm_embedding_eq]
  exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j ↦ ‖w.embedding (y j)‖ ^ 2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i))

/-- At an infinite place, the Euclidean norm of an embedded tuple is at most `√#ι` times its
maximum norm. -/
private theorem sqrt_sum_sq_le (w : InfinitePlace K) (y : ι → K) :
    letI := Fintype.ofFinite ι
    √(∑ i, ‖w.embedding (y i)‖ ^ 2) ≤ √(Nat.card ι) * ⨆ i, w (y i) := by
  let _ := Fintype.ofFinite ι
  have hM : 0 ≤ ⨆ i, w (y i) := Real.iSup_nonneg_of_nonnegHomClass w _
  rw [← Real.sqrt_sq hM, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc
    ∑ i, ‖w.embedding (y i)‖ ^ 2 ≤ ∑ _i : ι, (⨆ j, w (y j)) ^ 2 := by
      refine Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [InfinitePlace.norm_embedding_eq]
      exact Finite.le_ciSup_of_le i le_rfl
    _ = Nat.card ι * (⨆ j, w (y j)) ^ 2 := by
      simp [Nat.card_eq_fintype_card]

/-- The infinite local factor of `arakelovMulHeight` is a power of the Euclidean norm. -/
private theorem rpow_sum_sq_eq_sqrt_pow (w : InfinitePlace K) (y : ι → K) :
    letI := Fintype.ofFinite ι
    (∑ i, ‖w.embedding (y i)‖ ^ 2) ^ ((w.mult : ℝ) / 2) =
      √(∑ i, ‖w.embedding (y i)‖ ^ 2) ^ w.mult := by
  let _ := Fintype.ofFinite ι
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  congr 1
  ring

variable [NumberField K]

/-- The projective sup height of a tuple over a number field is at most its relative Euclidean
projective height. At the zero tuple both heights are one. -/
theorem mulHeight_le_arakelovMulHeight (y : ι → K) : mulHeight y ≤ arakelovMulHeight y := by
  let _ := Fintype.ofFinite ι
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [NumberField.mulHeight_eq hy, arakelovMulHeight_eq hy]
  refine mul_le_mul_of_nonneg_right ?_
    (finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v _)
  refine Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass w _) _)
    fun w _ ↦ ?_
  rw [rpow_sum_sq_eq_sqrt_pow]
  exact pow_le_pow_left₀ (Real.iSup_nonneg_of_nonnegHomClass w _) (iSup_le_sqrt_sum_sq w y) _

/-- The relative Euclidean projective height of a tuple over a number field `K` indexed by a
nonempty type `ι` is at most `√#ι ^ [K : ℚ]` times its projective sup height. The nonemptiness
is only needed at the zero tuple, where both heights are one. -/
theorem arakelovMulHeight_le_sqrt_natCard_pow_mul_mulHeight [Nonempty ι] (y : ι → K) :
    arakelovMulHeight y ≤ √(Nat.card ι) ^ finrank ℚ K * mulHeight y := by
  let _ := Fintype.ofFinite ι
  rcases eq_or_ne y 0 with rfl | hy
  · have hc : 1 ≤ √(Nat.card ι) :=
      Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr (Nat.card_pos (α := ι)))
    simpa using one_le_pow₀ hc
  rw [NumberField.mulHeight_eq hy, arakelovMulHeight_eq hy, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_
    (finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v _)
  rw [← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ ↦ by positivity) fun w _ ↦ ?_
  rw [rpow_sum_sq_eq_sqrt_pow, ← mul_pow]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_sum_sq_le w y) _

/-- The absolute sup height of a nonzero tuple over a number field is at most its absolute
Euclidean height. The zero tuple is excluded, since there `height2` is zero. -/
theorem absoluteProjectiveTupleHeight_le_height2 {y : ι → K} (hy : y ≠ 0) :
    absoluteProjectiveTupleHeight y ≤ height2 y := by
  have h := arakelovMulHeight_eq_height2 y
  rw [ite_eq_right hy] at h
  rw [absoluteProjectiveTupleHeight_eq, ← h, ← one_div]
  exact Real.rpow_le_rpow (mulHeight_pos y).le (mulHeight_le_arakelovMulHeight y)
    (by positivity)

/-- The absolute Euclidean height of a tuple over a number field indexed by `ι` is at most `√#ι`
times its absolute sup height. -/
theorem height2_le_sqrt_natCard_mul_absoluteProjectiveTupleHeight (y : ι → K) :
    height2 y ≤ √(Nat.card ι) * absoluteProjectiveTupleHeight y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [height2_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (absoluteProjectiveTupleHeight_pos _).le
  obtain ⟨i, -⟩ := Function.ne_iff.mp hy
  have : Nonempty ι := ⟨i⟩
  have h := arakelovMulHeight_eq_height2 y
  rw [ite_eq_right hy] at h
  have hD : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  rw [absoluteProjectiveTupleHeight_eq, ← h]
  calc
    arakelovMulHeight y ^ ((1 : ℝ) / finrank ℚ K) ≤
        (√(Nat.card ι) ^ finrank ℚ K * mulHeight y) ^ ((1 : ℝ) / finrank ℚ K) :=
      Real.rpow_le_rpow (arakelovMulHeight_nonneg y)
        (arakelovMulHeight_le_sqrt_natCard_pow_mul_mulHeight y) (by positivity)
    _ = √(Nat.card ι) * mulHeight y ^ (finrank ℚ K : ℝ)⁻¹ := by
      rw [Real.mul_rpow (by positivity) (mulHeight_pos y).le, ← Real.rpow_natCast,
        ← Real.rpow_mul (Real.sqrt_nonneg _), mul_one_div_cancel hD, Real.rpow_one, one_div]

/-- The logarithmic form of `mulHeight_le_arakelovMulHeight`. -/
theorem logHeight_le_arakelovLogHeight (y : ι → K) : logHeight y ≤ arakelovLogHeight y := by
  rw [logHeight_eq_log_mulHeight, arakelovLogHeight_eq_log_arakelovMulHeight]
  exact Real.log_le_log (mulHeight_pos y) (mulHeight_le_arakelovMulHeight y)

/-- The logarithmic form of `arakelovMulHeight_le_sqrt_natCard_pow_mul_mulHeight`: the relative
logarithmic Euclidean height exceeds the logarithmic sup height by at most
`[K : ℚ] / 2 · log #ι`. -/
theorem arakelovLogHeight_le_mul_log_natCard_add_logHeight (y : ι → K) :
    arakelovLogHeight y ≤ finrank ℚ K / 2 * Real.log (Nat.card ι) + logHeight y := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Subsingleton.elim y 0, Nat.card_of_isEmpty, Nat.cast_zero, Real.log_zero]
    simp
  have hc : 0 < √(Nat.card ι) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
  rw [arakelovLogHeight_eq_log_arakelovMulHeight]
  calc
    Real.log (arakelovMulHeight y) ≤ Real.log (√(Nat.card ι) ^ finrank ℚ K * mulHeight y) :=
      Real.log_le_log (arakelovMulHeight_pos y)
        (arakelovMulHeight_le_sqrt_natCard_pow_mul_mulHeight y)
    _ = finrank ℚ K / 2 * Real.log (Nat.card ι) + logHeight y := by
      rw [Real.log_mul (pow_pos hc _).ne' (mulHeight_pos y).ne', Real.log_pow,
        Real.log_sqrt (Nat.cast_nonneg _), logHeight_eq_log_mulHeight]
      ring

end TauCeti
