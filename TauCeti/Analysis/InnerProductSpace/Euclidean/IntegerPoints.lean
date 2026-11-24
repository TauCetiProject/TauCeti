/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Gaussian.LatticeSum

/-!
# Integer points in Euclidean balls

A closed ball of radius `R ≥ 0` about the origin of `EuclideanSpace ℝ ι` contains finitely many
integer points, and at most `(e (1 + √π R / √n))ⁿ` of them, where `n` is the cardinality of `ι`.
For `R` of order at least `√n` this is of order `(C R / √n)ⁿ`, like the volume of the ball, while
the packing bound for `1`-separated points only gives `(1 + 2 R)ⁿ`. Counts of this kind bound the
size of nets made of normalized integer points.

The proof uses an exponential weight. Each integer point `p` of the ball has
`1 ≤ exp (t (R² - ‖p‖²))` for `t ≥ 0`. The sum of these weights over the integer points of a box
is `exp (t R²)` times the `n`-th power of a one-dimensional Gaussian lattice sum, which
`Real.gaussianLatticeSum_zero_left_le` bounds by `1 + √(π / t)`. The choice `t = n / R²` gives the
bound.

## Main results

* `TauCeti.finite_setOf_norm_toLp_intCast_le`: a closed ball contains finitely many integer
  points.
* `TauCeti.card_le_of_forall_norm_toLp_intCast_le`: the bound `(e (1 + √π R / √n))ⁿ`.

## References

* M. Rudelson and R. Vershynin, *Smallest singular value of a random rectangular matrix*,
  Comm. Pure Appl. Math. 62 (2009), proof of Lemma 4.7, where a bound of this order is used.
-/

public section

open Finset Real

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The coordinates of an integer point of the closed ball of radius `R` about the origin lie in
`[-⌈R⌉₊, ⌈R⌉₊]`. -/
private theorem mem_Icc_of_norm_toLp_intCast_le {p : ι → ℤ} {R : ℝ}
    (hp : ‖WithLp.toLp 2 (fun i ↦ (p i : ℝ))‖ ≤ R) (i : ι) :
    p i ∈ Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊ := by
  have hi := (PiLp.norm_apply_le (WithLp.toLp 2 fun i ↦ (p i : ℝ)) i).trans
    (hp.trans (Nat.le_ceil R))
  rw [PiLp.toLp_apply, Real.norm_eq_abs, ← Int.cast_abs] at hi
  exact mem_Icc.2 (abs_le.1 (by exact_mod_cast hi))

/-- A closed ball about the origin of `EuclideanSpace ℝ ι` contains finitely many integer
points. -/
theorem finite_setOf_norm_toLp_intCast_le (R : ℝ) :
    {p : ι → ℤ | ‖WithLp.toLp 2 (fun i ↦ (p i : ℝ))‖ ≤ R}.Finite :=
  (Set.Finite.pi' fun _ ↦ (Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊).finite_toSet).subset
    fun _ hp i ↦ mem_Icc_of_norm_toLp_intCast_le hp i

/-- The one-dimensional Gaussian sums over integers `|k| ≤ M` with weight `exp (-(n / R²) k²)`
are at most `1 + √π R / √n`. -/
private theorem sum_Icc_exp_neg_mul_sq_le {n R : ℝ} (hn : 0 < n) (hR : 0 < R) (M : ℕ) :
    ∑ k ∈ Icc (-(M : ℤ)) M, rexp (-(n / R ^ 2) * (k : ℝ) ^ 2) ≤ 1 + √π * R / √n := by
  have hσ : 0 < R / √(2 * n) := by positivity
  have hsq : (R / √(2 * n)) ^ 2 = R ^ 2 / (2 * n) := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  calc
    _ = ∑ k ∈ Icc (-(M : ℤ)) M, rexp (-((k : ℝ) - 0) ^ 2 / (2 * (R / √(2 * n)) ^ 2)) := by
      refine sum_congr rfl fun k _ ↦ ?_
      rw [sub_zero, hsq]
      congr 1
      field_simp
    _ ≤ gaussianLatticeSum 0 (R / √(2 * n)) :=
      sum_le_hasSum _ (fun _ _ ↦ (exp_pos _).le) (hasSum_gaussianLatticeSum 0 hσ.ne')
    _ ≤ 1 + √(2 * π) * |R / √(2 * n)| := gaussianLatticeSum_zero_left_le _
    _ = 1 + √π * R / √n := by
      rw [abs_of_pos hσ, Real.sqrt_mul zero_le_two, Real.sqrt_mul zero_le_two]
      field_simp

/-- A finite set of integer points of the closed ball of radius `R ≥ 0` about the origin of
`EuclideanSpace ℝ ι` has at most `(e (1 + √π R / √n))ⁿ` elements, where `n` is the cardinality
of `ι`. -/
theorem card_le_of_forall_norm_toLp_intCast_le {s : Finset (ι → ℤ)} {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ p ∈ s, ‖WithLp.toLp 2 (fun i ↦ (p i : ℝ))‖ ≤ R) :
    (s.card : ℝ) ≤ (rexp 1 * (1 + √π * R / √(Fintype.card ι))) ^ Fintype.card ι := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simpa using card_le_one_of_subsingleton s
  rcases hR.eq_or_lt with rfl | hR
  · -- Only the origin lies in the ball of radius zero.
    have hs0 : s ⊆ {0} := fun p hp ↦ by
      have h := congrArg (fun x : EuclideanSpace ℝ ι ↦ fun i ↦ x i) (norm_le_zero_iff.1 (hs p hp))
      simpa [funext_iff] using h
    calc
      (s.card : ℝ) ≤ 1 := by exact_mod_cast (card_le_card hs0).trans (card_singleton _).le
      _ ≤ _ := by simp
  set n := Fintype.card ι
  have hn : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  set t : ℝ := n / R ^ 2
  have ht : 0 ≤ t := by positivity
  have htR : t * R ^ 2 = n := div_mul_cancel₀ _ (pow_ne_zero 2 hR.ne')
  -- Each integer point of the ball has weight `exp (t (R² - ‖p‖²)) ≥ 1`.
  have hweight : ∀ p ∈ s, 1 ≤ rexp (t * R ^ 2) * ∏ i, rexp (-t * (p i : ℝ) ^ 2) := by
    intro p hp
    have hsq : ∑ i, (p i : ℝ) ^ 2 ≤ R ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) (hs p hp) 2
      simpa [EuclideanSpace.real_norm_sq_eq] using h
    rw [← exp_sum, ← exp_add, ← mul_sum]
    exact one_le_exp (by nlinarith [mul_le_mul_of_nonneg_left hsq ht])
  have hsB : s ⊆ Fintype.piFinset fun _ ↦ Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊ := fun p hp ↦
    Fintype.mem_piFinset.2 (mem_Icc_of_norm_toLp_intCast_le (hs p hp))
  calc
    (s.card : ℝ) = ∑ _p ∈ s, (1 : ℝ) := by simp
    _ ≤ ∑ p ∈ s, rexp (t * R ^ 2) * ∏ i, rexp (-t * (p i : ℝ) ^ 2) := sum_le_sum hweight
    _ ≤ ∑ p ∈ Fintype.piFinset fun _ ↦ Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊,
          rexp (t * R ^ 2) * ∏ i, rexp (-t * (p i : ℝ) ^ 2) :=
      sum_le_sum_of_subset_of_nonneg hsB fun _ _ _ ↦ by positivity
    _ = rexp (t * R ^ 2) *
        (∑ k ∈ Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊, rexp (-t * (k : ℝ) ^ 2)) ^ n := by
      have h := sum_prod_piFinset (Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊)
        fun (_ : ι) (k : ℤ) ↦ rexp (-t * (k : ℝ) ^ 2)
      rw [← mul_sum, h, prod_const, card_univ]
    _ ≤ rexp (t * R ^ 2) * (1 + √π * R / √n) ^ n := by
      gcongr
      exact sum_Icc_exp_neg_mul_sq_le hn hR _
    _ = (rexp 1 * (1 + √π * R / √n)) ^ n := by rw [htR, mul_pow, exp_one_pow]

end TauCeti
