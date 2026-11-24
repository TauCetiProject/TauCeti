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

This file defines the lattice point `TauCeti.latticePoint j` of `EuclideanSpace ℝ ι` with integer
coordinates `j : ι → ℤ`. A closed ball of radius `R ≥ 0` about the origin contains finitely many
lattice points, and at most `(e (1 + √π R / √n))ⁿ` of them, where `n` is the cardinality of `ι`.
For `R` of order at least `√n` this is of order `(C R / √n)ⁿ`, like the volume of the ball, while
the packing bound for `1`-separated points only gives `(1 + 2 R)ⁿ`. Counts of this kind bound the
size of nets made of normalized integer points.

The proof uses an exponential weight. Each lattice point `latticePoint p` of the ball has
`1 ≤ exp (t (R² - ‖latticePoint p‖²))` for `t ≥ 0`. The sum of these weights over the integer
points of a box is `exp (t R²)` times the `n`-th power of a one-dimensional Gaussian sum, which
`Real.sum_exp_neg_mul_int_sq_le` bounds by `1 + √(π / t)`. The choice `t = n / R²` gives the
bound.

## Main definitions

* `TauCeti.latticePoint j`: the point of `EuclideanSpace ℝ ι` with integer coordinates `j`.

## Main results

* `TauCeti.finite_setOf_norm_latticePoint_le`: a closed ball contains finitely many lattice
  points.
* `TauCeti.card_le_of_forall_norm_latticePoint_le`: the bound `(e (1 + √π R / √n))ⁿ`.

## References

* M. Rudelson and R. Vershynin, *Smallest singular value of a random rectangular matrix*,
  Comm. Pure Appl. Math. 62 (2009), proof of Lemma 4.7, where a bound of this order is used.
-/

public section

open Finset Real

namespace TauCeti

/-- The point of `EuclideanSpace ℝ ι` with integer coordinates `j`. -/
noncomputable def latticePoint {ι : Type*} (j : ι → ℤ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ (j i : ℝ)

@[simp]
theorem latticePoint_apply {ι : Type*} (j : ι → ℤ) (i : ι) : latticePoint j i = j i :=
  (rfl)

theorem latticePoint_sub {ι : Type*} (j j' : ι → ℤ) :
    latticePoint (j - j') = latticePoint j - latticePoint j' := by
  ext i
  simp

/-- The lattice point with coordinates `j` is the integer combination `∑ i, j i • eᵢ` of the
standard basis vectors. -/
theorem latticePoint_eq_sum {ι : Type*} [Fintype ι] (j : ι → ℤ) :
    latticePoint j = ∑ i, (j i : ℝ) • EuclideanSpace.basisFun ι ℝ i := by
  classical
  ext k
  simp [EuclideanSpace.basisFun_apply, Pi.single_apply]

variable {ι : Type*} [Fintype ι]

/-- The coordinates of a lattice point of the closed ball of radius `R` about the origin lie in
`[-⌈R⌉₊, ⌈R⌉₊]`. -/
private theorem mem_Icc_of_norm_latticePoint_le {p : ι → ℤ} {R : ℝ}
    (hp : ‖latticePoint p‖ ≤ R) (i : ι) :
    p i ∈ Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊ := by
  have hi := (PiLp.norm_apply_le (latticePoint p) i).trans (hp.trans (Nat.le_ceil R))
  rw [latticePoint_apply, Real.norm_eq_abs, ← Int.cast_abs] at hi
  exact mem_Icc.2 (abs_le.1 (by exact_mod_cast hi))

/-- A closed ball about the origin of `EuclideanSpace ℝ ι` contains finitely many lattice
points. -/
theorem finite_setOf_norm_latticePoint_le (R : ℝ) :
    {p : ι → ℤ | ‖latticePoint p‖ ≤ R}.Finite :=
  (Set.Finite.pi' fun _ ↦ (Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊).finite_toSet).subset
    fun _ hp i ↦ mem_Icc_of_norm_latticePoint_le hp i

/-- A finite set of lattice points of the closed ball of radius `R ≥ 0` about the origin of
`EuclideanSpace ℝ ι` has at most `(e (1 + √π R / √n))ⁿ` elements, where `n` is the cardinality
of `ι`. -/
theorem card_le_of_forall_norm_latticePoint_le {s : Finset (ι → ℤ)} {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ p ∈ s, ‖latticePoint p‖ ≤ R) :
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
  set t : ℝ := n / R ^ 2 with ht_def
  have ht : 0 < t := by positivity
  have htR : t * R ^ 2 = n := div_mul_cancel₀ _ (pow_ne_zero 2 hR.ne')
  have hπt : π / t = (√π * R / √n) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt pi_pos.le, Real.sq_sqrt hn.le, ht_def]
    field_simp
  -- Each lattice point of the ball has weight `exp (t (R² - ‖p‖²)) ≥ 1`.
  have hweight : ∀ p ∈ s, 1 ≤ rexp (t * R ^ 2) * ∏ i, rexp (-t * (p i : ℝ) ^ 2) := by
    intro p hp
    have hsq : ∑ i, (p i : ℝ) ^ 2 ≤ R ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) (hs p hp) 2
      simpa [EuclideanSpace.real_norm_sq_eq] using h
    rw [← exp_sum, ← exp_add, ← mul_sum]
    exact one_le_exp (by nlinarith [mul_le_mul_of_nonneg_left hsq ht.le])
  have hsB : s ⊆ Fintype.piFinset fun _ ↦ Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊ := fun p hp ↦
    Fintype.mem_piFinset.2 (mem_Icc_of_norm_latticePoint_le (hs p hp))
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
      calc
        _ ≤ 1 + √(π / t) := sum_exp_neg_mul_int_sq_le ht _
        _ = 1 + √π * R / √n := by rw [hπt, Real.sqrt_sq (by positivity)]
    _ = (rexp 1 * (1 + √π * R / √n)) ^ n := by rw [htR, mul_pow, exp_one_pow]

end TauCeti
