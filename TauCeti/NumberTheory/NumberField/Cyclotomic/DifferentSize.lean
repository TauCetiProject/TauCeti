/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Archimedean size of a cyclotomic different generator

In a cyclotomic extension of an imaginary quadratic field, the different generator has
three factors: a correction of complex absolute value one, the cyclotomic derivative,
and the quadratic different generator. When the cyclotomic level grows without adding
new prime divisors, the placewise size divided by the level multiplier and the square
root of the quadratic discriminant is controlled by derivatives at the fixed base level.

The normalization and logarithmic budget are those of
`New.Parameters.exists_abs_log_le_and_apply_deltaE_eq` in
`grh/src/New/Derivatives/Field/ChosenPlaces.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open Polynomial NumberField.IsCMField

namespace NumberField.InfinitePlace

/-- At an infinite place of a CM field, the product of a norm-one correction, a cyclotomic
derivative at a primitive root of order `n * m`, and a square root of `-d` has size
`A * m * √d`. If `m` introduces no new primes, the logarithmic size of `A` is bounded by
the sum of absolute logarithms of the derivative sizes at level `n`. -/
theorem exists_pos_apply_cyclotomic_different_generator {E : Type*} [Field E] [CharZero E]
    [IsCMField E] [Algebra.IsIntegral ℚ E] (v : InfinitePlace E) {n m d : ℕ} {ζ u b : E}
    (hn : n ≠ 0) (hprimes : m.primeFactors ⊆ n.primeFactors)
    (hζ : IsPrimitiveRoot ζ (n * m)) (hu : u * complexConj E u = 1) (hb : b ^ 2 = -(d : E)) :
    ∃ A : ℝ, 0 < A ∧
      v (u * (cyclotomic (n * m) E).derivative.eval ζ * b) = A * m * √(d : ℝ) ∧
      |Real.log A| ≤ ∑ w ∈ primitiveRoots n ℂ, |Real.log ‖(cyclotomic n ℂ).derivative.eval w‖| := by
  obtain rfl | hm := eq_or_ne m 0
  · exact ⟨1, one_pos, by simp, by simp [Finset.sum_nonneg]⟩
  have hu' : v u * v u = 1 := by simpa using congrArg v hu
  have huv : v u = 1 := (sq_eq_sq₀ (apply_nonneg v u) zero_le_one).mp (by simpa [sq] using hu')
  have hbv : v b = √(d : ℝ) := by
    have hs : v b ^ 2 = (d : ℝ) := by
      rw [← map_pow, hb, ← norm_embedding_eq]
      simp
    rw [← hs, Real.sqrt_sq (apply_nonneg v b)]
  have hder : v ((cyclotomic (n * m) E).derivative.eval ζ) =
      ‖(cyclotomic (n * m) ℂ).derivative.eval (v.embedding ζ)‖ := by
    rw [← norm_embedding_eq, ← eval_map_apply, ← derivative_map, map_cyclotomic]
  obtain ⟨A, hA, heq, hlog⟩ := TauCeti.exists_pos_norm_eval_derivative_cyclotomic_mul
    (mul_ne_zero hn hm) hprimes (hζ.map_of_injective v.embedding.injective)
  refine ⟨A, hA, ?_, hlog⟩
  simp only [map_mul, huv, one_mul, hder, heq, hbv, mul_comm (m : ℝ) A]

end NumberField.InfinitePlace
