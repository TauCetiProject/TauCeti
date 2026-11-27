/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Analysis.Real.Sqrt
import TauCeti.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Archimedean sizes of cyclotomic different generators

In a quadratic cyclotomic compositum the absolute different can have a generator of the
form `u · Φ′(ζ) · η`, with `u` a root of unity and `η` the quadratic different generator.
When the level grows without introducing new prime factors, the size of this expression
at each complex embedding is the tower factor times `√|η²|`, up to a multiplicative
error controlled by the base cyclotomic polynomial alone.

The factorization of the size follows `New.Parameters.exists_abs_log_le_and_apply_deltaE_eq`
in `grh/src/New/Derivatives/Field/ChosenPlaces.lean` of lsernau/grh-lean (`72fead1`), using
`TauCeti.exists_pos_norm_eval_derivative_cyclotomic_mul` for the cyclotomic factor.
-/

public section

open Polynomial

namespace RingHom

/-- At a complex embedding, the norm of `u · Φ′_(n*m)(ζ) · η`, with `u` a root of unity
and `η² = D`, is `A · m · √|D|`. The positive factor `A` has absolute logarithm at most
`∑ |log ‖Φ′_n(w)‖|` over the primitive `n`th roots of unity. Here every prime divisor
of `m` divides `n`, and the image of `ζ` is primitive of order `n*m`. -/
theorem exists_pos_norm_apply_cyclotomic_different_eq {E : Type*} [Ring E] (σ : E →+* ℂ)
    {n m : ℕ} {D : ℤ} {u ζ η : E} (hn : n ≠ 0) (hsupport : m.primeFactors ⊆ n.primeFactors)
    (hu : IsOfFinOrder u) (hζ : IsPrimitiveRoot (σ ζ) (n * m)) (hη : η ^ 2 = (D : E)) :
    ∃ A : ℝ, 0 < A ∧
      ‖σ (u * (cyclotomic (n * m) E).derivative.eval ζ * η)‖ = A * m * √|(D : ℝ)| ∧
      |Real.log A| ≤ ∑ w ∈ primitiveRoots n ℂ,
        |Real.log ‖(cyclotomic n ℂ).derivative.eval w‖| := by
  obtain rfl | hm := eq_or_ne m 0
  · exact ⟨1, one_pos, by simp, by simp [Finset.sum_nonneg]⟩
  obtain ⟨A, hA, hder, hlog⟩ := TauCeti.exists_pos_norm_eval_derivative_cyclotomic_mul
    (mul_ne_zero hn hm) hsupport hζ
  obtain ⟨k, hk, huk⟩ := hu.exists_pow_eq_one
  have unorm : ‖σ u‖ = 1 := Complex.norm_eq_one_of_pow_eq_one
    (by simpa using congrArg σ huk) hk.ne'
  have ηnorm : ‖σ η‖ = √|(D : ℝ)| := by
    have hsquare : ‖σ η‖ ^ 2 = |(D : ℝ)| := by
      have h := congrArg (fun x : E ↦ ‖σ x‖) hη
      simpa only [map_pow, norm_pow, map_intCast, Complex.norm_intCast] using h
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      (hsquare.trans (Real.sq_sqrt (abs_nonneg _)).symm)
  refine ⟨A, hA, ?_, hlog⟩
  have hmap : σ ((cyclotomic (n * m) E).derivative.eval ζ) =
      (cyclotomic (n * m) ℂ).derivative.eval (σ ζ) := by
    rw [← eval_map_apply, ← derivative_map, map_cyclotomic]
  simp only [map_mul, norm_mul, unorm, one_mul, ηnorm, hmap, hder, mul_comm (m : ℝ) A]

end RingHom
