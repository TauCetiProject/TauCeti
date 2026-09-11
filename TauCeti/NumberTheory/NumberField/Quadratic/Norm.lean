/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Basic
import Mathlib.NumberTheory.NumberField.Units.Basic
import TauCeti.RingTheory.Norm.Quadratic

/-!
# The field norm on a quadratic number field

For a quadratic number field `K = ℚ(√d)` presented by an algebraic integer `θ : 𝓞 K` generating
`K` over `ℚ` with `minpoly ℤ θ = X² - d`, this file computes the field norm `Algebra.norm ℚ` on
`K` in terms of the coordinates in the basis `1, θ`:

* `norm_gen_eq_neg_radicand`: the norm of the generator, `N(θ) = -d` (negative of the radicand);
* `norm_add_mul_gen`: in the coordinates `x = b + aθ` the norm is `N(b + aθ) = b² - d·a²`;
* `norm_pos_of_radicand_neg`: when `d < 0` — the imaginary quadratic case, where `K` is totally
  complex — the norm is strictly positive on every nonzero element;
* `radicand_pos_of_norm_eq_neg_one`: consequently a unit of norm `-1` forces `0 < d`;
* `exists_norm_eq_neg_one_of_sq_sub_mul_sq_eq_neg_one`: a solution of the negative Pell equation
  `b² - d a² = -1` supplies a unit of norm `-1`.

The positivity is a descent input for the genus theory of the multiquadratic roadmap: for a
norm-`±1` element `α` it upgrades `N(α) = ±1` to `N(α) = 1`, the hypothesis of Hilbert's
Theorem 90 used to realise a `2`-torsion class by an ambiguous ideal.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*.
-/

public section

open Polynomial NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The norm of the generator is the negative of the radicand:** `N(θ) = -d`. It is the constant
coefficient of the minimal polynomial `X² - d`, times the sign `(-1)^{[K:ℚ]} = +1`. -/
@[simp] theorem norm_gen_eq_neg_radicand (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.norm ℚ (θ : K) = -(d : ℚ) := by
  have hint : IsIntegral ℚ (θ : K) := θ.isIntegral_coe.tower_top
  have hgen' : (PowerBasis.ofAdjoinEqTop' hint hgen).gen = (θ : K) :=
    PowerBasis.ofAdjoinEqTop'_gen hint hgen
  have hdim : (PowerBasis.ofAdjoinEqTop' hint hgen).dim = 2 := by
    rw [← (PowerBasis.ofAdjoinEqTop' hint hgen).natDegree_minpoly, hgen',
      minpoly_rat_quadratic hmin, natDegree_X_pow_sub_C]
  rw [← hgen', Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, hgen',
    minpoly_rat_quadratic hmin]
  simp [coeff_sub, coeff_X_pow]

/-- **The norm in the basis `1, θ`:** `N(b + aθ) = b² - d·a²`. This is the generic quadratic norm
formula with `Tr(θ) = 0` and `N(θ) = -d`. The left-hand side uses the rat-cast normal form
`↑b + ↑a * θ` (`simp` rewrites `algebraMap ℚ K` to `↑` via `eq_ratCast`), so it is a valid `@[simp]`
normalization rule. -/
@[simp] theorem norm_add_mul_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (a b : ℚ) :
    Algebra.norm ℚ ((b : K) + (a : K) * (θ : K)) = b ^ 2 - (d : ℚ) * a ^ 2 := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨finrank_rat_eq_two hmin hgen⟩
  rw [← eq_ratCast (algebraMap ℚ K) b, ← eq_ratCast (algebraMap ℚ K) a,
    Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul, trace_gen_eq_zero hmin,
    norm_gen_eq_neg_radicand hmin hgen]
  ring

/-- **The norm is positive in the imaginary case.** When `d < 0` the field `K = ℚ(√d)` is totally
complex, and `N(b + aθ) = b² + |d|·a²`, so the norm is strictly positive on every nonzero element.
This is the sign input that turns a norm-`±1` element into a norm-`1` one for Hilbert 90. -/
theorem norm_pos_of_radicand_neg (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : d < 0) {x : K} (hx : x ≠ 0) :
    0 < Algebra.norm ℚ x := by
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_gen hmin hgen x
  simp only [eq_ratCast]
  rw [norm_add_mul_gen hmin hgen]
  have hdq : (d : ℚ) < 0 := by exact_mod_cast hd
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hx (by rw [h.1, h.2]; simp)
  rcases hab with ha | hb
  · nlinarith [mul_self_pos.mpr ha, sq_nonneg b, sq_nonneg a]
  · nlinarith [mul_self_pos.mpr hb, sq_nonneg a, sq_nonneg b]

/-- **A unit of norm `-1` only exists in the real case.** For `d < 0` the norm is positive on every
nonzero element (`norm_pos_of_radicand_neg`), and `d = 0` is excluded because the radicand is not a
square; so a unit of norm `-1` forces `0 < d`. -/
theorem radicand_pos_of_norm_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {u : (𝓞 K)ˣ}
    (hu : Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1) : 0 < d := by
  have hune : ((u : 𝓞 K) : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr u.ne_zero
  rcases lt_trichotomy d 0 with hd | hd | hd
  · have := norm_pos_of_radicand_neg hmin hgen hd hune
    rw [hu] at this
    norm_num at this
  · -- `d = 0` makes the radicand the square `0 * 0`.
    subst hd
    exact absurd ⟨0, by norm_num⟩ (not_isSquare_radicand hmin)
  · exact hd

/-- **A solution of the negative Pell equation gives a unit of norm `-1`.** If `b² - d a² = -1`
then `b + aθ` has norm `-1`, hence is a unit of `𝓞 K` (an algebraic integer is a unit exactly when
its norm is `±1`). This is a concrete source of units of norm `-1`: for `d = 2`, `a = b = 1`
gives the unit `1 + √2`. -/
theorem exists_norm_eq_neg_one_of_sq_sub_mul_sq_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {a b : ℤ} (hab : b ^ 2 - d * a ^ 2 = -1) :
    ∃ u : (𝓞 K)ˣ, Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1 := by
  set x : 𝓞 K := (b : 𝓞 K) + (a : 𝓞 K) * θ with hxdef
  have habq : ((b : ℤ) : ℚ) ^ 2 - ((d : ℤ) : ℚ) * ((a : ℤ) : ℚ) ^ 2 = -1 := by exact_mod_cast hab
  have hnorm : Algebra.norm ℚ ((x : K)) = -1 := by
    have hval : ((x : 𝓞 K) : K)
        = (((b : ℤ) : ℚ) : K) + (((a : ℤ) : ℚ) : K) * (θ : K) := by
      rw [hxdef]
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast,
        Rat.cast_intCast]
    rw [hval, norm_add_mul_gen hmin hgen, habq]
  have hunit : IsUnit x := by
    rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm, hnorm]
    norm_num
  exact ⟨hunit.unit, by rwa [IsUnit.unit_spec]⟩

end NumberField
