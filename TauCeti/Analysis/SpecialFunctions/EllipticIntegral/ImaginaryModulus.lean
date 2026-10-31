/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Gauss
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Trigonometric

/-!
# The imaginary-modulus transformation

The real integral with radicand `1 + c² sin² θ` reduces to the complete integral
`legendreK` at the real modulus `c / √(1 + c²)`. This modulus always has square less
than one, so the transformation evaluates a convergent integral without introducing a
complex-valued extension of `legendreK`.

The proof uses symmetry and homogeneity of the AGM integral. This is the real-integral
counterpart of Bastiaan J Braams' `Carlson.legendreK_imaginary_modulus` in
`Carlson/Elliptic/CompleteK.lean` of `bjbraams/lean-codes` (Apache-2.0), which instead
uses the symmetric integral `R_K`.

## References

* NIST *Digital Library of Mathematical Functions*, §19.7.5, <https://dlmf.nist.gov/19.7.E5>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Exercise 6.10-5.
-/

public section

open scoped Real

namespace TauCeti.Real

open _root_.Real

/-- The first-kind integral at an imaginary modulus, expressed entirely over the reals,
is integrable on every bounded interval. -/
theorem intervalIntegrable_one_add_mul_sin_sq_rpow_neg_half (c a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ ↦ (1 + c ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ))
      MeasureTheory.volume a b := by
  have hcont : Continuous (fun θ : ℝ ↦ (1 + c ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) := by
    apply Continuous.rpow_const (by fun_prop)
    intro θ
    left
    exact ne_of_gt (by positivity)
  exact hcont.intervalIntegrable a b

/-- **Imaginary-modulus transformation** (DLMF 19.7.5): the complete first-kind integral
with radicand `1 + c² sin² θ` is `K(c / √(1 + c²)) / √(1 + c²)`.
The integral converges for every real `c`. -/
theorem legendreK_imaginary_modulus (c : ℝ) :
    (∫ θ in (0 : ℝ)..π / 2, (1 + c ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) =
      legendreK (c / √(1 + c ^ 2)) / √(1 + c ^ 2) := by
  have hpos : 0 < 1 + c ^ 2 := by positivity
  have hs : 0 < √(1 + c ^ 2) := sqrt_pos.2 hpos
  have hsq : (√(1 + c ^ 2)) ^ 2 = 1 + c ^ 2 := sq_sqrt hpos.le
  have hk : (c / √(1 + c ^ 2)) ^ 2 < 1 := by
    rw [div_pow, hsq, div_lt_one hpos]
    linarith
  have hcomp : √(1 - (c / √(1 + c ^ 2)) ^ 2) = 1 / √(1 + c ^ 2) := by
    have heq : 1 - (c / √(1 + c ^ 2)) ^ 2 = (1 / √(1 + c ^ 2)) ^ 2 := by
      rw [div_pow, div_pow, hsq]
      field_simp
      ring
    rw [heq, sqrt_sq (by positivity)]
  have hint : (∫ θ in (0 : ℝ)..π / 2, (1 + c ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) =
      agmIntegral 1 √(1 + c ^ 2) := by
    rw [agmIntegral_def, ← integral_rpow_cos_sq_add_sin_sq_eq_integral_Ioi one_ne_zero hs.ne']
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [one_pow, one_mul, hsq]
    congr 1
    linear_combination -(cos_sq_add_sin_sq θ)
  rw [hint, legendreK_eq_agmIntegral hk, hcomp]
  have hscale := agmIntegral_mul_left √(1 + c ^ 2) 1 (1 / √(1 + c ^ 2))
  rw [mul_one, mul_one_div_cancel hs.ne', abs_of_pos hs, agmIntegral_comm] at hscale
  exact hscale

end TauCeti.Real
