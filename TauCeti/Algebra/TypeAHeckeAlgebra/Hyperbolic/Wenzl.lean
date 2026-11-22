/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Wenzl
public import TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam.Analytic
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The hyperbolic parameter dictionary for Wenzl's Markov trace parameters

In `TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic`, at the Hecke parameter `q = exp (-θ)` and
rescaled braid generators `γ i = I * exp (-α) • T i`, the positive and negative stabilization
constants of a Markov trace with native projection parameter `η` agree (for `cosh α * cosh θ ≠ 0`)
if and only if

`η = (1 - tanh α * tanh θ) / 2` (`TauCeti.hyperbolicProjParam`),

while Wenzl's complementary projection convention `e_i^W = 1 - P_i`
(`TauCeti.BalancedProjectionAlgebra.wenzlHeckeEquiv`) assigns to the same Markov trace the
projection parameter

`η_W = 1 - η = (1 + tanh α * tanh θ) / 2` (`TauCeti.hyperbolicWenzlProjParam`).

This file establishes Wenzl's projection rule in hyperbolic parameters and the dictionary between
the hyperbolic parameters and Wenzl's discrete parameters `a_d(Q)` (`TauCeti.wenzlParam`) at
`Q = q ^ 2 = exp (-2 * θ)` along the **exceptional discrete lines** `α = k * θ + π * I / 2`
(`k ∈ ℤ \ {0}`): the native projection parameter is `a_(-k)(exp (-2 * θ))` and Wenzl's
projection parameter is `a_k(exp (-2 * θ))`, with common stabilization constant
`-sinh θ / sinh (k * θ)`. The root-of-unity specialization is in
`TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.RootOfUnity`.

## Main results

* `TauCeti.wenzlParam_neg_two_mul_hyperbolicHeckeParam_add_inv_sq` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_hyperbolic_wenzlProjection`:
  balanced-projection compatibility and Wenzl's projection rule in hyperbolic parameters.
* `TauCeti.hyperbolicProjParam_mul_add_pi_mul_I_div_two`,
  `TauCeti.hyperbolicWenzlProjParam_mul_add_pi_mul_I_div_two`, and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_line_eq_iff`: the exceptional
  discrete line dictionary `α = k * θ + π * I / 2`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5–6, 11.
* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett and A. Ocneanu, *A new
  polynomial invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-! ### Wenzl's projection convention in hyperbolic parameters -/

/-- When `cosh θ ≠ 0`, the Jones parameter `a_(-2)(exp (-2 * θ))` satisfies the balanced-projection
compatibility `τ * (q + q⁻¹) ^ 2 = 1` for `q = hyperbolicHeckeParam θ`. -/
theorem wenzlParam_neg_two_mul_hyperbolicHeckeParam_add_inv_sq {θ : ℂ} (hθ : cosh θ ≠ 0) :
    wenzlParam (-2) (exp (-2 * θ)) *
      ((hyperbolicHeckeParam θ : ℂ) + ↑(hyperbolicHeckeParam θ)⁻¹) ^ 2 = 1 := by
  have hsum : (hyperbolicHeckeParam θ : ℂ) + ↑(hyperbolicHeckeParam θ)⁻¹ = 2 * cosh θ := by
    rw [val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, two_cosh, add_comm]
  have htwo : (2 : ℂ) ^ 2 = 4 := by norm_num
  rw [wenzlParam_neg_two_exp_neg_two_mul, hsum, mul_pow, htwo]
  exact inv_mul_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hθ))

namespace InfiniteTypeAHeckeAlgebra

variable {α θ z η ηW : ℂ} {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ) →ₗ[ℂ] ℂ}

/-- **Wenzl's projection rule in hyperbolic parameters.** When `cosh θ ≠ 0` and
`z = exp (-θ) * (1 - η_W) - exp θ * η_W`, appending Wenzl's projection
`(1 + exp (-2 * θ))⁻¹ • (exp (-2 * θ) - exp (-θ) • T n)` to `x` in the stage on `n + 1` strands
multiplies a Markov trace `τ` by `η_W`. -/
theorem IsMarkovTrace.map_mul_hyperbolic_wenzlProjection (hτ : IsMarkovTrace z τ)
    (hθ : cosh θ ≠ 0) (hz : z = exp (-θ) * (1 - ηW) - exp θ * ηW) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ)}
    (hx : x ∈ stage ℂ (hyperbolicHeckeParam θ) (n + 1)) :
    τ (x * (1 + exp (-2 * θ))⁻¹ • (algebraMap ℂ _ (exp (-2 * θ)) - exp (-θ) • T _ n)) =
      ηW * τ x := by
  have hq2 : exp (-θ) ^ 2 = exp (-2 * θ) := by rw [← exp_natCast_mul]; ring_nf
  have hu0 : 1 + exp (-2 * θ) ≠ 0 := by
    rw [neg_mul, ← mul_neg, one_add_exp_two_mul, cosh_neg]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hθ) (exp_ne_zero _)
  have h := hτ.map_mul_wenzlProjection (Units.mk0 (1 + exp (-2 * θ)) hu0)
    (by rw [Units.val_mk0, val_hyperbolicHeckeParam, hq2]) (η := 1 - ηW)
    (by rw [val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, sub_sub_cancel, hz]) hx
  simpa only [Units.val_inv_eq_inv_val, Units.val_mk0, val_hyperbolicHeckeParam, hq2,
    sub_sub_cancel] using h

end InfiniteTypeAHeckeAlgebra

/-! ### Exceptional discrete line states `α = k * θ + π * I / 2` -/

/-- **Native projection parameter on the exceptional line `α = k * θ + π * I / 2`.** Whenever
`cosh θ ≠ 0` and `sinh (k * θ) ≠ 0`, `hyperbolicProjParam (k * θ + π * I / 2) θ` equals
`a_(-k)(exp (-2 * θ))`. -/
theorem hyperbolicProjParam_mul_add_pi_mul_I_div_two {k : ℤ} {θ : ℂ} (hθ : cosh θ ≠ 0)
    (hk : sinh (k * θ) ≠ 0) :
    hyperbolicProjParam (k * θ + π * I / 2) θ = wenzlParam (-k) (exp (-2 * θ)) := by
  have hk_neg : sinh ((-k : ℤ) * θ) ≠ 0 := by simpa [Int.cast_neg, neg_mul, sinh_neg] using hk
  -- Normalize the shifted exponent `(-k + 1) * θ` as `-(k * θ - θ)` for `sinh_neg` and `sinh_sub`.
  have harg : (-(k : ℂ) + 1) * θ = -(k * θ - θ) := by ring
  rw [hyperbolicProjParam_def, tanh_add_pi_mul_I_div_two, tanh_eq_sinh_div_cosh,
    wenzlParam_exp_neg_two_mul (-k) hθ hk_neg, Int.cast_neg, neg_mul, sinh_neg, harg, sinh_neg,
    sinh_sub]
  field_simp [hθ, hk]

/-- **Wenzl projection parameter on the exceptional line `α = k * θ + π * I / 2`.** Whenever
`cosh θ ≠ 0` and `sinh (k * θ) ≠ 0`, `hyperbolicWenzlProjParam (k * θ + π * I / 2) θ` equals
`a_k(exp (-2 * θ))`. -/
theorem hyperbolicWenzlProjParam_mul_add_pi_mul_I_div_two {k : ℤ} {θ : ℂ} (hθ : cosh θ ≠ 0)
    (hk : sinh (k * θ) ≠ 0) :
    hyperbolicWenzlProjParam (k * θ + π * I / 2) θ = wenzlParam k (exp (-2 * θ)) := by
  have hθ' : cosh (-θ) ≠ 0 := by simpa using hθ
  have hk' : sinh ((-k : ℤ) * (-θ)) ≠ 0 := by simpa using hk
  have h := hyperbolicProjParam_mul_add_pi_mul_I_div_two hθ' hk'
  rw [Int.cast_neg, neg_mul_neg, hyperbolicProjParam_neg_right, neg_neg, mul_neg, exp_neg,
    wenzlParam_inv] at h
  exact h

/-- **Common stabilization constant on the exceptional line.** At `α = k * θ + π * I / 2` and
`η = a_(-k)(exp (-2 * θ))`, the common stabilization constant is `-sinh θ / sinh (k * θ)`. -/
theorem hyperbolicStabilization_mul_add_pi_mul_I_div_two {k : ℤ} {θ : ℂ} (hθ : cosh θ ≠ 0)
    (hk : sinh (k * θ) ≠ 0) :
    hyperbolicStabilization (k * θ + π * I / 2) θ (wenzlParam (-k) (exp (-2 * θ))) =
      -sinh θ / sinh (k * θ) := by
  rw [hyperbolicStabilization_eq_neg_I_mul_sinh_div_cosh
    (cosh_add_pi_mul_I_div_two_ne_zero.2 hk) hθ
    (hyperbolicProjParam_mul_add_pi_mul_I_div_two hθ hk).symm, cosh_add_pi_mul_I_div_two]
  field_simp [I_ne_zero]

/-- **Real-`θ` exceptional line parameter (`k ≠ 0`, `θ ≠ 0`).** At real `θ ≠ 0` and integer `k ≠ 0`,
`hyperbolicProjParam (k * θ + π * I / 2) θ = a_(-k)(exp (-2 * θ))`. -/
theorem hyperbolicProjParam_ofReal_mul_add_pi_mul_I_div_two {k : ℤ} (hk : k ≠ 0) {θ : ℝ}
    (hθ : θ ≠ 0) :
    hyperbolicProjParam (k * (θ : ℂ) + π * I / 2) θ =
      ↑(wenzlParam (-k) (Real.exp (-2 * θ))) := by
  have hs : sinh ((k : ℂ) * θ) ≠ 0 := by
    simpa using sinh_ofReal_ne_zero.2 (mul_ne_zero (Int.cast_ne_zero.2 hk) hθ)
  rw [hyperbolicProjParam_mul_add_pi_mul_I_div_two (cosh_ofReal_ne_zero θ) hs]
  symm
  simpa using map_wenzlParam Complex.ofRealHom (-k) (Real.exp (-2 * θ))

/-- At real `θ ≠ 0` and integer `k ≠ 0`, Wenzl's parameter on `α = k * θ + π * I / 2` is
`a_k(exp (-2 * θ))`. -/
theorem hyperbolicWenzlProjParam_ofReal_mul_add_pi_mul_I_div_two {k : ℤ} (hk : k ≠ 0) {θ : ℝ}
    (hθ : θ ≠ 0) :
    hyperbolicWenzlProjParam (k * (θ : ℂ) + π * I / 2) θ =
      ↑(wenzlParam k (Real.exp (-2 * θ))) := by
  have h := hyperbolicProjParam_ofReal_mul_add_pi_mul_I_div_two (neg_ne_zero.2 hk)
    (neg_ne_zero.2 hθ)
  rw [Int.cast_neg, ofReal_neg, neg_mul_neg, hyperbolicProjParam_neg_right, neg_neg, mul_neg,
    Real.exp_neg, wenzlParam_inv] at h
  exact h

namespace InfiniteTypeAHeckeAlgebra

variable {k : ℤ} {θ z η ηW : ℂ}
  {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ) →ₗ[ℂ] ℂ}

/-- **Markov trace characterization on the exceptional line (native convention).** For
`cosh θ ≠ 0` and `sinh (k * θ) ≠ 0`, a Markov trace with native projection parameter `η` has equal
stabilization constants at `α = k * θ + π * I / 2` if and only if `η = a_(-k)(exp (-2 * θ))`. -/
theorem IsMarkovTrace.map_hyperbolicGen_line_eq_iff (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-θ) * η - exp θ * (1 - η)) (hθ : cosh θ ≠ 0) (hk : sinh (k * θ) ≠ 0)
    (n : ℕ) :
    τ (hyperbolicGen (k * θ + π * I / 2) θ n) =
        τ ↑(hyperbolicGen (k * θ + π * I / 2) θ n)⁻¹ ↔
      η = wenzlParam (-k) (exp (-2 * θ)) := by
  rw [hτ.map_hyperbolicGen_eq_map_inv_iff hz (cosh_add_pi_mul_I_div_two_ne_zero.2 hk) hθ n,
    hyperbolicProjParam_mul_add_pi_mul_I_div_two hθ hk]

/-- **Markov trace characterization on the exceptional line (Wenzl convention).** For `cosh θ ≠ 0`
and `sinh (k * θ) ≠ 0`, a Markov trace with Wenzl projection parameter `η_W` has equal
stabilization constants at `α = k * θ + π * I / 2` if and only if `η_W = a_k(exp (-2 * θ))`. -/
theorem IsMarkovTrace.map_hyperbolicGen_line_eq_iff_wenzl (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-θ) * (1 - ηW) - exp θ * ηW) (hθ : cosh θ ≠ 0) (hk : sinh (k * θ) ≠ 0)
    (n : ℕ) :
    τ (hyperbolicGen (k * θ + π * I / 2) θ n) =
        τ ↑(hyperbolicGen (k * θ + π * I / 2) θ n)⁻¹ ↔
      ηW = wenzlParam k (exp (-2 * θ)) := by
  rw [hτ.map_hyperbolicGen_eq_map_inv_iff_wenzl hz (cosh_add_pi_mul_I_div_two_ne_zero.2 hk) hθ n,
    hyperbolicWenzlProjParam_mul_add_pi_mul_I_div_two hθ hk]

/-- Precomposing with `complementEquiv` on the exceptional line `α = k * θ + π * I / 2` gives the
complementary parameter `a_k(exp (-2 * θ))`. -/
theorem IsMarkovTrace.map_complementEquiv_hyperbolicGen_line_eq_iff (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-θ) * η - exp θ * (1 - η)) (hθ : cosh θ ≠ 0) (hk : sinh (k * θ) ≠ 0)
    (n : ℕ) :
    τ (complementEquiv _ (hyperbolicGen (k * θ + π * I / 2) θ n)) =
        τ (complementEquiv _ ↑(hyperbolicGen (k * θ + π * I / 2) θ n)⁻¹) ↔
      η = wenzlParam k (exp (-2 * θ)) := by
  rw [hτ.map_complementEquiv_hyperbolicGen_eq_iff hz (cosh_add_pi_mul_I_div_two_ne_zero.2 hk) hθ n,
    hyperbolicWenzlProjParam_mul_add_pi_mul_I_div_two hθ hk]

end InfiniteTypeAHeckeAlgebra

end TauCeti
