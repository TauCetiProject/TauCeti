/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam.Analytic
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Tactic.FieldSimp

/-!
# The exceptional discrete line dictionary for hyperbolic Markov traces

In `TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic`, at the Hecke parameter `q = exp (-θ)` and
rescaled braid generators `γ i = I * exp (-α) • T i`, the positive and negative stabilization
constants of a Markov trace with native projection parameter `η` agree (for `cosh α * cosh θ ≠ 0`)
if and only if

`η = (1 - tanh α * tanh θ) / 2` (`TauCeti.hyperbolicProjParam`),

while Wenzl's complementary projection convention assigns

`η_W = 1 - η = (1 + tanh α * tanh θ) / 2` (`TauCeti.hyperbolicWenzlProjParam`).

This file establishes the dictionary between the hyperbolic parameters and Wenzl's discrete
parameters `a_d(Q)` (`TauCeti.wenzlParam`) at `Q = q ^ 2 = exp (-2 * θ)` along the
**exceptional discrete lines** `α = k * θ + π * I / 2` (`k ∈ ℤ \ {0}`): the native projection
parameter is `a_(-k)(exp (-2 * θ))` and Wenzl's projection parameter is `a_k(exp (-2 * θ))`, with
common stabilization constant `-sinh θ / sinh (k * θ)`. The root-of-unity specialization is in
`TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.RootOfUnity`.

## Main results

* `TauCeti.hyperbolicProjParam_mul_add_pi_mul_I_div_two`,
  `TauCeti.hyperbolicWenzlProjParam_mul_add_pi_mul_I_div_two`,
  `TauCeti.hyperbolicStabilization_mul_add_pi_mul_I_div_two`,
  `TauCeti.hyperbolicProjParam_ofReal_mul_add_pi_mul_I_div_two`, and
  `TauCeti.hyperbolicWenzlProjParam_ofReal_mul_add_pi_mul_I_div_two`: exceptional discrete line
  parameter evaluations on `α = k * θ + π * I / 2`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_line_eq_iff`,
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_line_eq_iff_wenzl`, and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_complementEquiv_hyperbolicGen_line_eq_iff`:
  the Markov trace characterizations along the exceptional discrete lines.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5–6, 11.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-- **Native projection parameter on the exceptional line `α = k * θ + π * I / 2`.** Whenever
`cosh θ ≠ 0` and `sinh (k * θ) ≠ 0`, `hyperbolicProjParam (k * θ + π * I / 2) θ` equals
`a_(-k)(exp (-2 * θ))`. -/
theorem hyperbolicProjParam_mul_add_pi_mul_I_div_two {k : ℤ} {θ : ℂ} (hθ : cosh θ ≠ 0)
    (hk : sinh (k * θ) ≠ 0) :
    hyperbolicProjParam (k * θ + π * I / 2) θ = wenzlParam (-k) (exp (-2 * θ)) := by
  have hk_neg : sinh ((-k : ℤ) * θ) ≠ 0 := by simpa [Int.cast_neg, neg_mul, sinh_neg] using hk
  rw [hyperbolicProjParam_def, tanh_add_pi_mul_I_div_two, tanh_eq_sinh_div_cosh,
    wenzlParam_exp_neg_two_mul (-k) hθ hk_neg]
  simp only [Int.cast_neg, neg_mul, add_mul, one_mul, sinh_add, cosh_neg, sinh_neg]
  field_simp [hθ, hk]
  ring

/-- **Wenzl projection parameter on the exceptional line `α = k * θ + π * I / 2`.** Whenever
`cosh θ ≠ 0` and `sinh (k * θ) ≠ 0`, `hyperbolicWenzlProjParam (k * θ + π * I / 2) θ` equals
`a_k(exp (-2 * θ))`. -/
theorem hyperbolicWenzlProjParam_mul_add_pi_mul_I_div_two {k : ℤ} {θ : ℂ} (hθ : cosh θ ≠ 0)
    (hk : sinh (k * θ) ≠ 0) :
    hyperbolicWenzlProjParam (k * θ + π * I / 2) θ = wenzlParam k (exp (-2 * θ)) := by
  have hθ' : cosh (-θ) ≠ 0 := by simpa using hθ
  have hk' : sinh ((-k : ℤ) * (-θ)) ≠ 0 := by simpa using hk
  simpa [mul_neg] using hyperbolicProjParam_mul_add_pi_mul_I_div_two hθ' hk'

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
  rw [hyperbolicProjParam_mul_add_pi_mul_I_div_two (cosh_ofReal_ne_zero θ)
    (sinh_intCast_mul_ofReal_ne_zero hk hθ)]
  symm
  simpa using map_wenzlParam Complex.ofRealHom (-k) (Real.exp (-2 * θ))

/-- At real `θ ≠ 0` and integer `k ≠ 0`, Wenzl's parameter on `α = k * θ + π * I / 2` is
`a_k(exp (-2 * θ))`. -/
theorem hyperbolicWenzlProjParam_ofReal_mul_add_pi_mul_I_div_two {k : ℤ} (hk : k ≠ 0) {θ : ℝ}
    (hθ : θ ≠ 0) :
    hyperbolicWenzlProjParam (k * (θ : ℂ) + π * I / 2) θ =
      ↑(wenzlParam k (Real.exp (-2 * θ))) := by
  simpa [mul_neg] using
    hyperbolicProjParam_ofReal_mul_add_pi_mul_I_div_two (neg_ne_zero.2 hk) (neg_ne_zero.2 hθ)

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
