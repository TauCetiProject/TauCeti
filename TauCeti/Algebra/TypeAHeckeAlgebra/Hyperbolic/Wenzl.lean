/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Wenzl
public import TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Real
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

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

Building on the pure real family in `TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Real`, this file
establishes the dictionary between these hyperbolic parameters and Wenzl's discrete parameters
`a_d(Q)` (`TauCeti.wenzlParam`) at `Q = q ^ 2 = exp (-2 * θ)` across all three regimes:

1. **The positive-real family** (`α, θ ∈ ℝ`, `Q = exp (-2 * θ) > 0`): the closure of the range
   `α ↦ realHyperbolicProjParam α θ` is characterized by the quadratic inequality
   `(4 * cosh θ ^ 2)⁻¹ ≤ η * (1 - η)`, with equality on the endpoints and Jones parameter
   `a_(-2)(Q) → 0` as `θ → ±∞`.
2. **The exceptional discrete lines** (`α = k * θ + π * I / 2`, `k ∈ ℤ \ {0}`): the native
   projection parameter is `a_(-k)(exp (-2 * θ))` and Wenzl's projection parameter is
   `a_k(exp (-2 * θ))`, with common stabilization constant `-sinh θ / sinh (k * θ)`.
3. **The root-of-unity exceptional points** (`θ = π * I / l`, `α = (k / l + 1 / 2) * π * I`,
   `l ≥ 3`, `0 < k < l`, `Q = exp (-2 * π * I / l)`): direct evaluation via
   `tanh α = -I * cot (k * π / l)` and `tanh θ = I * tan (π / l)` gives native parameter
   `a_(-k)(Q)` and Wenzl parameter `a_k(Q)`. Replacing `k` by `l - k` exchanges the two projection
   conventions, `k = m` at `l = 2 * m` gives `1 / 2`, and `k ∈ {1, l - 1}` (all of `l = 3`) gives
   scalar endpoints `{0, 1}` whereas `2 ≤ k ≤ l - 2` (`l ≥ 4`) lies strictly in `(0, 1)`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_hyperbolic_wenzlProjection` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_eq_map_inv_iff_wenzl`:
  Wenzl's projection rule and equal stabilization constants in hyperbolic parameters.
* `TauCeti.inv_four_mul_cosh_sq_eq_mul_one_sub_iff`,
  `TauCeti.inv_four_mul_cosh_sq_le_mul_one_sub_iff`,
  `TauCeti.inv_four_mul_cosh_sq_lt_mul_one_sub_iff`, and
  `TauCeti.tendsto_wenzlParam_neg_two_real_exp_neg_two_mul_atTop`: the quadratic boundary relation
  `τ = η * (1 - η)` on the real hyperbolic family and scalar limit of the Jones parameter as
  `θ → ±∞`.
* `TauCeti.hyperbolicProjParam_mul_add_pi_mul_I_div_two`,
  `TauCeti.hyperbolicWenzlProjParam_mul_add_pi_mul_I_div_two`, and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_line_eq_iff`: the exceptional
  discrete line dictionary `α = k * θ + π * I / 2`.
* `TauCeti.hyperbolicProjParam_rootOfUnity`, `TauCeti.hyperbolicWenzlProjParam_rootOfUnity`,
  `TauCeti.hyperbolicProjParam_rootOfUnity_sub`, `TauCeti.hyperbolicProjParam_rootOfUnity_middle`,
  and `TauCeti.exists_mem_Ioo_hyperbolicProjParam_rootOfUnity_iff`: the root-of-unity exceptional
  points across `1 ≤ k ≤ l - 1`, complementary states, middle value, and separation of scalar
  endpoints from `(0, 1)` interior parameters.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5–6, 11.
* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett and A. Ocneanu, *A new
  polynomial invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246.
-/

public section

open Complex
open scoped Real Topology

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

/-- **Equal stabilization constants in Wenzl's projection convention.** For `cosh α * cosh θ ≠ 0`
and Wenzl projection parameter `η_W` (`z = exp (-θ) * (1 - η_W) - exp θ * η_W`),
`τ (γ n) = τ (γ n⁻¹)` if and only if `η_W = hyperbolicWenzlProjParam α θ`. -/
theorem IsMarkovTrace.map_hyperbolicGen_eq_map_inv_iff_wenzl
    (hτ : IsMarkovTrace z τ) (hz : z = exp (-θ) * (1 - ηW) - exp θ * ηW) (hα : cosh α ≠ 0)
    (hθ : cosh θ ≠ 0) (n : ℕ) :
    τ (hyperbolicGen α θ n) = τ ↑(hyperbolicGen α θ n)⁻¹ ↔ ηW = hyperbolicWenzlProjParam α θ := by
  rw [hτ.map_hyperbolicGen_eq_map_inv_iff (η := 1 - ηW)
      (by rw [sub_sub_cancel, hz]) hα hθ n, hyperbolicWenzlProjParam_eq_one_sub]
  constructor <;> intro h <;> linear_combination -h

end InfiniteTypeAHeckeAlgebra

/-! ### Quadratic boundary relation and Jones parameter limits on the real family -/

/-- **Boundary relation `τ = η * (1 - η)`.** For every real `θ` and `η`,
`(4 * cosh θ ^ 2)⁻¹ = η * (1 - η)` holds if and only if `η` is one of the two interval endpoints
`1 / (1 + exp (-2 * θ))` or `exp (-2 * θ) / (1 + exp (-2 * θ))`. -/
theorem inv_four_mul_cosh_sq_eq_mul_one_sub_iff {θ η : ℝ} :
    (4 * Real.cosh θ ^ 2)⁻¹ = η * (1 - η) ↔
      η = 1 / (1 + Real.exp (-2 * θ)) ∨ η = Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)) := by
  rw [← wenzlParam_neg_two_real_exp_neg_two_mul,
    wenzlParam_neg_two_eq_mul_one_sub_iff (by positivity)]

/-- **Closed-interval characterization `(4 * cosh θ ^ 2)⁻¹ ≤ η * (1 - η)`.** For every real `θ` and
`η`, `(4 * cosh θ ^ 2)⁻¹ ≤ η * (1 - η)` holds if and only if `η` belongs to the closure of the real
hyperbolic parameter family `α ↦ realHyperbolicProjParam α θ`. -/
theorem inv_four_mul_cosh_sq_le_mul_one_sub_iff {θ η : ℝ} :
    (4 * Real.cosh θ ^ 2)⁻¹ ≤ η * (1 - η) ↔
      η ∈ closure (Set.range fun α ↦ realHyperbolicProjParam α θ) := by
  rw [closure_range_realHyperbolicProjParam, ← wenzlParam_neg_two_real_exp_neg_two_mul,
    wenzlParam_neg_two_le_mul_one_sub_iff (by positivity)]

/-- **Open-interval characterization `(4 * cosh θ ^ 2)⁻¹ < η * (1 - η)`.** For every real `θ` and
`η`, the strict inequality `(4 * cosh θ ^ 2)⁻¹ < η * (1 - η)` holds if and only if `θ ≠ 0` and
`η = realHyperbolicProjParam α θ` for some `α : ℝ`. -/
theorem inv_four_mul_cosh_sq_lt_mul_one_sub_iff {θ η : ℝ} :
    (4 * Real.cosh θ ^ 2)⁻¹ < η * (1 - η) ↔
      θ ≠ 0 ∧ η ∈ Set.range fun α ↦ realHyperbolicProjParam α θ := by
  rw [← wenzlParam_neg_two_real_exp_neg_two_mul,
    wenzlParam_neg_two_lt_mul_one_sub_iff (by positivity)]
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp
  · simp [hθ, range_realHyperbolicProjParam_of_ne_zero hθ]

/-- **Scalar limit of the Jones parameter as `θ → +∞` (`Q → 0⁺`).** -/
theorem tendsto_wenzlParam_neg_two_real_exp_neg_two_mul_atTop :
    Filter.Tendsto (fun θ : ℝ ↦ wenzlParam (-2) (Real.exp (-2 * θ))) Filter.atTop (𝓝 0) := by
  simp_rw [wenzlParam_neg_two_real_exp_neg_two_mul]
  exact tendsto_inv_atTop_zero.comp
    ((Filter.tendsto_const_mul_pow_atTop (by positivity) (by positivity)).comp
      Real.tendsto_cosh_atTop)

/-- **Scalar limit of the Jones parameter as `θ → -∞` (`Q → +∞`).** -/
theorem tendsto_wenzlParam_neg_two_real_exp_neg_two_mul_atBot :
    Filter.Tendsto (fun θ : ℝ ↦ wenzlParam (-2) (Real.exp (-2 * θ))) Filter.atBot (𝓝 0) := by
  have h : (fun θ : ℝ ↦ wenzlParam (-2) (Real.exp (-2 * θ))) =
      (fun θ : ℝ ↦ wenzlParam (-2) (Real.exp (-2 * (-θ)))) := by
    ext θ
    rw [wenzlParam_neg_two_real_exp_neg_two_mul, wenzlParam_neg_two_real_exp_neg_two_mul,
      Real.cosh_neg]
  rw [h]
  exact tendsto_wenzlParam_neg_two_real_exp_neg_two_mul_atTop.comp Filter.tendsto_neg_atBot_atTop

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

/-! ### Exceptional root-of-unity point states `θ = π * I / l`, `α = (k / l + 1 / 2) * π * I` -/

/-- **Squared-cosine Jones parameter at `θ = π * I / l`.** For
`q = hyperbolicHeckeParam (π * I / l)` (so `Q = q ^ 2 = exp (-2 * π * I / l)`), the Jones parameter
`a_(-2)(Q)` is `(4 * cos (π / l) ^ 2)⁻¹` for every `l : ℕ`. -/
theorem wenzlParam_neg_two_hyperbolicHeckeParam_rootOfUnity_sq (l : ℕ) :
    wenzlParam (-2) ((hyperbolicHeckeParam (π * I / l) : ℂ) ^ 2) =
      (((4 * Real.cos (π / l) ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hq : (hyperbolicHeckeParam (π * I / l) : ℂ) ^ 2 = exp (2 * (-(π / l : ℂ)) * I) := by
    rw [val_hyperbolicHeckeParam, ← exp_natCast_mul]
    ring_nf
  rw [hq, wenzlParam_neg_two_exp_mul_I, cos_neg, ← ofReal_natCast, ← ofReal_div, ← ofReal_cos]
  norm_cast

private theorem cos_pi_div_natCast_ne_zero {l : ℕ} (hl : 3 ≤ l) : Real.cos (π / l) ≠ 0 := by
  have hl2 : (2 : ℝ) < l := by exact_mod_cast (by omega : 2 < l)
  exact (cos_pi_div_pos hl2).ne'

private theorem sin_natCast_mul_pi_div_natCast_ne_zero {l k : ℕ} (hk₀ : 0 < k) (hkl : k < l) :
    Real.sin (k * π / l) ≠ 0 :=
  (sin_mul_pi_div_pos (Nat.cast_pos.2 hk₀) (Nat.cast_lt.2 hkl)).ne'

private theorem pi_mul_I_div_natCast_eq (l : ℕ) :
    (π : ℂ) * I / l = ↑(π / (l : ℝ)) * I := by
  rw [ofReal_div, ofReal_natCast, mul_div_right_comm]

private theorem rootOfUnity_alpha_eq (l k : ℕ) :
    ((k : ℂ) / l + 1 / 2) * π * I = ↑((k : ℝ) * π / l + π / 2) * I := by
  push_cast
  ring

private theorem cosh_pi_mul_I_div_natCast_ne_zero {l : ℕ} (hl : 3 ≤ l) :
    cosh (π * I / l) ≠ 0 := by
  rw [pi_mul_I_div_natCast_eq, cosh_mul_I, ← ofReal_cos]
  exact_mod_cast cos_pi_div_natCast_ne_zero hl

private theorem cosh_rootOfUnity_alpha_ne_zero {l k : ℕ} (hk₀ : 0 < k) (hkl : k < l) :
    cosh (((k : ℂ) / l + 1 / 2) * π * I) ≠ 0 := by
  rw [rootOfUnity_alpha_eq, cosh_mul_I, ← ofReal_cos, Real.cos_add_pi_div_two]
  exact_mod_cast neg_ne_zero.2 (sin_natCast_mul_pi_div_natCast_ne_zero hk₀ hkl)

/-- **Native projection parameter at the root-of-unity exceptional points.** For `l ≥ 3` and
`0 < k < l`, at `θ = π * I / l` and `α = (k / l + 1 / 2) * π * I`, direct evaluation via
`tanh α = -I * cot (k * π / l)` and `tanh θ = I * tan (π / l)` identifies the native parameter
`hyperbolicProjParam α θ` with `a_(-k)(exp (-2 * π * I / l))`. -/
theorem hyperbolicProjParam_rootOfUnity {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    hyperbolicProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) =
      wenzlParam (-(k : ℤ)) (exp (-(2 * π * I / l))) := by
  have hcos : Real.cos (π / l) ≠ 0 := cos_pi_div_natCast_ne_zero hl
  have hsin : Real.sin (k * π / l) ≠ 0 := sin_natCast_mul_pi_div_natCast_ne_zero hk₀ hkl
  -- Direct evaluations `tanh θ = I * tan (π / l)` and `tanh α = -I * cot (k * π / l)`.
  have hθ_tanh : tanh (π * I / l) = I * ↑(Real.tan (π / l)) := by
    rw [pi_mul_I_div_natCast_eq, tanh_mul_I, ← ofReal_tan, mul_comm]
  have hα_tanh : tanh (((k : ℂ) / l + 1 / 2) * π * I) = -I * ↑(Real.cot (k * π / l)) := by
    rw [rootOfUnity_alpha_eq, tanh_mul_I, ← ofReal_tan, Real.tan_eq_sin_div_cos,
      Real.sin_add_pi_div_two, Real.cos_add_pi_div_two, div_neg, ← Real.cot_eq_cos_div_sin,
      ofReal_neg]
    ring
  have hprod : (-I * ↑(Real.cot (k * π / l))) * (I * ↑(Real.tan (π / l))) =
      ↑(Real.cot (k * π / l) * Real.tan (π / l)) := by
    rw [ofReal_mul]
    linear_combination -↑(Real.cot (k * π / l)) * ↑(Real.tan (π / l)) * I_sq
  rw [hyperbolicProjParam_def, hα_tanh, hθ_tanh, hprod,
    wenzlParam_neg_exp_neg_two_pi_mul_I_div hl hk₀ hkl]
  have hreal : (1 - Real.cot (k * π / l) * Real.tan (π / l)) / 2 =
      Real.sin ((k - 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l)) := by
    have hsub : ((k : ℝ) - 1) * π / l = k * π / l - π / l := by ring
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, hsub, Real.sin_sub]
    field_simp [hcos, hsin]
  exact_mod_cast hreal

/-- **Wenzl projection parameter at the root-of-unity exceptional points.** For `l ≥ 3` and
`0 < k < l`, at `θ = π * I / l` and `α = (k / l + 1 / 2) * π * I`, Wenzl's parameter
`hyperbolicWenzlProjParam α θ = 1 - hyperbolicProjParam α θ` equals
`a_k(exp (-2 * π * I / l))`. -/
theorem hyperbolicWenzlProjParam_rootOfUnity {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    hyperbolicWenzlProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) =
      wenzlParam (k : ℤ) (exp (-(2 * π * I / l))) := by
  have hsum := wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl
  rw [hyperbolicWenzlProjParam_eq_one_sub, hyperbolicProjParam_rootOfUnity hl hk₀ hkl, exp_neg,
    wenzlParam_inv, wenzlParam_inv]
  linear_combination -hsum

/-- **Complementary state `l - k` at the roots of unity (native convention).** Replacing `k` by
`l - k` in `{1, ..., l - 1}` exchanges the native parameter with Wenzl's parameter at `k`. -/
theorem hyperbolicProjParam_rootOfUnity_sub {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    hyperbolicProjParam ((((l - k : ℕ) : ℂ) / l + 1 / 2) * π * I) (π * I / l) =
      hyperbolicWenzlProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) := by
  have h1 := wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div (l := l) (k := l - k) hl
    (by omega) (by omega)
  have h2 := wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl
  have hsub := wenzlParam_sub_exp_two_pi_mul_I_div hl hkl.le
  rw [hyperbolicProjParam_rootOfUnity hl (by omega) (by omega),
    hyperbolicWenzlProjParam_rootOfUnity hl hk₀ hkl, exp_neg, wenzlParam_inv, wenzlParam_inv]
  linear_combination h1 - h2 - hsub

/-- **Complementary state `l - k` at the roots of unity (Wenzl convention).** Replacing `k` by
`l - k` in `{1, ..., l - 1}` exchanges Wenzl's parameter with the native parameter at `k`. -/
theorem hyperbolicWenzlProjParam_rootOfUnity_sub {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    hyperbolicWenzlProjParam ((((l - k : ℕ) : ℂ) / l + 1 / 2) * π * I) (π * I / l) =
      hyperbolicProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) := by
  rw [hyperbolicWenzlProjParam_rootOfUnity hl (by omega) (by omega),
    hyperbolicProjParam_rootOfUnity hl hk₀ hkl, wenzlParam_sub_exp_neg_two_pi_mul_I_div hl hkl.le]

/-- **Middle value at even `l = 2 * m`.** For every `m : ℕ`, the native root-of-unity
exceptional parameter at `l = 2 * m` and `k = m` is `1 / 2`. -/
theorem hyperbolicProjParam_rootOfUnity_middle (m : ℕ) :
    hyperbolicProjParam (((m : ℂ) / (2 * m : ℕ) + 1 / 2) * π * I) (π * I / (2 * m : ℕ)) =
      1 / 2 := by
  rw [hyperbolicProjParam_def]
  by_cases hm : m = 0
  · subst hm
    simp
  · have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    have hα : ((m : ℂ) / (2 * m : ℕ) + 1 / 2) * π * I = π * I := by
      push_cast
      field_simp [hmC]
      ring
    have htanh : tanh (π * I) = 0 := by
      simpa using tanh_add_pi_mul_I 0
    rw [hα, htanh, zero_mul, sub_zero]

/-- **Middle value at even `l = 2 * m` (Wenzl convention).** For every `m : ℕ`, Wenzl's
root-of-unity exceptional parameter at `l = 2 * m` and `k = m` is `1 / 2`. -/
theorem hyperbolicWenzlProjParam_rootOfUnity_middle (m : ℕ) :
    hyperbolicWenzlProjParam (((m : ℂ) / (2 * m : ℕ) + 1 / 2) * π * I) (π * I / (2 * m : ℕ)) =
      1 / 2 := by
  rw [hyperbolicWenzlProjParam_eq_one_sub, hyperbolicProjParam_rootOfUnity_middle m]
  norm_num

/-- **Nontrivial `(0, 1)` interior characterization at the roots of unity (native convention).**
For `l ≥ 3` and `0 < k < l`, the native root-of-unity parameter lies strictly in `(0, 1)` if and
only if `2 ≤ k` and `k + 2 ≤ l` (hence `l ≥ 4`). -/
theorem exists_mem_Ioo_hyperbolicProjParam_rootOfUnity_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    (∃ η ∈ Set.Ioo (0 : ℝ) 1,
      hyperbolicProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) = η) ↔
        2 ≤ k ∧ k + 2 ≤ l := by
  rw [← hyperbolicWenzlProjParam_rootOfUnity_sub hl hk₀ hkl,
    hyperbolicWenzlProjParam_rootOfUnity hl (by omega) (by omega), exp_neg, wenzlParam_inv,
    exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div_iff hl (by omega) (by omega)]
  omega

/-- **Nontrivial `(0, 1)` interior characterization at the roots of unity (Wenzl convention).**
For `l ≥ 3` and `0 < k < l`, Wenzl's root-of-unity parameter lies strictly in `(0, 1)` if and only
if `2 ≤ k` and `k + 2 ≤ l`. -/
theorem exists_mem_Ioo_hyperbolicWenzlProjParam_rootOfUnity_iff {l k : ℕ} (hl : 3 ≤ l)
    (hk₀ : 0 < k) (hkl : k < l) :
    (∃ η ∈ Set.Ioo (0 : ℝ) 1,
      hyperbolicWenzlProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) = η) ↔
        2 ≤ k ∧ k + 2 ≤ l := by
  rw [hyperbolicWenzlProjParam_rootOfUnity hl hk₀ hkl, exp_neg, wenzlParam_inv,
    exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div_iff hl hk₀ hkl]

/-- **Scalar-endpoint `{0, 1}` characterization at the roots of unity (native convention).** For
`l ≥ 3` and `0 < k < l`, the native root-of-unity parameter belongs to `{0, 1}` if and only if
`k = 1` or `k + 1 = l` (which covers every `0 < k < 3` when `l = 3`). -/
theorem hyperbolicProjParam_rootOfUnity_mem_pair_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    hyperbolicProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) ∈ ({0, 1} : Set ℂ) ↔
      k = 1 ∨ k + 1 = l := by
  rw [← hyperbolicWenzlProjParam_rootOfUnity_sub hl hk₀ hkl,
    hyperbolicWenzlProjParam_rootOfUnity hl (by omega) (by omega), exp_neg, wenzlParam_inv,
    wenzlParam_exp_two_pi_mul_I_div_mem_pair_iff hl (by omega) (by omega)]
  omega

/-- **Scalar-endpoint `{0, 1}` characterization at the roots of unity (Wenzl convention).** For
`l ≥ 3` and `0 < k < l`, Wenzl's root-of-unity parameter belongs to `{0, 1}` if and only if
`k = 1` or `k + 1 = l`. -/
theorem hyperbolicWenzlProjParam_rootOfUnity_mem_pair_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    hyperbolicWenzlProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) ∈ ({0, 1} : Set ℂ) ↔
      k = 1 ∨ k + 1 = l := by
  rw [hyperbolicWenzlProjParam_rootOfUnity hl hk₀ hkl, exp_neg, wenzlParam_inv,
    wenzlParam_exp_two_pi_mul_I_div_mem_pair_iff hl hk₀ hkl]

namespace InfiniteTypeAHeckeAlgebra

/-- **Markov trace characterization at the root-of-unity exceptional points (native convention).**
For `l ≥ 3` and `0 < k < l`, on the Hecke algebra at `θ = π * I / l` (`Q = exp (-2 * π * I / l)`),
a Markov trace with native projection parameter `η` has equal stabilization constants at
`α = (k / l + 1 / 2) * π * I` if and only if `η = a_(-k)(Q)`. -/
theorem IsMarkovTrace.map_hyperbolicGen_rootOfUnity_eq_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) {z η : ℂ}
    {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam (π * I / l)) →ₗ[ℂ] ℂ}
    (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-(π * I / l)) * η - exp (π * I / l) * (1 - η)) (n : ℕ) :
    τ (hyperbolicGen (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) n) =
        τ ↑(hyperbolicGen (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) n)⁻¹ ↔
      η = wenzlParam (-(k : ℤ)) (exp (-(2 * π * I / l))) := by
  rw [hτ.map_hyperbolicGen_eq_map_inv_iff hz (cosh_rootOfUnity_alpha_ne_zero hk₀ hkl)
      (cosh_pi_mul_I_div_natCast_ne_zero hl) n,
    hyperbolicProjParam_rootOfUnity hl hk₀ hkl]

/-- **Markov trace characterization at the root-of-unity exceptional points (Wenzl convention).**
For `l ≥ 3` and `0 < k < l`, a Markov trace with Wenzl projection parameter `η_W` has equal
stabilization constants at `θ = π * I / l`, `α = (k / l + 1 / 2) * π * I` if and only if
`η_W = a_k(exp (-2 * π * I / l))`. -/
theorem IsMarkovTrace.map_hyperbolicGen_rootOfUnity_eq_iff_wenzl {l k : ℕ} (hl : 3 ≤ l)
    (hk₀ : 0 < k) (hkl : k < l) {z ηW : ℂ}
    {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam (π * I / l)) →ₗ[ℂ] ℂ}
    (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-(π * I / l)) * (1 - ηW) - exp (π * I / l) * ηW) (n : ℕ) :
    τ (hyperbolicGen (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) n) =
        τ ↑(hyperbolicGen (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) n)⁻¹ ↔
      ηW = wenzlParam (k : ℤ) (exp (-(2 * π * I / l))) := by
  have hsum := wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl
  rw [hτ.map_hyperbolicGen_rootOfUnity_eq_iff hl hk₀ hkl (η := 1 - ηW)
      (by rw [sub_sub_cancel, hz]) n, exp_neg, wenzlParam_inv, wenzlParam_inv]
  constructor <;> intro h <;> linear_combination -hsum - h

end InfiniteTypeAHeckeAlgebra

end TauCeti
