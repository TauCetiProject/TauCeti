/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Wenzl
public import TauCeti.Algebra.TypeAHeckeAlgebra.Hyperbolic.Basic
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

This file builds the dictionary between these hyperbolic parameters and Wenzl's parameters
`a_d(Q)` (`TauCeti.wenzlParam`) at `Q = q ^ 2 = exp (-2 * θ)` across all three regimes:

1. **The positive-real family** (`α, θ ∈ ℝ`, `Q = exp (-2 * θ) > 0`): for `0 < θ`, the native map
   `α ↦ (1 - tanh α * tanh θ) / 2` is a strictly decreasing bijection onto the open interval
   `(Q / (1 + Q), 1 / (1 + Q))`, with `α → ±∞` endpoint limits `Q / (1 + Q)` and `1 / (1 + Q)`.
   For every real `θ`, the closure of the range is `[min (1 / (1 + Q)) (Q / (1 + Q)),
   max (1 / (1 + Q)) (Q / (1 + Q))]` (reducing to `{1 / 2}` at `θ = 0`, `Q = 1`), characterized by
   the quadratic inequality `(4 * cosh θ ^ 2)⁻¹ ≤ η * (1 - η)`, with equality on the endpoints and
   scalar limits `{0, 1}` as `θ → ±∞`.
2. **The exceptional discrete lines** (`α = k * θ + π * I / 2`, `k ∈ ℤ \ {0}`): the native
   projection parameter is `a_(-k)(exp (-2 * θ))` and Wenzl's projection parameter is
   `a_k(exp (-2 * θ))`, with common stabilization constant `-sinh θ / sinh (k * θ)`.
3. **The root-of-unity exceptional points** (`θ = π * I / l`, `α = (k / l + 1 / 2) * π * I`,
   `l ≥ 3`, `0 < k < l`, `Q = exp (-2 * π * I / l)`): direct evaluation via
   `tanh α = -I * cot (k * π / l)` and `tanh θ = I * tan (π / l)` gives native parameter
   `a_(-k)(Q)` and Wenzl parameter `a_k(Q)`. Replacing `k` by `l - k` exchanges the two projection
   conventions, `k = m` at `l = 2 * m` gives `1 / 2`, and `k ∈ {1, l - 1}` (all of `l = 3`) gives
   scalar endpoints `{0, 1}` whereas `2 ≤ k ≤ l - 2` (`l ≥ 4`) lies strictly in `(0, 1)`.

## Main definitions

* `TauCeti.hyperbolicProjParam`: the native hyperbolic projection parameter
  `(1 - tanh α * tanh θ) / 2` over `ℂ`.
* `TauCeti.hyperbolicWenzlProjParam`: Wenzl's hyperbolic projection parameter
  `(1 + tanh α * tanh θ) / 2` over `ℂ`.
* `TauCeti.realHyperbolicProjParam` and `TauCeti.realHyperbolicWenzlProjParam`: their real
  counterparts on `ℝ`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_hyperbolic_wenzlProjection` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_eq_map_inv_iff_wenzl`:
  Wenzl's projection rule and equal stabilization constants in hyperbolic parameters.
* `TauCeti.bijOn_realHyperbolicProjParam`, `TauCeti.closure_range_realHyperbolicProjParam`,
  `TauCeti.inv_four_mul_cosh_sq_eq_mul_one_sub_iff`,
  `TauCeti.inv_four_mul_cosh_sq_le_mul_one_sub_iff`, and
  `TauCeti.tendsto_sInf_range_realHyperbolicProjParam_atTop`: the real interval bijection, endpoint
  limits, quadratic boundary relation `τ = η * (1 - η)`, and scalar limits as `θ → ±∞`.
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

/-! ### Native and Wenzl hyperbolic projection parameters -/

/-- The native hyperbolic projection parameter `η = (1 - tanh α * tanh θ) / 2` at which the
positive and negative stabilization constants of `γ i = I * exp (-α) • T i` agree on the Hecke
algebra with parameter `q = exp (-θ)`. -/
noncomputable def hyperbolicProjParam (α θ : ℂ) : ℂ :=
  (1 - tanh α * tanh θ) / 2

/-- Wenzl's hyperbolic projection parameter `η_W = (1 + tanh α * tanh θ) / 2 = 1 - η`, attached to
the complementary projection `e_i^W = (1 + Q)⁻¹ • (Q - q • T i)`. -/
noncomputable def hyperbolicWenzlProjParam (α θ : ℂ) : ℂ :=
  (1 + tanh α * tanh θ) / 2

/-- Defining formula for `hyperbolicProjParam`. -/
theorem hyperbolicProjParam_def (α θ : ℂ) :
    hyperbolicProjParam α θ = (1 - tanh α * tanh θ) / 2 := (rfl)

/-- Defining formula for `hyperbolicWenzlProjParam`. -/
theorem hyperbolicWenzlProjParam_def (α θ : ℂ) :
    hyperbolicWenzlProjParam α θ = (1 + tanh α * tanh θ) / 2 := (rfl)

/-- Wenzl's hyperbolic projection parameter is `1` minus the native parameter. -/
theorem hyperbolicWenzlProjParam_eq_one_sub (α θ : ℂ) :
    hyperbolicWenzlProjParam α θ = 1 - hyperbolicProjParam α θ := by
  rw [hyperbolicWenzlProjParam_def, hyperbolicProjParam_def]
  ring

/-- The native hyperbolic projection parameter is `1` minus Wenzl's parameter. -/
theorem hyperbolicProjParam_eq_one_sub (α θ : ℂ) :
    hyperbolicProjParam α θ = 1 - hyperbolicWenzlProjParam α θ := by
  rw [hyperbolicWenzlProjParam_eq_one_sub]
  ring

/-- The native and Wenzl hyperbolic projection parameters sum to `1`. -/
theorem hyperbolicProjParam_add_hyperbolicWenzlProjParam (α θ : ℂ) :
    hyperbolicProjParam α θ + hyperbolicWenzlProjParam α θ = 1 := by
  rw [hyperbolicWenzlProjParam_eq_one_sub]
  ring

/-- `hyperbolicProjParam` is symmetric in its two arguments. -/
theorem hyperbolicProjParam_comm (α θ : ℂ) :
    hyperbolicProjParam α θ = hyperbolicProjParam θ α := by
  rw [hyperbolicProjParam_def, hyperbolicProjParam_def, mul_comm]

/-- `hyperbolicWenzlProjParam` is symmetric in its two arguments. -/
theorem hyperbolicWenzlProjParam_comm (α θ : ℂ) :
    hyperbolicWenzlProjParam α θ = hyperbolicWenzlProjParam θ α := by
  rw [hyperbolicWenzlProjParam_def, hyperbolicWenzlProjParam_def, mul_comm]

/-- Negating `α` exchanges the native and Wenzl hyperbolic projection parameters. -/
@[simp]
theorem hyperbolicProjParam_neg_left (α θ : ℂ) :
    hyperbolicProjParam (-α) θ = hyperbolicWenzlProjParam α θ := by
  simp [hyperbolicProjParam_def, hyperbolicWenzlProjParam_def, sub_eq_add_neg]

/-- Negating `θ` exchanges the native and Wenzl hyperbolic projection parameters. -/
@[simp]
theorem hyperbolicProjParam_neg_right (α θ : ℂ) :
    hyperbolicProjParam α (-θ) = hyperbolicWenzlProjParam α θ := by
  simp [hyperbolicProjParam_def, hyperbolicWenzlProjParam_def, sub_eq_add_neg]

/-- Negating `α` turns Wenzl's hyperbolic projection parameter into the native one. -/
@[simp]
theorem hyperbolicWenzlProjParam_neg_left (α θ : ℂ) :
    hyperbolicWenzlProjParam (-α) θ = hyperbolicProjParam α θ := by
  simp [hyperbolicProjParam_def, hyperbolicWenzlProjParam_def, sub_eq_add_neg]

/-- Negating `θ` turns Wenzl's hyperbolic projection parameter into the native one. -/
@[simp]
theorem hyperbolicWenzlProjParam_neg_right (α θ : ℂ) :
    hyperbolicWenzlProjParam α (-θ) = hyperbolicProjParam α θ := by
  simp [hyperbolicProjParam_def, hyperbolicWenzlProjParam_def, sub_eq_add_neg]

/-- At `α = 0`, the native hyperbolic projection parameter is `1 / 2`. -/
@[simp]
theorem hyperbolicProjParam_zero_left (θ : ℂ) : hyperbolicProjParam 0 θ = 1 / 2 := by
  simp [hyperbolicProjParam_def]

/-- At `θ = 0` (`Q = 1`), the native hyperbolic projection parameter is `1 / 2` for every `α`. -/
@[simp]
theorem hyperbolicProjParam_zero_right (α : ℂ) : hyperbolicProjParam α 0 = 1 / 2 := by
  simp [hyperbolicProjParam_def]

/-- At `α = 0`, Wenzl's hyperbolic projection parameter is `1 / 2`. -/
@[simp]
theorem hyperbolicWenzlProjParam_zero_left (θ : ℂ) : hyperbolicWenzlProjParam 0 θ = 1 / 2 := by
  simp [hyperbolicWenzlProjParam_def]

/-- At `θ = 0` (`Q = 1`), Wenzl's hyperbolic projection parameter is `1 / 2` for every `α`. -/
@[simp]
theorem hyperbolicWenzlProjParam_zero_right (α : ℂ) : hyperbolicWenzlProjParam α 0 = 1 / 2 := by
  simp [hyperbolicWenzlProjParam_def]

/-- Hyperbolic-cosine form `hyperbolicProjParam α θ = cosh (α - θ) / (2 * cosh α * cosh θ)` when
`cosh α * cosh θ ≠ 0`. -/
theorem hyperbolicProjParam_eq_cosh_sub_div {α θ : ℂ} (hα : cosh α ≠ 0) (hθ : cosh θ ≠ 0) :
    hyperbolicProjParam α θ = cosh (α - θ) / (2 * cosh α * cosh θ) :=
  (cosh_sub_div_eq_one_sub_tanh_mul_tanh_div_two hα hθ).symm

/-- Hyperbolic-cosine form `hyperbolicWenzlProjParam α θ = cosh (α + θ) / (2 * cosh α * cosh θ)`
when `cosh α * cosh θ ≠ 0`. -/
theorem hyperbolicWenzlProjParam_eq_cosh_add_div {α θ : ℂ} (hα : cosh α ≠ 0) (hθ : cosh θ ≠ 0) :
    hyperbolicWenzlProjParam α θ = cosh (α + θ) / (2 * cosh α * cosh θ) := by
  have hθ' : cosh (-θ) ≠ 0 := by simpa using hθ
  rw [← hyperbolicProjParam_neg_right, hyperbolicProjParam_eq_cosh_sub_div hα hθ', sub_neg_eq_add,
    cosh_neg]

/-- When `cosh θ ≠ 0`, the Jones parameter `a_(-2)(exp (-2 * θ))` satisfies the balanced-projection
compatibility `τ * (q + q⁻¹) ^ 2 = 1` for `q = hyperbolicHeckeParam θ`. -/
theorem wenzlParam_neg_two_mul_hyperbolicHeckeParam_add_inv_sq {θ : ℂ} (hθ : cosh θ ≠ 0) :
    wenzlParam (-2) (exp (-2 * θ)) *
      ((hyperbolicHeckeParam θ : ℂ) + ↑(hyperbolicHeckeParam θ)⁻¹) ^ 2 = 1 := by
  have hsum : (hyperbolicHeckeParam θ : ℂ) + ↑(hyperbolicHeckeParam θ)⁻¹ = 2 * cosh θ := by
    rw [val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, two_cosh, add_comm]
  rw [wenzlParam_neg_two_exp_neg_two_mul, hsum, show (2 * cosh θ) ^ 2 = 4 * cosh θ ^ 2 by ring]
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
  have hq2 : exp (-θ) ^ 2 = exp (-2 * θ) := by rw [← exp_nat_mul]; ring_nf
  have hu0 : 1 + exp (-2 * θ) ≠ 0 := by
    have e₁ : exp θ * exp (-θ) = 1 := by rw [← exp_add]; simp
    have e₂ : exp (-θ) * exp (-θ) = exp (-2 * θ) := by rw [← exp_add]; ring_nf
    have h1 : 1 + exp (-2 * θ) = 2 * cosh θ * exp (-θ) := by
      rw [two_cosh]
      linear_combination -e₁ - e₂
    rw [h1]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hθ) (exp_ne_zero _)
  have h := hτ.map_mul_wenzlProjection (Units.mk0 (1 + exp (-2 * θ)) hu0)
    (by rw [Units.val_mk0, val_hyperbolicHeckeParam, hq2]) (η := 1 - ηW)
    (by rw [val_hyperbolicHeckeParam, val_inv_hyperbolicHeckeParam, sub_sub_cancel, hz]) hx
  simpa only [Units.val_inv_eq_inv_val, Units.val_mk0, val_hyperbolicHeckeParam, hq2,
    sub_sub_cancel] using h

/-- **Equal stabilization constants in the native projection convention.** For `cosh α * cosh θ ≠ 0`
and native projection parameter `η`, `τ (γ n) = τ (γ n⁻¹)` if and only if
`η = hyperbolicProjParam α θ`. -/
theorem IsMarkovTrace.map_hyperbolicGen_eq_map_inv_iff_hyperbolicProjParam (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-θ) * η - exp θ * (1 - η)) (hα : cosh α ≠ 0) (hθ : cosh θ ≠ 0) (n : ℕ) :
    τ (hyperbolicGen α θ n) = τ ↑(hyperbolicGen α θ n)⁻¹ ↔ η = hyperbolicProjParam α θ :=
  hτ.map_hyperbolicGen_eq_map_inv_iff hz hα hθ n

/-- **Equal stabilization constants in Wenzl's projection convention.** For `cosh α * cosh θ ≠ 0`
and Wenzl projection parameter `η_W` (`z = exp (-θ) * (1 - η_W) - exp θ * η_W`),
`τ (γ n) = τ (γ n⁻¹)` if and only if `η_W = hyperbolicWenzlProjParam α θ`. -/
theorem IsMarkovTrace.map_hyperbolicGen_eq_map_inv_iff_wenzl
    (hτ : IsMarkovTrace z τ) (hz : z = exp (-θ) * (1 - ηW) - exp θ * ηW) (hα : cosh α ≠ 0)
    (hθ : cosh θ ≠ 0) (n : ℕ) :
    τ (hyperbolicGen α θ n) = τ ↑(hyperbolicGen α θ n)⁻¹ ↔ ηW = hyperbolicWenzlProjParam α θ := by
  rw [hτ.map_hyperbolicGen_eq_map_inv_iff_hyperbolicProjParam (η := 1 - ηW)
      (by rw [sub_sub_cancel, hz]) hα hθ n, hyperbolicWenzlProjParam_eq_one_sub]
  constructor <;> intro h <;> linear_combination -h

end InfiniteTypeAHeckeAlgebra

/-! ### The positive-real hyperbolic family, interval endpoints, and boundary relation -/

/-- The real native hyperbolic projection parameter `(1 - Real.tanh α * Real.tanh θ) / 2`. -/
noncomputable def realHyperbolicProjParam (α θ : ℝ) : ℝ :=
  (1 - Real.tanh α * Real.tanh θ) / 2

/-- The real Wenzl hyperbolic projection parameter `(1 + Real.tanh α * Real.tanh θ) / 2`. -/
noncomputable def realHyperbolicWenzlProjParam (α θ : ℝ) : ℝ :=
  (1 + Real.tanh α * Real.tanh θ) / 2

/-- Defining formula for `realHyperbolicProjParam`. -/
theorem realHyperbolicProjParam_def (α θ : ℝ) :
    realHyperbolicProjParam α θ = (1 - Real.tanh α * Real.tanh θ) / 2 := (rfl)

/-- Defining formula for `realHyperbolicWenzlProjParam`. -/
theorem realHyperbolicWenzlProjParam_def (α θ : ℝ) :
    realHyperbolicWenzlProjParam α θ = (1 + Real.tanh α * Real.tanh θ) / 2 := (rfl)

/-- Coercion of `realHyperbolicProjParam` to `ℂ` agrees with `hyperbolicProjParam`. -/
@[simp]
theorem ofReal_realHyperbolicProjParam (α θ : ℝ) :
    (realHyperbolicProjParam α θ : ℂ) = hyperbolicProjParam α θ := by
  simp [realHyperbolicProjParam_def, hyperbolicProjParam_def]

/-- Coercion of `realHyperbolicWenzlProjParam` to `ℂ` agrees with `hyperbolicWenzlProjParam`. -/
@[simp]
theorem ofReal_realHyperbolicWenzlProjParam (α θ : ℝ) :
    (realHyperbolicWenzlProjParam α θ : ℂ) = hyperbolicWenzlProjParam α θ := by
  simp [realHyperbolicWenzlProjParam_def, hyperbolicWenzlProjParam_def]

/-- `realHyperbolicWenzlProjParam` is `1` minus `realHyperbolicProjParam`. -/
theorem realHyperbolicWenzlProjParam_eq_one_sub (α θ : ℝ) :
    realHyperbolicWenzlProjParam α θ = 1 - realHyperbolicProjParam α θ := by
  rw [realHyperbolicWenzlProjParam_def, realHyperbolicProjParam_def]
  ring

/-- The real native and Wenzl hyperbolic projection parameters sum to `1`. -/
theorem realHyperbolicProjParam_add_realHyperbolicWenzlProjParam (α θ : ℝ) :
    realHyperbolicProjParam α θ + realHyperbolicWenzlProjParam α θ = 1 := by
  rw [realHyperbolicWenzlProjParam_eq_one_sub]
  ring

/-- Negating `α` exchanges the real native and Wenzl hyperbolic projection parameters. -/
@[simp]
theorem realHyperbolicProjParam_neg_left (α θ : ℝ) :
    realHyperbolicProjParam (-α) θ = realHyperbolicWenzlProjParam α θ := by
  simp [realHyperbolicProjParam_def, realHyperbolicWenzlProjParam_def, Real.tanh_neg,
    sub_eq_add_neg]

/-- Negating `θ` exchanges the real native and Wenzl hyperbolic projection parameters. -/
@[simp]
theorem realHyperbolicProjParam_neg_right (α θ : ℝ) :
    realHyperbolicProjParam α (-θ) = realHyperbolicWenzlProjParam α θ := by
  simp [realHyperbolicProjParam_def, realHyperbolicWenzlProjParam_def, Real.tanh_neg,
    sub_eq_add_neg]

/-- Negating `α` turns the real Wenzl hyperbolic projection parameter into the native one. -/
@[simp]
theorem realHyperbolicWenzlProjParam_neg_left (α θ : ℝ) :
    realHyperbolicWenzlProjParam (-α) θ = realHyperbolicProjParam α θ := by
  simp [realHyperbolicProjParam_def, realHyperbolicWenzlProjParam_def, Real.tanh_neg,
    sub_eq_add_neg]

/-- Negating `θ` turns the real Wenzl hyperbolic projection parameter into the native one. -/
@[simp]
theorem realHyperbolicWenzlProjParam_neg_right (α θ : ℝ) :
    realHyperbolicWenzlProjParam α (-θ) = realHyperbolicProjParam α θ := by
  simp [realHyperbolicProjParam_def, realHyperbolicWenzlProjParam_def, Real.tanh_neg,
    sub_eq_add_neg]

/-- Negating both `α` and `θ` leaves `realHyperbolicProjParam` unchanged. -/
theorem realHyperbolicProjParam_neg_neg (α θ : ℝ) :
    realHyperbolicProjParam (-α) (-θ) = realHyperbolicProjParam α θ := by
  simp

/-- At `α = 0`, `realHyperbolicProjParam 0 θ = 1 / 2` for every real `θ`. -/
@[simp]
theorem realHyperbolicProjParam_zero_left (θ : ℝ) : realHyperbolicProjParam 0 θ = 1 / 2 := by
  simp [realHyperbolicProjParam_def]

/-- At `θ = 0` (`Q = 1`), `realHyperbolicProjParam α 0 = 1 / 2` for every real `α`. -/
@[simp]
theorem realHyperbolicProjParam_zero_right (α : ℝ) : realHyperbolicProjParam α 0 = 1 / 2 := by
  simp [realHyperbolicProjParam_def]

/-- At `α = 0`, `realHyperbolicWenzlProjParam 0 θ = 1 / 2` for every real `θ`. -/
@[simp]
theorem realHyperbolicWenzlProjParam_zero_left (θ : ℝ) :
    realHyperbolicWenzlProjParam 0 θ = 1 / 2 := by
  simp [realHyperbolicWenzlProjParam_def]

/-- At `θ = 0` (`Q = 1`), `realHyperbolicWenzlProjParam α 0 = 1 / 2` for every real `α`. -/
@[simp]
theorem realHyperbolicWenzlProjParam_zero_right (α : ℝ) :
    realHyperbolicWenzlProjParam α 0 = 1 / 2 := by
  simp [realHyperbolicWenzlProjParam_def]

/-- On the real hyperbolic family (`α, θ ∈ ℝ`), no nonvanishing side-conditions are needed: the
stabilization constants of a Markov trace with native parameter `η` agree if and only if
`η = realHyperbolicProjParam α θ`. -/
theorem InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_hyperbolicGen_ofReal_eq_iff {α θ : ℝ}
    {z η : ℂ} {τ : InfiniteTypeAHeckeAlgebra ℂ (hyperbolicHeckeParam θ) →ₗ[ℂ] ℂ}
    (hτ : InfiniteTypeAHeckeAlgebra.IsMarkovTrace z τ)
    (hz : z = exp (-(θ : ℂ)) * η - exp (θ : ℂ) * (1 - η)) (n : ℕ) :
    τ (InfiniteTypeAHeckeAlgebra.hyperbolicGen α θ n) =
        τ ↑(InfiniteTypeAHeckeAlgebra.hyperbolicGen α θ n)⁻¹ ↔
      η = realHyperbolicProjParam α θ := by
  rw [hτ.map_hyperbolicGen_eq_map_inv_iff_hyperbolicProjParam hz
    (by exact_mod_cast (Real.cosh_pos α).ne') (by exact_mod_cast (Real.cosh_pos θ).ne') n,
    ofReal_realHyperbolicProjParam]

private theorem one_sub_tanh_div_two (θ : ℝ) :
    (1 - Real.tanh θ) / 2 = Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)) := by
  have e₁ : Real.exp θ * Real.exp (-θ) = 1 := by rw [← Real.exp_add]; simp
  have e₂ : Real.exp (-θ) * Real.exp (-θ) = Real.exp (-2 * θ) := by rw [← Real.exp_add]; ring_nf
  have h1 : 1 + Real.exp (-2 * θ) = 2 * Real.cosh θ * Real.exp (-θ) := by
    rw [Real.cosh_eq]; linear_combination -e₁ - e₂
  rw [Real.one_sub_tanh, h1, div_div, mul_comm (Real.cosh θ) 2,
    ← mul_div_mul_right _ _ (Real.exp_pos (-θ)).ne', e₂]

private theorem one_add_tanh_div_two (θ : ℝ) :
    (1 + Real.tanh θ) / 2 = 1 / (1 + Real.exp (-2 * θ)) := by
  have e₁ : Real.exp θ * Real.exp (-θ) = 1 := by rw [← Real.exp_add]; simp
  have e₂ : Real.exp (-θ) * Real.exp (-θ) = Real.exp (-2 * θ) := by rw [← Real.exp_add]; ring_nf
  have h1 : 1 + Real.exp (-2 * θ) = 2 * Real.cosh θ * Real.exp (-θ) := by
    rw [Real.cosh_eq]; linear_combination -e₁ - e₂
  rw [Real.one_add_tanh, h1, div_div, mul_comm (Real.cosh θ) 2,
    ← mul_div_mul_right _ _ (Real.exp_pos (-θ)).ne', e₁]

private theorem range_realHyperbolicProjParam_neg (θ : ℝ) :
    (Set.range fun α ↦ realHyperbolicProjParam α (-θ)) =
      Set.range fun α ↦ realHyperbolicProjParam α θ := by
  ext y
  refine ⟨fun ⟨α, hα⟩ ↦ ⟨-α, ?_⟩, fun ⟨α, hα⟩ ↦ ⟨-α, ?_⟩⟩
  · dsimp only at hα ⊢
    rw [← realHyperbolicProjParam_neg_neg (-α) θ, neg_neg, hα]
  · dsimp only at hα ⊢
    rw [realHyperbolicProjParam_neg_neg α θ, hα]

private theorem endpoints_ne_of_ne_zero {θ : ℝ} (hθ : θ ≠ 0) :
    1 / (1 + Real.exp (-2 * θ)) ≠ Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)) := by
  intro heq
  have hpos : 1 + Real.exp (-2 * θ) ≠ 0 := by positivity
  field_simp [hpos] at heq
  have h0 := Real.exp_injective (heq.symm.trans Real.exp_zero.symm)
  exact hθ (by linarith)

/-- **Upper-`α` endpoint limit.** For every real `θ`, as `α → +∞`, `realHyperbolicProjParam α θ`
tends to `exp (-2 * θ) / (1 + exp (-2 * θ))`. -/
theorem tendsto_realHyperbolicProjParam_atTop (θ : ℝ) :
    Filter.Tendsto (fun α ↦ realHyperbolicProjParam α θ) Filter.atTop
      (𝓝 (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)))) := by
  rw [← one_sub_tanh_div_two, ← one_mul (Real.tanh θ)]
  exact (tendsto_const_nhds.sub (Real.tendsto_tanh_atTop.mul_const _)).div_const 2

/-- **Lower-`α` endpoint limit.** For every real `θ`, as `α → -∞`, `realHyperbolicProjParam α θ`
tends to `1 / (1 + exp (-2 * θ))`. -/
theorem tendsto_realHyperbolicProjParam_atBot (θ : ℝ) :
    Filter.Tendsto (fun α ↦ realHyperbolicProjParam α θ) Filter.atBot
      (𝓝 (1 / (1 + Real.exp (-2 * θ)))) := by
  have hend : (1 - (-1) * Real.tanh θ) / 2 = 1 / (1 + Real.exp (-2 * θ)) := by
    rw [neg_one_mul, sub_neg_eq_add, one_add_tanh_div_two]
  rw [← hend]
  exact (tendsto_const_nhds.sub (Real.tendsto_tanh_atBot.mul_const _)).div_const 2

/-- For every real `θ`, as `α → +∞`, `realHyperbolicWenzlProjParam α θ` tends to
`1 / (1 + exp (-2 * θ))`. -/
theorem tendsto_realHyperbolicWenzlProjParam_atTop (θ : ℝ) :
    Filter.Tendsto (fun α ↦ realHyperbolicWenzlProjParam α θ) Filter.atTop
      (𝓝 (1 / (1 + Real.exp (-2 * θ)))) := by
  simpa [Function.comp_def] using
    (tendsto_realHyperbolicProjParam_atBot θ).comp Filter.tendsto_neg_atTop_atBot

/-- For every real `θ`, as `α → -∞`, `realHyperbolicWenzlProjParam α θ` tends to
`exp (-2 * θ) / (1 + exp (-2 * θ))`. -/
theorem tendsto_realHyperbolicWenzlProjParam_atBot (θ : ℝ) :
    Filter.Tendsto (fun α ↦ realHyperbolicWenzlProjParam α θ) Filter.atBot
      (𝓝 (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)))) := by
  simpa [Function.comp_def] using
    (tendsto_realHyperbolicProjParam_atTop θ).comp Filter.tendsto_neg_atBot_atTop

/-- For `0 < θ`, `α ↦ realHyperbolicProjParam α θ` is strictly decreasing. -/
theorem strictAnti_realHyperbolicProjParam {θ : ℝ} (hθ : 0 < θ) :
    StrictAnti fun α ↦ realHyperbolicProjParam α θ := by
  have ht : 0 < Real.tanh θ := by simpa using Real.tanh_strictMono hθ
  intro a b hab
  have h := mul_lt_mul_of_pos_right (Real.tanh_strictMono hab) ht
  dsimp only
  rw [realHyperbolicProjParam_def, realHyperbolicProjParam_def]
  linarith

/-- For `0 < θ`, `α ↦ realHyperbolicWenzlProjParam α θ` is strictly increasing. -/
theorem strictMono_realHyperbolicWenzlProjParam {θ : ℝ} (hθ : 0 < θ) :
    StrictMono fun α ↦ realHyperbolicWenzlProjParam α θ := by
  have ht : 0 < Real.tanh θ := by simpa using Real.tanh_strictMono hθ
  intro a b hab
  have h := mul_lt_mul_of_pos_right (Real.tanh_strictMono hab) ht
  dsimp only
  rw [realHyperbolicWenzlProjParam_def, realHyperbolicWenzlProjParam_def]
  linarith

/-- **Positive-real interval bijection (`0 < θ`).** For `0 < θ` (so `Q = exp (-2 * θ) ∈ (0, 1)`),
`α ↦ realHyperbolicProjParam α θ` is a bijection from `ℝ` onto the open interval
`(Q / (1 + Q), 1 / (1 + Q))`. -/
theorem bijOn_realHyperbolicProjParam {θ : ℝ} (hθ : 0 < θ) :
    Set.BijOn (fun α ↦ realHyperbolicProjParam α θ) Set.univ
      (Set.Ioo (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) (1 / (1 + Real.exp (-2 * θ)))) := by
  have ht : 0 < Real.tanh θ := by simpa using Real.tanh_strictMono hθ
  refine ⟨fun α _ ↦ ?_, (strictAnti_realHyperbolicProjParam hθ).injective.injOn, fun η hη ↦ ?_⟩
  · dsimp only
    rw [Set.mem_Ioo, ← one_sub_tanh_div_two, ← one_add_tanh_div_two, realHyperbolicProjParam_def]
    exact ⟨by nlinarith [Real.tanh_lt_one α], by nlinarith [Real.neg_one_lt_tanh α]⟩
  · rw [Set.mem_Ioo, ← one_sub_tanh_div_two, ← one_add_tanh_div_two] at hη
    let t := (1 - 2 * η) / Real.tanh θ
    have ht_mem : t ∈ Set.Ioo (-1 : ℝ) 1 := by
      rw [Set.mem_Ioo, lt_div_iff₀ ht, div_lt_iff₀ ht]
      exact ⟨by linarith [hη.2], by linarith [hη.1]⟩
    refine ⟨Real.artanh t, Set.mem_univ _, ?_⟩
    dsimp only
    rw [realHyperbolicProjParam_def, Real.tanh_artanh ht_mem]
    dsimp only [t]
    field_simp [ht.ne']
    ring

/-- For `0 < θ`, Wenzl's parameter `α ↦ realHyperbolicWenzlProjParam α θ` is also a bijection from
`ℝ` onto `(exp (-2 * θ) / (1 + exp (-2 * θ)), 1 / (1 + exp (-2 * θ)))`. -/
theorem bijOn_realHyperbolicWenzlProjParam {θ : ℝ} (hθ : 0 < θ) :
    Set.BijOn (fun α ↦ realHyperbolicWenzlProjParam α θ) Set.univ
      (Set.Ioo (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) (1 / (1 + Real.exp (-2 * θ)))) := by
  have hneg : Set.BijOn Neg.neg (Set.univ : Set ℝ) Set.univ :=
    ⟨fun _ _ ↦ trivial, neg_injective.injOn, fun x _ ↦ ⟨-x, trivial, neg_neg x⟩⟩
  simpa [Function.comp_def] using (bijOn_realHyperbolicProjParam hθ).comp hneg

/-- For `0 < θ`, the range of `α ↦ realHyperbolicProjParam α θ` is
`(exp (-2 * θ) / (1 + exp (-2 * θ)), 1 / (1 + exp (-2 * θ)))`. -/
theorem range_realHyperbolicProjParam_of_pos {θ : ℝ} (hθ : 0 < θ) :
    Set.range (fun α ↦ realHyperbolicProjParam α θ) =
      Set.Ioo (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) (1 / (1 + Real.exp (-2 * θ))) := by
  rw [← Set.image_univ]
  exact (bijOn_realHyperbolicProjParam hθ).image_eq

/-- For every nonzero real `θ`, the range of `α ↦ realHyperbolicProjParam α θ` is the open interval
between `1 / (1 + exp (-2 * θ))` and `exp (-2 * θ) / (1 + exp (-2 * θ))`. -/
theorem range_realHyperbolicProjParam_of_ne_zero {θ : ℝ} (hθ : θ ≠ 0) :
    Set.range (fun α ↦ realHyperbolicProjParam α θ) =
      Set.Ioo (min (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))))
        (max (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)))) := by
  rcases lt_or_gt_of_ne hθ with hlt | hgt
  · have hpos : 0 < -θ := neg_pos.2 hlt
    have e₁ : Real.exp (2 * θ) * Real.exp (-2 * θ) = 1 := by rw [← Real.exp_add]; simp
    have hQ₁ : Real.exp (-2 * (-θ)) / (1 + Real.exp (-2 * (-θ))) =
        1 / (1 + Real.exp (-2 * θ)) := by
      rw [show -2 * -θ = 2 * θ by ring, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination e₁
    have hQ₂ : 1 / (1 + Real.exp (-2 * (-θ))) =
        Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)) := by
      rw [show -2 * -θ = 2 * θ by ring, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination -e₁
    have hle : 1 / (1 + Real.exp (-2 * θ)) ≤ Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)) :=
      div_le_div_of_nonneg_right (Real.one_le_exp (by linarith)) (by positivity)
    rw [← range_realHyperbolicProjParam_neg, range_realHyperbolicProjParam_of_pos hpos, hQ₁, hQ₂,
      min_eq_left hle, max_eq_right hle]
  · have hle : Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)) ≤ 1 / (1 + Real.exp (-2 * θ)) :=
      div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by linarith)) (by positivity)
    rw [range_realHyperbolicProjParam_of_pos hgt, min_eq_right hle, max_eq_left hle]

/-- **Closure of the real hyperbolic family.** For every real `θ` (including `θ = 0`, where both
sides equal `{1 / 2}`), the closure of the range of `α ↦ realHyperbolicProjParam α θ` is the closed
interval `[min (1 / (1 + Q)) (Q / (1 + Q)), max (1 / (1 + Q)) (Q / (1 + Q))]` at
`Q = exp (-2 * θ)`. -/
theorem closure_range_realHyperbolicProjParam (θ : ℝ) :
    closure (Set.range fun α ↦ realHyperbolicProjParam α θ) =
      Set.Icc (min (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))))
        (max (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ)))) := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp [Set.range_const]
    norm_num
  · rw [range_realHyperbolicProjParam_of_ne_zero hθ]
    exact closure_Ioo (min_lt_max.2 (endpoints_ne_of_ne_zero hθ)).ne

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

/-- The greatest lower bound of `α ↦ realHyperbolicProjParam α θ` is
`min (1 / (1 + exp (-2 * θ))) (exp (-2 * θ) / (1 + exp (-2 * θ)))`. -/
theorem sInf_range_realHyperbolicProjParam (θ : ℝ) :
    sInf (Set.range fun α ↦ realHyperbolicProjParam α θ) =
      min (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp [Set.range_const]
    norm_num
  · rw [range_realHyperbolicProjParam_of_ne_zero hθ]
    exact csInf_Ioo (min_lt_max.2 (endpoints_ne_of_ne_zero hθ))

/-- The least upper bound of `α ↦ realHyperbolicProjParam α θ` is
`max (1 / (1 + exp (-2 * θ))) (exp (-2 * θ) / (1 + exp (-2 * θ)))`. -/
theorem sSup_range_realHyperbolicProjParam (θ : ℝ) :
    sSup (Set.range fun α ↦ realHyperbolicProjParam α θ) =
      max (1 / (1 + Real.exp (-2 * θ))) (Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp [Set.range_const]
    norm_num
  · rw [range_realHyperbolicProjParam_of_ne_zero hθ]
    exact csSup_Ioo (min_lt_max.2 (endpoints_ne_of_ne_zero hθ))

private theorem tendsto_exp_neg_two_mul_atTop :
    Filter.Tendsto (fun θ : ℝ ↦ Real.exp (-2 * θ)) Filter.atTop (𝓝 0) := by
  simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp
    (Filter.tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))

/-- **Scalar limit of the Jones parameter as `θ → +∞` (`Q → 0⁺`).** -/
theorem tendsto_wenzlParam_neg_two_real_exp_neg_two_mul_atTop :
    Filter.Tendsto (fun θ : ℝ ↦ wenzlParam (-2) (Real.exp (-2 * θ))) Filter.atTop (𝓝 0) := by
  have hc : ContinuousAt (wenzlParam (-2) : ℝ → ℝ) 0 :=
    continuousAt_wenzlParam (by simp [Finset.sum_range_succ])
  rw [← wenzlParam_neg_natCast_zero (K := ℝ) 2]
  exact hc.tendsto.comp tendsto_exp_neg_two_mul_atTop

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

private theorem tendsto_inv_one_add_exp_atTop :
    Filter.Tendsto (fun θ : ℝ ↦ 1 / (1 + Real.exp (-2 * θ))) Filter.atTop (𝓝 1) := by
  have h : Filter.Tendsto (fun θ : ℝ ↦ 1 / (1 + Real.exp (-2 * θ))) Filter.atTop
      (𝓝 (1 / (1 + 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_exp_neg_two_mul_atTop) (by norm_num)
  rwa [add_zero, div_one] at h

private theorem tendsto_exp_div_one_add_exp_atTop :
    Filter.Tendsto (fun θ : ℝ ↦ Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) Filter.atTop
      (𝓝 0) := by
  have h : Filter.Tendsto (fun θ : ℝ ↦ Real.exp (-2 * θ) / (1 + Real.exp (-2 * θ))) Filter.atTop
      (𝓝 (0 / (1 + 0))) :=
    tendsto_exp_neg_two_mul_atTop.div
      (tendsto_const_nhds.add tendsto_exp_neg_two_mul_atTop) (by norm_num)
  rwa [zero_div] at h

/-- **Scalar limit of the lower interval endpoint as `θ → +∞`.** As `θ → +∞` (`Q → 0⁺`), the lower
endpoint of the real hyperbolic interval tends to `0 = a_(-1)(Q)`. -/
theorem tendsto_sInf_range_realHyperbolicProjParam_atTop :
    Filter.Tendsto (fun θ ↦ sInf (Set.range fun α ↦ realHyperbolicProjParam α θ)) Filter.atTop
      (𝓝 0) := by
  simpa [sInf_range_realHyperbolicProjParam] using
    tendsto_inv_one_add_exp_atTop.min tendsto_exp_div_one_add_exp_atTop

/-- **Scalar limit of the upper interval endpoint as `θ → +∞`.** As `θ → +∞` (`Q → 0⁺`), the upper
endpoint of the real hyperbolic interval tends to `1 = a_1(Q)`. -/
theorem tendsto_sSup_range_realHyperbolicProjParam_atTop :
    Filter.Tendsto (fun θ ↦ sSup (Set.range fun α ↦ realHyperbolicProjParam α θ)) Filter.atTop
      (𝓝 1) := by
  simpa [sSup_range_realHyperbolicProjParam] using
    tendsto_inv_one_add_exp_atTop.max tendsto_exp_div_one_add_exp_atTop

/-- **Scalar limit of the lower interval endpoint as `θ → -∞`.** As `θ → -∞` (`Q → +∞`), the lower
endpoint of the real hyperbolic interval tends to `0`. -/
theorem tendsto_sInf_range_realHyperbolicProjParam_atBot :
    Filter.Tendsto (fun θ ↦ sInf (Set.range fun α ↦ realHyperbolicProjParam α θ)) Filter.atBot
      (𝓝 0) := by
  have h : (fun θ : ℝ ↦ sInf (Set.range fun α ↦ realHyperbolicProjParam α θ)) =
      (fun θ : ℝ ↦ sInf (Set.range fun α ↦ realHyperbolicProjParam α (-θ))) := by
    ext θ; rw [range_realHyperbolicProjParam_neg]
  rw [h]
  exact tendsto_sInf_range_realHyperbolicProjParam_atTop.comp Filter.tendsto_neg_atBot_atTop

/-- **Scalar limit of the upper interval endpoint as `θ → -∞`.** As `θ → -∞` (`Q → +∞`), the upper
endpoint of the real hyperbolic interval tends to `1`. -/
theorem tendsto_sSup_range_realHyperbolicProjParam_atBot :
    Filter.Tendsto (fun θ ↦ sSup (Set.range fun α ↦ realHyperbolicProjParam α θ)) Filter.atBot
      (𝓝 1) := by
  have h : (fun θ : ℝ ↦ sSup (Set.range fun α ↦ realHyperbolicProjParam α θ)) =
      (fun θ : ℝ ↦ sSup (Set.range fun α ↦ realHyperbolicProjParam α (-θ))) := by
    ext θ; rw [range_realHyperbolicProjParam_neg]
  rw [h]
  exact tendsto_sSup_range_realHyperbolicProjParam_atTop.comp Filter.tendsto_neg_atBot_atTop

/-! ### Exceptional discrete line states `α = k * θ + π * I / 2` -/

private theorem cosh_add_pi_mul_I_div_two (z : ℂ) : cosh (z + π * I / 2) = I * sinh z := by
  rw [show π * I / 2 = (π / 2 : ℂ) * I by ring, cosh_add, cosh_mul_I, sinh_mul_I,
    cos_pi_div_two, sin_pi_div_two]
  ring

private theorem tanh_add_pi_mul_I_div_two (z : ℂ) :
    tanh (z + π * I / 2) = cosh z / sinh z := by
  have hsinh : sinh (z + π * I / 2) = I * cosh z := by
    rw [show π * I / 2 = (π / 2 : ℂ) * I by ring, sinh_add, cosh_mul_I, sinh_mul_I,
      cos_pi_div_two, sin_pi_div_two]
    ring
  rw [tanh_eq_sinh_div_cosh, hsinh, cosh_add_pi_mul_I_div_two, mul_div_mul_left _ _ I_ne_zero]

/-- **Native projection parameter on the exceptional line `α = k * θ + π * I / 2`.** Whenever
`cosh θ ≠ 0` and `sinh (k * θ) ≠ 0`, `hyperbolicProjParam (k * θ + π * I / 2) θ` equals
`a_(-k)(exp (-2 * θ))`. -/
theorem hyperbolicProjParam_mul_add_pi_mul_I_div_two {k : ℤ} {θ : ℂ} (hθ : cosh θ ≠ 0)
    (hk : sinh (k * θ) ≠ 0) :
    hyperbolicProjParam (k * θ + π * I / 2) θ = wenzlParam (-k) (exp (-2 * θ)) := by
  have hk_neg : sinh ((-k : ℤ) * θ) ≠ 0 := by simpa [Int.cast_neg, neg_mul, sinh_neg] using hk
  rw [hyperbolicProjParam_def, tanh_add_pi_mul_I_div_two, tanh_eq_sinh_div_cosh,
    wenzlParam_exp_neg_two_mul (-k) hθ hk_neg, Int.cast_neg, neg_mul, sinh_neg,
    show (-(k : ℂ) + 1) * θ = -(k * θ - θ) by ring, sinh_neg, sinh_sub]
  field_simp [hθ, hk]

/-- **Wenzl projection parameter on the exceptional line `α = k * θ + π * I / 2`.** Whenever
`cosh θ ≠ 0` and `sinh (k * θ) ≠ 0`, `hyperbolicWenzlProjParam (k * θ + π * I / 2) θ` equals
`a_k(exp (-2 * θ))`. -/
theorem hyperbolicWenzlProjParam_mul_add_pi_mul_I_div_two {k : ℤ} {θ : ℂ} (hθ : cosh θ ≠ 0)
    (hk : sinh (k * θ) ≠ 0) :
    hyperbolicWenzlProjParam (k * θ + π * I / 2) θ = wenzlParam k (exp (-2 * θ)) := by
  rw [hyperbolicWenzlProjParam_def, tanh_add_pi_mul_I_div_two, tanh_eq_sinh_div_cosh,
    wenzlParam_exp_neg_two_mul k hθ hk, show ((k : ℂ) + 1) * θ = k * θ + θ by ring, sinh_add]
  field_simp [hθ, hk]

/-- **Common stabilization constant on the exceptional line.** At `α = k * θ + π * I / 2` and
`η = a_(-k)(exp (-2 * θ))`, the common stabilization constant is `-sinh θ / sinh (k * θ)`. -/
theorem hyperbolicStabilization_mul_add_pi_mul_I_div_two {k : ℤ} {θ : ℂ} (hθ : cosh θ ≠ 0)
    (hk : sinh (k * θ) ≠ 0) :
    hyperbolicStabilization (k * θ + π * I / 2) θ (wenzlParam (-k) (exp (-2 * θ))) =
      -sinh θ / sinh (k * θ) := by
  have hα : cosh (k * θ + π * I / 2) ≠ 0 := by
    rw [cosh_add_pi_mul_I_div_two]; exact mul_ne_zero I_ne_zero hk
  rw [hyperbolicStabilization_eq_neg_I_mul_sinh_div_cosh hα hθ
    (hyperbolicProjParam_mul_add_pi_mul_I_div_two hθ hk).symm, cosh_add_pi_mul_I_div_two]
  field_simp [I_ne_zero]

/-- **Real-`θ` exceptional line parameter (`k ≠ 0`, `θ ≠ 0`).** At real `θ ≠ 0` and integer `k ≠ 0`,
`hyperbolicProjParam (k * θ + π * I / 2) θ = a_(-k)(exp (-2 * θ))`. -/
theorem hyperbolicProjParam_ofReal_mul_add_pi_mul_I_div_two {k : ℤ} (hk : k ≠ 0) {θ : ℝ}
    (hθ : θ ≠ 0) :
    hyperbolicProjParam (k * (θ : ℂ) + π * I / 2) θ =
      ↑(wenzlParam (-k) (Real.exp (-2 * θ))) := by
  have hc : cosh (θ : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos θ).ne'
  have hs : sinh ((k : ℂ) * θ) ≠ 0 := by
    have : Real.sinh ((k : ℝ) * θ) ≠ 0 :=
      Real.sinh_ne_zero.2 (mul_ne_zero (Int.cast_ne_zero.2 hk) hθ)
    exact_mod_cast this
  rw [hyperbolicProjParam_mul_add_pi_mul_I_div_two hc hs]
  symm
  simpa using map_wenzlParam Complex.ofRealHom (-k) (Real.exp (-2 * θ))

/-- At real `θ ≠ 0` and integer `k ≠ 0`, Wenzl's parameter on `α = k * θ + π * I / 2` is
`a_k(exp (-2 * θ))`. -/
theorem hyperbolicWenzlProjParam_ofReal_mul_add_pi_mul_I_div_two {k : ℤ} (hk : k ≠ 0) {θ : ℝ}
    (hθ : θ ≠ 0) :
    hyperbolicWenzlProjParam (k * (θ : ℂ) + π * I / 2) θ =
      ↑(wenzlParam k (Real.exp (-2 * θ))) := by
  have hc : cosh (θ : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos θ).ne'
  have hs : sinh ((k : ℂ) * θ) ≠ 0 := by
    have : Real.sinh ((k : ℝ) * θ) ≠ 0 :=
      Real.sinh_ne_zero.2 (mul_ne_zero (Int.cast_ne_zero.2 hk) hθ)
    exact_mod_cast this
  rw [hyperbolicWenzlProjParam_mul_add_pi_mul_I_div_two hc hs]
  symm
  simpa using map_wenzlParam Complex.ofRealHom k (Real.exp (-2 * θ))

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
  have hα : cosh (k * θ + π * I / 2) ≠ 0 := by
    rw [cosh_add_pi_mul_I_div_two]; exact mul_ne_zero I_ne_zero hk
  rw [hτ.map_hyperbolicGen_eq_map_inv_iff_hyperbolicProjParam hz hα hθ n,
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
  have hα : cosh (k * θ + π * I / 2) ≠ 0 := by
    rw [cosh_add_pi_mul_I_div_two]; exact mul_ne_zero I_ne_zero hk
  rw [hτ.map_hyperbolicGen_eq_map_inv_iff_wenzl hz hα hθ n,
    hyperbolicWenzlProjParam_mul_add_pi_mul_I_div_two hθ hk]

/-- Precomposing with `complementEquiv` on the exceptional line `α = k * θ + π * I / 2` gives the
complementary parameter `a_k(exp (-2 * θ))`. -/
theorem IsMarkovTrace.map_complementEquiv_hyperbolicGen_line_eq_iff (hτ : IsMarkovTrace z τ)
    (hz : z = exp (-θ) * η - exp θ * (1 - η)) (hθ : cosh θ ≠ 0) (hk : sinh (k * θ) ≠ 0)
    (n : ℕ) :
    τ (complementEquiv _ (hyperbolicGen (k * θ + π * I / 2) θ n)) =
        τ (complementEquiv _ ↑(hyperbolicGen (k * θ + π * I / 2) θ n)⁻¹) ↔
      η = wenzlParam k (exp (-2 * θ)) := by
  have hα : cosh (k * θ + π * I / 2) ≠ 0 := by
    rw [cosh_add_pi_mul_I_div_two]; exact mul_ne_zero I_ne_zero hk
  rw [hτ.map_complementEquiv_hyperbolicGen_eq_iff hz hα hθ n, ← hyperbolicWenzlProjParam_def,
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
    rw [val_hyperbolicHeckeParam, ← exp_nat_mul]
    ring_nf
  rw [hq, wenzlParam_neg_two_exp_mul_I, cos_neg,
    show (π : ℂ) / l = ↑(π / (l : ℝ)) by push_cast; rfl, ← ofReal_cos]
  push_cast
  rfl

/-- **Native projection parameter at the root-of-unity exceptional points.** For `l ≥ 3` and
`0 < k < l`, at `θ = π * I / l` and `α = (k / l + 1 / 2) * π * I`, direct evaluation via
`tanh α = -I * cot (k * π / l)` and `tanh θ = I * tan (π / l)` identifies the native parameter
`hyperbolicProjParam α θ` with `a_(-k)(exp (-2 * π * I / l))`. -/
theorem hyperbolicProjParam_rootOfUnity {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    hyperbolicProjParam (((k : ℂ) / l + 1 / 2) * π * I) (π * I / l) =
      wenzlParam (-(k : ℤ)) (exp (-(2 * π * I / l))) := by
  have hl₀ : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hcos : Real.cos (π / l) ≠ 0 := (cos_pi_div_pos (by exact_mod_cast (by omega : 2 < l))).ne'
  have hsin : Real.sin (k * π / l) ≠ 0 := by
    refine (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    rw [div_lt_iff₀ hl₀, mul_comm π]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hkl) Real.pi_pos
  -- Direct evaluations `tanh θ = I * tan (π / l)` and `tanh α = -I * cot (k * π / l)`.
  have hθ_tanh : tanh (π * I / l) = I * ↑(Real.tan (π / l)) := by
    rw [show π * I / (l : ℂ) = ↑(π / (l : ℝ)) * I by push_cast; ring, tanh_mul_I, ← ofReal_tan,
      mul_comm]
  have hα_tanh : tanh (((k : ℂ) / l + 1 / 2) * π * I) = -I * ↑(Real.cot (k * π / l)) := by
    rw [show ((k : ℂ) / l + 1 / 2) * π * I = ((k * π / l + π / 2 : ℝ) : ℂ) * I by push_cast; ring,
      tanh_mul_I, ← ofReal_tan, Real.tan_eq_sin_div_cos, Real.sin_add_pi_div_two,
      Real.cos_add_pi_div_two, div_neg, ← Real.cot_eq_cos_div_sin, ofReal_neg]
    ring
  have hprod : (-I * ↑(Real.cot (k * π / l))) * (I * ↑(Real.tan (π / l))) =
      ↑(Real.cot (k * π / l) * Real.tan (π / l)) := by
    rw [ofReal_mul]
    linear_combination -↑(Real.cot (k * π / l)) * ↑(Real.tan (π / l)) * I_sq
  rw [hyperbolicProjParam_def, hα_tanh, hθ_tanh, hprod,
    wenzlParam_neg_exp_neg_two_pi_mul_I_div hl hk₀ hkl]
  have hreal : (1 - Real.cot (k * π / l) * Real.tan (π / l)) / 2 =
      Real.sin ((k - 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l)) := by
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos,
      show ((k : ℝ) - 1) * π / l = k * π / l - π / l by ring, Real.sin_sub]
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

/-- **Middle value at even `l = 2 * m`.** For `m ≥ 2` and `k = m`, the native root-of-unity
exceptional parameter is `1 / 2`. -/
theorem hyperbolicProjParam_rootOfUnity_middle {m : ℕ} (hm : 2 ≤ m) :
    hyperbolicProjParam (((m : ℂ) / (2 * m : ℕ) + 1 / 2) * π * I) (π * I / (2 * m : ℕ)) =
      1 / 2 := by
  have hsub : 2 * m - m = m := by omega
  have h := hyperbolicProjParam_rootOfUnity_sub (l := 2 * m) (k := m) (by omega) (by omega)
    (by omega)
  rw [hsub, hyperbolicWenzlProjParam_rootOfUnity (by omega) (by omega) (by omega), exp_neg,
    wenzlParam_inv] at h
  push_cast at h ⊢
  rw [h, wenzlParam_exp_two_pi_mul_I_div_two_mul hm]

/-- **Middle value at even `l = 2 * m` (Wenzl convention).** For `m ≥ 2` and `k = m`, Wenzl's
root-of-unity exceptional parameter is `1 / 2`. -/
theorem hyperbolicWenzlProjParam_rootOfUnity_middle {m : ℕ} (hm : 2 ≤ m) :
    hyperbolicWenzlProjParam (((m : ℂ) / (2 * m : ℕ) + 1 / 2) * π * I) (π * I / (2 * m : ℕ)) =
      1 / 2 := by
  rw [hyperbolicWenzlProjParam_eq_one_sub, hyperbolicProjParam_rootOfUnity_middle hm]
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
  have hl₀ : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hθ : cosh (π * I / l) ≠ 0 := by
    have hcos : Real.cos (π / l) ≠ 0 := (cos_pi_div_pos (by exact_mod_cast (by omega : 2 < l))).ne'
    rw [show π * I / (l : ℂ) = ↑(π / (l : ℝ)) * I by push_cast; ring, cosh_mul_I, ← ofReal_cos]
    exact_mod_cast hcos
  have hα : cosh (((k : ℂ) / l + 1 / 2) * π * I) ≠ 0 := by
    have hsin : Real.sin (k * π / l) ≠ 0 := by
      refine (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
      rw [div_lt_iff₀ hl₀, mul_comm π]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hkl) Real.pi_pos
    rw [show ((k : ℂ) / l + 1 / 2) * π * I = ((k * π / l + π / 2 : ℝ) : ℂ) * I by push_cast; ring,
      cosh_mul_I, ← ofReal_cos, Real.cos_add_pi_div_two]
    exact_mod_cast neg_ne_zero.2 hsin
  rw [hτ.map_hyperbolicGen_eq_map_inv_iff_hyperbolicProjParam hz hα hθ n,
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
