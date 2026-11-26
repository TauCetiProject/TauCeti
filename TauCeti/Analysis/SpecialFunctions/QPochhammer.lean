/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import TauCeti.Algebra.Ring.Parity
public import TauCeti.Algebra.Ring.QPochhammer
public import TauCeti.Analysis.Normed.Ring.InfiniteProd
public import TauCeti.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# The infinite q-Pochhammer products `∏_{n ≥ 1} (1 - qⁿ w)`

For `‖q‖ < 1` in a complete normed field, the product `∏_{n ≥ 1} (1 - qⁿ w)` (the q-Pochhammer
symbol `(q w; q)_∞`) converges absolutely. This file records its convergence, the shift identity
obtained by splitting off the first factor, and its nonvanishing. It also introduces the theta
product `θ_q(w) = (w; q)_∞ (q w⁻¹; q)_∞ = (1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)` and proves its
convergence, its nonvanishing and its quasi-periodicity `θ_q(q w) = -w⁻¹ θ_q(w)`, and evaluates it
at `w = -1` and at `q = w²`. These evaluations, together with Euler's identity
`∏_{n ≥ 1} (1 + qⁿ) ∏_{n ≥ 0} (1 - q^{2n+1}) = 1`, compute the Siegel functions of level two. Its
evaluations at `q = w³` and at a primitive cube root of unity `w`, multiplied by an Euler function,
compute those of level three. Euler's two series expansions of `(z; q)_∞ = ∏_{n ≥ 0} (1 - z qⁿ)`
and of its reciprocal are the input to Jacobi's triple product identity. When
`q` and
`w` depend continuously on `τ` in an open set `U ⊆ ℂ` with `‖q‖ < 1` on `U`, the product converges
locally uniformly on `U`, and is holomorphic there when `q` and `w` are; for example
`q = e^{2π i τ}` on the upper half-plane. The locally uniform convergence and
holomorphy argument is adapted from `Mathlib.NumberTheory.ModularForms.DedekindEta`
(C. Birkbeck, D. Loeffler).

## Main results

* `TauCeti.multipliable_one_sub_pow_mul`: for `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w)`
  converges.
* `TauCeti.tprod_one_sub_pow_mul_eq`: `∏_{n ≥ 1} (1 - qⁿ w) = (1 - q w) ∏_{n ≥ 1} (1 - qⁿ (q w))`.
* `TauCeti.tprod_one_sub_pow_mul_ne_zero`: the product is nonzero when all of its factors are.
* `TauCeti.tendsto_tprod_one_sub_pow_mul`: `∏_{n ≥ 1} (1 - qⁿ w) → 1` when `q → 0` and
  `q w → 0`; `w` may be unbounded, and no completeness assumption is needed.
* `TauCeti.tprod_one_sub_pow_ne_zero`: the Euler function `∏_{n ≥ 1} (1 - qⁿ)` is nonzero.
* `TauCeti.norm_tprod_one_sub_pow_mul_le`, `TauCeti.norm_qTheta_le`: the bounds
  `‖∏_{n ≥ 1} (1 - qⁿ w)‖ ≤ exp (‖q‖ ‖w‖ / (1 - ‖q‖))` and
  `‖θ_q(w)‖ ≤ ‖1 - w‖ exp (‖q‖ (‖w‖ + ‖w‖⁻¹) / (1 - ‖q‖))` for `‖q‖ < 1`.
* `TauCeti.norm_tprod_one_sub_pow_mul_sub_one_le`, `TauCeti.norm_tprod_one_add_pow_sub_one_le`:
  the product is close to `1` for small `q`,
  `‖∏_{n ≥ 1} (1 - qⁿ w) - 1‖ ≤ exp (‖q‖ ‖w‖ / (1 - ‖q‖)) - 1`, and
  `‖∏_{n ≥ 1} (1 + qⁿ) - 1‖ ≤ ‖q‖ / (1 - 2‖q‖)` for `‖q‖ < 1/2`.
* `TauCeti.multipliable_one_add_pow`, `TauCeti.multipliable_one_sub_pow_odd`,
  `TauCeti.multipliable_one_add_pow_odd`: for `‖q‖ < 1` the products `∏_{n ≥ 1} (1 + qⁿ)` and
  `∏_{n ≥ 0} (1 ∓ q^{2n+1})` converge.
* `TauCeti.qTheta`: the theta product `θ_q(w) = (1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)`.
* `TauCeti.multipliable_qTheta`, `TauCeti.qTheta_ne_zero`: for `‖q‖ < 1` the product in
  `θ_q(w)` converges, and `θ_q(w) ≠ 0` when `w` is not an integral power of `q`.
* `TauCeti.qTheta_mul_left`: its quasi-periodicity `θ_q(q w) = -w⁻¹ θ_q(w)` for
  `0 < ‖q‖ < 1` and `w ≠ 0`.
* `TauCeti.qTheta_one`, `TauCeti.differentiableOn_qTheta`, `TauCeti.hasDerivAt_qTheta_one`:
  `θ_q(1) = 0`, and for `‖q‖ < 1` the theta product is holomorphic on `ℂ \ {0}` with derivative
  `-(∏_{n ≥ 1} (1 - qⁿ))²` at `w = 1`.
* `TauCeti.qTheta_eq_mul_tprod_mul_tprod`: `θ_q(w)` is `1 - w` times its two half products.
* `TauCeti.differentiable_qTheta_exp`, `TauCeti.hasDerivAt_qTheta_exp_zero`: for `‖q‖ < 1`,
  `z ↦ θ_q(e^{2π i z})` is entire, with derivative `-2π i (∏_{n ≥ 1} (1 - qⁿ))²` at `z = 0`.
* `TauCeti.qTheta_neg_one`, `TauCeti.qTheta_sq_self`: `θ_q(-1) = 2 (∏_{n ≥ 1} (1 + qⁿ))²` and
  `θ_{s²}(s) = (∏_{n ≥ 0} (1 - s^{2n+1}))²`.
* `TauCeti.qTheta_pow_three_self_mul`, `TauCeti.qTheta_mul_tprod_of_sq_add_add_one_eq_zero`:
  `θ_{s³}(s) ∏_{n ≥ 1} (1 - s^{3n}) = ∏_{n ≥ 1} (1 - sⁿ)`, and
  `θ_q(ω) ∏_{n ≥ 1} (1 - qⁿ) = (1 - ω) ∏_{n ≥ 1} (1 - q^{3n})` for a primitive cube root of
  unity `ω`.
* `TauCeti.tprod_one_sub_pow_eq_tprod_one_sub_pow_odd_mul`,
  `TauCeti.tprod_one_add_pow_mul_tprod_one_sub_pow`: the Euler function `∏_{n ≥ 1} (1 - qⁿ)` is
  `∏_{n ≥ 0} (1 - q^{2n+1}) ∏_{n ≥ 1} (1 - q^{2n})`, and multiplying it by `∏_{n ≥ 1} (1 + qⁿ)`
  gives `∏_{n ≥ 1} (1 - q^{2n})`.
* `TauCeti.tprod_one_add_pow_mul_tprod_one_sub_pow_odd`: **Euler's identity**
  `∏_{n ≥ 1} (1 + qⁿ) ∏_{n ≥ 0} (1 - q^{2n+1}) = 1` for `‖q‖ < 1`, the analytic form of the
  equinumerosity of partitions into distinct parts and into odd parts.
* `TauCeti.tprod_one_sub_pow_odd_ne_zero`: `∏_{n ≥ 0} (1 - q^{2n+1}) ≠ 0` for `‖q‖ < 1`.
* `TauCeti.tprod_one_sub_div_one_add_pow`, `TauCeti.tprod_one_sub_div_one_add_pow_eq_div`: the
  ratio product `∏_{n ≥ 1} (1 - qⁿ) / (1 + qⁿ)` splits as
  `(∏_{n ≥ 1} (1 - qⁿ)) / ∏_{n ≥ 1} (1 + qⁿ)` and equals
  `(∏_{n ≥ 0} (1 - q^{2n+1}))² ∏_{n ≥ 1} (1 - q^{2n})`.
* `TauCeti.hasDerivAt_tprod_one_sub_pow_odd`: the odd product `∏_{n ≥ 0} (1 - s^{2n+1})` has
  derivative `-1` at `s = 0`.
* `TauCeti.tendsto_tprod_one_sub_pow_odd_pow_sub_neg_div`: for `P(s) = ∏_{n ≥ 0} (1 - s^{2n+1})`,
  `(P(s)ᵏ - P(-s)ᵏ) / s → -2k` as `s → 0`.
* `TauCeti.tendsto_tprod_one_sub_qParam_pow_odd_pow`: `P(q)ᵏ → 1` at `i∞`, for
  `q = e^{2π i τ}` on the upper half-plane.
* `TauCeti.multipliable_one_sub_mul_pow`, `TauCeti.tendsto_qPochhammer_atTop`: for `‖q‖ < 1` the
  infinite q-Pochhammer product `(z; q)_∞ = ∏_{n ≥ 0} (1 - z qⁿ)` converges, and is the limit of
  the finite products `(z; q)_N` (`TauCeti.qPochhammer`); these do not vanish when `‖z‖ < 1`
  (`TauCeti.qPochhammer_ne_zero_of_norm_lt_one`).
* `TauCeti.tprod_one_sub_mul_pow_eq_qPochhammer_mul`: for `‖q‖ < 1` the infinite product splits
  as `(z; q)_∞ = (z; q)_N (z q^N; q)_∞`.
* `TauCeti.hasSum_tprod_one_sub_mul_pow`, `TauCeti.hasSum_inv_tprod_one_sub_mul_pow`: **Euler's
  expansions** `(z; q)_∞ = ∑_{k ≥ 0} (-1)ᵏ q^{k(k-1)/2} zᵏ / (q; q)_k` for every `z`, and
  `1 / (z; q)_∞ = ∑_{k ≥ 0} zᵏ / (q; q)_k` for `‖z‖ < 1`, the latter absolutely convergent
  (`TauCeti.summable_norm_pow_div_qPochhammer`). Both follow from the q-difference equation
  `F(z) = (1 - z) F(z q)` of `F = (z; q)_∞`, iterated towards `z = 0`.
* `TauCeti.hasProdLocallyUniformlyOn_one_sub_pow_mul`: for `q` and `w` continuous on an open set
  `U` with `‖q‖ < 1` there, `∏_{n ≥ 1} (1 - q(τ)ⁿ w(τ))` converges locally uniformly on `U`.
* `TauCeti.differentiableOn_tprod_one_sub_pow_mul`: for `q` and `w` holomorphic on such a `U`,
  so is this product.
-/

public section

namespace TauCeti

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜]

/-- For `‖q‖ < 1` the norms `‖qⁿ⁺¹ w‖` are summable. -/
theorem summable_norm_pow_succ_mul {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Summable fun n : ℕ ↦ ‖q ^ (n + 1) * w‖ := by
  simpa [norm_pow, pow_succ, mul_assoc] using
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right (‖q‖ * ‖w‖)

/-- For `‖q‖ < 1`, `∑_{n ≥ 1} ‖qⁿ w‖ = ‖q‖ ‖w‖ / (1 - ‖q‖)`. -/
theorem tsum_norm_pow_succ_mul {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    ∑' n : ℕ, ‖q ^ (n + 1) * w‖ = ‖q‖ * ‖w‖ / (1 - ‖q‖) := by
  simp only [norm_mul, norm_pow, pow_succ]
  rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one (norm_nonneg q) hq]
  ring

/-- For `‖q‖ < 1`, `‖∏_{n ≥ 1} (1 - qⁿ w)‖ ≤ exp (‖q‖ ‖w‖ / (1 - ‖q‖))`. -/
theorem norm_tprod_one_sub_pow_mul_le {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    ‖∏' n : ℕ, (1 - q ^ (n + 1) * w)‖ ≤ Real.exp (‖q‖ * ‖w‖ / (1 - ‖q‖)) := by
  have h := norm_tprod_one_add_le_exp_tsum (f := fun n : ℕ ↦ -(q ^ (n + 1) * w))
    (by simpa only [norm_neg] using summable_norm_pow_succ_mul hq w)
  simpa only [← sub_eq_add_neg, norm_neg, tsum_norm_pow_succ_mul hq] using h

/-- For `‖q‖ < 1`, `‖∏_{n ≥ 1} (1 - qⁿ w) - 1‖ ≤ exp (‖q‖ ‖w‖ / (1 - ‖q‖)) - 1`. -/
theorem norm_tprod_one_sub_pow_mul_sub_one_le {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    ‖∏' n : ℕ, (1 - q ^ (n + 1) * w) - 1‖ ≤ Real.exp (‖q‖ * ‖w‖ / (1 - ‖q‖)) - 1 := by
  have h := norm_tprod_one_add_sub_one_le (f := fun n : ℕ ↦ -(q ^ (n + 1) * w))
    (by simpa only [norm_neg] using summable_norm_pow_succ_mul hq w)
  simpa only [← sub_eq_add_neg, norm_neg, tsum_norm_pow_succ_mul hq] using h

/-- For `‖q‖ < 1/2`, `‖∏_{n ≥ 1} (1 + qⁿ) - 1‖ ≤ ‖q‖ / (1 - 2‖q‖)`. -/
theorem norm_tprod_one_add_pow_sub_one_le {q : 𝕜} (hq : 2 * ‖q‖ < 1) :
    ‖∏' n : ℕ, (1 + q ^ (n + 1)) - 1‖ ≤ ‖q‖ / (1 - 2 * ‖q‖) := by
  set A := ‖q‖
  have hA : 0 ≤ A := norm_nonneg q
  have h₁ : 0 < 1 - 2 * A := by linarith
  have h := norm_tprod_one_sub_pow_mul_sub_one_le (by linarith : A < 1) (-1)
  simp only [mul_neg, mul_one, sub_neg_eq_add, norm_neg, norm_one] at h
  -- `e^y ≤ 1 / (1 - y)` with `y = A / (1 - A)`, and `1 / (1 - y) - 1 = A / (1 - 2A)`.
  have hy : A / (1 - A) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hexp := Real.exp_bound_div_one_sub_of_interval (div_nonneg hA (by linarith)) hy
  have heq : 1 / (1 - A / (1 - A)) - 1 = A / (1 - 2 * A) := by
    have h₂ : 1 - A / (1 - A) = (1 - 2 * A) / (1 - A) := by
      field_simp [show 1 - A ≠ 0 by linarith]
      ring
    rw [h₂, one_div_div, div_sub_one h₁.ne']
    ring
  linarith

/-- The **theta product** `θ_q(w) = (w; q)_∞ (q w⁻¹; q)_∞`, written as
`(1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)`. The product converges for `‖q‖ < 1`; otherwise the
value is a junk value. With `q = e^{2π i τ}` and `w = e^{2π i (r₁ τ + r₂)}` it is the product in
the Siegel function `g_r(τ)`. -/
noncomputable def qTheta (q w : 𝕜) : 𝕜 :=
  (1 - w) * ∏' n : ℕ, (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹)

/-- The defining product of the theta product `θ_q(w)`. -/
theorem qTheta_def (q w : 𝕜) :
    qTheta q w = (1 - w) * ∏' n : ℕ, (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹) :=
  (rfl)

/-- The theta product vanishes at `w = 1`. -/
@[simp]
theorem qTheta_one (q : 𝕜) : qTheta q 1 = 0 := by
  simp [qTheta_def]

variable [CompleteSpace 𝕜]

/-- For `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w)` converges. -/
theorem multipliable_one_sub_pow_mul {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) * w :=
  multipliable_one_sub_of_summable (summable_norm_pow_succ_mul hq w)

omit [CompleteSpace 𝕜] in
/-- The product `∏_{n ≥ 1} (1 - qⁿ w)` tends to `1` whenever `q → 0` and `q w → 0`.
The argument `w` itself need not converge or remain bounded. -/
theorem tendsto_tprod_one_sub_pow_mul {α : Type*} {l : Filter α} {q w : α → 𝕜}
    (hq : Filter.Tendsto q l (nhds 0))
    (hqw : Filter.Tendsto (fun x ↦ q x * w x) l (nhds 0)) :
    Filter.Tendsto (fun x ↦ ∏' n : ℕ, (1 - q x ^ (n + 1) * w x)) l (nhds 1) := by
  have hsmall : ∀ᶠ x in l, ‖q x‖ < 1 := hq.norm.eventually (gt_mem_nhds (by norm_num))
  have hqnorm : Filter.Tendsto (fun x ↦ ‖q x‖) l (nhds 0) := by simpa using hq.norm
  have hqwnorm : Filter.Tendsto (fun x ↦ ‖q x * w x‖) l (nhds 0) := by
    simpa using hqw.norm
  have hbound : Filter.Tendsto
      (fun x ↦ Real.exp (‖q x * w x‖ / (1 - ‖q x‖)) - 1) l (nhds 0) := by
    have hdiv := hqwnorm.div (tendsto_const_nhds.sub hqnorm)
      (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa using ((Real.continuous_exp.tendsto _).comp hdiv).sub_const 1
  refine tendsto_iff_norm_sub_tendsto_zero.mpr <|
    squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hbound
  filter_upwards [hsmall] with x hx
  have h := norm_tprod_one_add_sub_one_le (f := fun n : ℕ ↦ -(q x ^ (n + 1) * w x))
    (by simpa only [norm_neg] using summable_norm_pow_succ_mul hx (w x))
  simp only [← sub_eq_add_neg, norm_neg, norm_mul, norm_pow, pow_succ] at h
  rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one (norm_nonneg _) hx] at h
  convert h using 1
  · simp only [pow_succ]
  · rw [norm_mul]
    congr 2
    ring

/-- Shifting the product: `∏_{n ≥ 1} (1 - qⁿ w) = (1 - q w) ∏_{n ≥ 1} (1 - qⁿ (q w))`. -/
theorem tprod_one_sub_pow_mul_eq {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    ∏' n : ℕ, (1 - q ^ (n + 1) * w) = (1 - q * w) * ∏' n : ℕ, (1 - q ^ (n + 1) * (q * w)) := by
  rw [tprod_eq_zero_mul' (by simpa [pow_succ, mul_assoc] using
    multipliable_one_sub_pow_mul hq (q * w))]
  simp [pow_succ, mul_assoc]

/-- Shifting the product with an inverted argument:
`∏_{n ≥ 1} (1 - qⁿ (q w)⁻¹) = (1 - w⁻¹) ∏_{n ≥ 1} (1 - qⁿ w⁻¹)` for `q ≠ 0`. -/
theorem tprod_one_sub_pow_mul_inv_eq {q : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) (w : 𝕜) :
    ∏' n : ℕ, (1 - q ^ (n + 1) * (q * w)⁻¹) = (1 - w⁻¹) * ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹) := by
  have h : ∀ n : ℕ, q ^ (n + 1) * (q * w)⁻¹ = q ^ n * w⁻¹ := fun n ↦ by
    rw [mul_inv, pow_succ]
    field_simp
  simp_rw [h]
  rw [tprod_eq_zero_mul' (f := fun n ↦ 1 - q ^ n * w⁻¹) (multipliable_one_sub_pow_mul hq w⁻¹)]
  simp

omit [CompleteSpace 𝕜] in
/-- If the factors `1 - qⁿ⁺¹ w` are nonzero, so is `∏_{n ≥ 1} (1 - qⁿ w)`. If the product is not
multipliable, it is `1` by convention. -/
theorem tprod_one_sub_pow_mul_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) {w : 𝕜}
    (h : ∀ n : ℕ, 1 - q ^ (n + 1) * w ≠ 0) : ∏' n : ℕ, (1 - q ^ (n + 1) * w) ≠ 0 := by
  by_cases hm : Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) * w
  swap
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero
  intro h0
  -- transport the product along the isometric embedding of `𝕜` into its completion
  let ι : 𝕜 →+* UniformSpace.Completion 𝕜 := UniformSpace.Completion.coeRingHom
  have hι : Continuous ι := UniformSpace.Completion.continuous_coe 𝕜
  have hmap := (hm.hasProd.map ι hι).tprod_eq
  rw [Function.comp_def, h0, map_zero] at hmap
  refine tprod_one_add_ne_zero_of_summable
    (f := fun n : ℕ ↦ -(ι q ^ (n + 1) * ι w)) (fun n ↦ ?_) ?_ ?_
  · rw [← sub_eq_add_neg, ← map_pow, ← map_mul, ← map_one ι, ← map_sub]
    exact (map_ne_zero ι).2 (h n)
  · have hnorm : ∀ x : 𝕜, ‖ι x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
    simpa only [norm_neg, ← map_pow, ← map_mul, hnorm] using summable_norm_pow_succ_mul hq w
  · convert hmap using 3 with n
    simp [ι, sub_eq_add_neg]

omit [CompleteSpace 𝕜] in
/-- For `‖q‖ < 1` the Euler function `∏_{n ≥ 1} (1 - qⁿ)` is nonzero. -/
theorem tprod_one_sub_pow_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) : ∏' n : ℕ, (1 - q ^ (n + 1)) ≠ 0 := by
  refine (tprod_congr fun n ↦ by rw [mul_one]).symm.trans_ne
    (tprod_one_sub_pow_mul_ne_zero hq (w := 1) fun n h ↦ ?_)
  have h1 := norm_pow_lt_one hq n.succ_ne_zero
  rw [mul_one, sub_eq_zero] at h
  simp [← h] at h1

/-- For `‖q‖ < 1` the product `∏_{n ≥ 1} (1 + qⁿ)` converges. -/
theorem multipliable_one_add_pow {q : 𝕜} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + q ^ (n + 1) := by
  simpa using multipliable_one_sub_pow_mul hq (-1)

/-- For `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)` in the theta product
converges. -/
theorem multipliable_qTheta {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Multipliable fun n : ℕ ↦ (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹) :=
  (multipliable_one_sub_pow_mul hq w).mul (multipliable_one_sub_pow_mul hq w⁻¹)

/-- For `‖q‖ < 1` the theta product `θ_q(w)` is `1 - w` times its two half products
`∏_{n ≥ 1} (1 - qⁿ w)` and `∏_{n ≥ 1} (1 - qⁿ w⁻¹)`. -/
theorem qTheta_eq_mul_tprod_mul_tprod {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    qTheta q w = (1 - w) *
      ((∏' n : ℕ, (1 - q ^ (n + 1) * w)) * ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹)) := by
  rw [qTheta_def, (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _)]

omit [CompleteSpace 𝕜] in
/-- For `‖q‖ < 1` the theta product is bounded by
`‖θ_q(w)‖ ≤ ‖1 - w‖ exp (‖q‖ (‖w‖ + ‖w‖⁻¹) / (1 - ‖q‖))`. -/
theorem norm_qTheta_le {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    ‖qTheta q w‖ ≤ ‖1 - w‖ * Real.exp (‖q‖ * (‖w‖ + ‖w‖⁻¹) / (1 - ‖q‖)) := by
  rw [qTheta_def, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  by_cases hm : Multipliable fun n : ℕ ↦ (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹)
  swap
  · rw [tprod_eq_one_of_not_multipliable hm, norm_one]
    exact Real.one_le_exp (div_nonneg (by positivity) (sub_nonneg.2 hq.le))
  -- transport the product along the isometric embedding of `𝕜` into its completion
  let ι : 𝕜 →+* UniformSpace.Completion 𝕜 := UniformSpace.Completion.coeRingHom
  have hι : Continuous ι := UniformSpace.Completion.continuous_coe 𝕜
  have hnorm : ∀ x : 𝕜, ‖ι x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
  have hq' : ‖ι q‖ < 1 := by rwa [hnorm]
  have hmap := (hm.hasProd.map ι hι).tprod_eq
  simp only [Function.comp_def, map_mul, map_sub, map_one, map_pow, map_inv₀] at hmap
  rw [← hnorm, ← hmap,
    (multipliable_one_sub_pow_mul hq' _).tprod_mul (multipliable_one_sub_pow_mul hq' _),
    norm_mul, mul_add, add_div, Real.exp_add]
  have hw := norm_tprod_one_sub_pow_mul_le hq' (ι w)
  have hw' := norm_tprod_one_sub_pow_mul_le hq' (ι w)⁻¹
  simp only [norm_inv, hnorm] at hw hw' ⊢
  exact mul_le_mul hw hw' (norm_nonneg _) (Real.exp_pos _).le

omit [CompleteSpace 𝕜] in
/-- For `‖q‖ < 1` the theta product `θ_q(w)` is nonzero when `w` is not an integral power of
`q`. If the defining product is not multipliable, it is `1` by convention. -/
theorem qTheta_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) {w : 𝕜} (hw : ∀ k : ℤ, w ≠ q ^ k) :
    qTheta q w ≠ 0 := by
  rw [qTheta_def]
  refine mul_ne_zero (sub_ne_zero.mpr fun h ↦ hw 0 (by simp [← h])) ?_
  by_cases hm : Multipliable fun n : ℕ ↦ (1 - q ^ (n + 1) * w) * (1 - q ^ (n + 1) * w⁻¹)
  swap
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero
  have h₁ : ∀ n : ℕ, 1 - q ^ (n + 1) * w ≠ 0 := fun n h ↦ hw (-(n + 1 : ℕ)) (by
    rw [zpow_neg, zpow_natCast]
    exact eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h).symm)
  have h₂ : ∀ n : ℕ, 1 - q ^ (n + 1) * w⁻¹ ≠ 0 := fun n h ↦ hw (n + 1 : ℕ) (by
    rw [zpow_natCast, ← inv_inj]
    exact eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h).symm)
  intro h0
  -- transport the product along the isometric embedding of `𝕜` into its completion
  let ι : 𝕜 →+* UniformSpace.Completion 𝕜 := UniformSpace.Completion.coeRingHom
  have hι : Continuous ι := UniformSpace.Completion.continuous_coe 𝕜
  have hq' : ‖ι q‖ < 1 := by
    have hnorm : ∀ x : 𝕜, ‖ι x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
    rwa [hnorm]
  have hmap := (hm.hasProd.map ι hι).tprod_eq
  rw [Function.comp_def, h0, map_zero] at hmap
  simp only [map_mul, map_sub, map_one, map_pow, map_inv₀] at hmap
  rw [(multipliable_one_sub_pow_mul hq' _).tprod_mul (multipliable_one_sub_pow_mul hq' _)] at hmap
  rcases mul_eq_zero.1 hmap with h | h
  · refine tprod_one_sub_pow_mul_ne_zero hq' (fun n ↦ ?_) h
    simpa only [map_mul, map_sub, map_one, map_pow] using (map_ne_zero ι).2 (h₁ n)
  · refine tprod_one_sub_pow_mul_ne_zero hq' (fun n ↦ ?_) h
    simpa only [map_mul, map_sub, map_one, map_pow, map_inv₀] using (map_ne_zero ι).2 (h₂ n)

/-- **Quasi-periodicity of the theta product**: `θ_q(q w) = -w⁻¹ θ_q(w)` for `0 < ‖q‖ < 1` and
`w ≠ 0`. -/
theorem qTheta_mul_left {q : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) {w : 𝕜} (hw : w ≠ 0) :
    qTheta q (q * w) = -w⁻¹ * qTheta q w := by
  rw [qTheta_def, qTheta_def,
    (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _),
    (multipliable_one_sub_pow_mul hq _).tprod_mul (multipliable_one_sub_pow_mul hq _),
    tprod_one_sub_pow_mul_inv_eq hq hq₀, tprod_one_sub_pow_mul_eq hq w]
  field_simp
  ring

/-- For `‖q‖ < 1` the product `∏_{n ≥ 0} (1 - q^{2n+1})` over the odd powers of `q` converges. -/
theorem multipliable_one_sub_pow_odd {q : 𝕜} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (2 * n + 1) := by
  refine multipliable_one_sub_of_summable ?_
  exact ((summable_geometric_of_lt_one (norm_nonneg _) (norm_pow_lt_one hq two_ne_zero)).mul_left
    ‖q‖).congr fun n ↦ by
      simp only [norm_pow]
      ring

/-- For `‖q‖ < 1` the product `∏_{n ≥ 0} (1 + q^{2n+1})` over the odd powers of `q` converges. -/
theorem multipliable_one_add_pow_odd {q : 𝕜} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + q ^ (2 * n + 1) :=
  (multipliable_one_sub_pow_odd (q := -q) (by rwa [norm_neg])).congr (one_sub_neg_pow_odd q)

/-- `∏_{n ≥ 0} (1 - q^{2n+1}) ∏_{n ≥ 0} (1 + q^{2n+1}) = ∏_{n ≥ 0} (1 - (q²)^{2n+1})` for
`‖q‖ < 1`. -/
theorem tprod_one_sub_pow_odd_mul_tprod_one_add_pow_odd {q : 𝕜} (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * ∏' n : ℕ, (1 + q ^ (2 * n + 1)) =
      ∏' n : ℕ, (1 - (q ^ 2) ^ (2 * n + 1)) := by
  rw [← (multipliable_one_sub_pow_odd hq).tprod_mul (multipliable_one_add_pow_odd hq)]
  exact tprod_congr fun n ↦ by ring

/-- The Euler product `∏_{n ≥ 1} (1 - qⁿ)` split into its odd and even factors:
`∏_{n ≥ 1} (1 - qⁿ) = ∏_{n ≥ 0} (1 - q^{2n+1}) ∏_{n ≥ 1} (1 - q^{2n})` for `‖q‖ < 1`. -/
theorem tprod_one_sub_pow_eq_tprod_one_sub_pow_odd_mul {q : 𝕜} (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - q ^ (n + 1)) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
  have hP₂ : Multipliable fun n : ℕ ↦ 1 - (q ^ 2) ^ (n + 1) := by
    simpa using multipliable_one_sub_pow_mul (norm_pow_lt_one hq two_ne_zero) 1
  rw [← tprod_even_mul_odd (f := fun n ↦ 1 - q ^ (n + 1))
    (multipliable_one_sub_pow_odd hq) (by simpa [← pow_mul, mul_add] using hP₂)]
  simp [← pow_mul, mul_add]

/-- `∏_{n ≥ 1} (1 + qⁿ) ∏_{n ≥ 1} (1 - qⁿ) = ∏_{n ≥ 1} (1 - q^{2n})` for `‖q‖ < 1`. -/
theorem tprod_one_add_pow_mul_tprod_one_sub_pow {q : 𝕜} (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 + q ^ (n + 1))) * ∏' n : ℕ, (1 - q ^ (n + 1)) =
      ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
  rw [← (multipliable_one_add_pow hq).tprod_mul (by simpa using multipliable_one_sub_pow_mul hq 1)]
  exact tprod_congr fun n ↦ by ring

/-- **Euler's identity** `∏_{n ≥ 1} (1 + qⁿ) ∏_{n ≥ 0} (1 - q^{2n+1}) = 1` for `‖q‖ < 1`. Comparing
coefficients, partitions into distinct parts and partitions into odd parts are equinumerous. -/
theorem tprod_one_add_pow_mul_tprod_one_sub_pow_odd {q : 𝕜} (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 + q ^ (n + 1))) * ∏' n : ℕ, (1 - q ^ (2 * n + 1)) = 1 := by
  have hmul := tprod_one_add_pow_mul_tprod_one_sub_pow hq
  rw [tprod_one_sub_pow_eq_tprod_one_sub_pow_odd_mul hq, ← mul_assoc] at hmul
  exact mul_right_cancel₀ (tprod_one_sub_pow_ne_zero (norm_pow_lt_one hq two_ne_zero))
    (hmul.trans (one_mul _).symm)

/-- For `‖q‖ < 1` the product `∏_{n ≥ 0} (1 - q^{2n+1})` over the odd powers of `q` does not
vanish: by Euler's identity it is the inverse of `∏_{n ≥ 1} (1 + qⁿ)`. -/
theorem tprod_one_sub_pow_odd_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - q ^ (2 * n + 1)) ≠ 0 :=
  right_ne_zero_of_mul_eq_one (tprod_one_add_pow_mul_tprod_one_sub_pow_odd hq)

/-- For `‖q‖ < 1` in a complete normed field,
`∏_{n ≥ 1} (1 - qⁿ) / (1 + qⁿ) = (∏_{n ≥ 1} (1 - qⁿ)) / ∏_{n ≥ 1} (1 + qⁿ)`. -/
theorem tprod_one_sub_div_one_add_pow_eq_div {q : 𝕜} (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1)) =
      (∏' n : ℕ, (1 - q ^ (n + 1))) / ∏' n : ℕ, (1 + q ^ (n + 1)) := by
  have hm₁ : Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) := by
    simpa using multipliable_one_sub_pow_mul hq 1
  have hP0 : ∏' n : ℕ, (1 + q ^ (n + 1)) ≠ 0 :=
    left_ne_zero_of_mul_eq_one (tprod_one_add_pow_mul_tprod_one_sub_pow_odd hq)
  exact hm₁.tprod_div₀ (multipliable_one_add_pow hq) hP0

/-- For `‖q‖ < 1` in a complete normed field, the ratio product
`∏_{n ≥ 1} (1 - qⁿ) / (1 + qⁿ)` equals
`(∏_{n ≥ 0} (1 - q^{2n+1}))² ∏_{n ≥ 1} (1 - q^{2n})`. -/
theorem tprod_one_sub_div_one_add_pow {q : 𝕜} (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1)) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
  have heuler := tprod_one_add_pow_mul_tprod_one_sub_pow_odd hq
  rw [tprod_one_sub_div_one_add_pow_eq_div hq, div_eq_mul_inv,
    inv_eq_of_mul_eq_one_right heuler, tprod_one_sub_pow_eq_tprod_one_sub_pow_odd_mul hq]
  ring

/-- The theta product at `w = -1`: `θ_q(-1) = 2 (∏_{n ≥ 1} (1 + qⁿ))²` for `‖q‖ < 1`. -/
theorem qTheta_neg_one {q : 𝕜} (hq : ‖q‖ < 1) :
    qTheta q (-1) = 2 * (∏' n : ℕ, (1 + q ^ (n + 1))) ^ 2 := by
  rw [qTheta_def, sq, ← (multipliable_one_add_pow hq).tprod_mul (multipliable_one_add_pow hq)]
  norm_num

/-- The theta product with nome the square of its argument:
`θ_{s²}(s) = (∏_{n ≥ 0} (1 - s^{2n+1}))²` for `‖s‖ < 1`. -/
theorem qTheta_sq_self {s : 𝕜} (hs : ‖s‖ < 1) :
    qTheta (s ^ 2) s = (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ 2 := by
  rcases eq_or_ne s 0 with rfl | hs₀
  · simp [qTheta_def]
  have hs2 := norm_pow_lt_one hs two_ne_zero
  rw [qTheta_def, (multipliable_one_sub_pow_mul hs2 _).tprod_mul
    (multipliable_one_sub_pow_mul hs2 _), ← mul_assoc]
  have hf : Multipliable fun n : ℕ ↦ 1 - s ^ (2 * (n + 1) + 1) :=
    (multipliable_one_sub_pow_mul hs2 s).congr fun n ↦ by ring
  -- The factors `1 - s^{2n+1}` with `n ≥ 1`, together with `1 - s`.
  have h₁ : (1 - s) * ∏' n : ℕ, (1 - (s ^ 2) ^ (n + 1) * s) =
      ∏' n : ℕ, (1 - s ^ (2 * n + 1)) := by
    rw [tprod_eq_zero_mul' (f := fun n ↦ 1 - s ^ (2 * n + 1)) hf]
    exact congrArg₂ (· * ·) (by norm_num) (tprod_congr fun n ↦ by ring)
  -- The factors `1 - s^{2n+1}` with `n ≥ 0`, from `s^{2n+2} s⁻¹ = s^{2n+1}`.
  have h₂ : ∏' n : ℕ, (1 - (s ^ 2) ^ (n + 1) * s⁻¹) = ∏' n : ℕ, (1 - s ^ (2 * n + 1)) :=
    tprod_congr fun n ↦ by
      field_simp
      ring
  rw [h₁, h₂, sq]

/-- The theta product with nome the cube of its argument, times the Euler function of the nome, is
the Euler function of the argument: `θ_{s³}(s) ∏_{n ≥ 1} (1 - s^{3n}) = ∏_{n ≥ 1} (1 - sⁿ)` for
`‖s‖ < 1`. -/
theorem qTheta_pow_three_self_mul {s : 𝕜} (hs : ‖s‖ < 1) :
    qTheta (s ^ 3) s * ∏' n : ℕ, (1 - (s ^ 3) ^ (n + 1)) = ∏' n : ℕ, (1 - s ^ (n + 1)) := by
  rcases eq_or_ne s 0 with rfl | hs₀
  · simp [qTheta_def]
  have hs3 := norm_pow_lt_one hs three_ne_zero
  -- The factors `1 - sᵐ` sorted by the residue of `m` modulo `3`.
  have h₁ : Multipliable fun n : ℕ ↦ 1 - s ^ (3 * n + 1) :=
    (multipliable_one_sub_pow_mul hs3 (s ^ 2)⁻¹).congr fun n ↦ by
      rw [← pow_mul, show 3 * (n + 1) = 3 * n + 1 + 2 by ring, pow_add,
        mul_inv_cancel_right₀ (pow_ne_zero 2 hs₀)]
  have h₂ : ∀ n : ℕ, 1 - (s ^ 3) ^ (n + 1) * s⁻¹ = 1 - s ^ (3 * n + 2) := fun n ↦ by
    rw [← pow_mul, show 3 * (n + 1) = 3 * n + 2 + 1 by ring, pow_succ, mul_inv_cancel_right₀ hs₀]
  have h₃ : ∀ n : ℕ, 1 - (s ^ 3) ^ (n + 1) = 1 - s ^ (3 * n + 3) := fun n ↦ by ring
  have hsplit : ∏' n : ℕ, (1 - s ^ (n + 1)) =
      ∏' n : ℕ, (1 - s ^ (3 * n + 1)) * (1 - s ^ (3 * n + 2)) * (1 - s ^ (3 * n + 3)) := by
    have hf : Multipliable fun n : ℕ ↦ 1 - s ^ (n + 1) := by
      simpa using multipliable_one_sub_pow_mul hs 1
    rw [← (hf.hasProd.prod_fin_mul_add_nat 3).tprod_eq]
    exact tprod_congr fun n ↦ by
      simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
      ring_nf
  -- `(1 - s) ∏_{n ≥ 1} (1 - s^{3n+1}) = ∏_{n ≥ 0} (1 - s^{3n+1})`.
  have h₄ : (1 - s) * ∏' n : ℕ, (1 - (s ^ 3) ^ (n + 1) * s) = ∏' n : ℕ, (1 - s ^ (3 * n + 1)) := by
    rw [tprod_eq_zero_mul' (f := fun n ↦ 1 - s ^ (3 * n + 1))
      (by simpa only [← pow_mul, ← pow_succ] using multipliable_one_sub_pow_mul hs3 s)]
    exact congrArg₂ (· * ·) (by norm_num) (tprod_congr fun n ↦ by ring)
  -- The three residue-class products multiply to the product of the blockwise factors.
  have hgroup : (∏' n : ℕ, (1 - s ^ (3 * n + 1))) * (∏' n : ℕ, (1 - s ^ (3 * n + 2))) *
      ∏' n : ℕ, (1 - s ^ (3 * n + 3)) =
      ∏' n : ℕ, (1 - s ^ (3 * n + 1)) * (1 - s ^ (3 * n + 2)) * (1 - s ^ (3 * n + 3)) := by
    have hm₂ := (multipliable_one_sub_pow_mul hs3 s⁻¹).congr h₂
    have hm₃ := (multipliable_one_sub_pow_mul hs3 1).congr fun n ↦ by rw [mul_one, h₃]
    rw [← h₁.tprod_mul hm₂, ← (h₁.mul hm₂).tprod_mul hm₃]
  rw [hsplit, ← hgroup, qTheta_def, (multipliable_one_sub_pow_mul hs3 _).tprod_mul
    (multipliable_one_sub_pow_mul hs3 _), ← mul_assoc, h₄, tprod_congr h₂, tprod_congr h₃]

/-- The theta product at a primitive cube root of unity, times the Euler function of the nome: if
`ω² + ω + 1 = 0` then `θ_q(ω) ∏_{n ≥ 1} (1 - qⁿ) = (1 - ω) ∏_{n ≥ 1} (1 - q^{3n})` for
`‖q‖ < 1`. -/
theorem qTheta_mul_tprod_of_sq_add_add_one_eq_zero {q ω : 𝕜} (hq : ‖q‖ < 1)
    (hω : ω ^ 2 + ω + 1 = 0) :
    qTheta q ω * ∏' n : ℕ, (1 - q ^ (n + 1)) = (1 - ω) * ∏' n : ℕ, (1 - (q ^ 3) ^ (n + 1)) := by
  have hinv : ω⁻¹ = -1 - ω := inv_eq_of_mul_eq_one_right (by linear_combination -hω)
  rw [qTheta_def, mul_assoc, ← (multipliable_qTheta hq ω).tprod_mul
    (by simpa using multipliable_one_sub_pow_mul hq 1)]
  -- Each factor is `(1 - x ω)(1 - x ω²)(1 - x) = 1 - x³` with `x = qⁿ`.
  exact congrArg₂ (· * ·) rfl (tprod_congr fun n ↦ by
    rw [hinv]
    linear_combination (-(1 - q ^ (n + 1)) * (q ^ (n + 1)) ^ 2) * hω)

section EulerExpansions

/-! ### Euler's expansions of `(z; q)_∞` and `1 / (z; q)_∞` -/

open Filter Topology

omit [CompleteSpace 𝕜] in
/-- For `‖x‖ < 1` and `‖q‖ ≤ 1` no factor of the finite q-Pochhammer product `(x; q)_n`
vanishes, so neither does the product. -/
theorem qPochhammer_ne_zero_of_norm_lt_one {x q : 𝕜} (hx : ‖x‖ < 1) (hq : ‖q‖ ≤ 1)
    (n : ℕ) : qPochhammer x q n ≠ 0 := by
  rw [Ne, qPochhammer_eq_zero_iff]
  rintro ⟨i, -, h⟩
  have h₁ : ‖x * q ^ i‖ < 1 := by
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg x) (pow_le_one₀ (norm_nonneg q) hq)).trans_lt hx
  exact one_sub_ne_zero_of_norm_lt_one h₁ (sub_eq_zero.2 h.symm)

/-- For `‖q‖ < 1` the infinite q-Pochhammer product `(z; q)_∞ = ∏_{n ≥ 0} (1 - z qⁿ)`
converges. -/
theorem multipliable_one_sub_mul_pow {q : 𝕜} (hq : ‖q‖ < 1) (z : 𝕜) :
    Multipliable fun n : ℕ ↦ 1 - z * q ^ n :=
  multipliable_one_sub_of_summable <| by
    simpa [norm_pow] using (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖z‖

/-- For `‖q‖ < 1` the finite q-Pochhammer products `(z; q)_N` tend to `(z; q)_∞` as `N → ∞`. -/
theorem tendsto_qPochhammer_atTop {q : 𝕜} (hq : ‖q‖ < 1) (z : 𝕜) :
    Tendsto (qPochhammer z q) atTop (𝓝 (∏' n : ℕ, (1 - z * q ^ n))) :=
  (multipliable_one_sub_mul_pow hq z).tendsto_prod_tprod_nat.congr fun N ↦
    (qPochhammer_def z q N).symm

/-- For `‖q‖ < 1` the infinite q-Pochhammer product splits as
`(z; q)_∞ = (z; q)_N (z q^N; q)_∞`. -/
theorem tprod_one_sub_mul_pow_eq_qPochhammer_mul {q : 𝕜} (hq : ‖q‖ < 1) (z : 𝕜) (N : ℕ) :
    ∏' n : ℕ, (1 - z * q ^ n) = qPochhammer z q N * ∏' n : ℕ, (1 - z * q ^ N * q ^ n) := by
  have hm : Multipliable fun n : ℕ ↦ 1 - z * q ^ (n + N) :=
    (multipliable_one_sub_mul_pow hq (z * q ^ N)).congr fun n ↦ by ring
  rw [← Multipliable.prod_mul_tprod_nat_mul' (f := fun n : ℕ ↦ 1 - z * q ^ n) hm,
    qPochhammer_def]
  exact congrArg _ (tprod_congr fun n ↦ by ring)

omit [CompleteSpace 𝕜] in
/-- The ratio of consecutive terms of Euler's expansion of `(z; q)_∞`. -/
private theorem euler_term_succ {q : 𝕜} (hq : ‖q‖ < 1) (z : 𝕜) (k : ℕ) :
    (-1) ^ (k + 1) * q ^ (k + 1).choose 2 * z ^ (k + 1) / qPochhammer q q (k + 1) *
        (1 - q ^ (k + 1)) =
      -(z * q ^ k) * ((-1) ^ k * q ^ k.choose 2 * z ^ k / qPochhammer q q k) := by
  have hD := qPochhammer_ne_zero_of_norm_lt_one hq hq.le k
  have h₁ : 1 - q ^ (k + 1) ≠ 0 := one_sub_pow_ne_zero hq k.succ_ne_zero
  rw [qPochhammer_succ, Nat.choose_succ_succ, Nat.choose_one_right, ← pow_succ']
  field_simp
  ring

omit [CompleteSpace 𝕜] in
/-- The terms of Euler's expansion of `(z; q)_∞` are absolutely summable for `‖q‖ < 1`. -/
private theorem summable_norm_euler_term {q : 𝕜} (hq : ‖q‖ < 1) (z : 𝕜) :
    Summable fun k : ℕ ↦ ‖(-1) ^ k * q ^ k.choose 2 * z ^ k / qPochhammer q q k‖ := by
  have hq₁ : 0 < 1 - ‖q‖ := by linarith
  have ht : Tendsto (fun k : ℕ ↦ ‖z‖ / (1 - ‖q‖) * ‖q‖ ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul
      (‖z‖ / (1 - ‖q‖))
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
  have h := congrArg norm (euler_term_succ hq z k)
  rw [norm_mul, norm_mul, norm_neg, norm_mul, norm_pow] at h
  rw [norm_norm, norm_norm]
  have hpos := one_sub_norm_le_norm_one_sub_pow hq.le k.succ_ne_zero
  calc _ ≤ ‖z‖ * ‖q‖ ^ k / (1 - ‖q‖) * _ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hq₁, ← h]
        exact mul_le_mul_of_nonneg_left hpos (norm_nonneg _)
    _ ≤ 1 / 2 * _ :=
        mul_le_mul_of_nonneg_right (by rw [mul_div_right_comm]; exact hk.le) (norm_nonneg _)

/-- The series `F(z) = ∑_{k ≥ 0} (-1)ᵏ q^{k(k-1)/2} zᵏ / (q; q)_k` satisfies the q-difference
equation `F(z) = (1 - z) F(z q)` of `(z; q)_∞`. -/
private theorem tsum_euler_term_eq {q : 𝕜} (hq : ‖q‖ < 1) (z : 𝕜) :
    ∑' k : ℕ, (-1) ^ k * q ^ k.choose 2 * z ^ k / qPochhammer q q k =
      (1 - z) * ∑' k : ℕ, (-1) ^ k * q ^ k.choose 2 * (z * q) ^ k / qPochhammer q q k := by
  have hs := (summable_norm_euler_term hq (z * q)).of_norm
  refine ((hasSum_nat_add_iff' 1).mp ?_).tsum_eq
  convert ((hasSum_nat_add_iff' 1).mpr hs.hasSum).sub (hs.hasSum.mul_left z) using 1
  · funext k
    have e := euler_term_succ hq z k
    simp only [mul_pow]
    linear_combination e
  · simp
    ring

/-- **Euler's expansion** of the infinite q-Pochhammer product: for `‖q‖ < 1` and every `z`,
`(z; q)_∞ = ∏_{n ≥ 0} (1 - z qⁿ) = ∑_{k ≥ 0} (-1)ᵏ q^{k(k-1)/2} zᵏ / (q; q)_k`
(Gasper–Rahman, *Basic Hypergeometric Series*, (1.3.16)). -/
theorem hasSum_tprod_one_sub_mul_pow {q : 𝕜} (hq : ‖q‖ < 1) (z : 𝕜) :
    HasSum (fun k : ℕ ↦ (-1) ^ k * q ^ k.choose 2 * z ^ k / qPochhammer q q k)
      (∏' n : ℕ, (1 - z * q ^ n)) := by
  set a : ℕ → 𝕜 → 𝕜 := fun k z ↦ (-1) ^ k * q ^ k.choose 2 * z ^ k / qPochhammer q q k
  set f : 𝕜 → 𝕜 := fun z ↦ ∑' k, a k z
  -- `f` is continuous at `0`, where it takes the value `1`.
  have hcont : ContinuousAt f 0 := by
    refine (continuousOn_tsum (u := fun k ↦ ‖a k 1‖) (s := Metric.closedBall 0 1)
      (fun k ↦ by simp only [a]; fun_prop) (summable_norm_euler_term hq 1)
      fun k x hx ↦ ?_).continuousAt (Metric.closedBall_mem_nhds 0 one_pos)
    rw [mem_closedBall_zero_iff] at hx
    simp only [a, one_pow, mul_one, norm_div, norm_mul, norm_pow]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg x) hx)) (norm_nonneg _)
  have hf0 : f 0 = 1 := by
    simp only [f]
    rw [tsum_eq_single 0 fun k hk ↦ by simp [a, hk]]
    simp [a]
  have hfq (z : 𝕜) : f z = (1 - z) * f (z * q) := by
    simp only [f, a]
    exact tsum_euler_term_eq hq z
  -- Iterating the q-difference equation, `f z = (z; q)_N f (z q^N) → (z; q)_∞`.
  have hiter : ∀ N z, f z = qPochhammer z q N * f (z * q ^ N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro z
      rw [hfq z, ih (z * q), qPochhammer_succ', pow_succ']
      ring_nf
  have hlim : Tendsto (fun N ↦ qPochhammer z q N * f (z * q ^ N)) atTop
      (𝓝 ((∏' n : ℕ, (1 - z * q ^ n)) * f 0)) := by
    refine (tendsto_qPochhammer_atTop hq z).mul (hcont.tendsto.comp ?_)
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul z
  rw [hf0, mul_one] at hlim
  rw [← tendsto_nhds_unique (tendsto_const_nhds.congr (hiter · z)) hlim]
  exact (summable_norm_euler_term hq z).of_norm.hasSum

omit [CompleteSpace 𝕜] in
/-- For `‖q‖ < 1` and `0 ≤ ρ < 1` the series `∑_{k ≥ 0} ρᵏ / ‖(q; q)_k‖` converges. -/
private theorem summable_pow_div_norm_qPochhammer {q : 𝕜} (hq : ‖q‖ < 1) {ρ : ℝ} (hρ₀ : 0 ≤ ρ)
    (hρ : ρ < 1) : Summable fun k : ℕ ↦ ρ ^ k / ‖qPochhammer q q k‖ := by
  have ht : Tendsto (fun k : ℕ ↦ ρ / (1 - ‖q‖ ^ (k + 1))) atTop (𝓝 (ρ / (1 - 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).comp
        (tendsto_add_atTop_nat 1))) (by norm_num)
  refine summable_of_ratio_norm_eventually_le (r := (1 + ρ) / 2) (by linarith) ?_
  filter_upwards [ht.eventually (gt_mem_nhds (show ρ / (1 - 0) < (1 + ρ) / 2 by
    rw [sub_zero, div_one]; linarith))] with k hk
  have hD := norm_pos_iff.2 (qPochhammer_ne_zero_of_norm_lt_one hq hq.le k)
  have hq₁ : ‖q‖ ^ (k + 1) < 1 := pow_lt_one₀ (norm_nonneg q) hq k.succ_ne_zero
  have h₁ : 1 - ‖q‖ ^ (k + 1) ≤ ‖1 - q ^ (k + 1)‖ := by
    simpa [norm_pow] using norm_sub_norm_le (1 : 𝕜) (q ^ (k + 1))
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), qPochhammer_succ,
    ← pow_succ', norm_mul, pow_succ, mul_div_mul_comm]
  calc ρ ^ k / ‖qPochhammer q q k‖ * (ρ / ‖1 - q ^ (k + 1)‖)
      ≤ ρ ^ k / ‖qPochhammer q q k‖ * (ρ / (1 - ‖q‖ ^ (k + 1))) := by
        gcongr
    _ ≤ ρ ^ k / ‖qPochhammer q q k‖ * ((1 + ρ) / 2) := by
        gcongr
    _ = (1 + ρ) / 2 * (ρ ^ k / ‖qPochhammer q q k‖) := mul_comm _ _

omit [CompleteSpace 𝕜] in
/-- For `‖q‖ < 1` and `‖z‖ < 1` the series `∑_{k ≥ 0} zᵏ / (q; q)_k` converges absolutely. -/
theorem summable_norm_pow_div_qPochhammer {q z : 𝕜} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Summable fun k : ℕ ↦ ‖z ^ k / qPochhammer q q k‖ := by
  simpa [norm_pow] using summable_pow_div_norm_qPochhammer hq (norm_nonneg z) hz

/-- The series `G(z) = ∑_{k ≥ 0} zᵏ / (q; q)_k` satisfies the q-difference equation
`(1 - z) G(z) = G(z q)` of `1 / (z; q)_∞`. -/
private theorem one_sub_mul_tsum_pow_div_qPochhammer {q z : 𝕜} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    (1 - z) * ∑' k : ℕ, z ^ k / qPochhammer q q k = ∑' k : ℕ, (z * q) ^ k / qPochhammer q q k := by
  have hs := (summable_norm_pow_div_qPochhammer hq hz).of_norm
  refine ((hasSum_nat_add_iff' 1).mp ?_).tsum_eq.symm
  convert ((hasSum_nat_add_iff' 1).mpr hs.hasSum).sub (hs.hasSum.mul_left z) using 1
  · funext k
    have hD := qPochhammer_ne_zero_of_norm_lt_one hq hq.le k
    have h₁ : 1 - q ^ (k + 1) ≠ 0 := one_sub_pow_ne_zero hq k.succ_ne_zero
    rw [qPochhammer_succ, ← pow_succ']
    field_simp
    ring
  · simp
    ring

/-- **Euler's expansion** of the reciprocal of the infinite q-Pochhammer product: for `‖q‖ < 1`
and `‖z‖ < 1`, `1 / (z; q)_∞ = 1 / ∏_{n ≥ 0} (1 - z qⁿ) = ∑_{k ≥ 0} zᵏ / (q; q)_k`
(Gasper–Rahman, *Basic Hypergeometric Series*, (1.3.15)). -/
theorem hasSum_inv_tprod_one_sub_mul_pow {q z : 𝕜} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ k / qPochhammer q q k) (∏' n : ℕ, (1 - z * q ^ n))⁻¹ := by
  set g : 𝕜 → 𝕜 := fun z ↦ ∑' k : ℕ, z ^ k / qPochhammer q q k
  -- `g` is continuous at `0`, where it takes the value `1`.
  have hcont : ContinuousAt g 0 := by
    refine (continuousOn_tsum (u := fun k ↦ (1 / 2 : ℝ) ^ k / ‖qPochhammer q q k‖)
      (s := Metric.closedBall 0 (1 / 2)) (fun k ↦ by fun_prop)
      (summable_pow_div_norm_qPochhammer hq (by norm_num) (by norm_num))
      fun k x hx ↦ ?_).continuousAt (Metric.closedBall_mem_nhds 0 (by norm_num))
    rw [mem_closedBall_zero_iff] at hx
    rw [norm_div, norm_pow]
    gcongr
  have hg0 : g 0 = 1 := by
    simp only [g]
    rw [tsum_eq_single 0 fun k hk ↦ by simp [hk]]
    simp
  have hgq {z : 𝕜} (hz : ‖z‖ < 1) : (1 - z) * g z = g (z * q) := by
    simp only [g]
    exact one_sub_mul_tsum_pow_div_qPochhammer hq hz
  -- Iterating, `g z (z; q)_N = g (z q^N) → 1`.
  have hiter : ∀ N z, ‖z‖ < 1 → g z * qPochhammer z q N = g (z * q ^ N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro z hz
      have hzq : ‖z * q‖ < 1 := by
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg z) hq.le).trans_lt hz
      rw [qPochhammer_succ', ← mul_assoc, mul_comm (g z), hgq hz, ih (z * q) hzq, pow_succ',
        mul_assoc]
  have hlim : Tendsto (fun N ↦ g z * qPochhammer z q N) atTop (𝓝 (g 0)) := by
    refine (tendsto_congr fun N ↦ (hiter N z hz).symm).mp (hcont.tendsto.comp ?_)
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul z
  have h := tendsto_nhds_unique (tendsto_qPochhammer_atTop hq z |>.const_mul (g z)) hlim
  rw [hg0] at h
  rw [← eq_inv_of_mul_eq_one_left h]
  exact (summable_norm_pow_div_qPochhammer hq hz).of_norm.hasSum

end EulerExpansions

end NormedField

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

open Asymptotics Filter in
/-- Near `s = 0` the odd product is `∏_{n ≥ 0} (1 - s^{2n+1}) = 1 - s + O(s²)`: it has derivative
`-1` at `0`. -/
theorem hasDerivAt_tprod_one_sub_pow_odd :
    HasDerivAt (fun s : 𝕜 ↦ ∏' n : ℕ, (1 - s ^ (2 * n + 1))) (-1) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (g := fun s : 𝕜 ↦ s ^ 2) ?_ (isLittleO_pow_id one_lt_two)
  refine IsBigO.of_bound 4 ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : 𝕜) one_half_pos] with s hs
  rw [Metric.mem_closedBall, dist_zero_right] at hs
  have hs1 : ‖s‖ < 1 := hs.trans_lt one_half_lt_one
  have hs2 : ‖s‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg s) hs1 two_ne_zero
  -- Split off the factor `1 - s`; the remaining product is `1 + O(s³)`.
  have hsum : Summable fun n : ℕ ↦ ‖-s ^ (2 * n + 3)‖ := by
    refine ((summable_geometric_of_lt_one (by positivity) hs2).mul_left (‖s‖ ^ 3)).congr
      fun n ↦ ?_
    rw [norm_neg, norm_pow, pow_add, pow_mul]
    ring
  have htsum : ∑' n : ℕ, ‖-s ^ (2 * n + 3)‖ ≤ 2 * ‖s‖ ^ 3 := by
    have h : ∑' n : ℕ, ‖-s ^ (2 * n + 3)‖ = ‖s‖ ^ 3 * (1 - ‖s‖ ^ 2)⁻¹ := by
      rw [← tsum_geometric_of_lt_one (by positivity) hs2, ← tsum_mul_left]
      exact tsum_congr fun n ↦ by rw [norm_neg, norm_pow, pow_add, pow_mul]; ring
    rw [h, mul_comm 2]
    gcongr
    rw [inv_le_comm₀ (by linarith) two_pos]
    nlinarith [norm_nonneg s]
  have hR : ‖∏' n : ℕ, (1 + -s ^ (2 * n + 3)) - 1‖ ≤ 4 * ‖s‖ ^ 3 := by
    have hx : |∑' n : ℕ, ‖-s ^ (2 * n + 3)‖| ≤ 1 := by
      rw [abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)]
      nlinarith [pow_le_pow_left₀ (norm_nonneg s) hs 3]
    refine (norm_tprod_one_add_sub_one_le hsum).trans ?_
    have := Real.abs_exp_sub_one_le hx
    rw [abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)] at this
    linarith [le_abs_self (Real.exp (∑' n : ℕ, ‖-s ^ (2 * n + 3)‖) - 1)]
  have hsplit : ∏' n : ℕ, (1 - s ^ (2 * n + 1)) =
      (1 - s) * ∏' n : ℕ, (1 + -s ^ (2 * n + 3)) := by
    rw [tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - s ^ (2 * n + 1))
      (by simpa [sub_eq_add_neg, mul_add, add_assoc] using
        multipliable_one_add_of_summable hsum)]
    simp [sub_eq_add_neg, mul_add, add_assoc]
  have h0 : ∏' n : ℕ, (1 - (0 : 𝕜) ^ (2 * n + 1)) = 1 := by simp
  simp only [zero_add, h0, hsplit, smul_eq_mul, mul_neg, mul_one, sub_neg_eq_add]
  calc ‖(1 - s) * ∏' n : ℕ, (1 + -s ^ (2 * n + 3)) - 1 + s‖
      = ‖1 - s‖ * ‖∏' n : ℕ, (1 + -s ^ (2 * n + 3)) - 1‖ := by
        rw [← norm_mul]; congr 1; ring
    _ ≤ 2 * (4 * ‖s‖ ^ 3) := by
        gcongr
        exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    _ ≤ 4 * ‖s ^ 2‖ := by
        rw [norm_pow]
        nlinarith [mul_le_mul_of_nonneg_left hs (pow_nonneg (norm_nonneg s) 2)]

open Filter Topology in
/-- The odd difference quotient of a power `P(s)ᵏ` of the odd product
`P(s) = ∏_{n ≥ 0} (1 - s^{2n+1})` tends to `-2k` at `s = 0`: `(P(s)ᵏ - P(-s)ᵏ) / s → -2k`, since
`P(s)ᵏ = 1 - k s + O(s²)`. -/
theorem tendsto_tprod_one_sub_pow_odd_pow_sub_neg_div (k : ℕ) :
    Tendsto (fun s : 𝕜 ↦ ((∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ k -
      (∏' n : ℕ, (1 - (-s) ^ (2 * n + 1))) ^ k) / s) (𝓝[≠] 0) (𝓝 (-(2 * k))) := by
  have hP : HasDerivAt (fun s : 𝕜 ↦ (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ k) (-k) 0 := by
    simpa using (hasDerivAt_tprod_one_sub_pow_odd (𝕜 := 𝕜)).fun_pow k
  have hPneg := (neg_zero (G := 𝕜) ▸ hP).comp (0 : 𝕜) (hasDerivAt_neg (0 : 𝕜))
  convert hP.tendsto_slope_zero.sub hPneg.tendsto_slope_zero using 2 with s
  · simp only [zero_add, Function.comp_apply, neg_zero, smul_eq_mul]
    ring
  · ring

end NontriviallyNormedField

open Filter Topology UpperHalfPlane in
/-- `(∏_{n ≥ 0} (1 - q^{2n+1}))ᵏ → 1` at `i∞`, for `q = e^{2π i τ}`. -/
theorem tendsto_tprod_one_sub_qParam_pow_odd_pow (k : ℕ) :
    Tendsto (fun τ : ℍ ↦ (∏' n : ℕ, (1 - Function.Periodic.qParam 1 τ ^ (2 * n + 1))) ^ k)
      atImInfty (𝓝 1) := by
  simpa using ((hasDerivAt_tprod_one_sub_pow_odd (𝕜 := ℂ)).continuousAt.tendsto.comp
    (((Function.Periodic.qParam_tendsto one_pos).mono_right nhdsWithin_le_nhds).comp
      tendsto_coe_atImInfty)).pow k

section LocallyUniform

variable {q w : ℂ → ℂ} {U : Set ℂ}

/-- For `q` and `w` continuous on an open set `U` with `‖q‖ < 1` on `U`, the product
`∏_{n ≥ 1} (1 - q(τ)ⁿ w(τ))` converges locally uniformly on `U`. -/
theorem hasProdLocallyUniformlyOn_one_sub_pow_mul (hU : IsOpen U) (hq : ContinuousOn q U)
    (hq₁ : ∀ τ ∈ U, ‖q τ‖ < 1) (hw : ContinuousOn w U) :
    HasProdLocallyUniformlyOn (fun (n : ℕ) τ ↦ 1 - q τ ^ (n + 1) * w τ)
      (fun τ ↦ ∏' n : ℕ, (1 - q τ ^ (n + 1) * w τ)) U := by
  simp_rw [sub_eq_add_neg]
  refine hasProdLocallyUniformlyOn_of_forall_compact hU fun S hSU hS ↦ ?_
  obtain ⟨ρ, hρ₀, hρ₁, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ τ ∈ S, ‖q τ‖ ≤ ρ := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, le_rfl, one_pos, by simp⟩
    obtain ⟨τ₀, hτ₀, hmax⟩ := hS.exists_isMaxOn hne (hq.mono hSU).norm
    exact ⟨_, norm_nonneg _, hq₁ τ₀ (hSU hτ₀), hmax⟩
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (hw.mono hSU)
  refine ((summable_geometric_of_lt_one hρ₀ hρ₁).mul_left (ρ * M)).hasProdUniformlyOn_nat_one_add
    hS (.of_forall fun n τ hτ ↦ ?_) fun n ↦ by
      have := hq.mono hSU
      have := hw.mono hSU
      fun_prop
  calc ‖-(q τ ^ (n + 1) * w τ)‖
      = ‖q τ‖ ^ (n + 1) * ‖w τ‖ := by simp [norm_pow]
    _ ≤ ρ ^ (n + 1) * M :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hρ τ hτ) _) (hM τ hτ) (norm_nonneg _)
        (pow_nonneg hρ₀ _)
    _ = ρ * M * ρ ^ n := by ring

/-- For `q` and `w` holomorphic on an open set `U` with `‖q‖ < 1` on `U`, the product
`∏_{n ≥ 1} (1 - q(τ)ⁿ w(τ))` is holomorphic on `U`. -/
theorem differentiableOn_tprod_one_sub_pow_mul (hU : IsOpen U) (hq : DifferentiableOn ℂ q U)
    (hq₁ : ∀ τ ∈ U, ‖q τ‖ < 1) (hw : DifferentiableOn ℂ w U) :
    DifferentiableOn ℂ (fun τ ↦ ∏' n : ℕ, (1 - q τ ^ (n + 1) * w τ)) U :=
  (hasProdLocallyUniformlyOn_one_sub_pow_mul hU hq.continuousOn hq₁
    hw.continuousOn).differentiableOn (.of_forall fun s ↦ by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd fun _ _ ↦ by fun_prop) hU

end LocallyUniform

section Holomorphic

variable {q : ℂ}

/-- The product of the two half products of `θ_q(w)` is holomorphic on `ℂ \ {0}`. -/
private theorem differentiableOn_tprod_mul_tprod (hq : ‖q‖ < 1) :
    DifferentiableOn ℂ (fun w : ℂ ↦
      (∏' n : ℕ, (1 - q ^ (n + 1) * w)) * ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹)) {0}ᶜ :=
  (differentiableOn_tprod_one_sub_pow_mul (q := fun _ ↦ q) isOpen_compl_singleton
    (differentiableOn_const q) (fun _ _ ↦ hq) differentiableOn_id).mul
    (differentiableOn_tprod_one_sub_pow_mul (q := fun _ ↦ q) isOpen_compl_singleton
      (differentiableOn_const q) (fun _ _ ↦ hq) (differentiableOn_inv.mono fun _ h ↦ h))

/-- For `‖q‖ < 1` the theta product `w ↦ θ_q(w)` is holomorphic on `ℂ \ {0}`. -/
theorem differentiableOn_qTheta (hq : ‖q‖ < 1) : DifferentiableOn ℂ (qTheta q) {0}ᶜ := by
  rw [show qTheta q = _ from funext (qTheta_eq_mul_tprod_mul_tprod hq)]
  exact (differentiableOn_const 1 |>.sub differentiableOn_id).mul
    (differentiableOn_tprod_mul_tprod hq)

/-- For `‖q‖ < 1` the theta product has a simple zero at `w = 1`: its derivative there is
`-(∏_{n ≥ 1} (1 - qⁿ))²`. -/
theorem hasDerivAt_qTheta_one (hq : ‖q‖ < 1) :
    HasDerivAt (qTheta q) (-(∏' n : ℕ, (1 - q ^ (n + 1))) ^ 2) 1 := by
  have h := ((hasDerivAt_id (1 : ℂ)).const_sub 1).mul
    (((differentiableOn_tprod_mul_tprod hq).differentiableAt
      (isOpen_compl_singleton.mem_nhds one_ne_zero)).hasDerivAt)
  rw [show qTheta q = _ from funext (qTheta_eq_mul_tprod_mul_tprod hq)]
  convert h using 1
  · funext w
    simp
  · simp [sq]

open Complex in
open scoped Real in
/-- For `‖q‖ < 1`, `z ↦ θ_q(e^{2π i z})` is an entire function. -/
theorem differentiable_qTheta_exp (hq : ‖q‖ < 1) :
    Differentiable ℂ fun z : ℂ ↦ qTheta q (cexp (2 * π * I * z)) := fun z ↦
  ((differentiableOn_qTheta hq).differentiableAt
    (isOpen_compl_singleton.mem_nhds (exp_ne_zero _))).comp (f := fun z ↦ cexp (2 * π * I * z)) z
    (by fun_prop)

open Complex in
open scoped Real in
/-- For `‖q‖ < 1` the derivative of `z ↦ θ_q(e^{2π i z})` at `z = 0` is
`-2π i (∏_{n ≥ 1} (1 - qⁿ))²`. -/
theorem hasDerivAt_qTheta_exp_zero (hq : ‖q‖ < 1) :
    HasDerivAt (fun z : ℂ ↦ qTheta q (cexp (2 * π * I * z)))
      (-(2 * π * I) * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 2) 0 := by
  have h := (hasDerivAt_qTheta_one hq).comp_of_eq (0 : ℂ)
    ((hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I)).cexp (by simp)
  convert h using 1
  · funext z
    simp
  · simp only [id, mul_zero, Complex.exp_zero, mul_one]
    ring

end Holomorphic

end TauCeti
