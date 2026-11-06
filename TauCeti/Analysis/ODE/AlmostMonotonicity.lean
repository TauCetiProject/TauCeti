/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.ODE.Gronwall

/-!
# Almost monotonicity of two-dimensional density ratios

A monotonicity formula controls the growth of an energy `E(σ)` of balls of radius `σ` through a
differential inequality of the form `E ≤ (σ / 2) E'`, which says exactly that the density ratio
`E(σ) / σ²` is nondecreasing. In applications the inequality only holds up to errors:

`E(σ) ≤ (σ / 2) (1 + C σ) (1 + δ) E'(σ) + K σ⁴`   for almost every `σ ∈ (a, b)`,

where `C σ` accounts for the curvature of the ambient geometry, `δ` is a small multiplicative
defect and `K σ⁴` a forcing error. This is the shape of Taubes's monotonicity inequality for the
local defect energy `E_r(B_σ) = (r / 4) ∫_{B_σ} |1 - |χ|²|` of a solution of the perturbed
Seiberg–Witten equations on a symplectic four-manifold, where `δ = C r^{-1/2}`.

Here `E` is only assumed to be monotone, as an energy of nested balls is, so `E'` exists almost
everywhere; no continuity of `E` is needed. The inequality is homogeneous in
`G(σ) = E(σ) + K σ⁴`, because `(σ / 2) (K σ⁴)' = 2 K σ⁴` leaves room to absorb the forcing term
`K σ⁴`. Integrating
the logarithmic derivative of `G` with `TauCeti.mul_exp_integral_le_of_mul_le_deriv` gives the
**almost monotonicity formula** (`TauCeti.monotoneOn_rpow_mul_add_of_le_deriv`): the quantity

`((1 + C σ) / σ) ^ (2 / (1 + δ)) · (E(σ) + K σ⁴)`

is nondecreasing on `[a, b]`. Comparing two radii yields quadratic growth bounds, provided the
defect is small at the radii in question, `δ ≤ M σ`. This is how the range `σ ≥ c r^{-1/2}`
enters for `δ = C r^{-1/2}`: there `δ ≤ (C / c) σ`, and the loss of the exponent `2 / (1 + δ)`
against `2` costs at most a factor `exp (2 M b)`.

* `TauCeti.le_mul_sq_of_le_deriv`: an upper bound `E(σ) ≤ A σ²` below the outer radius `b`, with
  `A = (1 + C b)² exp (2 M b) (E(b) + K b⁴) / b²`.
* `TauCeti.mul_sq_sub_le_of_le_deriv`: a lower bound `c' σ² - K σ⁴ ≤ E(σ)` above the inner
  radius `a`, with `c' = c exp (-2 M σ) / (1 + C σ)²`, as soon as `E(a) ≥ c a²`.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. **9** (1996), 845–918.
-/

public section

open Set Filter Real MeasureTheory

namespace TauCeti

/-- The weight `log ((1 + C σ) / σ) = log (1 + C σ) - log σ` of the monotonicity formula has
derivative `-1 / (σ (1 + C σ))`. -/
private lemma hasDerivAt_log_one_add_mul_sub_log {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 < σ) :
    HasDerivAt (fun x ↦ Real.log (1 + C * x) - Real.log x) (-(1 / (σ * (1 + C * σ)))) σ := by
  have h1 : 0 < 1 + C * σ := by positivity
  have hd : HasDerivAt (fun x ↦ Real.log (1 + C * x)) (C / (1 + C * σ)) σ := by
    simpa using (((hasDerivAt_id σ).const_mul C).const_add 1).log h1.ne'
  convert hd.fun_sub (Real.hasDerivAt_log hσ.ne') using 1
  field_simp
  ring

/-- The two-point form of the almost monotonicity formula, before the weights are written as
powers: `G(s) exp (∫ₛᵗ k) ≤ G(t)` for `G = E + K σ⁴` and `k = 2 / ((1 + δ) σ (1 + C σ))`. -/
private lemma mul_exp_integral_le_add {E : ℝ → ℝ} {a b C δ K : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hmono : MonotoneOn E (Icc a b))
    (hE : ∀ᵐ σ, σ ∈ Ioo a b →
      E σ ≤ σ / 2 * ((1 + C * σ) * (1 + δ)) * deriv E σ + K * σ ^ 4)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    (E s + K * s ^ 4) *
        Real.exp (∫ σ in s..t, 2 / ((1 + δ) * (σ * (1 + C * σ)))) ≤ E t + K * t ^ 4 := by
  set G : ℝ → ℝ := fun σ ↦ E σ + K * σ ^ 4
  set k : ℝ → ℝ := fun σ ↦ 2 / ((1 + δ) * (σ * (1 + C * σ)))
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have hpos (σ : ℝ) (hσ : σ ∈ Icc s t) : 0 < σ := ha.trans_le (hsub hσ).1
  have hG : MonotoneOn G (Icc s t) := fun x hx y hy hxy ↦
    add_le_add (hmono (hsub hx) (hsub hy) hxy)
      (by gcongr; exact (hpos x hx).le)
  have hk_nonneg (σ : ℝ) (hσ : σ ∈ Icc s t) : 0 ≤ k σ := by
    have := hpos σ hσ
    positivity
  have hk : IntervalIntegrable k volume s t := by
    refine ContinuousOn.intervalIntegrable_of_Icc hst ?_
    refine continuousOn_const.div (by fun_prop) fun σ hσ ↦ ?_
    have := hpos σ hσ
    positivity
  -- At almost every point the inequality for `E` gives `k G ≤ G'`.
  have hder : ∀ᵐ σ, σ ∈ Ioo s t → k σ * G σ ≤ deriv G σ := by
    filter_upwards [hE,
      (hmono.mono (Ioo_subset_Icc_self.trans hsub)).ae_differentiableWithinAt_of_mem]
      with σ hσE hd hσ
    have hσab : σ ∈ Ioo a b := ⟨hs.1.trans_lt hσ.1, hσ.2.trans_le ht.2⟩
    have hσ0 : 0 < σ := hpos σ (Ioo_subset_Icc_self hσ)
    have hdE := ((hd hσ).differentiableAt (Ioo_mem_nhds hσ.1 hσ.2)).hasDerivAt
    have hdG : HasDerivAt G (deriv E σ + K * (4 * σ ^ 3)) σ := by
      simpa using hdE.fun_add ((hasDerivAt_pow 4 σ).const_mul K)
    rw [hdG.deriv]
    have hA : 1 ≤ (1 + C * σ) * (1 + δ) := one_le_mul_of_one_le_of_one_le
      (by nlinarith) (by linarith)
    have hden : 0 < (1 + δ) * (σ * (1 + C * σ)) := by positivity
    have hEσ := hσE hσab
    simp only [k, G]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have hK4 : 0 ≤ K * σ ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hA hK4]
  rcases le_or_gt 0 (G s) with hGs | hGs
  · exact mul_exp_integral_le_of_mul_le_deriv hst hG hGs hk hder
  -- If `G s < 0` the factor `exp (∫ k) ≥ 1` only decreases `G s`.
  have hint : 0 ≤ ∫ σ in s..t, k σ :=
    intervalIntegral.integral_nonneg hst fun σ hσ ↦ hk_nonneg σ hσ
  calc G s * Real.exp (∫ σ in s..t, k σ) ≤ G s :=
        mul_le_of_one_le_right hGs.le (Real.one_le_exp_iff.2 hint)
    _ ≤ G t := hG ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

/-- The integral of `k = 2 / ((1 + δ) σ (1 + C σ))` in terms of the weight
`log ((1 + C σ) / σ)`. -/
private lemma integral_two_div_mul {C δ s t : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hs : 0 < s)
    (hst : s ≤ t) :
    ∫ σ in s..t, 2 / ((1 + δ) * (σ * (1 + C * σ))) =
      2 / (1 + δ) * ((Real.log (1 + C * s) - Real.log s) -
        (Real.log (1 + C * t) - Real.log t)) := by
  have hpos (σ : ℝ) (hσ : σ ∈ uIcc s t) : 0 < σ := by
    rw [uIcc_of_le hst] at hσ
    exact hs.trans_le hσ.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x ↦ -(2 / (1 + δ)) * (Real.log (1 + C * x) - Real.log x))]
  · ring
  · intro σ hσ
    convert (hasDerivAt_log_one_add_mul_sub_log hC (hpos σ hσ)).const_mul (-(2 / (1 + δ)))
      using 1
    field_simp
  · refine ContinuousOn.intervalIntegrable fun σ hσ ↦ ?_
    have := hpos σ hσ
    exact (continuousAt_const.div (by fun_prop) (by positivity)).continuousWithinAt

/-- The weight of the monotonicity formula as an exponential. -/
private lemma rpow_eq_exp_mul_log {C x : ℝ} (hC : 0 ≤ C) (hx : 0 < x) (l : ℝ) :
    ((1 + C * x) / x) ^ l = Real.exp (l * (Real.log (1 + C * x) - Real.log x)) := by
  have h1 : 0 < 1 + C * x := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.log_div h1.ne' hx.ne', mul_comm]

/-- The exponent `l = 2 / (1 + δ)` satisfies `0 < l ≤ 2` and `2 - l ≤ 2 δ`. -/
private lemma two_div_one_add_bounds {δ : ℝ} (hδ : 0 ≤ δ) :
    0 < 2 / (1 + δ) ∧ 2 / (1 + δ) ≤ 2 ∧ 2 - 2 / (1 + δ) ≤ 2 * δ := by
  refine ⟨by positivity, div_le_self zero_le_two (by linarith), ?_⟩
  have : 2 - 2 / (1 + δ) = 2 * δ / (1 + δ) := by field_simp; ring
  rw [this]
  exact div_le_self (by positivity) (by linarith)

/-- **Almost monotonicity of the density ratio.** Let `E` be monotone on `[a, b]`, `0 < a`, and
suppose that for almost every `σ ∈ (a, b)`

`E(σ) ≤ (σ / 2) (1 + C σ) (1 + δ) E'(σ) + K σ⁴`

with `C, δ, K ≥ 0`. Then `((1 + C σ) / σ) ^ (2 / (1 + δ)) (E(σ) + K σ⁴)` is nondecreasing on
`[a, b]`. For `C = δ = K = 0` this is the monotonicity of the density ratio `E(σ) / σ²`. -/
theorem monotoneOn_rpow_mul_add_of_le_deriv {E : ℝ → ℝ} {a b C δ K : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hmono : MonotoneOn E (Icc a b))
    (hE : ∀ᵐ σ, σ ∈ Ioo a b →
      E σ ≤ σ / 2 * ((1 + C * σ) * (1 + δ)) * deriv E σ + K * σ ^ 4) :
    MonotoneOn (fun σ ↦ ((1 + C * σ) / σ) ^ (2 / (1 + δ)) * (E σ + K * σ ^ 4)) (Icc a b) := by
  intro s hs t ht hst
  have hs0 : 0 < s := ha.trans_le hs.1
  have h := mul_exp_integral_le_add ha hC hδ hK hmono hE hs ht hst
  rw [integral_two_div_mul hC hδ hs0 hst, mul_sub, Real.exp_sub, mul_div_assoc',
    div_le_iff₀ (Real.exp_pos _)] at h
  simp only [rpow_eq_exp_mul_log hC hs0, rpow_eq_exp_mul_log hC (hs0.trans_le hst)]
  linarith [mul_comm (Real.exp (2 / (1 + δ) * (Real.log (1 + C * t) - Real.log t)))
    (E t + K * t ^ 4), mul_comm (Real.exp (2 / (1 + δ) * (Real.log (1 + C * s) - Real.log s)))
    (E s + K * s ^ 4)]

/-- **Quadratic upper bound from almost monotonicity.** Under the hypotheses of
`TauCeti.monotoneOn_rpow_mul_add_of_le_deriv`, with `0 ≤ E(b)`, every `σ ∈ [a, b]` whose defect
satisfies `δ ≤ M σ` has

`E(σ) ≤ (1 + C b)² exp (2 M b) (E(b) + K b⁴) σ² / b²`. -/
theorem le_mul_sq_of_le_deriv {E : ℝ → ℝ} {a b C δ K M σ : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hmono : MonotoneOn E (Icc a b))
    (hE : ∀ᵐ σ, σ ∈ Ioo a b →
      E σ ≤ σ / 2 * ((1 + C * σ) * (1 + δ)) * deriv E σ + K * σ ^ 4)
    (hEb : 0 ≤ E b) (hσ : σ ∈ Icc a b) (hδM : δ ≤ M * σ) :
    E σ ≤ (1 + C * b) ^ 2 * Real.exp (2 * M * b) * (E b + K * b ^ 4) / b ^ 2 * σ ^ 2 := by
  have hσ0 : 0 < σ := ha.trans_le hσ.1
  have hb0 : 0 < b := hσ0.trans_le hσ.2
  have h := monotoneOn_rpow_mul_add_of_le_deriv ha hC hδ hK hmono hE hσ
    ⟨hσ.1.trans hσ.2, le_rfl⟩ hσ.2
  simp only [rpow_eq_exp_mul_log hC hσ0, rpow_eq_exp_mul_log hC hb0] at h
  obtain ⟨hl0, hl2, hl2δ⟩ := two_div_one_add_bounds hδ
  set l := 2 / (1 + δ)
  set wσ := Real.exp (l * (Real.log (1 + C * σ) - Real.log σ))
  have h1b : 0 < 1 + C * b := by positivity
  -- In logarithms, the ratio of weights `w(b) / w(σ)` is at most `(1 + C b)² exp (2 M b) σ² / b²`.
  have hexp : l * (Real.log (1 + C * b) - Real.log b) ≤
      l * (Real.log (1 + C * σ) - Real.log σ) +
        ((Real.log (1 + C * b) + Real.log (1 + C * b)) + 2 * M * b +
          (Real.log σ + Real.log σ) - (Real.log b + Real.log b)) := by
    have hlogσ : 0 ≤ Real.log (1 + C * σ) := Real.log_nonneg (by nlinarith)
    have hlogb : 0 ≤ Real.log (1 + C * b) := Real.log_nonneg (by nlinarith)
    have hbσ0 : 0 ≤ Real.log b - Real.log σ := sub_nonneg.2 (Real.log_le_log hσ0 hσ.2)
    have hbσ : Real.log b - Real.log σ ≤ b / σ := by
      rw [← Real.log_div hb0.ne' hσ0.ne']
      exact Real.log_le_self (by positivity)
    have h1 : (2 - l) * (Real.log b - Real.log σ) ≤ 2 * δ * (b / σ) :=
      mul_le_mul hl2δ hbσ hbσ0 (by positivity)
    have h2 : 2 * δ * (b / σ) ≤ 2 * M * b := by
      rw [mul_div_assoc', div_le_iff₀ hσ0]; nlinarith
    nlinarith [mul_nonneg hl0.le hlogσ]
  have hratio : Real.exp (l * (Real.log (1 + C * b) - Real.log b)) ≤
      wσ * ((1 + C * b) ^ 2 * Real.exp (2 * M * b) / b ^ 2 * σ ^ 2) := by
    refine (Real.exp_le_exp.2 hexp).trans_eq ?_
    simp only [Real.exp_add, Real.exp_sub, Real.exp_log h1b, Real.exp_log hσ0, Real.exp_log hb0]
    ring
  have key : wσ * (E σ + K * σ ^ 4) ≤
      wσ * ((1 + C * b) ^ 2 * Real.exp (2 * M * b) * (E b + K * b ^ 4) / b ^ 2 * σ ^ 2) := by
    calc _ ≤ Real.exp (l * (Real.log (1 + C * b) - Real.log b)) * (E b + K * b ^ 4) := h
      _ ≤ wσ * ((1 + C * b) ^ 2 * Real.exp (2 * M * b) / b ^ 2 * σ ^ 2) * (E b + K * b ^ 4) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := by ring
  have hK4 : 0 ≤ K * σ ^ 4 := by positivity
  linarith [le_of_mul_le_mul_left key (Real.exp_pos _)]

/-- **Quadratic lower bound from almost monotonicity.** Under the hypotheses of
`TauCeti.monotoneOn_rpow_mul_add_of_le_deriv`, suppose that `E` has quadratic size at the inner
radius, `c a² ≤ E(a)` with `0 ≤ c`, and that the defect satisfies `δ ≤ M a`. Then every
`σ ∈ [a, b]` has

`c exp (-2 M σ) σ² / (1 + C σ)² - K σ⁴ ≤ E(σ)`. -/
theorem mul_sq_sub_le_of_le_deriv {E : ℝ → ℝ} {a b C δ K M c σ : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hmono : MonotoneOn E (Icc a b))
    (hE : ∀ᵐ σ, σ ∈ Ioo a b →
      E σ ≤ σ / 2 * ((1 + C * σ) * (1 + δ)) * deriv E σ + K * σ ^ 4)
    (hc : 0 ≤ c) (hEa : c * a ^ 2 ≤ E a) (hσ : σ ∈ Icc a b) (hδM : δ ≤ M * a) :
    c * Real.exp (-(2 * M * σ)) / (1 + C * σ) ^ 2 * σ ^ 2 - K * σ ^ 4 ≤ E σ := by
  have hσ0 : 0 < σ := ha.trans_le hσ.1
  have h := monotoneOn_rpow_mul_add_of_le_deriv ha hC hδ hK hmono hE
    ⟨le_rfl, hσ.1.trans hσ.2⟩ hσ hσ.1
  simp only [rpow_eq_exp_mul_log hC ha, rpow_eq_exp_mul_log hC hσ0] at h
  obtain ⟨hl0, hl2, hl2δ⟩ := two_div_one_add_bounds hδ
  set l := 2 / (1 + δ)
  set wσ := Real.exp (l * (Real.log (1 + C * σ) - Real.log σ))
  set wa := Real.exp (l * (Real.log (1 + C * a) - Real.log a))
  have h1σ : 0 < 1 + C * σ := by positivity
  -- In logarithms, `w(σ) exp (-2 M σ) σ² / (1 + C σ)² ≤ w(a) a²`.
  have hexp : l * (Real.log (1 + C * σ) - Real.log σ) +
      (-(2 * M * σ) - (Real.log (1 + C * σ) + Real.log (1 + C * σ)) +
        (Real.log σ + Real.log σ) - (Real.log a + Real.log a)) ≤
        l * (Real.log (1 + C * a) - Real.log a) := by
    have hlogσ : 0 ≤ Real.log (1 + C * σ) := Real.log_nonneg (by nlinarith)
    have hloga : 0 ≤ Real.log (1 + C * a) := Real.log_nonneg (by nlinarith)
    have hσa0 : 0 ≤ Real.log σ - Real.log a := sub_nonneg.2 (Real.log_le_log ha hσ.1)
    have hσa : Real.log σ - Real.log a ≤ σ / a := by
      rw [← Real.log_div hσ0.ne' ha.ne']
      exact Real.log_le_self (by positivity)
    have h1 : (2 - l) * (Real.log σ - Real.log a) ≤ 2 * δ * (σ / a) :=
      mul_le_mul hl2δ hσa hσa0 (by positivity)
    have h2 : 2 * δ * (σ / a) ≤ 2 * M * σ := by
      rw [mul_div_assoc', div_le_iff₀ ha]; nlinarith
    nlinarith [mul_nonneg hl0.le hloga]
  have hratio : wσ * (Real.exp (-(2 * M * σ)) / (1 + C * σ) ^ 2 * σ ^ 2) ≤ wa * a ^ 2 := by
    have := Real.exp_le_exp.2 hexp
    simp only [Real.exp_add, Real.exp_sub, Real.exp_log h1σ, Real.exp_log hσ0,
      Real.exp_log ha] at this
    calc _ = wσ * (Real.exp (-(2 * M * σ)) / ((1 + C * σ) * (1 + C * σ)) * (σ * σ) / (a * a)) *
          a ^ 2 := by field_simp
      _ ≤ wa * a ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
  have key : wσ * (c * Real.exp (-(2 * M * σ)) / (1 + C * σ) ^ 2 * σ ^ 2) ≤
      wσ * (E σ + K * σ ^ 4) := by
    calc _ = c * (wσ * (Real.exp (-(2 * M * σ)) / (1 + C * σ) ^ 2 * σ ^ 2)) := by ring
      _ ≤ c * (wa * a ^ 2) := mul_le_mul_of_nonneg_left hratio hc
      _ = wa * (c * a ^ 2) := by ring
      _ ≤ wa * (E a + K * a ^ 4) :=
          mul_le_mul_of_nonneg_left (by nlinarith [pow_pos ha 4]) (Real.exp_pos _).le
      _ ≤ _ := h
  linarith [le_of_mul_le_mul_left key (Real.exp_pos _)]

end TauCeti
