/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev

/-!
# The energy form under a small drift, and splitting off the mass term

Two facts about the energy form `TauCeti.PDE.energyFormH1` of
`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`, used to treat the drift and the mass term separately.

* `TauCeti.PDE.energyFormH1_eq_energyFormH1_zero_add_setIntegral`: with bounded coefficients,
  `a_{b,c}(u, v) = a_{b,0}(u, v) + ∫_Ω c u v`, so the mass term can be moved to the right-hand
  side of an equation.
* `TauCeti.PDE.UniformlyEllipticOn.mul_norm_gradient_sq_le_energyFormH1_self_of_small_drift`:
  Gårding's inequality absorbs a drift that is small against the gradient,
  `2β ‖u‖_{L²} ≤ λ ‖∇u‖_{L²}`, giving `(λ/4) ‖∇u‖²_{L²} ≤ a(u, u)`. On `H¹₀` of a ball of radius
  `ρ` this holds when `2βρ ≤ λ`, by the Poincaré inequality
  `TauCeti.W1p.norm_value_le_mul_norm_gradient_of_eq_ball`.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
  {lam Lam beta gamma : ℝ}

/-- **Splitting off the mass term.** With an essentially bounded energy density for the principal
and drift coefficients and a bounded mass coefficient `c`, the energy form of
`-∂ᵢ(aⁱʲ ∂ⱼ·) + bⁱ ∂ᵢ + c` is that of `-∂ᵢ(aⁱʲ ∂ⱼ·) + bⁱ ∂ᵢ` plus the `L²` pairing of `c u` with
`v`:

`a_{b,c}(u, v) = a_{b,0}(u, v) + ∫_Ω c u v`. -/
theorem energyFormH1_eq_energyFormH1_zero_add_setIntegral {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hab : MemLp (fun x => energyIntegrand (a x) (b x) 0) ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) (u v : W1p mu Omega 2) :
    energyFormH1 a b c u v =
      energyFormH1 a b 0 u v + ∫ x in Omega, c x * W1p.value u x * W1p.value v x ∂mu := by
  have hC : MemLp (fun x => c x * W1p.value u x) 2 (mu.restrict Omega) :=
    hc.fun_mul (Lp.memLp _)
  have hCv : Integrable (fun x => c x * W1p.value u x * W1p.value v x) (mu.restrict Omega) :=
    hC.integrable_mul (Lp.memLp _)
  rw [energyFormH1_def, energyFormH1_def,
    ← integral_add (integrable_energyIntegrand_jetField (c := 0) hab u v) hCv]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply,
    Pi.zero_apply]
  ring

namespace UniformlyEllipticOn

variable [DecidableEq ι]

/-- **Coercivity under a small drift.** Let `a` be uniformly elliptic on `Ω` with constants
`λ, Λ`, let the drift satisfy `‖b‖ ≤ β`, and let the mass coefficient satisfy `0 ≤ c ≤ γ` on `Ω`.
If the drift is small against the gradient of `u`, `2β ‖u‖_{L²} ≤ λ ‖∇u‖_{L²}`, then Gårding's
inequality absorbs the drift term:

`(λ/4) ‖∇u‖²_{L²} ≤ a(u, u)`.

On `H¹₀(Ω)` the smallness holds when `2βP ≤ λ` for a Poincaré constant `P` of `Ω`, for instance
when `2βρ ≤ λ` on a ball of radius `ρ`. -/
theorem mul_norm_gradient_sq_le_energyFormH1_self_of_small_drift
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {u : W1p mu Omega 2}
    (hu : 2 * beta * ‖W1p.value u‖ ≤ lam * ‖W1p.gradient u‖) :
    lam / 4 * ‖W1p.gradient u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  have hlam := h.pos
  -- Gårding's inequality with the drift bound `max β 0`, which is nonnegative.
  have hg := garding_energyFormH1_self h ha hb hc
    (fun x hx => (hb_bound x hx).trans (le_max_left beta 0)) hc_bound hc_nonneg u
  have hsmall : 2 * max beta 0 * ‖W1p.value u‖ ≤ lam * ‖W1p.gradient u‖ := by
    rcases le_total beta 0 with hβ | hβ
    · rw [max_eq_right hβ, mul_zero, zero_mul]
      positivity
    · rwa [max_eq_left hβ]
  -- `β²‖u‖² ≤ (λ²/4)‖∇u‖²`, so the drift defect is at most `(λ/8)‖∇u‖²`.
  have hsq := mul_self_le_mul_self (by positivity) hsmall
  have hdefect : max beta 0 ^ 2 / (2 * lam) * ‖W1p.value u‖ ^ 2 ≤
      lam / 8 * ‖W1p.gradient u‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [sq_nonneg ‖W1p.gradient u‖]

end UniformlyEllipticOn

end PDE

end TauCeti
