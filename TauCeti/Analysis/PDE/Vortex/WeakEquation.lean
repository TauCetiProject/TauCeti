/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ReducedFunctional
public import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.PDE.Vortex.Minimizer
import TauCeti.Analysis.SpecialFunctions.Exp.Modular

/-!
# The weak reduced vortex equation for minimizers of Taubes's functional

Let `P` be a complex polynomial of degree `m ≥ 1`, and put

`h = ‖P‖² / (1 + ‖P‖²)`,    `g = 2 ‖P'‖² / (1 + ‖P‖²)²`.

A vortex with zero divisor `P` is obtained from a solution `w` of the reduced equation
`Δw = (h exp (2w) - 1) / 8 + g`, and Taubes obtains `w` as a minimizer of the functional `I` of
`TauCeti.Vortex.sobolevReducedFunctional` on `H¹(ℂ) = W^{1,2}(ℂ)`. This file proves that every
minimizer `u` of `I` solves the reduced equation weakly:

* `TauCeti.Vortex.exists_hasDerivAt_sobolevReducedFunctional_add_smul`: the first variation. If
  `I(u)` is finite and `φ` is a compactly supported `C¹` function, then `t ↦ I(u + tφ)` is finite
  and has derivative `∫ ⟪∇u, ∇φ⟫ + ∫ ((h exp (2u) - 1) / 8 + g) φ` at `t = 0`;
* `TauCeti.Vortex.integral_inner_gradient_eq_neg_integral_of_forall_le`: for every compactly
  supported `C¹` function `φ`,
  `∫ ⟪∇u, ∇φ⟫ = -∫ ((h exp (2u) - 1) / 8 + g) φ`;
* `TauCeti.Vortex.integral_laplacian_mul_eq_integral_of_forall_le`: equivalently, for every test
  function `φ`, `∫ Δφ u = ∫ ((h exp (2u) - 1) / 8 + g) φ`, so `Δu = (h exp (2u) - 1) / 8 + g` in
  the sense of distributions;
* `TauCeti.Vortex.exists_forall_integral_laplacian_mul_eq`: combined with the existence of a
  minimizer (`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`), the reduced equation
  has a weak solution in `H¹(ℂ)`.

The proof differentiates `t ↦ I(u + t φ)` at `t = 0`. The Dirichlet energy and the linear term are
polynomial in `t`. The potential `∫ h (exp (2u) - 1 - 2u)` of a minimizer is finite, because
`I(u) ≤ I(0) = 0`; since `h exp (2u) ≤ h (exp (2u) - 1 - 2u) + 1 + 2 |u|`, the derivative
`h (2 exp (2(u + tφ)) - 2) φ` of the potential density is dominated, for `t` in a bounded set, by
an integrable function, using only that `φ` is bounded, integrable and square integrable. This
needs no exponential integrability of `H¹` functions. Differentiation under the integral sign then
gives the first variation, which vanishes at a minimum.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter InnerProductSpace Laplacian MeasureTheory Set TopologicalSpace
open scoped Distributions Gradient

/-! ### The first variation of the potential -/

section Potential

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The derivative `η (2 exp (2(a + b)) - 2)` of the potential density, for `0 ≤ η ≤ 1` and
`|b| ≤ B`, is bounded in terms of the potential `η (exp (2a) - 1 - 2a)` at `a`, because
`η exp (2a) ≤ η (exp (2a) - 1 - 2a) + 1 + 2 |a|`. -/
private theorem abs_mul_two_mul_exp_sub_two_le {η a b B : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hb : |b| ≤ B) :
    |η * (2 * Real.exp (2 * (a + b)) - 2)| ≤
      2 * (Real.exp (2 * B) * (η * (Real.exp (2 * a) - 1 - 2 * a) + 1 + 2 * |a|) + 1) := by
  have hexp : Real.exp (2 * (a + b)) ≤ Real.exp (2 * a) * Real.exp (2 * B) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [le_abs_self b])
  have hηa : η * Real.exp (2 * a) ≤ η * (Real.exp (2 * a) - 1 - 2 * a) + 1 + 2 * |a| := by
    nlinarith [neg_abs_le a, le_abs_self a, abs_nonneg a]
  have hΦ := mul_nonneg hη₀ (Real.exp_two_mul_sub_one_sub_two_mul_nonneg a)
  have hB := (Real.exp_pos (2 * B)).le
  have hE := (Real.exp_pos (2 * (a + b))).le
  rw [abs_le]
  constructor
  · nlinarith [abs_nonneg a, mul_nonneg hB (add_nonneg (add_nonneg hΦ zero_le_one)
      (mul_nonneg zero_le_two (abs_nonneg a)))]
  · nlinarith [mul_le_mul_of_nonneg_left hexp hη₀, mul_le_mul_of_nonneg_right hηa hB]

/-- The derivative in `s` of the potential density `η (exp (2(a + s c)) - 1 - 2(a + s c))`. -/
private theorem hasDerivAt_mul_exp_sub_one_sub (η a c s : ℝ) :
    HasDerivAt (fun s ↦ η * (Real.exp (2 * (a + s * c)) - 1 - 2 * (a + s * c)))
      (η * (2 * Real.exp (2 * (a + s * c)) - 2) * c) s := by
  have hlin : HasDerivAt (fun s ↦ 2 * (a + s * c)) (2 * c) s := by
    simpa using (((hasDerivAt_id s).mul_const c).const_add a).const_mul 2
  convert ((hlin.exp.sub_const 1).sub hlin).const_mul η using 1
  ring

/-- The function `2 |φ| (exp (2B) (η (exp (2v) - 1 - 2v) + 1 + 2 |v|) + 1)`, which dominates the
derivatives of the potential density along `φ` at parameters `t` with `|t φ| ≤ B`, is
integrable. -/
private theorem integrable_potentialBound {η v φ : α → ℝ} {M : ℝ} (B : ℝ)
    (hφm : AEStronglyMeasurable φ μ) (hφM : ∀ x, |φ x| ≤ M) (hφ : Integrable φ μ)
    (hφv : Integrable (fun x ↦ φ x * v x) μ)
    (hpot : Integrable (fun x ↦ η x * (Real.exp (2 * v x) - 1 - 2 * v x)) μ) :
    Integrable (fun x ↦ 2 * |φ x| *
      (Real.exp (2 * B) * (η x * (Real.exp (2 * v x) - 1 - 2 * v x) + 1 + 2 * |v x|) + 1)) μ := by
  have h₁ : Integrable (fun x ↦ |φ x| * (η x * (Real.exp (2 * v x) - 1 - 2 * v x))) μ :=
    hpot.bdd_mul (continuous_abs.comp_aestronglyMeasurable hφm)
      (ae_of_all _ fun x ↦ by simpa using hφM x)
  refine (((h₁.const_mul (2 * Real.exp (2 * B))).add
    (hφ.abs.const_mul (2 * (Real.exp (2 * B) + 1)))).add
    (hφv.abs.const_mul (4 * Real.exp (2 * B)))).congr (ae_of_all _ fun x ↦ ?_)
  simp only [Pi.add_apply, abs_mul]
  ring

variable {η v φ : α → ℝ} {M : ℝ}

/-- Along a bounded, integrable direction `φ` with `φ v` integrable, the potential density
`η (exp (2(v + tφ)) - 1 - 2(v + tφ))` stays integrable for every `t` once it is integrable at
`t = 0`. -/
private theorem integrable_potential_add_mul (hη : AEStronglyMeasurable η μ)
    (hη₀ : ∀ x, 0 ≤ η x) (hη₁ : ∀ x, η x ≤ 1) (hv : AEStronglyMeasurable v μ)
    (hφm : AEStronglyMeasurable φ μ) (hφM : ∀ x, |φ x| ≤ M) (hφ : Integrable φ μ)
    (hφv : Integrable (fun x ↦ φ x * v x) μ)
    (hpot : Integrable (fun x ↦ η x * (Real.exp (2 * v x) - 1 - 2 * v x)) μ) (t : ℝ) :
    Integrable (fun x ↦ η x * (Real.exp (2 * (v x + t * φ x)) - 1 - 2 * (v x + t * φ x))) μ := by
  have hΦ : Continuous fun s : ℝ ↦ Real.exp (2 * s) - 1 - 2 * s := by fun_prop
  have hmeas : AEStronglyMeasurable
      (fun x ↦ η x * (Real.exp (2 * (v x + t * φ x)) - 1 - 2 * (v x + t * φ x))) μ :=
    hη.mul (hΦ.comp_aestronglyMeasurable (hv.add (hφm.const_mul t)))
  -- The mean value theorem on `[-|t|, |t|]` bounds the change of the density by `|t|` times the
  -- dominating function with `B = |t| M`.
  have hdiff : Integrable (fun x ↦
      η x * (Real.exp (2 * (v x + t * φ x)) - 1 - 2 * (v x + t * φ x)) -
        η x * (Real.exp (2 * v x) - 1 - 2 * v x)) μ := by
    refine Integrable.mono' ((integrable_potentialBound (|t| * M) hφm hφM hφ hφv hpot).const_mul
      |t|) (hmeas.sub hpot.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s ↦ η x * (Real.exp (2 * (v x + s * φ x)) - 1 - 2 * (v x + s * φ x)))
      (C := 2 * |φ x| * (Real.exp (2 * (|t| * M)) *
        (η x * (Real.exp (2 * v x) - 1 - 2 * v x) + 1 + 2 * |v x|) + 1))
      (fun s _ ↦ (hasDerivAt_mul_exp_sub_one_sub (η x) (v x) (φ x) s).hasDerivWithinAt)
      (fun s hs ↦ ?_) (convex_closedBall (0 : ℝ) |t|) (Metric.mem_closedBall_self (abs_nonneg t))
      (show t ∈ Metric.closedBall (0 : ℝ) |t| by simp)
    · simpa [Real.norm_eq_abs, mul_comm] using hmvt
    · rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at hs
      rw [Real.norm_eq_abs, abs_mul]
      have hb : |s * φ x| ≤ |t| * M := by
        rw [abs_mul]
        exact mul_le_mul hs (hφM x) (abs_nonneg _) (abs_nonneg t)
      nlinarith [abs_mul_two_mul_exp_sub_two_le (a := v x) (hη₀ x) (hη₁ x) hb, abs_nonneg (φ x)]
  refine (hdiff.add hpot).congr (ae_of_all _ fun x ↦ ?_)
  simp only [Pi.add_apply, sub_add_cancel]

/-- **The first variation of the potential.** Along a bounded, integrable direction `φ` with
`φ v` integrable, `t ↦ ∫ η (exp (2(v + tφ)) - 1 - 2(v + tφ))` has derivative
`∫ η (2 exp (2v) - 2) φ` at `t = 0`, and the integrand of the derivative is integrable. -/
private theorem hasDerivAt_integral_potential_add_mul (hη : AEStronglyMeasurable η μ)
    (hη₀ : ∀ x, 0 ≤ η x) (hη₁ : ∀ x, η x ≤ 1) (hv : AEStronglyMeasurable v μ)
    (hφm : AEStronglyMeasurable φ μ) (hφM : ∀ x, |φ x| ≤ M) (hφ : Integrable φ μ)
    (hφv : Integrable (fun x ↦ φ x * v x) μ)
    (hpot : Integrable (fun x ↦ η x * (Real.exp (2 * v x) - 1 - 2 * v x)) μ) :
    Integrable (fun x ↦ η x * (2 * Real.exp (2 * v x) - 2) * φ x) μ ∧
      HasDerivAt (fun t : ℝ ↦
        ∫ x, η x * (Real.exp (2 * (v x + t * φ x)) - 1 - 2 * (v x + t * φ x)) ∂μ)
        (∫ x, η x * (2 * Real.exp (2 * v x) - 2) * φ x ∂μ) 0 := by
  have hexp : Continuous fun s : ℝ ↦ 2 * Real.exp (2 * s) - 2 := by fun_prop
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := (0 : ℝ))
    (F' := fun t x ↦ η x * (2 * Real.exp (2 * (v x + t * φ x)) - 2) * φ x)
    (bound := fun x ↦ 2 * |φ x| *
      (Real.exp (2 * M) * (η x * (Real.exp (2 * v x) - 1 - 2 * v x) + 1 + 2 * |v x|) + 1))
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t ↦
      (integrable_potential_add_mul hη hη₀ hη₁ hv hφm hφM hφ hφv hpot t).aestronglyMeasurable)
    (integrable_potential_add_mul hη hη₀ hη₁ hv hφm hφM hφ hφv hpot 0)
    ((hη.mul (hexp.comp_aestronglyMeasurable (hv.add (hφm.const_mul 0)))).mul hφm)
    (ae_of_all _ fun x t ht ↦ ?_) (integrable_potentialBound M hφm hφM hφ hφv hpot)
    (ae_of_all _ fun x t _ ↦ hasDerivAt_mul_exp_sub_one_sub (η x) (v x) (φ x) t)
  · simpa using h
  · rw [mem_ball_zero_iff, Real.norm_eq_abs] at ht
    rw [Real.norm_eq_abs, abs_mul]
    have hb : |t * φ x| ≤ M := by
      rw [abs_mul]
      nlinarith [abs_nonneg t, abs_nonneg (φ x), hφM x]
    nlinarith [abs_mul_two_mul_exp_sub_two_le (a := v x) (hη₀ x) (hη₁ x) hb, abs_nonneg (φ x)]

end Potential

/-! ### The weak Euler–Lagrange equation -/

variable {P : Polynomial ℂ}

/-- If Taubes's functional is finite at `u ∈ H¹(ℂ)`, then the potential
`h (exp (2u) - 1 - 2u)` of `u` is integrable. -/
private theorem integrable_potential_of_ne_top {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : sobolevReducedFunctional P u ≠ ⊤) :
    Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) := by
  by_contra hni
  exact hu (sobolevReducedFunctional_eq_top hni)

/-- Taubes's functional on the line `u + t w` in `H¹(ℂ)`, where the value of `w` is represented by
a square-integrable function `φ`, at a parameter `t` where the potential is integrable: the
Dirichlet energy is `‖∇u + t ∇w‖₂² / 2` and the linear term is affine in `t`. -/
private theorem sobolevReducedFunctional_add_smul_eq (hm : 0 < P.natDegree)
    {u w : W1p (volume : Measure ℂ) ⊤ 2} {φ : ℂ → ℝ} (hφ2 : MemLp φ 2)
    (hwv : (W1p.value w : ℂ → ℝ) =ᵐ[volume] φ) {t : ℝ}
    (hpot : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * (W1p.value u z + t * φ z)) - 1 - 2 * (W1p.value u z + t * φ z))) :
    sobolevReducedFunctional P (u + t • w) =
      ((‖W1p.gradient u + t • W1p.gradient w‖ ^ 2 / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * (W1p.value u z + t * φ z)) - 1 - 2 * (W1p.value u z + t * φ z))) / 16 +
        ((∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
            (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z) +
          t * ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
            (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * φ z) : ℝ) : EReal) := by
  have hc2 := memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm
  have hv2 : MemLp (W1p.value u : ℂ → ℝ) 2 := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (W1p.value u)
  have hval : (W1p.value (u + t • w) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ W1p.value u z + t * φ z := by
    have h₁ := W1p.value_add_ae u (t • w)
    have h₂ := W1p.value_smul_ae t w
    simp only [Opens.coe_top, Measure.restrict_univ] at h₁ h₂
    filter_upwards [h₁, h₂, hwv] with z hz₁ hz₂ hz₃
    rw [hz₁, Pi.add_apply, hz₂, Pi.smul_apply, hz₃, smul_eq_mul]
  have hpotae : (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value (u + t • w) z) - 1 - 2 * W1p.value (u + t • w) z)) =ᵐ[volume]
      fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * (W1p.value u z + t * φ z)) - 1 - 2 * (W1p.value u z + t * φ z)) :=
    hval.mono fun z hz ↦ by simp only [hz]
  have hlin := integral_congr_ae (hval.mono fun z hz ↦
    congrArg ((2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * ·) hz)
  have hgrad : W1p.gradient (t • w) = t • W1p.gradient w := by
    rw [← W1p.gradientL_apply, map_smul, W1p.gradientL_apply]
  rw [sobolevReducedFunctional_eq_coe ((integrable_congr hpotae).2 hpot),
    integral_congr_ae hpotae, hlin, W1p.gradient_add, hgrad, ← integral_const_mul]
  congr 2
  rw [← integral_add]
  · exact integral_congr_ae (ae_of_all _ fun z ↦ by ring)
  · exact hc2.integrable_mul hv2
  · exact (hc2.integrable_mul hφ2).const_mul t

/-- **The first variation of Taubes's functional.** Let `P` be a complex polynomial of degree at
least one, let `u ∈ H¹(ℂ)` be a point where `TauCeti.Vortex.sobolevReducedFunctional P` is finite,
and let `w ∈ H¹(ℂ)` be represented by a compactly supported `C¹` function `φ`. Then the functional
is finite on the whole line `u + t w`, and as a function of `t` it has derivative

`∫ ⟪∇u, ∇φ⟫ + ∫ ((h exp (2u) - 1) / 8 + g) φ`

at `t = 0`, where `h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`. -/
theorem exists_hasDerivAt_sobolevReducedFunctional_add_smul (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2} (hu : sobolevReducedFunctional P u ≠ ⊤) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) {w : W1p (volume : Measure ℂ) ⊤ 2}
    (hwv : (W1p.value w : ℂ → ℝ) =ᵐ[volume] φ) (hwg : (W1p.gradient w : ℂ → ℂ) =ᵐ[volume] ∇ φ) :
    ∃ G : ℝ → ℝ, (∀ t : ℝ, sobolevReducedFunctional P (u + t • w) = G t) ∧
      HasDerivAt G ((∫ z, ⟪(W1p.gradient u : ℂ → ℂ) z, ∇ φ z⟫_ℝ) +
        ∫ z, ((‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * Real.exp (2 * W1p.value u z) - 1) / 8 +
          2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * φ z) 0 := by
  set η : ℂ → ℝ := fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) with hη_def
  set c : ℂ → ℝ := fun z ↦ 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
    (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8 with hc_def
  set v : ℂ → ℝ := (W1p.value u : ℂ → ℝ)
  -- Integrability and boundedness facts.
  have hφ2 : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hv2 : MemLp v 2 := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (W1p.value u)
  have hcφ : Integrable fun z ↦ c z * φ z :=
    (memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm).integrable_mul hφ2
  have hη : Continuous η := by
    simp only [hη_def]
    fun_prop (disch := intro z; positivity)
  have hη₀ (z : ℂ) : 0 ≤ η z := by positivity
  have hη₁ (z : ℂ) : η z ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hφM (z : ℂ) : |φ z| ≤ M := by simpa using hM z
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hφv : Integrable fun z ↦ φ z * v z := hφ2.integrable_mul hv2
  have hpot := integrable_potential_of_ne_top hu
  obtain ⟨hF'int, hF'⟩ := hasDerivAt_integral_potential_add_mul hη.aestronglyMeasurable hη₀ hη₁
    hv2.aestronglyMeasurable hφi.aestronglyMeasurable hφM hφi hφv hpot
  -- The functional along the line, as a real function of `t`.
  refine ⟨fun t ↦ ‖W1p.gradient u + t • W1p.gradient w‖ ^ 2 / 2 +
    (∫ z, η z * (Real.exp (2 * (v z + t * φ z)) - 1 - 2 * (v z + t * φ z))) / 16 +
    ((∫ z, c z * v z) + t * ∫ z, c z * φ z), fun t ↦ sobolevReducedFunctional_add_smul_eq hm hφ2
    hwv (integrable_potential_add_mul hη.aestronglyMeasurable hη₀ hη₁ hv2.aestronglyMeasurable
      hφi.aestronglyMeasurable hφM hφi hφv hpot t), ?_⟩
  -- Differentiate the Dirichlet energy, the potential and the linear term.
  have hnorm : HasDerivAt (fun t : ℝ ↦ ‖W1p.gradient u + t • W1p.gradient w‖ ^ 2 / 2)
      (⟪W1p.gradient u, W1p.gradient w⟫_ℝ) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).smul_const (W1p.gradient w)).const_add
      (W1p.gradient u)).norm_sq.div_const 2
    simp only [zero_smul, add_zero, one_smul] at h
    convert h using 1
    ring
  have hlin : HasDerivAt (fun t : ℝ ↦ (∫ z, c z * v z) + t * ∫ z, c z * φ z)
      (∫ z, c z * φ z) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (∫ z, c z * φ z)).const_add (∫ z, c z * v z)
  convert (hnorm.add (hF'.div_const 16)).add hlin using 1
  -- Identify the derivative.
  have hinner : ⟪W1p.gradient u, W1p.gradient w⟫_ℝ =
      ∫ z, ⟪(W1p.gradient u : ℂ → ℂ) z, ∇ φ z⟫_ℝ := by
    rw [MeasureTheory.L2.inner_def]
    simp only [Opens.coe_top, Measure.restrict_univ]
    exact integral_congr_ae (hwg.mono fun z hz ↦ by simp only [hz])
  have hsource : (∫ z, η z * (2 * Real.exp (2 * v z) - 2) * φ z) / 16 + ∫ z, c z * φ z =
      ∫ z, ((η z * Real.exp (2 * v z) - 1) / 8 +
        2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * φ z := by
    rw [← integral_div, ← integral_add (hF'int.div_const 16) hcφ]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    have hpos : 0 < 1 + ‖P.eval z‖ ^ 2 := by positivity
    simp only [hη_def, hc_def]
    field_simp
    ring
  simp only [hη_def] at hsource
  rw [hinner, add_assoc, hsource]

/-- **Minimizers of Taubes's functional solve the reduced equation weakly.** For a complex
polynomial `P` of degree at least one, let `u ∈ H¹(ℂ)` minimize
`TauCeti.Vortex.sobolevReducedFunctional P`. Then for every compactly supported `C¹` function `φ`,

`∫ ⟪∇u, ∇φ⟫ = -∫ ((h exp (2u) - 1) / 8 + g) φ`,

where `h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`: `u` is a weak solution of the
reduced vortex equation `Δu = (h exp (2u) - 1) / 8 + g`. -/
theorem integral_inner_gradient_eq_neg_integral_of_forall_le (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ z, ⟪(W1p.gradient u : ℂ → ℂ) z, ∇ φ z⟫_ℝ =
      -∫ z, ((‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * Real.exp (2 * W1p.value u z) - 1) / 8 +
        2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * φ z := by
  -- Represent `φ` in `H¹(ℂ)`.
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn
    (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2) hφ.contDiffOn
    ((hφ.continuous.memLp_of_hasCompactSupport hφc).restrict _) (hφc.memLp_gradient hφ)
  simp only [Opens.coe_top, Measure.restrict_univ] at hwv hwg
  -- The functional is finite at `u`, since `I(u) ≤ I(0) = 0`.
  obtain ⟨G, hG, hG'⟩ := exists_hasDerivAt_sobolevReducedFunctional_add_smul hm
    (ne_top_of_le_ne_top (by simp) (hu 0)) hφ hφc hwv hwg
  -- The function `G = I(u + t w)` has a minimum at `t = 0`, so its derivative vanishes there.
  have h0 := hG 0
  rw [zero_smul, add_zero] at h0
  have hmin : IsLocalMin G 0 := Eventually.of_forall fun t ↦ by
    have h := hu (u + t • w)
    rw [hG t, h0] at h
    exact EReal.coe_le_coe_iff.1 h
  exact eq_neg_of_add_eq_zero_left (hmin.hasDerivAt_eq_zero hG')

/-- **Minimizers of Taubes's functional solve the reduced equation in the sense of
distributions.** For a complex polynomial `P` of degree at least one and a minimizer `u ∈ H¹(ℂ)` of
`TauCeti.Vortex.sobolevReducedFunctional P`, every test function `φ` satisfies

`∫ Δφ u = ∫ ((h exp (2u) - 1) / 8 + g) φ`,

where `h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`. -/
theorem integral_laplacian_mul_eq_integral_of_forall_le (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v) (φ : 𝓓(⊤, ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z * W1p.value u z =
      ∫ z, ((‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * Real.exp (2 * W1p.value u z) - 1) / 8 +
        2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * φ z := by
  have h := (W1p.hasWeakFDerivOn u).integral_laplacian_smul_eq_neg_integral_inner φ
  simp only [smul_eq_mul] at h
  rw [h, neg_eq_iff_eq_neg, ← integral_inner_gradient_eq_neg_integral_of_forall_le hm hu
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport]
  exact integral_congr_ae (ae_of_all _ fun z ↦ real_inner_comm _ _)

/-- **The reduced vortex equation has a weak solution in `H¹(ℂ)`.** For a complex polynomial `P`
of degree at least one there is `u ∈ H¹(ℂ)` with

`∫ Δφ u = ∫ ((h exp (2u) - 1) / 8 + g) φ`

for every test function `φ`, where `h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`: a
minimizer of Taubes's functional. -/
theorem exists_forall_integral_laplacian_mul_eq (hm : 0 < P.natDegree) :
    ∃ u : W1p (volume : Measure ℂ) ⊤ 2, ∀ φ : 𝓓(⊤, ℝ),
      ∫ z, Δ (φ : ℂ → ℝ) z * W1p.value u z =
        ∫ z, ((‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * Real.exp (2 * W1p.value u z) - 1) / 8 +
          2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) * φ z :=
  (exists_forall_sobolevReducedFunctional_le hm).imp fun _ hu ↦
    integral_laplacian_mul_eq_integral_of_forall_le hm hu

end TauCeti.Vortex
