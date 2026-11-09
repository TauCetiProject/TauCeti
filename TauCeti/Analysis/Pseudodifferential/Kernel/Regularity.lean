/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Kernel.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# Regularity of the kernel of the Kohn–Nirenberg quantization

For a coefficient `a(x, ξ)` whose frequency slices are integrable, the kernel of its left
quantization is the absolutely convergent integral

`K_a(x, y) = ∫ exp(2πi ⟪ζ, x - y⟫) a(x, 2πζ) dζ`

(`TauCeti.quantizationKernel`). For a symbol `a ∈ S^m_{1,0}` on `ℝⁿ` this file proves that `K_a`
is as regular as the decay of `a` allows, and that off the diagonal it is smooth as soon as it is
defined by this integral, that is for every order `m < -n`.

Differentiating under the integral sign, a derivative of `K_a` in the position `x` falls either
on the position variable of `a` or on the phase, and a derivative in `y` falls on the phase:

`∂ K_a(x, y) · (h, h') = K_{∂ₓ a · h}(x, y) + K_{i ⟪ξ, h - h'⟫ a}(x, y)`.

The factor `⟪ξ, v⟫` is a symbol of order one (`TauCeti.Symbol.frequencyInner`), so each
derivative costs one order of decay, and `K_a` is `C^k` whenever `m + k < -n`. In particular the
kernel of a smoothing symbol is smooth.

Off the diagonal no decay is lost. Integrating by parts in the frequency gives
`(x - y)ⱼ K_a = K_{i ∂_{ξⱼ} a}` (`TauCeti.Symbol.quantizationKernel_frequencyDeriv`), so the
frequency Laplacian `Δ_ξ a = ∑ⱼ ∂²_{ξⱼ} a` (`TauCeti.Symbol.frequencyLaplacian`), which lowers the
order by two, satisfies `K_{Δ_ξ a}(x, y) = -‖x - y‖² K_a(x, y)`. Hence
`K_a(x, y) = (-‖x - y‖²)⁻ᴺ K_{Δ_ξᴺ a}(x, y)` for `x ≠ y`, and taking `N` large makes the right side
as regular as wanted.

## Main results

* `TauCeti.Symbol.differentiable_quantizationKernel` and
  `TauCeti.Symbol.fderiv_quantizationKernel_apply`: for a symbol of order `m` with `m + 1 < -n`,
  the kernel is differentiable, with the derivative displayed above.
* `TauCeti.Symbol.frequencyInner`: the symbol `⟪ξ, v⟫` of order one.
* `TauCeti.Symbol.contDiff_quantizationKernel`: the kernel of a symbol of order `m` is `C^k`
  when `m + k < -n`.
* `TauCeti.Symbol.IsSmoothing.contDiff_quantizationKernel`: the kernel of a smoothing symbol is
  smooth.
* `TauCeti.Symbol.quantizationKernel_frequencyLaplacian`: `K_{Δ_ξ a} = -‖x - y‖² K_a`.
* `TauCeti.Symbol.contDiffOn_quantizationKernel`: the kernel of a symbol of order `m < -n` is
  smooth off the diagonal.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform RealInnerProductSpace ContDiff
open MeasureTheory Real Module ContinuousLinearMap

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-! ### Differentiation of the kernel -/

section Deriv

/-! The kernel integrand is treated for a coefficient with values in an arbitrary complex normed
space `F`, which in the applications is `V →L[ℂ] W`. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {a : E × E → F} {m : ℝ}

/-- The derivative in `p = (x, y)` of the kernel integrand
`p ↦ 𝐞 ⟪ζ, x - y⟫ • a (x, 2πζ)`. -/
private def kernelIntegrandFDeriv (a : E × E → F) (p : E × E) (ζ : E) : E × E →L[ℝ] F :=
  (𝐞 ⟪ζ, p.1 - p.2⟫ : ℂ) • ((fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) p.1).comp (fst ℝ E E)) +
    ((toSpanSingleton ℝ (2 * π * Complex.I * 𝐞 ⟪ζ, p.1 - p.2⟫)).comp
      ((innerSL ℝ ζ).comp (fst ℝ E E - snd ℝ E E))).smulRight (a (p.1, (2 * π) • ζ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma kernelIntegrandFDeriv_apply (p : E × E) (ζ : E) (q : E × E) :
    kernelIntegrandFDeriv a p ζ q =
      (𝐞 ⟪ζ, p.1 - p.2⟫ : ℂ) • fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) p.1 q.1 +
        (𝐞 ⟪ζ, p.1 - p.2⟫ : ℂ) • ((Complex.I * ⟪(2 * π) • ζ, q.1 - q.2⟫ : ℂ) •
          a (p.1, (2 * π) • ζ)) := by
  simp only [kernelIntegrandFDeriv, add_apply, smul_apply, comp_apply, coe_fst',
    smulRight_apply, toSpanSingleton_apply, innerSL_apply_apply, sub_apply, coe_snd', smul_smul,
    inner_smul_left, conj_trivial, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 2
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma hasFDerivAt_kernelIntegrand (ha : ContDiff ℝ 1 a) (ζ : E) (p : E × E) :
    HasFDerivAt (fun p : E × E ↦ 𝐞 ⟪ζ, p.1 - p.2⟫ • a (p.1, (2 * π) • ζ))
      (kernelIntegrandFDeriv a p ζ) p := by
  have hg : HasFDerivAt (fun p : E × E ↦ a (p.1, (2 * π) • ζ))
      ((fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) p.1).comp (fst ℝ E E)) p :=
    (((ha.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero
      p.1).hasFDerivAt).comp p hasFDerivAt_fst
  have hc := (Real.hasDerivAt_fourierChar ⟪ζ, p.1 - p.2⟫).hasFDerivAt.comp p
    (((innerSL ℝ ζ).comp (fst ℝ E E - snd ℝ E E)).hasFDerivAt (x := p))
  simp only [Circle.smul_def]
  exact hc.smul hg

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the kernel integrand is dominated by `⟨2πζ⟩ ^ (m + 1)`: the derivative of
the phase costs one power of the frequency. -/
private lemma norm_kernelIntegrandFDeriv_le {p : E × E} {C C' : ℝ}
    (hC : ∀ ξ, ‖a (p.1, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ ξ, ‖fderiv ℝ (fun y ↦ a (y, ξ)) p.1‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (ζ : E) :
    ‖kernelIntegrandFDeriv a p ζ‖ ≤ (C' + 2 * C) * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m + 1) / 2) := by
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  have hC'0 : 0 ≤ C' := by
    have := (norm_nonneg (fderiv ℝ (fun y ↦ a (y, 0)) p.1)).trans (hC' 0)
    simpa using this
  set ξ := (2 * π) • ζ
  set w := 1 + ‖ξ‖ ^ 2
  have hw₁ : w ^ (m / 2) * ‖ξ‖ ≤ w ^ ((m + 1) / 2) := one_add_norm_sq_rpow_mul_norm_le ξ m
  have hw₂ : w ^ (m / 2) ≤ w ^ ((m + 1) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)
  refine opNorm_le_bound _ (by positivity) fun q ↦ ?_
  rw [kernelIntegrandFDeriv_apply]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, Circle.norm_coe, one_mul]
  have hq : ‖q.1 - q.2‖ ≤ 2 * ‖q‖ := by
    have := norm_fst_le q
    have := norm_snd_le q
    linarith [norm_sub_le q.1 q.2]
  have h₁ : ‖fderiv ℝ (fun y ↦ a (y, ξ)) p.1 q.1‖ ≤ C' * w ^ (m / 2) * ‖q‖ :=
    (le_opNorm _ _).trans (mul_le_mul (hC' ξ) (norm_fst_le q) (norm_nonneg _) (by positivity))
  have h₂ : ‖(Complex.I * ⟪ξ, q.1 - q.2⟫ : ℂ)‖ * ‖a (p.1, ξ)‖ ≤
      2 * C * (w ^ (m / 2) * ‖ξ‖) * ‖q‖ := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |⟪ξ, q.1 - q.2⟫| * ‖a (p.1, ξ)‖ ≤ (‖ξ‖ * (2 * ‖q‖)) * (C * w ^ (m / 2)) :=
          mul_le_mul ((abs_real_inner_le_norm _ _).trans (by gcongr)) (hC ξ) (norm_nonneg _)
            (by positivity)
      _ = 2 * C * (w ^ (m / 2) * ‖ξ‖) * ‖q‖ := by ring
  calc _ ≤ C' * w ^ (m / 2) * ‖q‖ + 2 * C * (w ^ (m / 2) * ‖ξ‖) * ‖q‖ := add_le_add h₁ h₂
    _ ≤ C' * w ^ ((m + 1) / 2) * ‖q‖ + 2 * C * w ^ ((m + 1) / 2) * ‖q‖ := by gcongr
    _ = (C' + 2 * C) * w ^ ((m + 1) / 2) * ‖q‖ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
private lemma continuous_kernelIntegrandFDeriv (ha : ContDiff ℝ 1 a) (p : E × E) :
    Continuous (kernelIntegrandFDeriv a p) := by
  have hD : Continuous fun ζ : E ↦ fderiv ℝ (fun y ↦ a (y, (2 * π) • ζ)) p.1 :=
    (ContDiff.fderiv (f := fun (ζ : E) (y : E) ↦ a (y, (2 * π) • ζ))
      (ha.comp (contDiff_snd.prodMk (contDiff_fst.const_smul _))) contDiff_const
      (n := 0) (by simp)).continuous
  have he : Continuous fun ζ : E ↦ (𝐞 ⟪ζ, p.1 - p.2⟫ : ℂ) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const))
  have ha' : Continuous fun ζ : E ↦ a (p.1, (2 * π) • ζ) :=
    ha.continuous.comp (continuous_const.prodMk (continuous_const_smul _))
  refine continuous_clm_apply.2 fun q ↦ ?_
  simp only [kernelIntegrandFDeriv_apply]
  fun_prop

omit [NormedSpace ℂ F] in
/-- A function bounded by `C ⟨ξ⟩ ^ s` with `s < -n` is integrable. -/
private lemma integrable_of_norm_le_rpow {f : E → F} (hf : AEStronglyMeasurable f) {C s : ℝ}
    (hs : s < -finrank ℝ E) (hC : ∀ ξ, ‖f ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (s / 2)) : Integrable f := by
  have hweight := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure E))
    (r := -s) (by linarith)
  exact (hweight.const_mul C).mono' hf (ae_of_all _ fun ξ ↦ by simpa only [neg_neg] using hC ξ)

end Deriv

namespace Symbol

/-! ### Kernels of symbols are as regular as their decay allows -/

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The weight `⟨2πζ⟩ ^ m` is integrable for `m < -n`. -/
private lemma integrable_weight_smul {m : ℝ} (hm : m < -n) :
    Integrable fun ζ : CoordinateSpace n ↦ (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) := by
  have h := (integrable_rpow_neg_one_add_norm_sq
    (μ := (volume : Measure (CoordinateSpace n))) (r := -m) (by simp; linarith)
    ).comp_smul two_pi_pos.ne'
  simpa only [neg_neg] using h

/-- Differentiation under the integral sign in the kernel integral. For a `C¹` coefficient whose
values and position derivatives are bounded by `C_K ⟨ξ⟩ ^ m` locally uniformly in the position,
`m + 1 < -n`, the derivative of the kernel integral is the integral of the derivative of the
integrand. -/
private lemma hasFDerivAt_integral_kernelIntegrand {m : ℝ}
    {a : CoordinateSpace n × CoordinateSpace n → F} (ha : ContDiff ℝ 1 a) (hm : m + 1 < -n)
    (hC : ∀ K : Set (CoordinateSpace n), IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ K : Set (CoordinateSpace n), IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, ‖fderiv ℝ (fun y ↦ a (y, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦
        ∫ ζ, 𝐞 ⟪ζ, p.1 - p.2⟫ • a (p.1, (2 * π) • ζ))
      (∫ ζ, kernelIntegrandFDeriv a p₀ ζ) p₀ := by
  have hn : (n : ℝ) = finrank ℝ (CoordinateSpace n) := by simp
  obtain ⟨C, hC⟩ := hC _ (isCompact_closedBall p₀.1 1)
  obtain ⟨C', hC'⟩ := hC' _ (isCompact_closedBall p₀.1 1)
  have hmem {p : CoordinateSpace n × CoordinateSpace n} (hp : p ∈ Metric.ball p₀ 1) :
      p.1 ∈ Metric.closedBall p₀.1 1 := by
    refine Metric.ball_subset_closedBall (Metric.mem_ball.2 (lt_of_le_of_lt ?_
      (Metric.mem_ball.1 hp)))
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hcont (p : CoordinateSpace n × CoordinateSpace n) :
      Continuous fun ζ ↦ 𝐞 ⟪ζ, p.1 - p.2⟫ • a (p.1, (2 * π) • ζ) :=
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      (ha.continuous.comp (continuous_const.prodMk (continuous_const_smul _)))
  have hslice : Integrable fun ξ ↦ a (p₀.1, ξ) :=
    integrable_of_norm_le_rpow
      (ha.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (by rw [← hn]; linarith) (hC p₀.1 (Metric.mem_closedBall_self zero_le_one))
  have hint : Integrable fun ζ ↦ 𝐞 ⟪ζ, p₀.1 - p₀.2⟫ • a (p₀.1, (2 * π) • ζ) :=
    (hslice.comp_smul two_pi_pos.ne').norm.mono' (hcont p₀).aestronglyMeasurable
      (ae_of_all _ fun ζ ↦ by rw [Circle.norm_smul])
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p₀ one_pos)
    (Filter.Eventually.of_forall fun p ↦ (hcont p).aestronglyMeasurable) hint
    (continuous_kernelIntegrandFDeriv ha p₀).aestronglyMeasurable
    (ae_of_all _ fun ζ p hp ↦ norm_kernelIntegrandFDeriv_le (hC p.1 (hmem hp))
      (hC' p.1 (hmem hp)) ζ)
    ((integrable_weight_smul hm).const_mul _)
    (ae_of_all _ fun ζ p _ ↦ hasFDerivAt_kernelIntegrand ha ζ p)

variable {m : ℝ}

/-- The frequency monomial `⟪ξ, v⟫`, acting on `V` by scalar multiplication, as a symbol of order
one. Up to the factor `i`, it is the symbol of the directional derivative `∂_v`. -/
def frequencyInner (v : CoordinateSpace n) : Symbol n V V 1 where
  coefficient p := (⟪p.2, v⟫ : ℂ) • ContinuousLinearMap.id ℂ V
  contDiff_coefficient :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_snd.inner ℝ contDiff_const)).smul contDiff_const
  exists_bound K _ α β := by
    -- the coefficient is the continuous linear map `L` of the frequency
    set L : CoordinateSpace n →L[ℝ] V →L[ℂ] V :=
      (Complex.ofRealCLM.comp (innerSL ℝ v)).smulRight (ContinuousLinearMap.id ℂ V)
    have hL (ξ : CoordinateSpace n) : L ξ = (⟪ξ, v⟫ : ℂ) • ContinuousLinearMap.id ℂ V := by
      simp [L, real_inner_comm]
    have hnorm (ξ : CoordinateSpace n) : ‖L ξ‖ ≤ ‖v‖ * ‖ξ‖ := by
      rw [hL]
      refine (opNorm_smul_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |⟪ξ, v⟫| * ‖ContinuousLinearMap.id ℂ V‖ ≤ (‖ξ‖ * ‖v‖) * 1 :=
            mul_le_mul (abs_real_inner_le_norm _ _) norm_id_le (norm_nonneg _) (by positivity)
        _ = ‖v‖ * ‖ξ‖ := by ring
    refine ⟨‖v‖, norm_nonneg _, fun x _ ξ ↦ ?_⟩
    have hβ : mixedDeriv α β (fun p : CoordinateSpace n × CoordinateSpace n ↦
        (⟪p.2, v⟫ : ℂ) • ContinuousLinearMap.id ℂ V) x ξ =
          mixedDeriv α β (fun p ↦ L p.2) x ξ := by simp only [hL]
    rw [hβ, mixedDeriv_def]
    dsimp only
    rcases α with _ | ⟨i, α⟩
    · rw [coordinateDeriv_nil]
      rcases β with _ | ⟨k, _ | ⟨k', β⟩⟩
      · simp only [coordinateDeriv_nil, List.length_nil, Nat.cast_zero, sub_zero]
        refine (hnorm ξ).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        simpa [one_div] using one_add_norm_sq_rpow_mul_norm_le ξ 0
      · simp only [L.coordinateDeriv_singleton, List.length_singleton, Nat.cast_one, sub_self,
          zero_div, Real.rpow_zero, mul_one]
        exact (hnorm _).trans (by simp)
      · rw [L.coordinateDeriv_cons_cons, Pi.zero_apply, norm_zero]
        exact mul_nonneg (norm_nonneg _) (rpow_weight_pos ξ _).le
    · rw [coordinateDeriv_const _ (List.cons_ne_nil i α), Pi.zero_apply, norm_zero]
      exact mul_nonneg (norm_nonneg _) (rpow_weight_pos ξ _).le

@[simp]
theorem coefficient_frequencyInner (v : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (frequencyInner v : Symbol n V V 1).coefficient p =
      (⟪p.2, v⟫ : ℂ) • ContinuousLinearMap.id ℂ V :=
  (rfl)

/-! ### Differentiation of the kernel of a symbol -/

private lemma uncurry_quantizationKernel_eq (a : Symbol n V W m) :
    Function.uncurry (quantizationKernel a.coefficient) =
      fun p : CoordinateSpace n × CoordinateSpace n ↦
        ∫ ζ, 𝐞 ⟪ζ, p.1 - p.2⟫ • a.coefficient (p.1, (2 * π) • ζ) :=
  funext fun p ↦ quantizationKernel_def a.coefficient p.1 p.2

private lemma hasFDerivAt_quantizationKernel (a : Symbol n V W m) (hm : m + 1 < -n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (Function.uncurry (quantizationKernel a.coefficient))
      (∫ ζ, kernelIntegrandFDeriv a.coefficient p ζ) p := by
  rw [uncurry_quantizationKernel_eq]
  exact hasFDerivAt_integral_kernelIntegrand (a.contDiff_coefficient.of_le (by simp)) hm
    (fun K hK ↦ (a.exists_bound_coefficient K hK).imp fun _ h ↦ h.2)
    a.exists_bound_fderiv_coefficient p

/-- **Differentiability of the kernel.** The kernel `(x, y) ↦ K_a(x, y)` of a symbol of order
`m` with `m + 1 < -n` is differentiable. -/
theorem differentiable_quantizationKernel (a : Symbol n V W m) (hm : m + 1 < -n) :
    Differentiable ℝ (Function.uncurry (quantizationKernel a.coefficient)) := fun p ↦
  (a.hasFDerivAt_quantizationKernel hm p).differentiableAt

/-- **Derivative of the kernel.** For a symbol of order `m` with `m + 1 < -n`, the derivative of
`K_a` at `(x, y)` in the direction `(h, h')` is
`K_{∂ₓ a · h}(x, y) + K_{i ⟪ξ, h - h'⟫ a}(x, y)`: the derivative falls either on the position
variable of the coefficient or on the phase `exp(i ⟪x - y, ξ⟫)`. -/
theorem fderiv_quantizationKernel_apply (a : Symbol n V W m) (hm : m + 1 < -n)
    (p q : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (Function.uncurry (quantizationKernel a.coefficient)) p q =
      quantizationKernel (fun r ↦ fderiv ℝ (fun y ↦ a.coefficient (y, r.2)) r.1 q.1) p.1 p.2 +
        quantizationKernel (fun r ↦ (Complex.I * ⟪r.2, q.1 - q.2⟫ : ℂ) • a.coefficient r)
          p.1 p.2 := by
  have ha : ContDiff ℝ 1 a.coefficient := a.contDiff_coefficient.of_le (by simp)
  have hn : m < -(finrank ℝ (CoordinateSpace n) : ℝ) := by simp; linarith
  obtain ⟨C, hC0, hC⟩ := a.exists_bound_coefficient {p.1} isCompact_singleton
  obtain ⟨C', hC'⟩ := a.exists_bound_fderiv_coefficient {p.1} isCompact_singleton
  have hC₁ := hC p.1 rfl
  have hC'₁ := hC' p.1 rfl
  have hD : Integrable (kernelIntegrandFDeriv a.coefficient p) :=
    ((integrable_weight_smul (m := m + 1) hm).const_mul (C' + 2 * C)).mono'
      (continuous_kernelIntegrandFDeriv ha p).aestronglyMeasurable
      (ae_of_all _ (norm_kernelIntegrandFDeriv_le hC₁ hC'₁))
  -- the frequency slices of the two new coefficients are integrable
  have hcont₁ : Continuous fun ξ ↦ fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) p.1 q.1 :=
    (ContDiff.fderiv (f := fun (ξ : CoordinateSpace n) (y : CoordinateSpace n) ↦
      a.coefficient (y, ξ)) (ha.comp (contDiff_snd.prodMk contDiff_fst)) contDiff_const
      (n := 0) (by simp)).continuous.clm_apply continuous_const
  have hint₁ : Integrable fun ξ ↦ fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) p.1 q.1 :=
    integrable_of_norm_le_rpow hcont₁.aestronglyMeasurable (C := C' * ‖q.1‖) hn fun ξ ↦
      ((le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hC'₁ ξ) (norm_nonneg _))).trans_eq
        (by ring)
  have hslice := a.continuous_coefficient_slice p.1
  have hint₂ : Integrable fun ξ ↦ (Complex.I * ⟪ξ, q.1 - q.2⟫ : ℂ) • a.coefficient (p.1, ξ) := by
    refine integrable_of_norm_le_rpow (by fun_prop) (C := ‖q.1 - q.2‖ * C) (s := m + 1)
      (by simp; linarith) fun ξ ↦ ?_
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |⟪ξ, q.1 - q.2⟫| * ‖a.coefficient (p.1, ξ)‖
        ≤ (‖q.1 - q.2‖ * ‖ξ‖) * (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
          mul_le_mul ((abs_real_inner_le_norm _ _).trans_eq (mul_comm _ _)) (hC₁ ξ)
            (norm_nonneg _) (by positivity)
      _ = ‖q.1 - q.2‖ * C * ((1 + ‖ξ‖ ^ 2) ^ (m / 2) * ‖ξ‖) := by ring
      _ ≤ ‖q.1 - q.2‖ * C * (1 + ‖ξ‖ ^ 2) ^ ((m + 1) / 2) := by
          gcongr
          exact one_add_norm_sq_rpow_mul_norm_le ξ m
  have hI₁ := integrable_quantizationKernel_integrand
    (a := fun r ↦ fderiv ℝ (fun y ↦ a.coefficient (y, r.2)) r.1 q.1) hint₁ p.2
  have hI₂ := integrable_quantizationKernel_integrand
    (a := fun r ↦ (Complex.I * ⟪r.2, q.1 - q.2⟫ : ℂ) • a.coefficient r) hint₂ p.2
  rw [(a.hasFDerivAt_quantizationKernel hm p).fderiv, integral_apply hD, quantizationKernel_def,
    quantizationKernel_def, ← integral_add hI₁ hI₂]
  refine integral_congr_ae (ae_of_all _ fun ζ ↦ ?_)
  simp only [kernelIntegrandFDeriv_apply, Circle.smul_def]

/-! ### Regularity of the kernel -/

/-- The coefficient of `∑ⱼ hⱼ ∂_{xⱼ} a` is the position derivative of `a` in the direction `h`. -/
private lemma coefficient_sum_smul_spatialDeriv (a : Symbol n V W m) (h : CoordinateSpace n)
    (r : CoordinateSpace n × CoordinateSpace n) :
    (∑ j, (h j : ℂ) • spatialDeriv j a).coefficient r =
      fderiv ℝ (fun y ↦ a.coefficient (y, r.2)) r.1 h := by
  obtain ⟨x, ξ⟩ := r
  simp only [coefficient_sum, Finset.sum_apply, coefficient_smul, Pi.smul_apply,
    ← fderiv_coefficient_single]
  simp only [Complex.coe_smul]
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h]
  simp

/-- **Regularity of the kernel.** The kernel `(x, y) ↦ K_a(x, y)` of a symbol of order `m` is `C^k`
whenever `m + k < -n`: each derivative of the kernel costs one order of decay of the symbol. -/
theorem contDiff_quantizationKernel (a : Symbol n V W m) {k : ℕ} (hk : m + k < -n) :
    ContDiff ℝ k (Function.uncurry (quantizationKernel a.coefficient)) := by
  induction k generalizing m with
  | zero => exact contDiff_zero.2 (a.continuous_quantizationKernel (by simpa using hk))
  | succ k ih =>
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    push_cast at hk
    have hm : m + 1 < -n := by linarith
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨a.differentiable_quantizationKernel hm, by simp,
      contDiff_clm_apply_iff.2 fun q ↦ ?_⟩
    -- each directional derivative is the sum of the kernels of two symbols of order `m + 1`
    have h₁ := ih (∑ j, (q.1 j : ℂ) • spatialDeriv j a) (by linarith)
    have h₂ := ih (Complex.I • (frequencyInner (V := W) (q.1 - q.2)).comp a) (by linarith)
    have heq : (fun p ↦ fderiv ℝ (Function.uncurry (quantizationKernel a.coefficient)) p q) =
        Function.uncurry (quantizationKernel (∑ j, (q.1 j : ℂ) • spatialDeriv j a).coefficient) +
          Function.uncurry (quantizationKernel
            (Complex.I • (frequencyInner (V := W) (q.1 - q.2)).comp a).coefficient) := by
      funext p
      rw [a.fderiv_quantizationKernel_apply hm p q, Pi.add_apply, Function.uncurry_def,
        Function.uncurry_def]
      congr 2 <;> funext r
      · rw [coefficient_sum_smul_spatialDeriv]
      · simp only [coefficient_smul, Pi.smul_apply, coefficient_comp, coefficient_frequencyInner,
          ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp, smul_smul]
    rw [heq]
    exact h₁.add h₂

/-- **Kernels of smoothing symbols are smooth.** -/
theorem IsSmoothing.contDiff_quantizationKernel {a : Symbol n V W m} (ha : a.IsSmoothing) :
    ContDiff ℝ ∞ (Function.uncurry (quantizationKernel a.coefficient)) :=
  contDiff_infty.2 fun k ↦ by
    obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha (-n - k - 1)
    rw [← hb]
    exact b.contDiff_quantizationKernel (by linarith)

/-! ### Smoothness off the diagonal -/

/-- The frequency Laplacian `Δ_ξ a = ∑ⱼ ∂²_{ξⱼ} a` of a symbol of order `m`, a symbol of order
`m - 2`. -/
def frequencyLaplacian : Symbol n V W m →ₗ[ℂ] Symbol n V W (m - 2) :=
  inclusion (by linarith : m - 1 - 1 ≤ m - 2) ∘ₗ ∑ j, frequencyDeriv j ∘ₗ frequencyDeriv j

@[simp]
theorem coefficient_frequencyLaplacian (a : Symbol n V W m) (x ξ : CoordinateSpace n) :
    (frequencyLaplacian a).coefficient (x, ξ) =
      ∑ j, coordinateDeriv [j, j] (fun η ↦ a.coefficient (x, η)) ξ := by
  simp only [frequencyLaplacian, LinearMap.coe_comp, Function.comp_apply, coefficient_inclusion,
    LinearMap.sum_apply, coefficient_sum, Finset.sum_apply, coefficient_frequencyDeriv]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show [j, j] = [j] ++ [j] from rfl, coordinateDeriv_append]

/-- **Kernel of the frequency Laplacian.** For a symbol of order `m < -n`, integrating by parts
twice in each frequency coordinate gives `K_{Δ_ξ a}(x, y) = -‖x - y‖² K_a(x, y)`. -/
theorem quantizationKernel_frequencyLaplacian (a : Symbol n V W m) (hm : m < -n)
    (x y : CoordinateSpace n) :
    quantizationKernel (frequencyLaplacian a).coefficient x y =
      (-‖x - y‖ ^ 2) • quantizationKernel a.coefficient x y := by
  have hcoef : (frequencyLaplacian a).coefficient =
      ∑ j, (frequencyDeriv j (frequencyDeriv j a)).coefficient := by
    simp [frequencyLaplacian]
  rw [hcoef, quantizationKernel_sum _ fun j _ ↦
    (frequencyDeriv j (frequencyDeriv j a)).integrable_coefficient (by linarith) x]
  simp only [quantizationKernel_frequencyDeriv _ (by linarith : m - 1 < -n),
    quantizationKernel_frequencyDeriv _ hm, smul_smul, ← Finset.sum_smul,
    EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [← Complex.coe_smul]
  congr 1
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  linear_combination ((x - y) j : ℂ) ^ 2 * Complex.I_sq

/-- Iterating `quantizationKernel_frequencyLaplacian`: some symbol of order `m - 2N`, namely
`Δ_ξᴺ a`, has kernel `(-‖x - y‖²)ᴺ K_a(x, y)`. -/
private lemma exists_quantizationKernel_eq_pow_smul (a : Symbol n V W m) (hm : m < -n) (N : ℕ) :
    ∃ b : Symbol n V W (m - 2 * N), ∀ x y,
      quantizationKernel b.coefficient x y =
        (-‖x - y‖ ^ 2) ^ N • quantizationKernel a.coefficient x y := by
  induction N with
  | zero => exact ⟨inclusion (by simp) a, fun x y ↦ by simp⟩
  | succ N ih =>
    obtain ⟨b, hb⟩ := ih
    have hN : (0 : ℝ) ≤ N := N.cast_nonneg
    refine ⟨inclusion (by push_cast; linarith) (frequencyLaplacian b), fun x y ↦ ?_⟩
    rw [coefficient_inclusion, b.quantizationKernel_frequencyLaplacian (by linarith), hb,
      smul_smul, ← pow_succ']

/-- **The kernel is smooth off the diagonal.** For a symbol of order `m < -n`, the kernel
`(x, y) ↦ K_a(x, y)` is smooth on `{x ≠ y}`. There `K_a = (-‖x - y‖²)⁻ᴺ K_{Δ_ξᴺ a}`, and
`Δ_ξᴺ a` has order `m - 2N`, so its kernel is `C^k` for `N ≥ k`. -/
theorem contDiffOn_quantizationKernel (a : Symbol n V W m) (hm : m < -n) :
    ContDiffOn ℝ ∞ (Function.uncurry (quantizationKernel a.coefficient)) {p | p.1 ≠ p.2} := by
  refine contDiffOn_infty.2 fun k ↦ ?_
  obtain ⟨b, hb⟩ := a.exists_quantizationKernel_eq_pow_smul hm k
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hbk := b.contDiff_quantizationKernel (k := k) (by linarith)
  have hw : ContDiff ℝ k fun p : CoordinateSpace n × CoordinateSpace n ↦ (-‖p.1 - p.2‖ ^ 2) ^ k :=
    ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)).neg.pow k
  have hne {p : CoordinateSpace n × CoordinateSpace n} (hp : p ∈ {p | p.1 ≠ p.2}) :
      (-‖p.1 - p.2‖ ^ 2) ^ k ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.2 (pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 hp))))
  refine ((hw.contDiffOn.inv fun p hp ↦ hne hp).smul hbk.contDiffOn).congr fun p hp ↦ ?_
  simp only [Function.uncurry_def, Pi.smul_apply', Pi.inv_apply, hb, smul_smul,
    inv_mul_cancel₀ (hne hp), one_smul]

end Symbol

end TauCeti
