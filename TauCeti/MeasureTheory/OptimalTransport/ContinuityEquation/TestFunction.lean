/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.FDeriv.Measurable

/-!
# Test functions for the continuity equation

The definition `TauCeti.IsContinuityEquation` tests the continuity equation
`∂ₜ μₜ + div (vₜ μₜ) = 0` on `(a, b)` only against smooth compactly supported functions
`φ : ℝ × E → ℝ` with support in `(a, b) × E`. The functions built in practice from a solution are
seldom of this kind: composing with the flow of a `C¹` velocity field gives only `C¹` functions,
and convolving with an everywhere positive kernel, or testing against a bounded function of space
alone, gives functions without compact support in space. This file shows that the distributional
identity

`∫_a^b ∫ (∂ₜ φ (t, x) + ⟨∇ₓ φ (t, x), vₜ x⟩) dμₜ(x) dt = 0`

holds for every `C¹` function `φ` with bounded derivative and support in `(a, b) × E`, with no
compactness of the support in space. Such a `φ` is automatically bounded, since it vanishes at the
time `a`; the integrability built into `TauCeti.IsContinuityEquation` of the total mass and of
`‖vₜ‖` against `μₜ dt` is exactly what makes the identity absolutely convergent.

The proof has two approximation steps, each closed by dominated convergence. A `C¹` compactly
supported test function is the limit of its convolutions with shrinking normalized smooth bumps,
which are smooth, compactly supported, have support in `(a, b) × E` once the bump is small, and
have derivatives converging pointwise with a uniform bound. A `C¹` test function with bounded
derivative is the limit of its products with the spatial cut-offs `x ↦ χ (x / R)` for a fixed bump
`χ` equal to `1` near `0`, whose derivatives are of size `1 / R`.

## Main results

* `TauCeti.IsContinuityEquation.integral_integral_fderiv_eq_zero_of_hasCompactSupport`: the
  continuity equation holds against every `C¹` compactly supported test function with support in
  `(a, b) × E`.
* `TauCeti.IsContinuityEquation.integral_integral_fderiv_eq_zero_of_norm_fderiv_le`: it holds
  against every `C¹` test function with bounded derivative and support in `(a, b) × E`.
* `TauCeti.IsContinuityEquation.integral_deriv_mul_integral_eq_neg`: for a bounded `C¹` function
  `u` of time and space with bounded derivative, the weak time derivative of `t ↦ ∫ u (t, ·) dμₜ`
  on `(a, b)` is `t ↦ ∫ (∂ₜ u + ⟨∇ₓ u, vₜ⟩) dμₜ`.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §8.1, equations (8.1.3) and (8.1.4).
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §4.1.
-/

public section

open MeasureTheory Set Function Filter Topology Metric ContinuousLinearMap
open scoped ENNReal Pointwise Convolution

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : ℝ → Measure E} {v : ℝ → E → E} {a b : ℝ}

/-- The derivative of the convolution of a normalized bump with a compactly supported `C¹` function
is the convolution of the bump with the derivative. -/
theorem fderiv_normed_convolution_apply_of_contDiff {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G] [FiniteDimensional ℝ G] {ν : Measure G}
    [ν.IsAddHaarMeasure] (β : ContDiffBump (0 : G)) {φ : G → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (q w : G) :
    fderiv ℝ (β.normed ν ⋆[lsmul ℝ ℝ, ν] φ) q w =
      (β.normed ν ⋆[lsmul ℝ ℝ, ν] fun p ↦ fderiv ℝ φ p w) q := by
  have hρ : LocallyIntegrable (β.normed ν) ν := β.continuous_normed.locallyIntegrable
  rw [(hφc.hasFDerivAt_convolution_right _ hρ hφ q).fderiv]
  exact convolution_precompR_apply _ hρ (hφc.fderiv ℝ) (hφ.continuous_fderiv one_ne_zero) q w

/-- Mollifying a compactly supported `C¹` function with a normalized bump multiplies the bound on
its derivative by at most `3`. -/
theorem norm_fderiv_normed_convolution_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [FiniteDimensional ℝ G] {ν : Measure G}
    [ν.IsAddHaarMeasure] (β : ContDiffBump (0 : G)) {φ : G → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) {C : ℝ} (hC : ∀ p, ‖fderiv ℝ φ p‖ ≤ C) (q w : G) :
    ‖fderiv ℝ (β.normed ν ⋆[lsmul ℝ ℝ, ν] φ) q w‖ ≤ 3 * (C * ‖w‖) := by
  have hDφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hg (p : G) : ‖fderiv ℝ φ p w‖ ≤ C * ‖w‖ := ((fderiv ℝ φ p).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hC p) (norm_nonneg _))
  have hdist := β.dist_normed_convolution_le (μ := ν) (x₀ := q)
    (g := fun p ↦ fderiv ℝ φ p w) (ε := 2 * (C * ‖w‖))
    (hDφ.clm_apply continuous_const).aestronglyMeasurable fun p _ ↦
      (dist_le_norm_add_norm _ _).trans (by linarith [hg p, hg q])
  rw [dist_eq_norm] at hdist
  rw [fderiv_normed_convolution_apply_of_contDiff β hφ hφc]
  linarith [norm_le_norm_add_norm_sub' ((β.normed ν ⋆[lsmul ℝ ℝ, ν]
    fun p ↦ fderiv ℝ φ p w) q) (fderiv ℝ φ q w), hg q]

/-- The space-time cut-off `(t, x) ↦ χ (s • x) * φ (t, x)` of a function vanishing outside the time
interval `(a, b)` has compact support, as soon as `χ` vanishes outside `ball 0 (s * R)`. -/
theorem hasCompactSupport_cutoff_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {a b : ℝ} {φ : ℝ × E → ℝ} {χ : ContDiffBump (0 : E)} {s R : ℝ}
    (hs : 0 < s) (hR : χ.rOut ≤ s * R) (hzero : ∀ q : ℝ × E, q.1 ∉ Ioo a b → φ q = 0) :
    HasCompactSupport fun q : ℝ × E ↦ χ (s • q.2) * φ q := by
  refine HasCompactSupport.intro ((isCompact_Icc (a := a) (b := b)).prod
    (isCompact_closedBall (0 : E) R)) fun q hq ↦ ?_
  by_cases ht : q.1 ∈ Icc a b
  · have hx : R < ‖q.2‖ := by
      by_contra hle
      exact hq ⟨ht, by simpa using not_lt.1 hle⟩
    have : χ (s • q.2) = 0 := χ.zero_of_le_dist <| by
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hs.le]
      exact hR.trans (mul_le_mul_of_nonneg_left hx.le hs.le)
    simp [this]
  · simp [hzero q fun h ↦ ht (Ioo_subset_Icc_self h)]

/-- The derivative of a space-time cut-off `(t, x) ↦ χ (s • x) * φ (t, x)` at `(1, w)`. -/
theorem fderiv_cutoff_mul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {φ : ℝ × E → ℝ} (hφd : Differentiable ℝ φ) (χ : ContDiffBump (0 : E))
    (s : ℝ) (q : ℝ × E) (w : E) :
    fderiv ℝ (fun p : ℝ × E ↦ χ (s • p.2) * φ p) q (1, w) =
      χ (s • q.2) * fderiv ℝ φ q (1, w) + φ q * fderiv ℝ χ (s • q.2) (s • w) := by
  have hc : HasFDerivAt (fun p : ℝ × E ↦ χ (s • p.2))
      ((fderiv ℝ χ (s • q.2)).comp (s • ContinuousLinearMap.snd ℝ ℝ E)) q :=
    ((χ.contDiff (n := 1)).differentiable_one _).hasFDerivAt.comp q
      (hasFDerivAt_snd.const_smul s)
  rw [fderiv_fun_mul hc.differentiableAt (hφd q), hc.fderiv]
  simp

/-- A function with derivative bounded by `C` that vanishes outside the time interval `(a, b)` is
bounded by `C * (b - a)`, by the mean value inequality from its value at the time `a`. -/
theorem norm_le_mul_sub_of_forall_notMem_Ioo_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} {φ : ℝ × E → ℝ} (hφd : Differentiable ℝ φ) {C : ℝ}
    (hC : ∀ q, ‖fderiv ℝ φ q‖ ≤ C) (hzero : ∀ q : ℝ × E, q.1 ∉ Ioo a b → φ q = 0) (hab : a ≤ b)
    (q : ℝ × E) : ‖φ q‖ ≤ C * (b - a) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  by_cases hq : q.1 ∈ Ioo a b
  · have hq' : q - (a, q.2) = (q.1 - a, 0) := by ext <;> simp
    have hn : ‖q - (a, q.2)‖ ≤ b - a := by
      rw [hq', Prod.norm_def, norm_zero, Real.norm_eq_abs, max_eq_left (abs_nonneg _),
        abs_of_pos (sub_pos.2 hq.1)]
      linarith [hq.2]
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun p _ ↦ hφd p) (fun p _ ↦ hC p)
      (mem_univ (a, q.2)) (mem_univ q)
    rw [hzero (a, q.2) (by simp), sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hn hC0)
  · rw [hzero q hq, norm_zero]
    exact mul_nonneg hC0 (sub_nonneg.2 hab)

/-- The bound on the derivative of a cut-off `χ (s • x) * φ (t, x)` at `(1, w)`: the cut-off does
not increase the derivative of `φ`, and the derivative of `χ` contributes at most `B * D` where
`B` bounds `φ` and `D` bounds the derivative of `χ`. -/
theorem norm_cutoff_fderiv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (χ : ContDiffBump (0 : E)) {φ : ℝ × E → ℝ} {C D B : ℝ}
    (hC : ∀ q, ‖fderiv ℝ φ q‖ ≤ C) (hD : ∀ p, ‖fderiv ℝ χ p‖ ≤ D) (hB : ∀ q, ‖φ q‖ ≤ B)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (q : ℝ × E) (w : E) :
    ‖χ (s • q.2) * fderiv ℝ φ q (1, w) + φ q * fderiv ℝ χ (s • q.2) (s • w)‖ ≤
      (C + B * D) * (1 + ‖w‖) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have h₁ : ‖χ (s • q.2) * fderiv ℝ φ q (1, w)‖ ≤ C * (1 + ‖w‖) := by
    rw [norm_mul, Real.norm_of_nonneg χ.nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) χ.le_one).trans <|
      ((fderiv ℝ φ q).le_opNorm _).trans (mul_le_mul (hC q)
        (norm_prod_le_iff.2 ⟨by simp, by simp⟩) (norm_nonneg _) hC0)
  have hsw : ‖s • w‖ ≤ 1 + ‖w‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
    nlinarith [norm_nonneg w]
  have h₂ : ‖φ q * fderiv ℝ χ (s • q.2) (s • w)‖ ≤ B * D * (1 + ‖w‖) := by
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hB q) (((fderiv ℝ χ _).le_opNorm _).trans
      (mul_le_mul (hD _) hsw (norm_nonneg _) hD0)) (norm_nonneg _) hB0
  linarith [norm_add_le (χ (s • q.2) * fderiv ℝ φ q (1, w))
    (φ q * fderiv ℝ χ (s • q.2) (s • w))]

/-- As the scale `s n` tends to `0`, the cut-off factor `χ (s n • x)` tends to `1` and the
derivative term `fderiv ℝ χ (s n • x) (s n • w)` to `0`. -/
theorem tendsto_cutoff_fderiv_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (χ : ContDiffBump (0 : E)) {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0))
    (x w : E) (c d : ℝ) :
    Tendsto (fun n ↦ χ (s n • x) * c + d * fderiv ℝ χ (s n • x) (s n • w)) atTop (𝓝 c) := by
  have hDχ : Continuous (fderiv ℝ χ) := (χ.contDiff (n := 1)).continuous_fderiv one_ne_zero
  have hχ1 : Tendsto (fun n ↦ χ (s n • x)) atTop (𝓝 1) := by
    have hx : Tendsto (fun n ↦ s n • x) atTop (𝓝 0) := by simpa using hs.smul_const x
    have := (χ.continuous.tendsto 0).comp hx
    rwa [χ.one_of_mem_closedBall (mem_closedBall_self χ.rIn_pos.le)] at this
  have hDχ0 : Tendsto (fun n ↦ fderiv ℝ χ (s n • x) (s n • w)) atTop (𝓝 0) := by
    have hcont : Continuous fun p : E × E ↦ fderiv ℝ χ p.1 p.2 :=
      (hDχ.comp continuous_fst).clm_apply continuous_snd
    have h0 : Tendsto (fun n ↦ (s n • x, s n • w)) atTop (𝓝 ((0 : E), (0 : E))) := by
      simpa using (hs.smul_const x).prodMk_nhds (hs.smul_const w)
    simpa only [Function.comp_def, map_zero] using (hcont.tendsto (0, 0)).comp h0
  simpa using (hχ1.mul tendsto_const_nhds).add (tendsto_const_nhds.mul hDχ0)

/-- The product `η (t) * u (t, x)` of a `C¹` function of time and a `C¹` function of time and space
has the expected derivative. -/
theorem hasFDerivAt_mul_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {η : ℝ → ℝ}
    {u : ℝ × E → ℝ} (hηd : Differentiable ℝ η) (hud : Differentiable ℝ u) (q : ℝ × E) :
    HasFDerivAt (fun p : ℝ × E ↦ η p.1 * u p)
      (η q.1 • fderiv ℝ u q + u q • (fderiv ℝ η q.1).comp (fst ℝ ℝ E)) q :=
  ((hηd q.1).hasFDerivAt.comp q hasFDerivAt_fst).mul (hud q).hasFDerivAt

/-- A bound for the derivative of the product `η (t) * u (t, x)` from bounds on `η`, `deriv η`,
`u` and `fderiv ℝ u`. -/
theorem norm_fderiv_mul_fst_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {η : ℝ → ℝ}
    {u : ℝ × E → ℝ} (hηd : Differentiable ℝ η) (hud : Differentiable ℝ u) {A A' M M' : ℝ}
    (hA : ∀ t, ‖η t‖ ≤ A) (hA' : ∀ t, ‖deriv η t‖ ≤ A') (hA0 : 0 ≤ A) (hM : 0 ≤ M)
    (huM : ∀ q, ‖u q‖ ≤ M) (hDu : ∀ q, ‖fderiv ℝ u q‖ ≤ M') (q : ℝ × E) :
    ‖fderiv ℝ (fun p : ℝ × E ↦ η p.1 * u p) q‖ ≤ A * M' + M * A' := by
  rw [(hasFDerivAt_mul_fst hηd hud q).fderiv]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul]
  · exact mul_le_mul (hA _) (hDu _) (norm_nonneg _) hA0
  · refine mul_le_mul (huM _) ((opNorm_comp_le _ _).trans (mul_le_of_le_one_right
      (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ E)) |>.trans ?_) (norm_nonneg _) hM
    rw [← norm_deriv_eq_norm_fderiv]
    exact hA' _

namespace IsContinuityEquation

/-- **Dominated convergence for test functions.** If `C¹` compactly supported functions `ψ n`
have derivatives converging pointwise to those of `φ`, with a bound `C (1 + ‖w‖)` on their values
at the space-time velocity `(1, w)`, then the integrals of the continuity equation against `ψ n`
converge to the integral against `φ`. -/
private lemma tendsto_integral_integral_fderiv (h : IsContinuityEquation μ v a b)
    {ψ : ℕ → ℝ × E → ℝ} (hψ : ∀ n, ContDiff ℝ 1 (ψ n)) (hψc : ∀ n, HasCompactSupport (ψ n))
    {φ : ℝ × E → ℝ} {C : ℝ} (hbound : ∀ n q (w : E), ‖fderiv ℝ (ψ n) q (1, w)‖ ≤ C * (1 + ‖w‖))
    (hlim : ∀ q (w : E),
      Tendsto (fun n ↦ fderiv ℝ (ψ n) q (1, w)) atTop (𝓝 (fderiv ℝ φ q (1, w)))) :
    Tendsto (fun n ↦ ∫ t in Ioo a b, ∫ x, fderiv ℝ (ψ n) (t, x) (1, v t x) ∂μ t) atTop
      (𝓝 (∫ t in Ioo a b, ∫ x, fderiv ℝ φ (t, x) (1, v t x) ∂μ t)) := by
  have hF (n : ℕ) (t : ℝ) :
      AEStronglyMeasurable (fun x ↦ fderiv ℝ (ψ n) (t, x) (1, v t x)) (μ t) :=
    ((measurable_fderiv_apply ℝ (ψ n)).comp ((measurable_const.prodMk measurable_id).prodMk
      (measurable_const.prodMk
        (h.measurable_velocity.comp measurable_prodMk_left)))).aestronglyMeasurable
  -- The integrable bound in time, and the inner dominated convergence at almost every time.
  have hinner : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∀ n, ‖∫ x, fderiv ℝ (ψ n) (t, x) (1, v t x) ∂μ t‖ ≤
        C * ((μ t).real univ + ∫ x, ‖v t x‖ ∂μ t)) ∧
      Tendsto (fun n ↦ ∫ x, fderiv ℝ (ψ n) (t, x) (1, v t x) ∂μ t) atTop
        (𝓝 (∫ x, fderiv ℝ φ (t, x) (1, v t x) ∂μ t)) := by
    filter_upwards [h.ae_isFiniteMeasure_and_integrable] with t ⟨_, hvi⟩
    have hbi : Integrable (fun x ↦ C * (1 + ‖v t x‖)) (μ t) :=
      ((integrable_const 1).add hvi.norm).const_mul C
    refine ⟨fun n ↦ ?_, tendsto_integral_of_dominated_convergence _ (fun n ↦ hF n t) hbi
      (fun n ↦ ae_of_all _ fun x ↦ hbound n _ _) (ae_of_all _ fun x ↦ hlim _ _)⟩
    refine (norm_integral_le_of_norm_le hbi (ae_of_all _ fun x ↦ hbound n _ _)).trans_eq ?_
    rw [integral_const_mul, integral_add (integrable_const 1) hvi.norm, integral_const,
      smul_eq_mul, mul_one]
  exact tendsto_integral_of_dominated_convergence _
    (fun n ↦ (h.integrableOn_integral_fderiv (hψ n) (hψc n)).aestronglyMeasurable)
    ((h.integrableOn_measureReal_univ.add h.integrableOn_integral_norm).const_mul C)
    (fun n ↦ hinner.mono fun t ht ↦ ht.1 n) (hinner.mono fun t ht ↦ ht.2)

/-- The continuity equation holds against every `C¹` compactly supported test function with
support in `(a, b) × E`, not only against smooth ones. For test functions without compact support
see `TauCeti.IsContinuityEquation.integral_integral_fderiv_eq_zero_of_norm_fderiv_le`. -/
theorem integral_integral_fderiv_eq_zero_of_hasCompactSupport (h : IsContinuityEquation μ v a b)
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo a b ×ˢ univ) :
    ∫ t in Ioo a b, ∫ x, fderiv ℝ φ (t, x) (1, v t x) ∂μ t = 0 := by
  let m : Measure (ℝ × E) := Measure.addHaar
  obtain ⟨δ, hδ, hδs⟩ :=
    hφc.isCompact.exists_cthickening_subset_open (isOpen_Ioo.prod isOpen_univ) hφs
  obtain ⟨C, hC⟩ :=
    (hφ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hφc.fderiv ℝ)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- Normalized bumps of radius `δ / (n + 1)` and the mollified test functions.
  let β (n : ℕ) : ContDiffBump (0 : ℝ × E) :=
    ⟨δ / (2 * (n + 1)), δ / (n + 1), by positivity, by
      rw [div_lt_div_iff_of_pos_left hδ (by positivity) (by positivity)]
      linarith⟩
  let ψ (n : ℕ) : ℝ × E → ℝ := (β n).normed m ⋆[lsmul ℝ ℝ, m] φ
  have hDφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hderiv (n : ℕ) (q w : ℝ × E) :
      fderiv ℝ (ψ n) q w = ((β n).normed m ⋆[lsmul ℝ ℝ, m] fun p ↦ fderiv ℝ φ p w) q :=
    fderiv_normed_convolution_apply_of_contDiff (β n) hφ hφc q w
  have hrOut : Tendsto (fun n ↦ (β n).rOut) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
    rw [mul_zero] at this
    refine this.congr fun n ↦ ?_
    simp [β, div_eq_mul_inv]
  have hψ (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (ψ n) :=
    (β n).hasCompactSupport_normed.contDiff_convolution_left _ (β n).contDiff_normed
      hφ.continuous.locallyIntegrable
  have hψc (n : ℕ) : HasCompactSupport (ψ n) := (β n).hasCompactSupport_normed.convolution _ hφc
  have hψs (n : ℕ) : tsupport (ψ n) ⊆ Ioo a b ×ˢ univ := by
    refine (closure_minimal ?_ isClosed_cthickening).trans hδs
    refine (support_convolution_subset _).trans ?_
    rw [(β n).support_normed_eq]
    refine (add_subset_add (ball_subset_ball (ε₂ := δ) ?_) (subset_tsupport φ)).trans ?_
    · exact div_le_self hδ.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    · rw [ball_add_zero]
      exact thickening_subset_cthickening _ _
  refine tendsto_nhds_unique
    (h.tendsto_integral_integral_fderiv (fun n ↦ (hψ n).of_le (by simp)) hψc (φ := φ)
      (C := 3 * C) (fun n q w ↦ ?_) fun q w ↦ ?_)
    (tendsto_const_nhds.congr fun n ↦
      (h.integral_integral_fderiv_eq_zero (hψ n) (hψc n) (hψs n)).symm)
  · -- Mollification does not increase the bound on the derivative.
    have hw : ‖((1 : ℝ), w)‖ ≤ 1 + ‖w‖ := norm_prod_le_iff.2 ⟨by simp, by simp⟩
    refine (norm_fderiv_normed_convolution_le (β n) hφ hφc hC q (1, w)).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hw (by positivity)
  · simp_rw [hderiv]
    exact ContDiffBump.convolution_tendsto_right_of_continuous hrOut
      (hDφ.clm_apply continuous_const) q

/-- **Test functions with bounded derivative.** The continuity equation holds against every `C¹`
test function `φ` with bounded derivative and support in `(a, b) × E`, with no compactness of the
support in space. Such a `φ` is bounded, since it vanishes at the time `a`. -/
theorem integral_integral_fderiv_eq_zero_of_norm_fderiv_le (h : IsContinuityEquation μ v a b)
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 1 φ) {C : ℝ} (hC : ∀ q, ‖fderiv ℝ φ q‖ ≤ C)
    (hφs : tsupport φ ⊆ Ioo a b ×ˢ univ) :
    ∫ t in Ioo a b, ∫ x, fderiv ℝ φ (t, x) (1, v t x) ∂μ t = 0 := by
  rcases le_or_gt b a with hba | hab
  · simp [Ioo_eq_empty_of_le hba]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hzero {q : ℝ × E} (hq : q.1 ∉ Ioo a b) : φ q = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hq (hφs h).1
  -- `φ` vanishes at the time `a`, so the mean value inequality bounds it by `C * (b - a)`.
  have hφB := norm_le_mul_sub_of_forall_notMem_Ioo_eq_zero hφd hC (fun q hq ↦ hzero hq) hab.le
  -- The cut-offs `x ↦ χ (s n • x)` with `s n = 1 / (n + 1)`, equal to `1` on `closedBall 0 (n + 1)`
  -- and vanishing outside `ball 0 (2 * (n + 1))`.
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hχrOut : χ.rOut = 2 := rfl
  have hDχ : Continuous (fderiv ℝ χ) := (χ.contDiff (n := 1)).continuous_fderiv one_ne_zero
  obtain ⟨D, hD⟩ := hDχ.bounded_above_of_compact_support (χ.hasCompactSupport.fderiv ℝ)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  let s (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ one_div _
  have hs0 (n : ℕ) : 0 < s n := by positivity
  have hs1 (n : ℕ) : s n ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  let ψ (n : ℕ) : ℝ × E → ℝ := fun q ↦ χ (s n • q.2) * φ q
  have hψ (n : ℕ) : ContDiff ℝ 1 (ψ n) := (χ.contDiff.comp (contDiff_snd.const_smul (s n))).mul hφ
  have hψc (n : ℕ) : HasCompactSupport (ψ n) :=
    hasCompactSupport_cutoff_mul (hs0 n) (R := 2 * ((n : ℝ) + 1)) (by
      rw [hχrOut]
      simp only [s]
      field_simp
      rfl) fun q hq ↦ hzero hq
  have hψs (n : ℕ) : tsupport (ψ n) ⊆ Ioo a b ×ˢ univ := tsupport_mul_subset_right.trans hφs
  have hderiv (n : ℕ) (q : ℝ × E) (w : E) : fderiv ℝ (ψ n) q (1, w) =
      χ (s n • q.2) * fderiv ℝ φ q (1, w) + φ q * fderiv ℝ χ (s n • q.2) (s n • w) :=
    fderiv_cutoff_mul_apply hφd χ (s n) q w
  refine tendsto_nhds_unique
    (h.tendsto_integral_integral_fderiv hψ hψc (φ := φ) (C := C + C * (b - a) * D)
      (fun n q w ↦ ?_) fun q w ↦ ?_)
    (tendsto_const_nhds.congr fun n ↦
      (h.integral_integral_fderiv_eq_zero_of_hasCompactSupport (hψ n) (hψc n) (hψs n)).symm)
  · -- The cut-off does not increase the derivative by more than a bounded amount.
    rw [hderiv]
    exact norm_cutoff_fderiv_le χ hC hD hφB (hs0 n) (hs1 n) q w
  · -- As `n → ∞` the cut-off tends to `1` and its derivative to `0`.
    simp_rw [hderiv]
    exact tendsto_cutoff_fderiv_add χ hs q.2 w _ _

/-- **The weak time derivative of `t ↦ ∫ u (t, ·) dμₜ`.** For a bounded `C¹` function `u` of
time and space with bounded derivative, the function `t ↦ ∫ u (t, x) dμₜ(x)` has weak derivative
`t ↦ ∫ (∂ₜ u (t, x) + ⟨∇ₓ u (t, x), vₜ x⟩) dμₜ(x)` on `(a, b)`, the integrand being written as the
space-time derivative `fderiv ℝ u (t, x)` applied to `(1, v t x)`: for every `C¹` function `η` with
support in `(a, b)`,
`∫_a^b η' (t) ∫ u (t, x) dμₜ(x) dt = - ∫_a^b η (t) ∫ fderiv ℝ u (t, x) (1, vₜ x) dμₜ(x) dt`. -/
theorem integral_deriv_mul_integral_eq_neg (h : IsContinuityEquation μ v a b) {η : ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) (hηs : tsupport η ⊆ Ioo a b) {u : ℝ × E → ℝ} (hu : ContDiff ℝ 1 u)
    {M M' : ℝ} (huM : ∀ q, ‖u q‖ ≤ M) (hDu : ∀ q, ‖fderiv ℝ u q‖ ≤ M') :
    ∫ t in Ioo a b, deriv η t * ∫ x, u (t, x) ∂μ t =
      -∫ t in Ioo a b, η t * ∫ x, fderiv ℝ u (t, x) (1, v t x) ∂μ t := by
  have hηc : HasCompactSupport η :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport η) ((isBounded_Ioo a b).subset hηs)
  have hη' : Continuous (deriv η) := hη.continuous_deriv le_rfl
  obtain ⟨A, hA⟩ := hη.continuous.bounded_above_of_compact_support hηc
  obtain ⟨A', hA'⟩ := hη'.bounded_above_of_compact_support hηc.deriv
  have hM : 0 ≤ M := (norm_nonneg _).trans (huM 0)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hηd : Differentiable ℝ η := hη.differentiable one_ne_zero
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  -- The space-time test function `φ (t, x) = η t * u (t, x)`.
  let φ : ℝ × E → ℝ := fun q ↦ η q.1 * u q
  have hφd (q : ℝ × E) : HasFDerivAt φ _ q := hasFDerivAt_mul_fst hηd hud q
  have hφ1 (t : ℝ) (x w : E) :
      fderiv ℝ φ (t, x) (1, w) = η t * fderiv ℝ u (t, x) (1, w) + u (t, x) * deriv η t := by
    simp [(hφd (t, x)).fderiv]
  have hφC (q : ℝ × E) : ‖fderiv ℝ φ q‖ ≤ A * M' + M * A' :=
    norm_fderiv_mul_fst_le hηd hud hA hA' hA0 hM huM hDu q
  have hφs : tsupport φ ⊆ Ioo a b ×ˢ univ :=
    tsupport_mul_subset_left.trans <| (tsupport_comp_subset_preimage η continuous_fst).trans
      fun q hq ↦ ⟨hηs hq, mem_univ _⟩
  have hφ : ContDiff ℝ 1 φ := (hη.comp contDiff_fst).mul hu
  have h0 := h.integral_integral_fderiv_eq_zero_of_norm_fderiv_le hφ hφC hφs
  -- The two terms of the identity are separately integrable in time.
  have h₁ : IntegrableOn (fun t ↦ deriv η t * ∫ x, u (t, x) ∂μ t) (Ioo a b) :=
    (h.integrableOn_integral_of_norm_le hu.continuous.stronglyMeasurable huM).bdd_mul
      hη'.aestronglyMeasurable (ae_of_all _ hA')
  have h₂ : IntegrableOn (fun t ↦ η t * ∫ x, fderiv ℝ u (t, x) (1, v t x) ∂μ t) (Ioo a b) :=
    (h.integrableOn_integral_fderiv_of_norm_fderiv_le hDu).bdd_mul
      hη.continuous.aestronglyMeasurable (ae_of_all _ hA)
  -- At almost every time, both terms are integrable in space.
  have hDuv : Measurable (uncurry fun t x ↦ fderiv ℝ u (t, x) (1, v t x)) :=
    (measurable_fderiv_apply ℝ u).comp
      (measurable_id.prodMk (measurable_const.prodMk h.measurable_velocity))
  have hDuB (t : ℝ) (x : E) : ‖fderiv ℝ u (t, x) (1, v t x)‖ ≤ M' * (1 + ‖v t x‖) :=
    (fderiv ℝ u _).le_of_opNorm_le_of_le (hDu _) (norm_prod_le_iff.2 ⟨by simp, by simp⟩)
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← integral_add h₁ h₂, ← h0]
  refine integral_congr_ae ?_
  filter_upwards [h.ae_isFiniteMeasure_and_integrable] with t ⟨_, hvi⟩
  have hui : Integrable (fun x ↦ u (t, x)) (μ t) :=
    (integrable_const M).mono' (hu.continuous.comp (Continuous.prodMk_right t)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ huM _)
  have hDui : Integrable (fun x ↦ fderiv ℝ u (t, x) (1, v t x)) (μ t) :=
    (((integrable_const 1).add hvi.norm).const_mul M').mono'
      (hDuv.comp measurable_prodMk_left).aestronglyMeasurable (ae_of_all _ fun x ↦ hDuB t x)
  simp_rw [hφ1]
  rw [integral_add (hDui.const_mul _) (hui.mul_const _), integral_const_mul, integral_mul_const]
  ring

end IsContinuityEquation

end TauCeti
