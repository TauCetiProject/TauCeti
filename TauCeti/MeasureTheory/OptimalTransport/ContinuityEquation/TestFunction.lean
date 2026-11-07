/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Sobolev.Mollification.Lipschitz

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
    hφc.fderiv_convolution_right_apply _ (β n).continuous_normed.locallyIntegrable hφ q w
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
      (C := C) (fun n q w ↦ ?_) fun q w ↦ ?_)
    (tendsto_const_nhds.congr fun n ↦
      (h.integral_integral_fderiv_eq_zero (hψ n) (hψc n) (hψs n)).symm)
  · -- Mollification does not increase the bound on the derivative.
    have hw : ‖((1 : ℝ), w)‖ ≤ 1 + ‖w‖ := norm_prod_le_iff.2 ⟨by simp, by simp⟩
    have hLip : LipschitzWith ⟨C, hC0⟩ φ :=
      lipschitzWith_of_nnnorm_fderiv_le (hφ.differentiable one_ne_zero) fun p ↦
        NNReal.coe_le_coe.1 (hC p)
    exact (hLip.norm_fderiv_normed_convolution_apply_le (β n) q (1, w)).trans
      (mul_le_mul_of_nonneg_left hw hC0)
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
    χ.hasCompactSupport_cutoff_mul (hs0 n) (R := 2 * ((n : ℝ) + 1)) (by
      rw [hχrOut]
      simp only [s]
      field_simp
      rfl) fun q hq ↦ hzero hq
  have hψs (n : ℕ) : tsupport (ψ n) ⊆ Ioo a b ×ˢ univ := tsupport_mul_subset_right.trans hφs
  have hderiv (n : ℕ) (q : ℝ × E) (w : E) : fderiv ℝ (ψ n) q (1, w) =
      χ (s n • q.2) * fderiv ℝ φ q (1, w) + φ q * fderiv ℝ χ (s n • q.2) (s n • w) :=
    χ.fderiv_cutoff_mul_apply (hφd q) (s n) w
  refine tendsto_nhds_unique
    (h.tendsto_integral_integral_fderiv hψ hψc (φ := φ) (C := C + C * (b - a) * D)
      (fun n q w ↦ ?_) fun q w ↦ ?_)
    (tendsto_const_nhds.congr fun n ↦
      (h.integral_integral_fderiv_eq_zero_of_hasCompactSupport (hψ n) (hψc n) (hψs n)).symm)
  · -- The cut-off does not increase the derivative by more than a bounded amount.
    rw [hderiv]
    exact χ.norm_cutoff_fderiv_le hC hD hφB (hs0 n) (hs1 n) q w
  · -- As `n → ∞` the cut-off tends to `1` and its derivative to `0`.
    simp_rw [hderiv]
    exact χ.tendsto_cutoff_fderiv_add hs q.2 w _ _

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
  have hηd : Differentiable ℝ η := hη.differentiable one_ne_zero
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  -- The space-time test function `φ (t, x) = η t * u (t, x)`.
  let φ : ℝ × E → ℝ := fun q ↦ η q.1 * u q
  have hφd (q : ℝ × E) : HasFDerivAt φ _ q := hasFDerivAt_mul_fst (hηd q.1) (hud q)
  have hφ1 (t : ℝ) (x w : E) :
      fderiv ℝ φ (t, x) (1, w) = η t * fderiv ℝ u (t, x) (1, w) + u (t, x) * deriv η t := by
    simp [(hφd (t, x)).fderiv]
  have hφC (q : ℝ × E) : ‖fderiv ℝ φ q‖ ≤ A * M' + M * A' :=
    norm_fderiv_mul_fst_le (hηd q.1) (hud q) hA hA' huM hDu
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
