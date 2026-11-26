/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals against a radial weight

Let `μ` be a measure on a pseudo-metric space, `x` a point, `r` a radius, and
write `d = dist(x, ·)`.

* If `μ` is s-finite and `f` is integrable on `ball x r`, the radial layer-cake identity
  `∫_{B_r(x)} f (r - d)² / 2 dμ = ∫₀^r ∫₀^τ ∫_{B_ρ(x)} f dμ dρ dτ` holds. It follows from Fubini's
  theorem, applied twice to the weights `1` and `τ - d`.
* If `f` is integrable and nonnegative on the larger ball and `0 ≤ t`, then
  `t² ∫_{B_{r - 2t}(x)} f dμ ≤ ∫_{B_r(x)} f (r - d)² / 2 dμ`, since the weight is at least `t²` on
  the smaller ball.

## Main statements

* `TauCeti.intervalIntegral_setIntegral_ball_mul_eq`: Fubini for a radial weight.
* `TauCeti.setIntegral_ball_mul_sq_sub_dist_div_two_eq`: the radial layer-cake identity.
* `TauCeti.sq_mul_integral_ball_le_integral_radialWeight`.

## References

* T. H. Colding and W. P. Minicozzi II, *The space of embedded minimal surfaces of fixed genus
  in a 3-manifold II; Multi-valued graphs in disks*, Ann. of Math. 160 (2004), Corollary 1.7.
-/

public section

open Filter MeasureTheory Metric Set

namespace TauCeti

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [SFinite μ] {f : X → ℝ} {x : X} {r : ℝ}

omit [OpensMeasurableSpace X] [SFinite μ] in
private theorem intervalIntegral_setIntegral_ball_eq_zero_of_nonpos (hr : r ≤ 0)
    (k : X → ℝ → ℝ) : (∫ τ in 0..r, ∫ y in ball x τ, k y τ ∂μ) = 0 := by
  apply intervalIntegral.integral_zero_ae
  exact Eventually.of_forall fun τ hτ ↦ by
    rw [uIoc_of_ge hr] at hτ
    simp [ball_eq_empty.2 hτ.2]

-- The indicator form is shared by the product-integrability and Fubini arguments.
private noncomputable def radialKernel (f : X → ℝ) (g : ℝ → ℝ) (x y : X) (τ : ℝ) : ℝ :=
  (ball x τ).indicator (fun y ↦ f y * g (τ - dist x y)) y

private theorem integrable_radialWeight_integrand (hr : 0 ≤ r)
    (hf : IntegrableOn f (ball x r) μ) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (Function.uncurry (radialKernel f g x))
      ((μ.restrict (ball x r)).prod (volume.restrict (Ioc 0 r))) := by
  classical
  have hd : Measurable fun p : X × ℝ ↦ dist x p.1 :=
    (continuous_const.dist continuous_id).measurable.comp measurable_fst
  have hS : MeasurableSet {p : X × ℝ | dist x p.1 < p.2} := measurableSet_lt hd measurable_snd
  have hFS : Function.uncurry (radialKernel f g x) =
      {p : X × ℝ | dist x p.1 < p.2}.indicator fun p ↦ f p.1 * g (p.2 - dist x p.1) := by
    funext p
    simp only [radialKernel, Set.indicator_apply, Function.uncurry, mem_ball', mem_ofPred_eq]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-r)) (b := r)).exists_bound_of_continuousOn
    hg.continuousOn
  have hmeas : AEStronglyMeasurable (Function.uncurry (radialKernel f g x))
      ((μ.restrict (ball x r)).prod (volume.restrict (Ioc 0 r))) := by
    rw [hFS]
    refine AEStronglyMeasurable.indicator ?_ hS
    exact (AEStronglyMeasurable.comp_fst (ν := volume.restrict (Ioc 0 r))
      hf.integrable.aestronglyMeasurable).mul
      (hg.measurable.comp (measurable_snd.sub hd)).aestronglyMeasurable
  refine Integrable.mono' (Integrable.mul_prod hf.integrable.norm (integrable_const C))
    hmeas ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_ball.prod measurableSet_Ioc)] with p hp
  have hp₂ := hp.2
  simp only [Function.uncurry, radialKernel, Set.indicator_apply, mem_ball']
  split_ifs with h
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_left (hC _ ?_) (norm_nonneg _)
    have := dist_nonneg (x := x) (y := p.1)
    constructor <;> linarith [hp₂.1, hp₂.2]
  · simpa using
      mul_nonneg (norm_nonneg (f p.1)) ((norm_nonneg _).trans (hC 0 ⟨by linarith, hr⟩))

/-- Fubini for a radial weight: for `f` integrable on `ball x r` and `g` continuous,
`∫₀^{r} ∫_{B_τ(x)} f g(τ - d) dμ dτ = ∫_{B_r(x)} f (∫_{d}^{r} g(τ - d) dτ) dμ`. -/
theorem intervalIntegral_setIntegral_ball_mul_eq
    (hf : IntegrableOn f (ball x r) μ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ τ in 0..r, ∫ y in ball x τ, f y * g (τ - dist x y) ∂μ =
      ∫ y in ball x r, f y * (∫ τ in dist x y..r, g (τ - dist x y)) ∂μ := by
  classical
  by_cases hr : 0 ≤ r
  swap
  · have hr' := le_of_not_ge hr
    rw [ball_eq_empty.2 hr', setIntegral_empty]
    exact intervalIntegral_setIntegral_ball_eq_zero_of_nonpos hr' _
  have hint := integrable_radialWeight_integrand hr hf hg
  calc ∫ τ in 0..r, ∫ y in ball x τ, f y * g (τ - dist x y) ∂μ
      = ∫ τ in Ioc 0 r, (∫ y in ball x r, radialKernel f g x y τ ∂μ) := by
        rw [intervalIntegral.integral_of_le hr]
        refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ ↦ ?_
        simp only [radialKernel, setIntegral_indicator measurableSet_ball,
          inter_eq_right.mpr (ball_subset_ball hτ.2)]
    _ = ∫ y in ball x r, (∫ τ in Ioc 0 r, radialKernel f g x y τ) ∂μ :=
      (integral_integral_swap hint).symm
    _ = ∫ y in ball x r, f y * (∫ τ in dist x y..r, g (τ - dist x y)) ∂μ := by
        refine setIntegral_congr_fun measurableSet_ball fun y hy ↦ ?_
        have h : (fun τ ↦ radialKernel f g x y τ) =
            (Ioi (dist x y)).indicator fun τ ↦ f y * g (τ - dist x y) := by
          funext τ
          simp only [radialKernel, Set.indicator_apply, mem_ball', mem_Ioi]
        rw [h, setIntegral_indicator measurableSet_Ioi, Ioc_inter_Ioi,
          max_eq_right dist_nonneg, ← intervalIntegral.integral_of_le (mem_ball'.mp hy).le,
          intervalIntegral.integral_const_mul]

/-- The radial layer-cake identity: for `f` integrable on `ball x r`,
`∫_{B_r(x)} f (r - d)² / 2 dμ = ∫₀^{r} ∫₀^{τ} ∫_{B_ρ(x)} f dμ dρ dτ`. -/
theorem setIntegral_ball_mul_sq_sub_dist_div_two_eq
    (hf : IntegrableOn f (ball x r) μ) :
    ∫ y in ball x r, f y * (r - dist x y) ^ 2 / 2 ∂μ =
      ∫ τ in 0..r, ∫ ρ in 0..τ, ∫ y in ball x ρ, f y ∂μ := by
  by_cases hr : 0 ≤ r
  swap
  · have hr' := le_of_not_ge hr
    rw [ball_eq_empty.2 hr', setIntegral_empty]
    symm
    apply intervalIntegral.integral_zero_ae
    exact Eventually.of_forall fun τ hτ ↦ by
      rw [uIoc_of_ge hr'] at hτ
      exact intervalIntegral_setIntegral_ball_eq_zero_of_nonpos hτ.2
        (x := x) (μ := μ) (fun y _ ↦ f y)
  have h₁ : ∀ τ ∈ uIcc 0 r, ∫ ρ in 0..τ, ∫ y in ball x ρ, f y ∂μ =
      ∫ y in ball x τ, f y * (τ - dist x y) ∂μ := by
    intro τ hτ
    rw [uIcc_of_le hr] at hτ
    have := intervalIntegral_setIntegral_ball_mul_eq
      (hf.mono_set (ball_subset_ball hτ.2)) (g := fun _ ↦ 1) continuous_const
    simpa using this
  have h₂ := intervalIntegral_setIntegral_ball_mul_eq hf (g := fun s ↦ s) continuous_id
  beta_reduce at h₂
  rw [intervalIntegral.integral_congr h₁, h₂]
  refine setIntegral_congr_fun measurableSet_ball fun y _ ↦ ?_
  rw [intervalIntegral.integral_comp_sub_right (fun τ ↦ τ), integral_id]
  ring

end PseudoMetric

/-- A quadratic radial weight bounds the mass of the smaller concentric ball. -/
theorem sq_mul_integral_ball_le_integral_radialWeight {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    {p : X} {r t : ℝ} (ht : 0 ≤ t) (hf : IntegrableOn f (ball p r) μ)
    (hf₀ : 0 ≤ᵐ[μ.restrict (ball p r)] f) :
    t ^ 2 * ∫ y in ball p (r - 2 * t), f y ∂μ ≤
      ∫ y in ball p r, f y * (r - dist p y) ^ 2 / 2 ∂μ := by
  let w (y : X) : ℝ := (r - dist p y) ^ 2 / 2
  have hw_def (y : X) : w y = (r - dist p y) ^ 2 / 2 := rfl
  have hw : Continuous w := by fun_prop
  have hsub : ball p (r - 2 * t) ⊆ ball p r := ball_subset_ball (by linarith)
  have hi : IntegrableOn (fun y ↦ f y * w y) (ball p r) μ := by
    refine hf.mul_bdd (c := r ^ 2) hw.measurable.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hd := mem_ball'.mp hy
    have h := dist_nonneg (x := p) (y := y)
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
    have hrad : 0 ≤ 2 * r - dist p y := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hrad]
  simp_rw [mul_div_assoc, ← hw_def]
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ y in ball p (r - 2 * t), f y * w y ∂μ := by
      refine setIntegral_mono_ae_restrict ((hf.mono_set hsub).const_mul _) (hi.mono_set hsub) ?_
      filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae_restrict_of_subset hsub
        hf₀] with y hy hy₀
      have hd : 2 * t ≤ r - dist p y := by linarith [mem_ball'.mp hy]
      have hsq := sq_le_sq' (by linarith : -(r - dist p y) ≤ 2 * t) hd
      have hweight : t ^ 2 ≤ w y := by
        dsimp [w]
        nlinarith [sq_nonneg t]
      exact (mul_le_mul_of_nonneg_right hweight hy₀).trans_eq (mul_comm _ _)
    _ ≤ _ := setIntegral_mono_set hi (hf₀.mono fun y hy ↦
      mul_nonneg hy (div_nonneg (sq_nonneg _) (by norm_num))) (Eventually.of_forall hsub)

end TauCeti
