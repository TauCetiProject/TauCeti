/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Joint continuity of the gradient of the Duhamel heat potential

For a bounded forcing term `f : ℝ → E → F`, the Duhamel heat potential
`w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` is `C¹` in space at every positive time, with
`‖D w(t, x)‖ ≤ C M √t` (`TauCeti.exists_norm_fderiv_heatDuhamelPotential_le`). This file shows
that when `f` is moreover jointly continuous and `F` is complete, the spatial gradient
`(t, x) ↦ D w(t, x)` is jointly continuous on `[0, ∞) × E`. No spatial Hölder continuity of `f`
is needed. Together with the gradient bound this makes `D w` a bounded continuous field on every
closed slab `E × [0, T]`, which is the gradient field required of a map in the order-two
parabolic Hölder space.

The time integrand `D(K_{t-s} ⋆ f(s, ·))(x)` is singular at `s = t`, with a singularity that moves
with `t`. Two changes of variables remove both difficulties. By the parabolic scaling of the heat
kernel,

`D^m (K_τ ⋆ g)(x) = (√τ)⁻¹ ^ m ∫ D^m K_1(y) ⊗ g(x - √τ • y) dy`

(`TauCeti.iteratedFDeriv_heatKernel_convolution_eq_smul_integral`). For `g = f(t - τ, ·)`, the
integral on the right is continuous in `(τ, t, x)` by dominated convergence against
`‖D^m K_1‖`. Substituting
`τ = t - s` in the time integral turns the singular factor into `(√τ)⁻¹`, which no longer depends
on `t`. Thus, for `0 ≤ t ≤ T`,

`D w(t, x) = ∫₀ᵀ 1_{τ ≤ t} (√τ)⁻¹ ∫ D K_1(y) ⊗ f(t - τ, x - √τ • y) dy dτ`,

whose integrand is dominated by the integrable function `C M τ^(-1/2)` and is continuous in
`(t, x)` at every `τ ≠ t`. Dominated convergence gives the continuity.

## Main declarations

* `TauCeti.continuousOn_fderiv_heatDuhamelPotential`: the spatial gradient of the Duhamel
  potential of a bounded, jointly continuous forcing is jointly continuous on `[0, ∞) × E`.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3 (the
  derivatives of the volume potential).
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Real Set Filter Topology
open scoped Convolution Interval

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {f : ℝ → E → F} {M : ℝ}

/-- The rescaled kernel integral `∫ D^m K_1(y) ⊗ f(t - τ, x - √τ • y) dy` is jointly continuous in
`(τ, t, x)` for a bounded, jointly continuous `f`. -/
private theorem continuous_integral_smulRight (hf : Continuous (Function.uncurry f))
    (hM : ∀ s y, ‖f s y‖ ≤ M) (m : ℕ) :
    Continuous fun p : ℝ × ℝ × E => ∫ y, (iteratedFDeriv ℝ m (heatKernel 1 : E → ℝ) y).smulRight
      (f (p.2.1 - p.1) (p.2.2 - √p.1 • y)) := by
  have hK : Continuous (iteratedFDeriv ℝ m (heatKernel 1 : E → ℝ)) :=
    (contDiff_heatKernel (k := ⊤) 1).continuous_iteratedFDeriv le_top
  refine continuous_of_dominated
    (bound := fun y => ‖iteratedFDeriv ℝ m (heatKernel 1 : E → ℝ) y‖ * M) (fun p => ?_)
    (fun p => ae_of_all _ fun y => ?_)
    ((integrable_iteratedFDeriv_heatKernel one_pos m).norm.mul_const M) (ae_of_all _ fun y => ?_)
  · exact ((ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => E) F).continuous₂.comp
      (hK.prodMk (hf.comp (by fun_prop :
        Continuous fun y : E => (p.2.1 - p.1, p.2.2 - √p.1 • y))))).aestronglyMeasurable
  · rw [ContinuousMultilinearMap.norm_smulRight]
    exact mul_le_mul_of_nonneg_left (hM _ _) (norm_nonneg _)
  · exact (ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => E) F
      (iteratedFDeriv ℝ m (heatKernel 1 : E → ℝ) y)).continuous.comp
        (hf.comp (by fun_prop :
          Continuous fun p : ℝ × ℝ × E => (p.2.1 - p.1, p.2.2 - √p.1 • y)))

/-- The integrand of the gradient of the Duhamel potential after the substitution `τ = t - s`,
cut off at `τ = t`: `1_{τ ≤ t} (√τ)⁻¹ ∫ D K_1(y) ⊗ f(t - τ, x - √τ • y) dy`. -/
private def gradientIntegrand (f : ℝ → E → F) (p : ℝ × E) (τ : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F :=
  (Iic p.1).indicator (fun τ => (√τ)⁻¹ •
    ∫ y, (iteratedFDeriv ℝ 1 (heatKernel 1 : E → ℝ) y).smulRight (f (p.1 - τ) (p.2 - √τ • y))) τ

/-- For `0 ≤ t ≤ T`, the gradient of the Duhamel potential is the integral over `[0, T]` of the
cut-off integrand. -/
private theorem iteratedFDeriv_one_heatDuhamelPotential_eq [CompleteSpace F]
    (hf : Continuous (Function.uncurry f)) (hM : ∀ s y, ‖f s y‖ ≤ M) {T t : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) (x : E) :
    iteratedFDeriv ℝ 1 (heatDuhamelPotential f t) x =
      ∫ τ in 0..T, gradientIntegrand f (t, x) τ := by
  have hrhs : ∫ τ in 0..T, gradientIntegrand f (t, x) τ =
      ∫ τ in 0..t, (√τ)⁻¹ • ∫ y, (iteratedFDeriv ℝ 1 (heatKernel 1 : E → ℝ) y).smulRight
        (f (t - τ) (x - √τ • y)) := by
    rw [intervalIntegral.integral_of_le (ht.trans htT), intervalIntegral.integral_of_le ht]
    simp only [gradientIntegrand]
    rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, inf_eq_right.2 htT]
  rw [hrhs]
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hfs (s : ℝ) : AEStronglyMeasurable (f s) :=
    (hf.comp (Continuous.prodMk_right s)).aestronglyMeasurable
  rw [congrFun (iteratedFDeriv_heatDuhamelPotential (M := M) hf.stronglyMeasurable
      (ae_of_all _ fun s => ae_of_all _ fun y => hM s y) ht le_rfl) x]
  -- Substitute `τ = t - s`.
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun τ => iteratedFDeriv ℝ 1 (heatKernel τ ⋆ f (t - τ)) x) (a := 0) (b := t) t
  simp only [sub_sub_cancel, sub_self, sub_zero] at hsub
  rw [hsub]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun τ hτ => ?_)
  rw [uIoc_of_le ht.le] at hτ
  rw [iteratedFDeriv_heatKernel_convolution_eq_smul_integral hτ.1 (hfs _)
    (ae_of_all _ fun y => hM _ y), pow_one]

/-- The cut-off integrand is bounded by `(√τ)⁻¹ C M`, where `C = ∫ ‖D K_1‖`. -/
private theorem norm_gradientIntegrand_le (hM : ∀ s y, ‖f s y‖ ≤ M) (p : ℝ × E) (τ : ℝ) :
    ‖gradientIntegrand f p τ‖ ≤
      (√τ)⁻¹ * ((∫ y, ‖iteratedFDeriv ℝ 1 (heatKernel 1 : E → ℝ) y‖) * M) := by
  refine (norm_indicator_le_norm_self _ _).trans ?_
  rw [norm_smul, norm_inv, norm_of_nonneg (sqrt_nonneg τ)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (sqrt_nonneg τ))
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le
    ((integrable_iteratedFDeriv_heatKernel one_pos 1).norm.mul_const M) (ae_of_all _ fun y => ?_)
  rw [ContinuousMultilinearMap.norm_smulRight]
  exact mul_le_mul_of_nonneg_left (hM _ _) (norm_nonneg _)

/-- The integral of the cut-off integrand over `[0, T]` is continuous in `(t, x)`. -/
private theorem continuous_integral_gradientIntegrand (hf : Continuous (Function.uncurry f))
    (hM : ∀ s y, ‖f s y‖ ≤ M) (T : ℝ) :
    Continuous fun p : ℝ × E => ∫ τ in 0..T, gradientIntegrand f p τ := by
  have hΨ := continuous_integral_smulRight hf hM 1
  have hcont (τ : ℝ) : Continuous fun p : ℝ × E => (√τ)⁻¹ • ∫ y,
      (iteratedFDeriv ℝ 1 (heatKernel 1 : E → ℝ) y).smulRight (f (p.1 - τ) (p.2 - √τ • y)) :=
    (hΨ.comp (by fun_prop : Continuous fun p : ℝ × E => (τ, p.1, p.2))).fun_const_smul _
  rw [continuous_iff_continuousAt]
  intro p₀
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun τ => (√τ)⁻¹ * ((∫ y, ‖iteratedFDeriv ℝ 1 (heatKernel 1 : E → ℝ) y‖) * M))
    (Eventually.of_forall fun p => ?_)
    (Eventually.of_forall fun p => ae_of_all _ fun τ _ => norm_gradientIntegrand_le hM p τ)
    ?_ ?_
  · exact ((continuous_sqrt.measurable.inv.stronglyMeasurable.smul
      (hΨ.comp (by fun_prop : Continuous fun τ : ℝ => (τ, p.1, p.2))).stronglyMeasurable).indicator
        measurableSet_Iic).aestronglyMeasurable
  · -- On `(0, T]`, `(√τ)⁻¹ = τ ^ (-1/2)`, which is integrable.
    refine IntervalIntegrable.mul_const ?_ _
    refine (intervalIntegral.intervalIntegrable_rpow' (r := -1 / 2) (by norm_num)).mono_fun'
      continuous_sqrt.measurable.inv.aestronglyMeasurable ?_
    refine ae_of_all _ fun τ ↦ ?_
    dsimp only
    rw [norm_inv, norm_of_nonneg (sqrt_nonneg τ)]
    exact (inv_sqrt_eq_rpow_neg_one_div_two τ).le
  · -- Away from `τ = p₀.1` the cut-off is locally constant in `p`.
    filter_upwards [Measure.ae_ne volume p₀.1] with τ hτ _
    rcases hτ.lt_or_gt with hlt | hlt
    · refine (hcont τ).continuousAt.congr_of_eventuallyEq ?_
      filter_upwards [continuous_fst.continuousAt.eventually (lt_mem_nhds hlt)] with p hp
      exact indicator_of_mem (mem_Iic.2 hp.le) _
    · refine (continuousAt_const (y := 0)).congr_of_eventuallyEq ?_
      filter_upwards [continuous_fst.continuousAt.eventually (gt_mem_nhds hlt)] with p hp
      exact indicator_of_notMem (notMem_Iic.2 hp) _

/-- **Continuity of the gradient of the Duhamel potential.** If `f` is jointly continuous and
bounded, then the spatial gradient `(t, x) ↦ D w(t, x)` of its Duhamel heat potential `w` is
jointly continuous on `[0, ∞) × E`. -/
theorem continuousOn_fderiv_heatDuhamelPotential [CompleteSpace F]
    (hf : Continuous (Function.uncurry f)) (hM : ∀ s y, ‖f s y‖ ≤ M) :
    ContinuousOn (fun p : ℝ × E => fderiv ℝ (heatDuhamelPotential f p.1) p.2) (Ici 0 ×ˢ univ) := by
  have hcurry (g : E → F) (x : E) :
      fderiv ℝ g x = continuousMultilinearCurryFin1 ℝ E F (iteratedFDeriv ℝ 1 g x) := by
    ext v
    simp [continuousMultilinearCurryFin1_apply]
  rintro p₀ ⟨hp₀, -⟩
  set T := p₀.1 + 1
  have hR := ((continuousMultilinearCurryFin1 ℝ E F).continuous.comp
    (continuous_integral_gradientIntegrand hf hM T)).continuousAt (x := p₀)
  refine (hR.continuousWithinAt.congr_of_eventuallyEq ?_ ?_)
  · have hmem : Icc 0 T ×ˢ (univ : Set E) ∈ 𝓝[Ici 0 ×ˢ univ] p₀ := by
      rw [nhdsWithin_prod_eq, nhdsWithin_univ, ← Ici_inter_Iic]
      exact prod_mem_prod (inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))) univ_mem
    filter_upwards [hmem] with p hp
    rw [Function.comp_apply, hcurry,
      iteratedFDeriv_one_heatDuhamelPotential_eq hf hM hp.1.1 hp.1.2]
  · rw [Function.comp_apply, hcurry,
      iteratedFDeriv_one_heatDuhamelPotential_eq (T := T) hf hM hp₀ (by linarith), Prod.mk.eta]

end TauCeti
