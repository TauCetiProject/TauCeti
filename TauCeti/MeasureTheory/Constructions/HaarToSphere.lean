/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Integration in polar coordinates

Let `E` be a nontrivial finite-dimensional real normed space of dimension `d` with an additive
Haar measure `μ`.  Mathlib's `MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`
identifies `μ` on `E \ {0}` with the product of the surface measure `μ.toSphere` on the unit
sphere and the radial measure `r ^ (d - 1) dr` on `(0, ∞)`, but upstream only integrates radial
functions against it (`MeasureTheory.integral_fun_norm_addHaar`).  This file records the
integral formula for an arbitrary integrable function,

`∫ x, f x ∂μ = ∫ u ∈ S, ∫ r in (0, ∞), r ^ (d - 1) • f (r • u) ∂μ.toSphere`,

and uses it for a radial fundamental theorem of calculus: for a `C¹` function `f` with compact
support,

`∫ x, ‖x‖ ^ (-d) * f' x x ∂μ = -(d * μ (ball 0 1)) * f 0`.

In the language of distributions the second formula says that the vector field `x / ‖x‖ ^ d`
has divergence `d μ(ball 0 1) δ₀`; it is the flux computation behind the fundamental solution of
the Laplacian.

## Main declarations

* `TauCeti.integral_eq_integral_toSphere_integral_Ioi`: integration in polar coordinates.
* `TauCeti.integral_norm_rpow_neg_finrank_mul_fderiv_apply_self`: the radial fundamental theorem
  of calculus.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Integration in polar coordinates.** An integrable function on a finite-dimensional real
normed space is integrated by first integrating along each ray `r ↦ r • u`, against the radial
Jacobian `r ^ (d - 1)`, and then over the unit sphere against `μ.toSphere`. -/
theorem integral_eq_integral_toSphere_integral_Ioi (f : E → F) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ u : sphere (0 : E) 1, (∫ r in Ioi (0 : ℝ),
      r ^ (Module.finrank ℝ E - 1) • f (r • (u : E))) ∂μ.toSphere := by
  set k := Module.finrank ℝ E - 1
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have hemb := (homeomorphUnitSphereProd E).measurableEmbedding
  set g : sphere (0 : E) 1 × Ioi (0 : ℝ) → F := fun p ↦ f ((p.2 : ℝ) • (p.1 : E)) with hg_def
  have hg : g ∘ homeomorphUnitSphereProd E = f ∘ Subtype.val := by
    funext x
    have hx : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
    simp [hg_def, smul_smul, hx]
  have hint : Integrable g (μ.toSphere.prod (Measure.volumeIoiPow k)) := by
    rw [← hmp.integrable_comp_emb hemb, hg,
      ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
    exact hf.integrableOn
  calc ∫ x, f x ∂μ = ∫ x : ({0}ᶜ : Set E), f x ∂(μ.comap Subtype.val) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl f,
          restrict_compl_singleton]
    _ = ∫ p, g p ∂(μ.toSphere.prod (Measure.volumeIoiPow k)) := by
        rw [← hmp.integral_comp hemb g]
        exact integral_congr_ae (ae_of_all _ fun x ↦ (congrFun hg x).symm)
    _ = ∫ u, ∫ r, g (u, r) ∂(Measure.volumeIoiPow k) ∂μ.toSphere := integral_prod g hint
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
        simp only [hg_def, Measure.volumeIoiPow, ENNReal.ofReal]
        rw [integral_withDensity_eq_integral_smul
            (measurable_subtype_coe.pow_const _).real_toNNReal,
          integral_subtype_comap measurableSet_Ioi
            fun r ↦ Real.toNNReal (r ^ k) • f (r • (u : E))]
        refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
        rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) _)]

/-- **Radial fundamental theorem of calculus.** For a `C¹` function `f` with compact support on a
nontrivial finite-dimensional real normed space of dimension `d`,
`∫ ‖x‖ ^ (-d) * f' x x ∂μ = -(d * μ (ball 0 1)) * f 0`.

In the language of distributions, `div (x / ‖x‖ ^ d) = d μ(ball 0 1) δ₀`. -/
theorem integral_norm_rpow_neg_finrank_mul_fderiv_apply_self {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∫ x, ‖x‖ ^ (-(Module.finrank ℝ E : ℝ)) * fderiv ℝ f x x ∂μ =
      -((Module.finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1)) * f 0 := by
  set d := Module.finrank ℝ E
  have hd : 1 ≤ d := Module.finrank_pos
  have hf' : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  -- The integrand is dominated by `‖x‖ ^ (1 - d) * ‖f' x‖`, a locally integrable singularity
  -- against a compactly supported continuous function.
  have hint : Integrable (fun x ↦ ‖x‖ ^ (-(d : ℝ)) * fderiv ℝ f x x) μ := by
    have hsing : LocallyIntegrable (fun x : E ↦ ‖x‖ ^ (1 - (d : ℝ))) μ := by
      refine locallyIntegrable_of_norm_le_rpow (μ := μ) hd (C := 1) (α := (d : ℝ) - 1)
        (by linarith) (ae_of_all _ fun x ↦ ?_) ?_
      · rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), one_mul, neg_sub]
      · exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable
    refine (hsing.integrable_smul_right_of_hasCompactSupport hf'.norm
      (hc.fderiv ℝ).norm).mono' ?_ (ae_of_all _ fun x ↦ ?_)
    · exact ((continuous_norm.measurable.pow_const _).aestronglyMeasurable).mul
        (hf'.clm_apply continuous_id).aestronglyMeasurable
    · rcases eq_or_ne x 0 with rfl | hx
      · simp only [map_zero, mul_zero, norm_zero, smul_eq_mul]
        positivity
      have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [smul_eq_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),
        show 1 - (d : ℝ) = -(d : ℝ) + 1 by ring, Real.rpow_add_one hx'.ne', mul_assoc]
      gcongr
      rw [mul_comm]
      exact (fderiv ℝ f x).le_opNorm x
  rw [integral_eq_integral_toSphere_integral_Ioi _ hint]
  -- Along each ray, the weighted integrand is the derivative of `r ↦ f (r • u)`.
  have hray : ∀ u : sphere (0 : E) 1, ∫ r in Ioi (0 : ℝ),
      r ^ (d - 1) • (‖r • (u : E)‖ ^ (-(d : ℝ)) * fderiv ℝ f (r • (u : E)) (r • (u : E))) =
        -f 0 := by
    intro u
    have hu : ‖(u : E)‖ = 1 := norm_eq_of_mem_sphere u
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun r ↦ fderiv ℝ f (r • (u : E)) u)
      fun r (hr : 0 < r) ↦ ?_]
    · obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
      have hzero : ∀ r : ℝ, R < |r| → r • (u : E) ∉ tsupport f := fun r hr hmem ↦ by
        have := hR hmem
        rw [mem_closedBall_zero_iff, norm_smul, hu, mul_one, Real.norm_eq_abs] at this
        linarith
      have hderiv : ∀ r : ℝ, HasDerivAt (fun s : ℝ ↦ f (s • (u : E)))
          (fderiv ℝ f (r • (u : E)) u) r := fun r ↦
        ((hdiff (r • (u : E))).hasFDerivAt.comp_hasDerivAt r
          ((hasDerivAt_id r).smul_const (u : E))).congr_deriv (by simp)
      have hcs : HasCompactSupport fun r : ℝ ↦ fderiv ℝ f (r • (u : E)) u := by
        refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) fun r hr ↦ ?_
        rw [mem_closedBall_zero_iff, Real.norm_eq_abs, not_le] at hr
        have h0 : fderiv ℝ f (r • (u : E)) = 0 :=
          Function.notMem_support.mp fun h ↦ hzero r hr (support_fderiv_subset ℝ h)
        simp [h0]
      rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ ↦ hderiv r)
        ((hf'.clm_apply continuous_const).comp (continuous_id.smul continuous_const)
          |>.integrable_of_hasCompactSupport hcs).integrableOn
        (m := 0) ?_]
      · simp
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop R] with r hr
        exact (image_eq_zero_of_notMem_tsupport
          (hzero r (lt_of_lt_of_le hr (le_abs_self r)))).symm
    · have hpow : r ^ (d - 1) * r ^ (-(d : ℝ)) * r = 1 := by
        rw [mul_right_comm, ← pow_succ, Nat.sub_add_cancel hd, ← Real.rpow_natCast,
          ← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero]
      rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le, map_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, ← mul_assoc, hpow, one_mul]
  rw [integral_congr_ae (ae_of_all _ hray), integral_const, smul_eq_mul,
    Measure.toSphere_real_apply_univ]
  ring

end TauCeti
