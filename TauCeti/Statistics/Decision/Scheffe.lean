/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.FisherSnedecor.Gaussian
public import TauCeti.Probability.Quantile
import TauCeti.Analysis.InnerProductSpace.Projection.DualNorm
import TauCeti.Probability.Distributions.FisherSnedecor.Quantile

/-!
# Scheffé's simultaneous confidence intervals

In a Gaussian linear model, the fitted vector is the orthogonal projection onto the model
subspace. The residual variance comes from its orthogonal complement. On a subspace of
contrasts, simultaneous coverage reduces to a bound on the projected estimation error,
and the corresponding ratio of mean squares has Fisher–Snedecor law.

## References

* G. A. F. Seber and A. J. Lee, *Linear Regression Analysis*, 2nd ed., §5.1.1 and A.4.11.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace TauCeti

open TauCeti.Probability

variable {ι : Type*} [Fintype ι]
  {L S : Submodule ℝ (EuclideanSpace ℝ ι)} {m : EuclideanSpace ℝ ι}

private theorem scheffe_event_iff {f : ℝ} (hf : 0 ≤ f) (hSL : S ≤ L) (hm : m ∈ L)
    (y : EuclideanSpace ℝ ι) (hy : 0 < ‖Lᗮ.starProjection (y - m)‖ ^ 2) :
    (∀ u ∈ S, |⟪u, L.starProjection y - m⟫| ≤
      Real.sqrt (Module.finrank ℝ S * f) *
        Real.sqrt (‖y - L.starProjection y‖ ^ 2 / Module.finrank ℝ Lᗮ) * ‖u‖) ↔
    ‖S.starProjection (y - m)‖ ^ 2 / Module.finrank ℝ S /
      (‖Lᗮ.starProjection (y - m)‖ ^ 2 / Module.finrank ℝ Lᗮ) ≤ f := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ S) with hz | hr
  · have hbot : S = ⊥ := Submodule.finrank_eq_zero.mp hz
    subst S
    simp [hf, Submodule.starProjection_bot]
  have hd : 0 < Module.finrank ℝ Lᗮ := by
    by_contra! h
    have hbot : Lᗮ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero h)
    simp [hbot, Submodule.starProjection_bot] at hy
  have hr' : (0 : ℝ) < Module.finrank ℝ S := by exact_mod_cast hr
  have hd' : (0 : ℝ) < Module.finrank ℝ Lᗮ := by exact_mod_cast hd
  have hres : y - L.starProjection y = Lᗮ.starProjection (y - m) := by
    rw [map_sub, Submodule.starProjection_orthogonal_apply_eq_zero hm, sub_zero,
      Submodule.starProjection_orthogonal_val]
  simp only [← Real.norm_eq_abs]
  rw [hres, S.forall_norm_inner_starProjection_sub_le_iff hSL y m (by positivity),
    ← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), div_le_iff₀ (div_pos hy hd'), div_le_iff₀ hr']
  rw [mul_comm _ (Module.finrank ℝ S : ℝ), ← mul_assoc]

/-- Scheffé's intervals for all contrasts in `S` simultaneously cover their true values
with probability `1 - α`. The model mean belongs to `L`, the residual degrees of freedom are
`finrank ℝ Lᗮ`, and the contrast degrees of freedom are `finrank ℝ S`. -/
theorem measureReal_scheffe_event_eq_one_sub [DecidableEq ι] (hSL : S ≤ L) (hm : m ∈ L)
    (hr : 0 < Module.finrank ℝ S) (hd : 0 < Module.finrank ℝ Lᗮ) {σ α : ℝ}
    (hσ : σ ≠ 0) (hα : α ∈ Ioc 0 1) :
    let r := Module.finrank ℝ S
    let d := Module.finrank ℝ Lᗮ
    let f := (fisherSnedecorMeasure r d).quantile (1 - α)
    (multivariateGaussian m (σ ^ 2 • (1 : Matrix ι ι ℝ))).real
      {y | ∀ u ∈ S, |⟪u, L.starProjection y - m⟫| ≤
        Real.sqrt (r * f) * Real.sqrt (‖y - L.starProjection y‖ ^ 2 / d) * ‖u‖} =
      1 - α := by
  let P := multivariateGaussian m (σ ^ 2 • (1 : Matrix ι ι ℝ))
  let r := Module.finrank ℝ S
  let d := Module.finrank ℝ Lᗮ
  let F := fisherSnedecorMeasure r d
  let f := F.quantile (1 - α)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlevel : 1 - α ∈ Ico (0 : ℝ) 1 := ⟨sub_nonneg.mpr hα.2, sub_lt_self _ hα.1⟩
  obtain ⟨hf, hcdf⟩ : 0 ≤ f ∧ cdf F f = 1 - α :=
    quantile_fisherSnedecorMeasure_spec hr' hd' hlevel
  have hY := HasLaw.id (μ := P)
  have hF := hY.fisherSnedecor_starProjection_ratio hσ
    ((Submodule.isOrtho_orthogonal_right L).mono_left hSL) hr hd
  have hres := hY.norm_sq_starProjection_sub_div_multivariateGaussian_smul_one hσ Lᗮ
  have hpos := (hres.ae_iff (measurableSet_setOfPred.mp measurableSet_Ioi)).2
    (ae_pos_chiSquaredMeasure hd')
  have hEvent : {y | ∀ u ∈ S, |⟪u, L.starProjection y - m⟫| ≤
        Real.sqrt (r * f) * Real.sqrt (‖y - L.starProjection y‖ ^ 2 / d) * ‖u‖} =ᵐ[P]
      {y | ‖S.starProjection (y - m)‖ ^ 2 / r / (‖Lᗮ.starProjection (y - m)‖ ^ 2 / d) ≤ f} := by
    filter_upwards [hpos] with y hy
    exact scheffe_event_iff hf hSL hm y
      ((div_pos_iff_of_pos_right (sq_pos_of_ne_zero hσ)).mp hy)
  have hprob := isProbabilityMeasure_fisherSnedecorMeasure hr' hd'
  dsimp only
  rw [measureReal_congr hEvent, ← hcdf, cdf_eq_real]
  simpa only [id_eq, r, d, F, f, Set.Iic] using
    hF.measureReal_eq (p := fun z ↦ z ≤ f) measurableSet_Iic

end TauCeti
