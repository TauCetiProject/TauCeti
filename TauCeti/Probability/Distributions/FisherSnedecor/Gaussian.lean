/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.FisherSnedecor.ChiSquared
public import TauCeti.Probability.Distributions.Gaussian.Isotropic

/-!
# Fisher–Snedecor laws from Gaussian projections

The ratio of the mean squares of two orthogonal projections of a centered isotropic
Gaussian has Fisher–Snedecor law. The degrees of freedom are the projection ranks.
-/

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {P : Measure Ω} {Y : Ω → EuclideanSpace ℝ ι} {m : EuclideanSpace ℝ ι} {σ : ℝ}

/-- The ratio of centered mean squares from two orthogonal projections of an isotropic
Gaussian has the Fisher–Snedecor law with the two projection ranks as degrees of freedom. -/
theorem HasLaw.fisherSnedecor_starProjection_ratio
    (hY : HasLaw Y (multivariateGaussian m (σ ^ 2 • (1 : Matrix ι ι ℝ))) P)
    (hσ : σ ≠ 0) {K L : Submodule ℝ (EuclideanSpace ℝ ι)} (hKL : K ⟂ L)
    (hk : 0 < Module.finrank ℝ K) (hl : 0 < Module.finrank ℝ L) :
    HasLaw (fun ω ↦ (‖K.starProjection (Y ω - m)‖ ^ 2 / Module.finrank ℝ K) /
      (‖L.starProjection (Y ω - m)‖ ^ 2 / Module.finrank ℝ L))
      (fisherSnedecorMeasure (Module.finrank ℝ K) (Module.finrank ℝ L)) P := by
  have hind := (hY.indepFun_orthogonalProjectionOnto_multivariateGaussian_smul_one hKL).comp
    (φ := fun k : K ↦ ‖k - K.orthogonalProjectionOnto m‖ ^ 2 / σ ^ 2)
    (ψ := fun l : L ↦ ‖l - L.orthogonalProjectionOnto m‖ ^ 2 / σ ^ 2)
    (by fun_prop) (by fun_prop)
  simp only [Function.comp_def, ← Submodule.norm_coe, ← map_sub,
    ← Submodule.starProjection_apply] at hind
  have hratio := hasLaw_fisherSnedecor_of_chiSquared
    (m := (Module.finrank ℝ K : ℝ)) (n := (Module.finrank ℝ L : ℝ))
    (by exact_mod_cast hk) (by exact_mod_cast hl) hind
    (hY.norm_sq_starProjection_sub_div_multivariateGaussian_smul_one hσ K)
    (hY.norm_sq_starProjection_sub_div_multivariateGaussian_smul_one hσ L)
  refine hratio.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
  dsimp only
  rw [div_right_comm (‖K.starProjection (Y ω - m)‖ ^ 2) (σ ^ 2),
    div_right_comm (‖L.starProjection (Y ω - m)‖ ^ 2) (σ ^ 2),
    div_div_div_cancel_right₀ (pow_ne_zero 2 hσ)]

end ProbabilityTheory
