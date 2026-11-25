/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Topology.UnitInterval
public import TauCeti.Probability.BrownianMotion.Bridge.Basic
public import TauCeti.Probability.BrownianMotion.WienerMeasure
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import TauCeti.MeasureTheory.Measure.ContinuousMap
import TauCeti.Probability.Distributions.Gaussian.IsGaussianProcess

/-!
# The standard Brownian bridge on continuous paths

The *standard Brownian bridge* is the centred Gaussian process on `[0, 1]` with covariance
`min s t - s t`. This file constructs its law `TauCeti.standardBrownianBridgeMeasure` as a Borel
probability measure on the space `C(unitInterval, ℝ)` of continuous paths, with the compact-open
(equivalently, uniform) topology: it is the image of Wiener measure under
`ω ↦ (t ↦ ω t - t ω 1)`. The law is characterized by its finite-dimensional marginals, the
centred multivariate Gaussian laws with covariance matrix `(min sᵢ sⱼ - sᵢ sⱼ)ᵢⱼ`.

On the product σ-algebra of all paths `Set.Iic T → ℝ`, the law of the bridge on `[0, T]` is
`TauCeti.brownianBridgeMeasure T`. The continuous carrier is needed wherever the bridge is used
through functionals of the whole path, such as the supremum norm. This is how the bridge enters
the asymptotics of empirical processes: it is the Gaussian limit of the uniform empirical process,
and its image under `x ↦ x ∘ F` is the limit law of the empirical process of a law on `ℝ` with
distribution function `F`.

## Main definitions

* `TauCeti.standardBrownianBridgePath`: the continuous map `ω ↦ (t ↦ ω t - t ω 1)` from paths
  on `ℝ≥0` to paths on `unitInterval`.
* `TauCeti.standardBrownianBridgeMeasure`: the law of the standard Brownian bridge on
  `C(unitInterval, ℝ)`.

## Main results

* `TauCeti.hasLaw_standardBrownianBridgePath`: under `wienerMeasure`,
  `standardBrownianBridgePath` has law `standardBrownianBridgeMeasure`.
* `TauCeti.isGaussianProcess_eval_standardBrownianBridgeMeasure`: the coordinate process is a
  Gaussian process.
* `TauCeti.integral_eval_standardBrownianBridgeMeasure`,
  `TauCeti.covariance_eval_standardBrownianBridgeMeasure`,
  `TauCeti.hasLaw_eval_standardBrownianBridgeMeasure`: it is centred, with covariance
  `min s t - s t` and marginal `gaussianReal 0 (t (1 - t))` at `t`.
* `TauCeti.ae_eval_zero_standardBrownianBridgeMeasure`,
  `TauCeti.ae_eval_one_standardBrownianBridgeMeasure`: almost every path vanishes at `0` and `1`.
* `TauCeti.map_toLp_standardBrownianBridgeMeasure`: the finite-dimensional marginals are
  `multivariateGaussian 0 (Matrix.of fun i j ↦ min (s i) (s j) - s i * s j)`.
* `TauCeti.eq_standardBrownianBridgeMeasure_iff`: these marginals characterize the law among all
  measures on `C(unitInterval, ℝ)`.
* `TauCeti.map_standardBrownianBridgeMeasure_eq_brownianBridgeMeasure`: viewed on the product
  σ-algebra of all paths on `[0, 1]`, the law is `brownianBridgeMeasure 1`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §5.6.B.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §19.1.
-/

public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped NNReal

namespace TauCeti

/-- The standard Brownian bridge path built from a path `ω` on `ℝ≥0`: `t ↦ ω t - t ω 1` on
`[0, 1]`. -/
noncomputable def standardBrownianBridgePath (ω : C(ℝ≥0, ℝ)) : C(I, ℝ) :=
  ⟨fun t ↦ brownianBridge (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) 1 (toNNReal t) ω,
    (continuous_brownianBridge ω.continuous).comp toNNReal_continuous⟩

@[simp]
theorem standardBrownianBridgePath_apply (ω : C(ℝ≥0, ℝ)) (t : I) :
    standardBrownianBridgePath ω t =
      brownianBridge (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) 1 (toNNReal t) ω := (rfl)

@[fun_prop]
theorem measurable_standardBrownianBridgePath : Measurable standardBrownianBridgePath :=
  ContinuousMap.measurable_iff_eval.2 fun t ↦ by
    simp only [standardBrownianBridgePath_apply]
    exact measurable_brownianBridge (ContinuousMap.measurable_eval _)
      (ContinuousMap.measurable_eval _)

/-- The **standard Brownian bridge** law on the continuous paths `C(unitInterval, ℝ)`: the law of
`t ↦ W t - t W 1` for a Brownian motion `W`, that is, the image of `wienerMeasure`. By
`TauCeti.eq_standardBrownianBridgeMeasure_iff` it is the unique measure on `C(unitInterval, ℝ)`
whose finite-dimensional marginals are the centred Gaussian laws with covariance
`min s t - s t`. -/
noncomputable def standardBrownianBridgeMeasure : Measure C(I, ℝ) :=
  wienerMeasure.map standardBrownianBridgePath

/-- Under `wienerMeasure`, the standard Brownian bridge path has law
`standardBrownianBridgeMeasure`. -/
theorem hasLaw_standardBrownianBridgePath :
    HasLaw standardBrownianBridgePath standardBrownianBridgeMeasure wienerMeasure :=
  ⟨measurable_standardBrownianBridgePath.aemeasurable, rfl⟩

instance : IsProbabilityMeasure standardBrownianBridgeMeasure :=
  hasLaw_standardBrownianBridgePath.isProbabilityMeasure_iff.1 inferInstance

/-- The bridge of the coordinate process of `wienerMeasure`, read at the times of `[0, 1]`, is a
Gaussian process. -/
private lemma isGaussianProcess_standardBrownianBridgePath :
    IsGaussianProcess (fun t ω ↦ standardBrownianBridgePath ω t) wienerMeasure := by
  simp only [standardBrownianBridgePath_apply]
  exact (isPreBrownianReal_eval_wienerMeasure.isGaussianProcess_brownianBridge 1).comp_right
    toNNReal

/-- Under the standard Brownian bridge law, the coordinate process is a Gaussian process. -/
theorem isGaussianProcess_eval_standardBrownianBridgeMeasure :
    IsGaussianProcess (fun t (x : C(I, ℝ)) ↦ x t) standardBrownianBridgeMeasure where
  hasGaussianLaw J := by
    have hJ := (isGaussianProcess_standardBrownianBridgePath.hasGaussianLaw J).isGaussian_map
    refine ⟨(ContinuousMap.measurable_finsetRestrict J).aemeasurable, ?_⟩
    rwa [standardBrownianBridgeMeasure, Measure.map_map (ContinuousMap.measurable_finsetRestrict J)
      measurable_standardBrownianBridgePath]

/-- The standard Brownian bridge is centred. -/
@[simp]
theorem integral_eval_standardBrownianBridgeMeasure (t : I) :
    ∫ x : C(I, ℝ), x t ∂standardBrownianBridgeMeasure = 0 := by
  rw [standardBrownianBridgeMeasure,
    integral_map measurable_standardBrownianBridgePath.aemeasurable
      (ContinuousMap.measurable_eval t).aestronglyMeasurable]
  simp only [standardBrownianBridgePath_apply]
  exact isPreBrownianReal_eval_wienerMeasure.integral_brownianBridge 1 (toNNReal t)

/-- The covariance of the standard Brownian bridge: `cov[x s, x t] = min s t - s t`. -/
@[simp]
theorem covariance_eval_standardBrownianBridgeMeasure (s t : I) :
    cov[fun x : C(I, ℝ) ↦ x s, fun x : C(I, ℝ) ↦ x t; standardBrownianBridgeMeasure] =
      min (s : ℝ) t - s * t := by
  rw [standardBrownianBridgeMeasure, covariance_map_fun
    (ContinuousMap.measurable_eval s).aestronglyMeasurable
    (ContinuousMap.measurable_eval t).aestronglyMeasurable
    measurable_standardBrownianBridgePath.aemeasurable]
  simp only [standardBrownianBridgePath_apply]
  rw [isPreBrownianReal_eval_wienerMeasure.covariance_brownianBridge
    (by exact_mod_cast s.property.2) (by exact_mod_cast t.property.2)]
  simp

/-- The variance of the standard Brownian bridge at time `t` is `t (1 - t)`. -/
@[simp]
theorem variance_eval_standardBrownianBridgeMeasure (t : I) :
    Var[fun x : C(I, ℝ) ↦ x t; standardBrownianBridgeMeasure] = t * (1 - t) := by
  rw [← covariance_self (ContinuousMap.measurable_eval t).aemeasurable,
    covariance_eval_standardBrownianBridgeMeasure, min_self]
  ring

/-- The marginal of the standard Brownian bridge at time `t` is the centred Gaussian law of
variance `t (1 - t)`. -/
theorem hasLaw_eval_standardBrownianBridgeMeasure (t : I) :
    HasLaw (fun x : C(I, ℝ) ↦ x t) (gaussianReal 0 (toNNReal t * toNNReal (σ t)))
      standardBrownianBridgeMeasure := by
  have hv : toNNReal t * (1 - toNNReal t) / 1 = toNNReal t * toNNReal (σ t) := by
    rw [div_one, ← toNNReal_add_toNNReal_symm t, add_tsub_cancel_left]
  have h := isPreBrownianReal_eval_wienerMeasure.hasLaw_brownianBridge
    (T := 1) (t := toNNReal t) (by exact_mod_cast t.property.2)
  rw [hv] at h
  have h' : HasLaw (fun ω ↦ standardBrownianBridgePath ω t)
      (gaussianReal 0 (toNNReal t * toNNReal (σ t))) wienerMeasure := by
    simpa only [standardBrownianBridgePath_apply] using h
  exact HasLaw.comp_of_hasLaw_comp (f := fun x : C(I, ℝ) ↦ x t)
    (ContinuousMap.measurable_eval t).aemeasurable
    hasLaw_standardBrownianBridgePath HasLaw.id h'

/-- Almost every path of the standard Brownian bridge starts at `0`. -/
theorem ae_eval_zero_standardBrownianBridgeMeasure :
    ∀ᵐ x ∂standardBrownianBridgeMeasure, x 0 = 0 := by
  rw [standardBrownianBridgeMeasure, ae_map_iff measurable_standardBrownianBridgePath.aemeasurable
    (measurableSet_eq_fun (ContinuousMap.measurable_eval 0) measurable_const)]
  filter_upwards [ae_eval_zero_wienerMeasure] with ω hω
  simp [hω]

/-- Almost every path of the standard Brownian bridge ends at `0`. -/
theorem ae_eval_one_standardBrownianBridgeMeasure :
    ∀ᵐ x ∂standardBrownianBridgeMeasure, x 1 = 0 := by
  rw [standardBrownianBridgeMeasure, ae_map_iff measurable_standardBrownianBridgePath.aemeasurable
    (measurableSet_eq_fun (ContinuousMap.measurable_eval 1) measurable_const)]
  exact Filter.Eventually.of_forall fun ω ↦ by simp

/-- The finite-dimensional marginals of the standard Brownian bridge: at times `s i`, not
necessarily distinct, the values form a centred Gaussian vector with covariance matrix
`(min (s i) (s j) - s i s j)ᵢⱼ`. -/
theorem map_toLp_standardBrownianBridgeMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → I) :
    standardBrownianBridgeMeasure.map (fun x ↦ WithLp.toLp 2 fun i ↦ x (s i)) =
      multivariateGaussian 0 (Matrix.of fun i j ↦ min (s i : ℝ) (s j) - s i * s j) := by
  rw [isGaussianProcess_eval_standardBrownianBridgeMeasure.map_toLp_eq_multivariateGaussian s]
  simp only [integral_eval_standardBrownianBridgeMeasure,
    covariance_eval_standardBrownianBridgeMeasure]
  rw [← Pi.zero_def, WithLp.toLp_zero]

/-- **Uniqueness of the standard Brownian bridge law.** A measure on `C(unitInterval, ℝ)` is the
standard Brownian bridge law if and only if, for all finitely many times `s 0, …, s (m - 1)`, the
values at these times form a centred Gaussian vector with covariance matrix
`(min (s i) (s j) - s i s j)ᵢⱼ`. -/
theorem eq_standardBrownianBridgeMeasure_iff {μ : Measure C(I, ℝ)} :
    μ = standardBrownianBridgeMeasure ↔ ∀ (m : ℕ) (s : Fin m → I),
      μ.map (fun x ↦ WithLp.toLp 2 fun i ↦ x (s i)) =
        multivariateGaussian 0 (Matrix.of fun i j ↦ min (s i : ℝ) (s j) - s i * s j) := by
  refine ⟨fun h m s ↦ h ▸ map_toLp_standardBrownianBridgeMeasure s, fun h ↦ ?_⟩
  refine continuousMap_measure_ext_of_forall_finset_map_restrict_eq fun J ↦ ?_
  -- the values on `J` are a measurable rearrangement of the vector of values at the times of `J`
  -- listed along `J.equivFin`
  let s : Fin J.card → I := fun i ↦ J.equivFin.symm i
  let Φ : EuclideanSpace ℝ (Fin J.card) → J → ℝ := fun y t ↦ y (J.equivFin t)
  have hΦ : Measurable Φ := by fun_prop
  have hV : Measurable fun x : C(I, ℝ) ↦ WithLp.toLp 2 fun i ↦ x (s i) :=
    (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun i ↦ ContinuousMap.measurable_eval _)
  have hrestrict : (fun x : C(I, ℝ) ↦ J.restrict (x : I → ℝ)) =
      Φ ∘ fun x ↦ WithLp.toLp 2 fun i ↦ x (s i) := by
    ext x t
    simp [Φ, s]
  rw [hrestrict, ← Measure.map_map hΦ hV, ← Measure.map_map hΦ hV, h,
    map_toLp_standardBrownianBridgeMeasure]

/-- Forgetting continuity, the standard Brownian bridge law is the law `brownianBridgeMeasure 1`
of the Brownian bridge on `[0, 1]` on the product σ-algebra of all paths `Set.Iic 1 → ℝ`. -/
theorem map_standardBrownianBridgeMeasure_eq_brownianBridgeMeasure :
    standardBrownianBridgeMeasure.map
        (fun x (t : Set.Iic (1 : ℝ≥0)) ↦ x ⟨t, t.val.property, by exact_mod_cast t.property⟩) =
      brownianBridgeMeasure 1 := by
  have hR : Measurable fun (x : C(I, ℝ)) (t : Set.Iic (1 : ℝ≥0)) ↦
      x ⟨t, t.val.property, by exact_mod_cast t.property⟩ :=
    Measurable.of_eval fun _ ↦ ContinuousMap.measurable_eval _
  have hm : AEMeasurable (fun (ω : C(ℝ≥0, ℝ)) (t : Set.Iic (1 : ℝ≥0)) ↦ ω t) wienerMeasure :=
    (Measurable.of_eval fun _ ↦ ContinuousMap.measurable_eval _).aemeasurable
  have hcomp : (fun (x : C(I, ℝ)) (t : Set.Iic (1 : ℝ≥0)) ↦
        x ⟨t, t.val.property, by exact_mod_cast t.property⟩) ∘ standardBrownianBridgePath =
      fun ω (t : Set.Iic (1 : ℝ≥0)) ↦ brownianBridge (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) 1 t ω := by
    funext ω t
    simp [toNNReal_mk]
  rw [standardBrownianBridgeMeasure, Measure.map_map hR measurable_standardBrownianBridgePath,
    hcomp]
  exact (isPreBrownianReal_eval_wienerMeasure.hasLaw_brownianBridgeMeasure hm).map_eq

end TauCeti
