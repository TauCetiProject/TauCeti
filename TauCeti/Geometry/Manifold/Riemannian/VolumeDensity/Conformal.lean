/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total

/-!
# The Riemannian volume under a conformal change of metric

Let `g` be a Riemannian metric on a manifold `M` of real dimension `N` and `f` a positive function,
and let `ĝ = f g` be the rescaled metric `Bundle.ContMDiffRiemannianMetric.rescale`. The two metrics
live on the copies `TauCeti.WithMetric g` and `TauCeti.WithMetric ĝ` of `M`, each carrying its own
Riemannian volume. This file proves that the volume measure of `ĝ` has density `f ^ (N / 2)` with
respect to that of `g`:

`dV_ĝ = f ^ (N / 2) dV_g`,

so that `∫ φ dV_ĝ = ∫ f ^ (N / 2) φ dV_g` for every function `φ` on `M`, and on a compact manifold
`Vol(ĝ) = ∫ f ^ (N / 2) dV_g`. For a nonnegative `u` whose Yamabe conformal factor
`f = u ^ (4 / (N - 2))` is `ContMDiff` and strictly positive, this is
`Vol(ĝ) = ∫ u ^ (2 N / (N - 2)) dV_g`; when `N > 2` the exponent is the critical Sobolev
exponent, while the identity itself holds in every dimension. More generally
`∫ |v| ^ (2 N / (N - 2)) dV_ĝ = ∫ |u v| ^ (2 N / (N - 2)) dV_g` for every function `v`, the
invariance of the denominator of the Yamabe quotient under `v ↦ u v`.

The copies of `M` carry their Borel `σ`-algebras. The identities refine the pointwise
comparison of chart densities `TauCeti.WithMetric.chartVolumeDensity_rescale`, and use no
orientation.

## Main results

* `TauCeti.WithMetric.riemannianVolume_rescale`: the Riemannian volume of `f g` is the image of
  the volume of `g` weighted by `f ^ (N / 2)`.
* `TauCeti.WithMetric.lintegral_riemannianVolume_rescale`,
  `TauCeti.WithMetric.integral_riemannianVolume_rescale`: integration against the volume of `f g`.
* `TauCeti.WithMetric.riemannianTotalVolume_rescale`: `Vol(f g) = ∫ f ^ (N / 2) dV_g`.
* `TauCeti.WithMetric.integral_abs_rpow_rescale_rpow`: for `ĝ = u ^ (4 / (N - 2)) g`,
  `∫ |v| ^ (2 N / (N - 2)) dV_ĝ = ∫ |u v| ^ (2 N / (N - 2)) dV_g`.
* `TauCeti.WithMetric.riemannianTotalVolume_rescale_rpow`: `Vol(u ^ (4 / (N - 2)) g) =
  ∫ u ^ (2 N / (N - 2)) dV_g`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle MeasureTheory Set
open scoped ENNReal Manifold ContDiff

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

variable {f : M → ℝ} {hf : ContMDiff I 𝓘(ℝ) n f} {hf_pos : ∀ x, 0 < f x}

/-- The identity map from the copy of `M` carrying `g` to the copy carrying `f g` is a measurable
embedding. -/
private theorem measurableEmbedding_toWithMetric_rescale :
    MeasurableEmbedding fun x : WithMetric g ↦
      toWithMetric (g.rescale f hf hf_pos) x.ofWithMetric :=
  .of_measurable_inverse (continuous_toWithMetric.comp continuous_ofWithMetric).measurable
    (by rw [range_eq_univ.2 fun y ↦ ⟨toWithMetric g y.ofWithMetric, rfl⟩]; exact .univ)
    (continuous_toWithMetric.comp continuous_ofWithMetric).measurable fun _ ↦ rfl

/-- The density `f ^ (N / 2)` of the volume of `f g` with respect to the volume of `g` is
measurable. -/
private theorem measurable_ofReal_rpow_rescale (hf : Continuous f) :
    Measurable fun x : WithMetric g ↦
      ENNReal.ofReal (f x.ofWithMetric ^ ((Module.finrank ℝ E : ℝ) / 2)) :=
  ((hf.comp continuous_ofWithMetric).measurable.pow_const _).ennreal_ofReal

variable [FiniteDimensional ℝ E] [LindelofSpace M]

/-- **Volume under conformal change.** In real dimension `N`, the Riemannian volume of the
rescaled metric `f g` is the image, under the identity map between the copies of `M`, of the
Riemannian volume of `g` weighted by the density `f ^ (N / 2)`. -/
theorem riemannianVolume_rescale :
    riemannianVolume I (WithMetric (g.rescale f hf hf_pos)) =
      ((riemannianVolume I (WithMetric g)).withDensity fun x ↦
          ENNReal.ofReal (f x.ofWithMetric ^ ((Module.finrank ℝ E : ℝ) / 2))).map
        fun x ↦ toWithMetric (g.rescale f hf hf_pos) x.ofWithMetric := by
  set ι : WithMetric g → WithMetric (g.rescale f hf hf_pos) :=
    fun x ↦ toWithMetric (g.rescale f hf hf_pos) x.ofWithMetric
  have hι : Measurable ι := measurableEmbedding_toWithMetric_rescale.measurable
  symm
  refine eq_riemannianVolume_iff.2 fun β ↦ ?_
  obtain ⟨β⟩ := β
  ext s hs
  have hS : MeasurableSet (s ∩ (chartAt H (toWithMetric (g.rescale f hf hf_pos) β)).source) :=
    hs.inter (chartAt H _).open_source.measurableSet
  have hsub : ι ⁻¹' (s ∩ (chartAt H (toWithMetric (g.rescale f hf hf_pos) β)).source) ⊆
      (chartAt H (toWithMetric g β)).source := fun x hx ↦
    (mem_chartAt_source_iff _ x).2 ((mem_chartAt_source_iff _ (ι x)).1 hx.2)
  rw [Measure.restrict_apply hs, Measure.map_apply hι hS, withDensity_apply _ (hι hS),
    setLIntegral_riemannianVolume_of_subset hsub (hι hS), chartRiemannianVolume_apply _ hs]
  -- Both sides are integrals over the same coordinate set, since the extended charts of the two
  -- copies of `M` agree, and their integrands agree by the pointwise density identity.
  have himage : extChartAt I (toWithMetric g β) ''
      (ι ⁻¹' (s ∩ (chartAt H (toWithMetric (g.rescale f hf hf_pos) β)).source)) =
      extChartAt I (toWithMetric (g.rescale f hf hf_pos) β) ''
        (s ∩ (extChartAt I (toWithMetric (g.rescale f hf hf_pos) β)).source) := by
    rw [extChartAt_source]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ι x, hx, by rw [WithMetric.extChartAt_apply, WithMetric.extChartAt_apply]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨toWithMetric g x.ofWithMetric, hx,
        by rw [WithMetric.extChartAt_apply, WithMetric.extChartAt_apply]⟩
  rw [himage]
  congr 1
  funext y
  simp only [WithMetric.extChartAt_symm_apply, ofWithMetric_toWithMetric,
    chartVolumeDensity_rescale]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hf_pos _).le _), mul_comm]

/-- Integration of a nonnegative function against the volume of the rescaled metric `f g`, in real
dimension `N`: `∫ φ dV_{f g} = ∫ f ^ (N / 2) φ dV_g`. -/
theorem lintegral_riemannianVolume_rescale (φ : M → ℝ≥0∞) :
    ∫⁻ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric (g.rescale f hf hf_pos)) =
      ∫⁻ x, ENNReal.ofReal (f x.ofWithMetric ^ ((Module.finrank ℝ E : ℝ) / 2)) *
        φ x.ofWithMetric ∂riemannianVolume I (WithMetric g) := by
  rw [riemannianVolume_rescale, measurableEmbedding_toWithMetric_rescale.lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (measurable_ofReal_rpow_rescale hf.continuous) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [Pi.mul_apply]

/-- Integration against the volume of the rescaled metric `f g`, in real dimension `N`:
`∫ φ dV_{f g} = ∫ f ^ (N / 2) φ dV_g`. -/
theorem integral_riemannianVolume_rescale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : M → F) :
    ∫ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric (g.rescale f hf hf_pos)) =
      ∫ x, f x.ofWithMetric ^ ((Module.finrank ℝ E : ℝ) / 2) • φ x.ofWithMetric
        ∂riemannianVolume I (WithMetric g) := by
  rw [riemannianVolume_rescale, measurableEmbedding_toWithMetric_rescale.integral_map,
    integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_rpow_rescale hf.continuous)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg (hf_pos _).le _)]

/-- **Total volume under conformal change.** On a compact manifold of real dimension `N`, the
total volume of the rescaled metric `f g` is `∫ f ^ (N / 2) dV_g`. -/
theorem riemannianTotalVolume_rescale [CompactSpace M] :
    riemannianTotalVolume I (WithMetric (g.rescale f hf hf_pos)) =
      ∫ x, f x.ofWithMetric ^ ((Module.finrank ℝ E : ℝ) / 2)
        ∂riemannianVolume I (WithMetric g) := by
  simpa only [integral_const, smul_eq_mul, mul_one, ← riemannianTotalVolume_def] using
    integral_riemannianVolume_rescale (hf := hf) (hf_pos := hf_pos) fun _ ↦ (1 : ℝ)

/-- **Total volume of a Yamabe conformal metric.** On a compact manifold of real dimension `N`,
let `u` be nonnegative and suppose that `u ^ (4 / (N - 2))` is `ContMDiff` of order `n` and
strictly positive. Then the metric `u ^ (4 / (N - 2)) g` has total volume
`∫ u ^ (2 N / (N - 2)) dV_g`. When `N > 2` the exponent `2 N / (N - 2)` is the critical Sobolev
exponent; the identity holds in every dimension. -/
theorem riemannianTotalVolume_rescale_rpow [CompactSpace M] {u : M → ℝ} (hu : ∀ x, 0 ≤ u x)
    {hf : ContMDiff I 𝓘(ℝ) n fun x ↦ u x ^ (4 / ((Module.finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((Module.finrank ℝ E : ℝ) - 2))} :
    riemannianTotalVolume I (WithMetric (g.rescale _ hf hf_pos)) =
      ∫ x, u x.ofWithMetric ^ (2 * (Module.finrank ℝ E : ℝ) / ((Module.finrank ℝ E : ℝ) - 2))
        ∂riemannianVolume I (WithMetric g) := by
  rw [riemannianTotalVolume_rescale]
  congr 1
  funext x
  rw [← Real.rpow_mul (hu _)]
  congr 1
  ring

/-- **Critical `Lᵖ` integrals under conformal change.** In real dimension `N`, for
`ĝ = u ^ (4 / (N - 2)) g` with `u ≥ 0` and any function `v`,
`∫ |v| ^ (2 N / (N - 2)) dV_ĝ = ∫ |u v| ^ (2 N / (N - 2)) dV_g`. -/
theorem integral_abs_rpow_rescale_rpow {u : M → ℝ} (hu : ∀ x, 0 ≤ u x)
    {hf : ContMDiff I 𝓘(ℝ) n fun x ↦ u x ^ (4 / ((Module.finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((Module.finrank ℝ E : ℝ) - 2))} (v : M → ℝ) :
    ∫ x, |v x.ofWithMetric| ^ (2 * (Module.finrank ℝ E : ℝ) / ((Module.finrank ℝ E : ℝ) - 2))
        ∂riemannianVolume I (WithMetric (g.rescale _ hf hf_pos)) =
      ∫ x, |u x.ofWithMetric * v x.ofWithMetric| ^
          (2 * (Module.finrank ℝ E : ℝ) / ((Module.finrank ℝ E : ℝ) - 2))
        ∂riemannianVolume I (WithMetric g) := by
  rw [integral_riemannianVolume_rescale fun y ↦ |v y| ^
    (2 * (Module.finrank ℝ E : ℝ) / ((Module.finrank ℝ E : ℝ) - 2))]
  congr 1
  funext x
  rw [smul_eq_mul, ← Real.rpow_mul (hu _), abs_mul, abs_of_nonneg (hu _),
    Real.mul_rpow (hu _) (abs_nonneg _)]
  congr 2
  ring

end TauCeti.WithMetric
