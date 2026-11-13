/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative
public import TauCeti.Geometry.Manifold.Riemannian.Conformal

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

* `Bundle.ContMDiffRiemannianMetric.relativeVolumeDensity_rescale`: the conformal relative density.

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

open Bundle MeasureTheory Set Bundle.ContMDiffRiemannianMetric
open scoped ENNReal Manifold ContDiff

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- **The conformal case.** In real dimension `N`, the relative volume density of the rescaled
metric `f g` with respect to `g` is `f ^ (N / 2)`. -/
@[simp]
theorem relativeVolumeDensity_rescale
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} {hf : ContMDiff I 𝓘(ℝ) n f}
    {hf_pos : ∀ x, 0 < f x} (x : M) :
    relativeVolumeDensity g (g.rescale f hf hf_pos) x =
      f x ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  have hpos := chartVolumeDensity_pos (I := I) (WithMetric.toWithMetric g x)
    (by simpa only [TangentBundle.trivializationAt_baseSet] using
      mem_chart_source H (WithMetric.toWithMetric g x))
  rw [relativeVolumeDensity_eq_div_chartVolumeDensity g _ (mem_chart_source H x),
    WithMetric.chartVolumeDensity_rescale, mul_div_cancel_right₀ _ hpos.ne']

/-- Rescaling the compared metric multiplies the relative density by the conformal factor. -/
@[simp]
theorem relativeVolumeDensity_rescale_right {n' : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} {hf : ContMDiff I 𝓘(ℝ) n' f} {hf_pos : ∀ x, 0 < f x} (x : M) :
    relativeVolumeDensity g (g'.rescale f hf hf_pos) x =
      f x ^ ((Module.finrank ℝ E : ℝ) / 2) * relativeVolumeDensity g g' x := by
  rw [relativeVolumeDensity_eq_mul g g', relativeVolumeDensity_rescale, mul_comm]

/-- Rescaling the reference metric divides the relative density by the conformal factor. -/
@[simp]
theorem relativeVolumeDensity_rescale_left {n' : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} {hf : ContMDiff I 𝓘(ℝ) n f} {hf_pos : ∀ x, 0 < f x} (x : M) :
    relativeVolumeDensity (g.rescale f hf hf_pos) g' x =
      relativeVolumeDensity g g' x / f x ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  rw [← relativeVolumeDensity_inv g' _, relativeVolumeDensity_rescale_right]
  simp only [mul_inv_rev, relativeVolumeDensity_inv, div_eq_mul_inv]

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}

variable {f : M → ℝ} {hf : ContMDiff I 𝓘(ℝ) n f} {hf_pos : ∀ x, 0 < f x}

variable [FiniteDimensional ℝ E] [LindelofSpace M]

/-- **Volume under conformal change.** In real dimension `N`, the Riemannian volume of the
rescaled metric `f g` is the image, under the identity map between the copies of `M`, of the
Riemannian volume of `g` weighted by the density `f ^ (N / 2)`. -/
theorem riemannianVolume_rescale :
    riemannianVolume I (WithMetric (g.rescale f hf hf_pos)) =
      ((riemannianVolume I (WithMetric g)).withDensity fun x ↦
          ENNReal.ofReal (f x.ofWithMetric ^ ((Module.finrank ℝ E : ℝ) / 2))).map
        fun x ↦ toWithMetric (g.rescale f hf hf_pos) x.ofWithMetric := by
  simpa only [relativeVolumeDensity_rescale] using
    riemannianVolume_eq_map_withDensity_relativeVolumeDensity g (g.rescale f hf hf_pos)

/-- Integration of a nonnegative function against the volume of the rescaled metric `f g`, in real
dimension `N`: `∫ φ dV_{f g} = ∫ f ^ (N / 2) φ dV_g`. -/
theorem lintegral_riemannianVolume_rescale (φ : M → ℝ≥0∞) :
    ∫⁻ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric (g.rescale f hf hf_pos)) =
      ∫⁻ x, ENNReal.ofReal (f x.ofWithMetric ^ ((Module.finrank ℝ E : ℝ) / 2)) *
        φ x.ofWithMetric ∂riemannianVolume I (WithMetric g) := by
  simpa only [relativeVolumeDensity_rescale] using
    lintegral_riemannianVolume_eq_lintegral_relativeVolumeDensity_mul
      g (g.rescale f hf hf_pos) φ

/-- Integration against the volume of the rescaled metric `f g`, in real dimension `N`:
`∫ φ dV_{f g} = ∫ f ^ (N / 2) φ dV_g`. -/
theorem integral_riemannianVolume_rescale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : M → F) :
    ∫ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric (g.rescale f hf hf_pos)) =
      ∫ x, f x.ofWithMetric ^ ((Module.finrank ℝ E : ℝ) / 2) • φ x.ofWithMetric
        ∂riemannianVolume I (WithMetric g) := by
  simpa only [relativeVolumeDensity_rescale] using
    integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul
      g (g.rescale f hf hf_pos) φ

/-- **Total volume under conformal change.** On a compact manifold of real dimension `N`, the
total volume of the rescaled metric `f g` is `∫ f ^ (N / 2) dV_g`. -/
theorem riemannianTotalVolume_rescale [CompactSpace M] :
    riemannianTotalVolume I (WithMetric (g.rescale f hf hf_pos)) =
      ∫ x, f x.ofWithMetric ^ ((Module.finrank ℝ E : ℝ) / 2)
        ∂riemannianVolume I (WithMetric g) := by
  simpa only [relativeVolumeDensity_rescale] using
    riemannianTotalVolume_eq_integral_relativeVolumeDensity g (g.rescale f hf hf_pos)

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
