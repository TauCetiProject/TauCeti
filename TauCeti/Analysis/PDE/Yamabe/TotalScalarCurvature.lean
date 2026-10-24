/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.ConformalLaplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal

/-!
# Total scalar curvature of a conformal metric

Let `g` be a smooth Riemannian metric on a manifold `M` of dimension `n ≠ 2`, and let
`ĝ = u ^ (4 / (n - 2)) g` for a positive function `u`. The scalar curvature of `ĝ` is
`Scal_ĝ = u ^ (-(n + 2) / (n - 2)) L_g u`, where `L_g` is the conformal Laplacian, and the volume
of `ĝ` has density `u ^ pₙ` with respect to that of `g`, where `pₙ = 2 n / (n - 2)`. Since
`pₙ - (n + 2) / (n - 2) = 1`, the two factors combine into the identity of densities

`Scal_ĝ dV_ĝ = u L_g u dV_g`.

Integrating it gives the total scalar curvature `∫ Scal_ĝ dV_ĝ = ∫ u L_g u dV_g`, and dividing by
`Vol(ĝ) ^ (2 / pₙ) = (∫ u ^ pₙ dV_g) ^ (2 / pₙ)` gives the identity between the
volume-normalized total scalar curvature of `ĝ` and a quotient of integrals against `g`:

`(∫ Scal_ĝ dV_ĝ) / Vol(ĝ) ^ (2 / pₙ) = (∫ u L_g u dV_g) / (∫ u ^ pₙ dV_g) ^ (2 / pₙ)`.

On a closed manifold, integration by parts turns `∫ u L_g u dV_g` into the energy
`∫ (aₙ |du|² + Scal_g u²) dV_g`, so the right-hand side is the Yamabe quotient `Q_g(u)`; this file
does not perform that integration by parts. When `u` is a positive solution of the Yamabe
equation `L_g u = λ u ^ (pₙ - 1)`, the numerator is `∫ u L_g u dV_g = λ ∫ u ^ pₙ dV_g`, so the
quotient equals `λ` when `u` has unit `L^pₙ` norm.

The integrals are Bochner integrals and the identities need no integrability hypothesis: the two
integrands agree pointwise once the volume of `ĝ` is written as a density against that of `g`.
As in `TauCeti.WithMetric.integral_riemannianVolume_rescale`, the two volumes live on the
metric-indexed copies `TauCeti.WithMetric g` and `TauCeti.WithMetric ĝ` of `M`, while the
conformal Laplacian of `g` is taken with `g` installed as the `RiemannianBundle` instance of `M`.

## Main results

* `TauCeti.Yamabe.rpow_criticalExponent_mul_scalarCurvature_rescale`: the pointwise identity
  `u ^ pₙ Scal_ĝ = u L_g u`.
* `TauCeti.Yamabe.integral_scalarCurvature_rescale`: `∫ Scal_ĝ dV_ĝ = ∫ u L_g u dV_g`.
* `TauCeti.Yamabe.integral_scalarCurvature_rescale_div_riemannianTotalVolume_rpow`: on a compact
  manifold, `(∫ Scal_ĝ dV_ĝ) / Vol(ĝ) ^ (2 / pₙ) = (∫ u L_g u dV_g) / (∫ u ^ pₙ dV_g) ^ (2 / pₙ)`.
* `TauCeti.Yamabe.integral_mul_conformalLaplacian_eq_mul_integral_rpow`: a positive solution of
  `L_g u = c u ^ (pₙ - 1)` has `∫ u L_g u dV_g = c ∫ u ^ pₙ dV_g`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2.
-/

public section

open Bundle MeasureTheory Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Yamabe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- **Scalar curvature density of a conformal metric.** In dimension `n ≠ 2`, let `u` be a
positive function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric. Then
`u ^ pₙ Scal_ĝ = u L_g u`, where `pₙ = 2 n / (n - 2)` and `L_g` is the conformal Laplacian of `g`.
Since `u ^ pₙ` is the density of the volume of `ĝ` against that of `g`, this is the identity of
densities `Scal_ĝ dV_ĝ = u L_g u dV_g`. -/
theorem rpow_criticalExponent_mul_scalarCurvature_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} (x : M) :
    u x ^ criticalExponent (finrank ℝ E) *
        (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).scalarCurvature x =
      u x * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalLaplacian I u x) := by
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn)
  have hexp : criticalExponent (finrank ℝ E) +
      -((finrank ℝ E : ℝ) + 2) / ((finrank ℝ E : ℝ) - 2) = 1 := by
    rw [criticalExponent_def]
    field_simp
    ring
  rw [scalarCurvature_rescale_eq_rpow_mul_conformalLaplacian g hn hu_pos x, ← mul_assoc,
    ← Real.rpow_add (hu_pos x), hexp, Real.rpow_one]

variable [LindelofSpace M]

/-- **Total scalar curvature of a conformal metric.** In dimension `n ≠ 2`, let `u` be a positive
function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric. Then
`∫ Scal_ĝ dV_ĝ = ∫ u L_g u dV_g`, where `L_g` is the conformal Laplacian of `g`. No integrability
hypothesis is needed: the two integrands agree once `dV_ĝ` is written as a density against
`dV_g`. -/
theorem integral_scalarCurvature_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} :
    ∫ x, (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).scalarCurvature
        x.ofWithMetric ∂riemannianVolume I (WithMetric (g.rescale _ hf hf_pos)) =
      ∫ x, u x.ofWithMetric *
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          conformalLaplacian I u x.ofWithMetric) ∂riemannianVolume I (WithMetric g) := by
  rw [WithMetric.integral_riemannianVolume_rescale]
  congr 1
  funext x
  rw [← Real.rpow_mul (hu_pos _).le, smul_eq_mul,
    ← rpow_criticalExponent_mul_scalarCurvature_rescale (hf := hf) (hf_pos := hf_pos) g hn hu_pos,
    criticalExponent_def]
  congr 2
  ring

/-- **Volume-normalized total scalar curvature of a conformal metric.** On a compact manifold of
dimension `n ≠ 2`, let `u` be a positive function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth
metric, and let `pₙ = 2 n / (n - 2)`. Then
`(∫ Scal_ĝ dV_ĝ) / Vol(ĝ) ^ (2 / pₙ) = (∫ u L_g u dV_g) / (∫ u ^ pₙ dV_g) ^ (2 / pₙ)`,
where `L_g` is the conformal Laplacian of `g`. -/
theorem integral_scalarCurvature_rescale_div_riemannianTotalVolume_rpow [CompactSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} :
    (∫ x, (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).scalarCurvature
          x.ofWithMetric ∂riemannianVolume I (WithMetric (g.rescale _ hf hf_pos))) /
        riemannianTotalVolume I (WithMetric (g.rescale _ hf hf_pos)) ^
          (2 / criticalExponent (finrank ℝ E)) =
      (∫ x, u x.ofWithMetric *
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
            conformalLaplacian I u x.ofWithMetric) ∂riemannianVolume I (WithMetric g)) /
        (∫ x, u x.ofWithMetric ^ criticalExponent (finrank ℝ E)
          ∂riemannianVolume I (WithMetric g)) ^ (2 / criticalExponent (finrank ℝ E)) := by
  rw [integral_scalarCurvature_rescale g hn hu_pos,
    WithMetric.riemannianTotalVolume_rescale_rpow fun x ↦ (hu_pos x).le, criticalExponent_def]

/-- **Integral of the Yamabe equation.** Let `u` be a positive solution of the Yamabe equation
`L_g u = c u ^ (pₙ - 1)`, where `L_g` is the conformal Laplacian and `pₙ = 2 n / (n - 2)`. Then
`∫ u L_g u dV_g = c ∫ u ^ pₙ dV_g`. -/
theorem integral_mul_conformalLaplacian_eq_mul_integral_rpow
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {u : M → ℝ} (hu_pos : ∀ x, 0 < u x) {c : ℝ}
    (hu : ∀ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      conformalLaplacian I u x) = c * u x ^ (criticalExponent (finrank ℝ E) - 1)) :
    ∫ x, u x.ofWithMetric *
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          conformalLaplacian I u x.ofWithMetric) ∂riemannianVolume I (WithMetric g) =
      c * ∫ x, u x.ofWithMetric ^ criticalExponent (finrank ℝ E)
        ∂riemannianVolume I (WithMetric g) := by
  rw [← integral_const_mul]
  congr 1
  funext x
  have hpow := Real.rpow_add (hu_pos x.ofWithMetric) 1 (criticalExponent (finrank ℝ E) - 1)
  rw [Real.rpow_one, add_sub_cancel] at hpow
  rw [hu, hpow]
  ring

end TauCeti.Yamabe
