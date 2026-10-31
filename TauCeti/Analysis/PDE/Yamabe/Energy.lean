/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.TotalScalarCurvature
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric

/-!
# The energy identity of the conformal Laplacian

On a smooth Riemannian manifold `(M, g)` without boundary, of dimension `n`, the conformal
Laplacian `L_g u = aₙ Δ⁺_g u + Scal_g u` is formally self-adjoint, and Green's first identity
turns its quadratic form into the energy

`∫ u L_g u dV_g = ∫ (aₙ |du|²_g + Scal_g u²) dV_g`

for compactly supported `C²` functions `u`; on a closed manifold every `C²` function qualifies.
The right-hand side is the numerator of the Yamabe quotient
`Q_g(u) = (∫ (aₙ |du|² + Scal_g u²) dV_g) / (∫ |u| ^ pₙ dV_g) ^ (2 / pₙ)`, where
`pₙ = 2 n / (n - 2)`. It only involves first derivatives of `u`, which is what makes `Q_g` the
quotient of the Yamabe variational problem.

Combining the energy identity with the integrated conformal covariance
`∫ v L_ĝ v dV_ĝ = ∫ (u v) L_g (u v) dV_g` for `ĝ = u ^ (4 / (n - 2)) g`
(`TauCeti.Yamabe.integral_mul_conformalLaplacian_rescale`) gives the conformal invariance of the
energy, and with the invariance of the denominator
(`TauCeti.WithMetric.integral_abs_rpow_rescale_rpow`) the conformal invariance of the Yamabe
quotient, `Q_ĝ(v) = Q_g(u v)`, for compactly supported `C²` functions `v`. Combined instead with
`∫ Scal_ĝ dV_ĝ = ∫ u L_g u dV_g` (`TauCeti.Yamabe.integral_scalarCurvature_rescale`) it identifies
the total scalar curvature of `ĝ` on a closed manifold with the energy of `u`.

These identities concern smooth functions; the extension of the quotient to the Sobolev space `H¹`
is not treated here.

As in `TauCeti.Analysis.PDE.Yamabe.TotalScalarCurvature`, in the conformal statements the two
volumes live on the metric-indexed copies `TauCeti.WithMetric g` and `TauCeti.WithMetric ĝ` of `M`
(compared through `TauCeti.WithMetric.integral_comp_ofWithMetric`), while the gradient and scalar
curvature of each metric are taken with that metric installed as the `RiemannianBundle` instance of
`M` within its own side of the identity.

## Main declarations

* `TauCeti.Yamabe.conformalEnergyDensity`: the energy density `aₙ |grad u|² + Scal_g u²`.
* `TauCeti.Yamabe.integral_mul_conformalLaplacian`: the bilinear energy identity
  `∫ f L_g h dV = ∫ (aₙ ⟪grad f, grad h⟫ + Scal_g f h) dV`.
* `TauCeti.Yamabe.integral_mul_conformalLaplacian_self`: the energy identity
  `∫ u L_g u dV = ∫ (aₙ |grad u|² + Scal_g u²) dV`.
* `TauCeti.Yamabe.integral_mul_conformalLaplacian_right_eq_left`: formal self-adjointness
  `∫ f L_g h dV = ∫ (L_g f) h dV`.
* `TauCeti.Yamabe.integral_conformalEnergyDensity_rescale`: conformal invariance of the energy,
  `∫ (aₙ |grad v|²_ĝ + Scal_ĝ v²) dV_ĝ = ∫ (aₙ |grad (u v)|²_g + Scal_g (u v)²) dV_g`.
* `TauCeti.Yamabe.integral_conformalEnergyDensity_div_rescale`: conformal invariance of the Yamabe
  quotient, `Q_ĝ(v) = Q_g(u v)`.
* `TauCeti.Yamabe.integral_scalarCurvature_rescale_eq_integral_conformalEnergyDensity`: on a closed
  manifold, `∫ Scal_ĝ dV_ĝ = ∫ (aₙ |grad u|²_g + Scal_g u²) dV_g`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2 (the
  conformal Laplacian, the Yamabe functional and its conformal invariance).
-/

public section

open Bundle MeasureTheory Module TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Yamabe

section Density

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The **conformal energy density** `aₙ |grad u|² + Scal_g u²` of a function `u` on a smooth
Riemannian manifold of dimension `n`, where `aₙ = 4 (n - 1) / (n - 2)` and `Scal_g` is the scalar
curvature. Its integral is the numerator of the Yamabe quotient, and equals `∫ u L_g u dV` for the
conformal Laplacian `L_g` (`TauCeti.Yamabe.integral_mul_conformalLaplacian_self`). -/
def conformalEnergyDensity (u : M → ℝ) (x : M) : ℝ :=
  conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2

/-- Unfolding lemma for `TauCeti.Yamabe.conformalEnergyDensity`. -/
theorem conformalEnergyDensity_def (u : M → ℝ) (x : M) :
    conformalEnergyDensity I u x =
      conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2 :=
  (rfl)

/-- The energy density of a constant function `c` is `Scal_g c²`. -/
@[simp]
theorem conformalEnergyDensity_const (c : ℝ) (x : M) :
    conformalEnergyDensity I (fun _ : M ↦ c) x =
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * c ^ 2 := by
  simp [conformalEnergyDensity_def]

/-- The energy density of the zero function vanishes. -/
@[simp]
theorem conformalEnergyDensity_zero (x : M) : conformalEnergyDensity I (0 : M → ℝ) x = 0 :=
  (conformalEnergyDensity_const I 0 x).trans (by simp)

/-- The energy density is even: `-u` and `u` have the same energy density. -/
@[simp]
theorem conformalEnergyDensity_neg (u : M → ℝ) (x : M) :
    conformalEnergyDensity I (-u) x = conformalEnergyDensity I u x := by
  simp [conformalEnergyDensity_def]

/-- The energy density is quadratic: scaling a differentiable function by `c` scales its energy
density by `c ^ 2`. -/
theorem conformalEnergyDensity_smul (c : ℝ) {u : M → ℝ} (hu : MDifferentiable I 𝓘(ℝ) u)
    (x : M) : conformalEnergyDensity I (c • u) x = c ^ 2 * conformalEnergyDensity I u x := by
  simp only [conformalEnergyDensity_def, mgradient_smul c hu, Pi.smul_apply, norm_smul,
    smul_eq_mul, Real.norm_eq_abs]
  rw [mul_pow, mul_pow, sq_abs]
  ring

end Density

section Energy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **The energy identity of the conformal Laplacian**, bilinear form. On a smooth Riemannian
manifold without boundary of dimension `n`, for a compactly supported `C¹` function `f` and a `C²`
function `h`, `∫ f L_g h dV = ∫ (aₙ ⟪grad f, grad h⟫ + Scal_g f h) dV`, where `L_g` is the
conformal Laplacian and `aₙ = 4 (n - 1) / (n - 2)`. -/
theorem integral_mul_conformalLaplacian {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hfc : HasCompactSupport f) (hh : ContMDiff I 𝓘(ℝ) 2 h) :
    ∫ x, f x * conformalLaplacian I h x ∂riemannianVolume I M =
      ∫ x, (conformalCoefficient (finrank ℝ E) * inner ℝ (mgradient I f x) (mgradient I h x) +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (f x * h x))
        ∂riemannianVolume I M := by
  have hS := (CovariantDerivative.leviCivitaConnection I M).continuous_scalarCurvature
  have hΔ : Integrable (fun x ↦ f x * laplaceBeltrami I h x) (riemannianVolume I M) :=
    (hf.continuous.mul (contMDiff_laplaceBeltrami (n := 0) (m := ∞) (k := ∞) (by simp) (by simp)
      (by simpa using hh)).continuous).integrable_of_hasCompactSupport
      hfc.mul_right
  have hSfh : Integrable
      (fun x ↦ (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (f x * h x))
      (riemannianVolume I M) :=
    (hS.mul (hf.continuous.mul hh.continuous)).integrable_of_hasCompactSupport
      hfc.mul_right.mul_left
  -- `⟪grad f, grad h⟫ = div (f grad h) - f Δh` is integrable since `f grad h` is a compactly
  -- supported `C¹` field.
  have hgrad : Integrable (fun x ↦ inner ℝ (mgradient I f x) (mgradient I h x))
      (riemannianVolume I M) := by
    have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
    have hX : ContMDiff I I.tangent 1 (T% (mgradient I h)) :=
      contMDiff_mgradient (n := 1) (by rwa [one_add_one_eq_two])
    have hfX : ContMDiff I I.tangent 1 (T% (fun x ↦ f x • mgradient I h x)) :=
      hf.smul_section hX
    have hdiv (x : M) : divergence I (fun x ↦ f x • mgradient I h x) x =
        f x * laplaceBeltrami I h x + inner ℝ (mgradient I f x) (mgradient I h x) := by
      rw [laplaceBeltrami_def, inner_mgradient]
      exact divergence_smul_function I f _ x ((hf x).mdifferentiableAt one_ne_zero)
        ((hX x).mdifferentiableAt one_ne_zero)
    refine ((integrable_divergence hfX (hfc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_left _ _))).sub hΔ).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply, hdiv]
    ring
  have hpt (x : M) : f x * conformalLaplacian I h x =
      -conformalCoefficient (finrank ℝ E) * (f x * laplaceBeltrami I h x) +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (f x * h x) := by
    rw [conformalLaplacian_def]
    ring
  simp_rw [hpt]
  rw [integral_add (hΔ.const_mul _) hSfh, integral_add (hgrad.const_mul _) hSfh,
    integral_const_mul, integral_const_mul, integral_mul_laplaceBeltrami hf hfc hh, neg_mul_neg]

/-- **The energy identity of the conformal Laplacian.** On a smooth Riemannian manifold without
boundary of dimension `n`, for a compactly supported `C²` function `u`,
`∫ u L_g u dV = ∫ (aₙ |grad u|² + Scal_g u²) dV`, where `L_g` is the conformal Laplacian and
`aₙ = 4 (n - 1) / (n - 2)`. The right-hand side is the numerator of the Yamabe quotient. -/
theorem integral_mul_conformalLaplacian_self {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (huc : HasCompactSupport u) :
    ∫ x, u x * conformalLaplacian I u x ∂riemannianVolume I M =
      ∫ x, conformalEnergyDensity I u x ∂riemannianVolume I M := by
  rw [integral_mul_conformalLaplacian (hu.of_le (by norm_num)) huc hu]
  simp_rw [conformalEnergyDensity_def, real_inner_self_eq_norm_sq, sq]

/-- **Formal self-adjointness of the conformal Laplacian.** On a smooth Riemannian manifold
without boundary, for a compactly supported `C²` function `f` and a `C²` function `h`,
`∫ f L_g h dV = ∫ (L_g f) h dV`, where `L_g` is the conformal Laplacian. -/
theorem integral_mul_conformalLaplacian_right_eq_left {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hfc : HasCompactSupport f) (hh : ContMDiff I 𝓘(ℝ) 2 h) :
    ∫ x, f x * conformalLaplacian I h x ∂riemannianVolume I M =
      ∫ x, conformalLaplacian I f x * h x ∂riemannianVolume I M := by
  have hS := (CovariantDerivative.leviCivitaConnection I M).continuous_scalarCurvature
  have hfΔ : Integrable (fun x ↦ f x * laplaceBeltrami I h x) (riemannianVolume I M) :=
    (hf.continuous.mul (contMDiff_laplaceBeltrami (n := 0) (m := ∞) (k := ∞) (by simp) (by simp)
      (by simpa using hh)).continuous).integrable_of_hasCompactSupport
      hfc.mul_right
  -- `Δf` vanishes off the support of `f`, so `(Δf) h` is compactly supported.
  have hΔf : Integrable (fun x ↦ laplaceBeltrami I f x * h x) (riemannianVolume I M) :=
    ((contMDiff_laplaceBeltrami (n := 0) (m := ∞) (k := ∞) (by simp) (by simp)
      (by simpa using hf)).continuous.mul hh.continuous).integrable_of_hasCompactSupport
      (hfc.mono' fun x hx ↦ by_contra fun hxf ↦
        hx (by rw [Pi.mul_apply, laplaceBeltrami_eq_zero_of_notMem_tsupport I hxf, zero_mul]))
  have hSfh : Integrable
      (fun x ↦ (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (f x * h x))
      (riemannianVolume I M) :=
    (hS.mul (hf.continuous.mul hh.continuous)).integrable_of_hasCompactSupport
      hfc.mul_right.mul_left
  have hl (x : M) : f x * conformalLaplacian I h x =
      -conformalCoefficient (finrank ℝ E) * (f x * laplaceBeltrami I h x) +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (f x * h x) := by
    rw [conformalLaplacian_def]
    ring
  have hr (x : M) : conformalLaplacian I f x * h x =
      -conformalCoefficient (finrank ℝ E) * (laplaceBeltrami I f x * h x) +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (f x * h x) := by
    rw [conformalLaplacian_def]
    ring
  simp_rw [hl, hr]
  rw [integral_add (hfΔ.const_mul _) hSfh, integral_add (hΔf.const_mul _) hSfh,
    integral_const_mul, integral_const_mul, integral_mul_laplaceBeltrami_right_eq_left hf hfc hh]

end Energy

section Rescale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]

/-- The energy identity `∫ w L_g w dV_g = ∫ (aₙ |grad w|² + Scal_g w²) dV_g`, integrated over the
metric-indexed copy carrying `g`. -/
private theorem integral_ofWithMetric_mul_conformalLaplacian_self [SigmaCompactSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {w : M → ℝ}
    (hw : ContMDiff I 𝓘(ℝ) 2 w) (hwc : HasCompactSupport w) :
    ∫ x, w x.ofWithMetric *
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          conformalLaplacian I w x.ofWithMetric) ∂riemannianVolume I (WithMetric g) =
      ∫ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          conformalEnergyDensity I w x.ofWithMetric) ∂riemannianVolume I (WithMetric g) := by
  rw [WithMetric.integral_comp_ofWithMetric g fun y ↦ w y *
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalLaplacian I w y),
    WithMetric.integral_comp_ofWithMetric g fun y ↦
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalEnergyDensity I w y)]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  exact integral_mul_conformalLaplacian_self hw hwc

/-- **Conformal invariance of the energy.** In dimension `n ≠ 2`, let `u` be a positive function
such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric. Then for every compactly supported `C²`
function `v`,
`∫ (aₙ |grad v|²_ĝ + Scal_ĝ v²) dV_ĝ = ∫ (aₙ |grad (u v)|²_g + Scal_g (u v)²) dV_g`. -/
theorem integral_conformalEnergyDensity_rescale [SigmaCompactSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (hvc : HasCompactSupport v) :
    ∫ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf
            hf_pos).toRiemannianMetric⟩;
          conformalEnergyDensity I v x.ofWithMetric)
        ∂riemannianVolume I (WithMetric (g.rescale _ hf hf_pos)) =
      ∫ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          conformalEnergyDensity I (u * v) x.ofWithMetric) ∂riemannianVolume I (WithMetric g) := by
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn)
  -- `u = (u ^ p) ^ p⁻¹` is smooth because the conformal factor `u ^ p` is.
  have hu : ContMDiff I 𝓘(ℝ) ∞ u :=
    (hf.rpow_const_of_ne (fun y ↦ (hf_pos y).ne') _).congr fun y ↦
      (Real.rpow_rpow_inv (hu_pos y).le (div_ne_zero four_ne_zero hn')).symm
  rw [← integral_ofWithMetric_mul_conformalLaplacian_self _ hv hvc,
    ← integral_ofWithMetric_mul_conformalLaplacian_self g ((hu.of_le (by simp)).mul hv)
      hvc.mul_left]
  exact integral_mul_conformalLaplacian_rescale g hn hu_pos hv

/-- **Conformal invariance of the Yamabe quotient.** In dimension `n ≠ 2`, let `u` be a positive
function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric, and let `pₙ = 2 n / (n - 2)`.
Then for every compactly supported `C²` function `v`, the Yamabe quotients
`Q(v) = (∫ (aₙ |grad v|² + Scal v²) dV) / (∫ |v| ^ pₙ dV) ^ (2 / pₙ)` of the two metrics satisfy
`Q_ĝ(v) = Q_g(u v)`. -/
theorem integral_conformalEnergyDensity_div_rescale [SigmaCompactSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (hvc : HasCompactSupport v) :
    (∫ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf
            hf_pos).toRiemannianMetric⟩;
          conformalEnergyDensity I v x.ofWithMetric)
        ∂riemannianVolume I (WithMetric (g.rescale _ hf hf_pos))) /
      (∫ x, |v x.ofWithMetric| ^ criticalExponent (finrank ℝ E)
        ∂riemannianVolume I (WithMetric (g.rescale _ hf hf_pos))) ^
          (2 / criticalExponent (finrank ℝ E)) =
    (∫ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          conformalEnergyDensity I (u * v) x.ofWithMetric) ∂riemannianVolume I (WithMetric g)) /
      (∫ x, |(u * v) x.ofWithMetric| ^ criticalExponent (finrank ℝ E)
        ∂riemannianVolume I (WithMetric g)) ^ (2 / criticalExponent (finrank ℝ E)) := by
  rw [integral_conformalEnergyDensity_rescale g hn hu_pos hv hvc, criticalExponent_def,
    WithMetric.integral_abs_rpow_rescale_rpow (fun x ↦ (hu_pos x).le) v]
  simp only [Pi.mul_apply]

/-- **Total scalar curvature as energy.** On a compact manifold of dimension `n ≠ 2`, let `u` be a
positive function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric. Then
`∫ Scal_ĝ dV_ĝ = ∫ (aₙ |grad u|²_g + Scal_g u²) dV_g`. With
`Vol(ĝ) = ∫ u ^ pₙ dV_g` (`TauCeti.WithMetric.riemannianTotalVolume_rescale_rpow`), this identifies
the volume-normalized total scalar curvature of `ĝ` with the Yamabe quotient `Q_g(u)`. -/
theorem integral_scalarCurvature_rescale_eq_integral_conformalEnergyDensity [CompactSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} :
    ∫ x, (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf hf_pos).scalarCurvature
        x.ofWithMetric ∂riemannianVolume I (WithMetric (g.rescale _ hf hf_pos)) =
      ∫ x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          conformalEnergyDensity I u x.ofWithMetric) ∂riemannianVolume I (WithMetric g) := by
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn)
  -- `u = (u ^ p) ^ p⁻¹` is smooth because the conformal factor `u ^ p` is.
  have hu : ContMDiff I 𝓘(ℝ) ∞ u :=
    (hf.rpow_const_of_ne (fun y ↦ (hf_pos y).ne') _).congr fun y ↦
      (Real.rpow_rpow_inv (hu_pos y).le (div_ne_zero four_ne_zero hn')).symm
  rw [integral_scalarCurvature_rescale g hn hu_pos,
    integral_ofWithMetric_mul_conformalLaplacian_self g (hu.of_le (by simp))
      (HasCompactSupport.of_compactSpace u)]

end Rescale

end TauCeti.Yamabe
