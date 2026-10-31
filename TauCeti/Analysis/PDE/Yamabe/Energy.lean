/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.TotalScalarCurvature
public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric

/-!
# The energy of the conformal Laplacian

On a Riemannian manifold `(M, g)` without boundary of dimension `n`, Green's first identity
`∫ f Δu dV = -∫ ⟪grad f, grad u⟫ dV` turns the conformal Laplacian
`L_g u = aₙ Δ⁺_g u + Scal_g u`, with `aₙ = 4 (n - 1) / (n - 2)` and `Δ⁺ = -Δ`, into its energy
form:

`∫ f L_g u dV_g = ∫ (aₙ ⟪grad f, grad u⟫ + Scal_g f u) dV_g`

for a compactly supported `C¹` function `f` and a `C²` function `u`. The right-hand side is
symmetric in `f` and `u`, so `L_g` is formally self-adjoint, and for `f = u` it is the energy

`∫ u L_g u dV_g = ∫ (aₙ |grad u|² + Scal_g u²) dV_g`,

the numerator of the Yamabe quotient `Q_g(u)`. On a closed manifold every function has compact
support, so these identities hold for all `C²` functions.

Combined with the conformal covariance `L_ĝ v = u ^ (-(n + 2) / (n - 2)) L_g (u v)` of the
conformal Laplacian, whose integrated form is
`TauCeti.Yamabe.integral_mul_conformalLaplacian_rescale`, the energy identity shows that the
energy is conformally invariant: for `ĝ = u ^ (4 / (n - 2)) g` with `u` positive and every
compactly supported `C²` function `v`,

`∫ (aₙ |grad_ĝ v|² + Scal_ĝ v²) dV_ĝ = ∫ (aₙ |grad_g (u v)|² + Scal_g (u v)²) dV_g`.

Together with the invariance `∫ |v| ^ pₙ dV_ĝ = ∫ |u v| ^ pₙ dV_g` of the denominator
(`TauCeti.WithMetric.integral_abs_rpow_rescale_rpow`), this is the invariance
`Q_ĝ(v) = Q_g(u v)` of the Yamabe quotient on compactly supported `C²` functions.

As in `TauCeti.Yamabe.integral_mul_conformalLaplacian_rescale`, the conformal invariance compares
the volumes of the metric-indexed copies `TauCeti.WithMetric g` and `TauCeti.WithMetric ĝ` of `M`,
while the gradient and scalar curvature of each metric are taken with that metric installed as the
`RiemannianBundle` instance of `M`. The volume of a copy is transported to `M` by
`TauCeti.WithMetric.integral_comp_ofWithMetric`.

## Main results

* `TauCeti.Yamabe.integral_mul_conformalLaplacian`:
  `∫ f L_g u dV = ∫ (aₙ ⟪grad f, grad u⟫ + Scal_g f u) dV`.
* `TauCeti.Yamabe.integral_mul_conformalLaplacian_right_eq_left`: the formal self-adjointness
  `∫ f L_g u dV = ∫ (L_g f) u dV`.
* `TauCeti.Yamabe.integral_mul_conformalLaplacian_self`: the energy identity
  `∫ u L_g u dV = ∫ (aₙ |grad u|² + Scal_g u²) dV`.
* `TauCeti.Yamabe.integral_energy_rescale`: the conformal invariance of the energy.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2 (the
  energy form of the Yamabe functional and its conformal invariance).
-/

public section

open Bundle MeasureTheory Module TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Yamabe

section Energy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- `Scal_g f u` is integrable for a compactly supported continuous `f` and a continuous `u`. -/
private theorem integrable_scalarCurvature_mul {f u : M → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hu : Continuous u) :
    Integrable (fun x ↦ (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x *
      (f x * u x)) (riemannianVolume I M) :=
  ((CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous.mul
    (hf.mul hu)).integrable_of_hasCompactSupport hfc.mul_right.mul_left

/-- Splitting `∫ f L_g u dV` into its zeroth-order and Laplacian parts:
`∫ f L_g u dV = ∫ Scal_g f u dV - aₙ ∫ f Δu dV`. -/
private theorem integral_mul_conformalLaplacian_eq_sub {f u : M → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hu : ContMDiff I 𝓘(ℝ) 2 u) :
    ∫ x, f x * conformalLaplacian I u x ∂riemannianVolume I M =
      ∫ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (f x * u x)
        ∂riemannianVolume I M -
      conformalCoefficient (finrank ℝ E) *
        ∫ x, f x * laplaceBeltrami I u x ∂riemannianVolume I M := by
  have hΔ : Integrable (fun x ↦ f x * laplaceBeltrami I u x) (riemannianVolume I M) :=
    (hf.mul (contMDiff_laplaceBeltrami (n := 0) (m := 2) (k := 1) (by norm_num)
      (by norm_num) (by simpa using hu)).continuous).integrable_of_hasCompactSupport hfc.mul_right
  rw [← integral_const_mul, ← integral_sub (integrable_scalarCurvature_mul hf hfc hu.continuous)
    (hΔ.const_mul _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [conformalLaplacian_def]
  ring

variable [I.Boundaryless]

/-- **Integration by parts for the conformal Laplacian** on a manifold without boundary: for a
compactly supported `C¹` function `f` and a `C²` function `u`,
`∫ f L_g u dV = ∫ (aₙ ⟪grad f, grad u⟫ + Scal_g f u) dV`, where `L_g` is the conformal Laplacian
and `aₙ = 4 (n - 1) / (n - 2)`. -/
theorem integral_mul_conformalLaplacian {f u : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hfc : HasCompactSupport f) (hu : ContMDiff I 𝓘(ℝ) 2 u) :
    ∫ x, f x * conformalLaplacian I u x ∂riemannianVolume I M =
      ∫ x, (conformalCoefficient (finrank ℝ E) * inner ℝ (mgradient I f x) (mgradient I u x) +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (f x * u x))
        ∂riemannianVolume I M := by
  have : IsManifold I (0 + 1) M := by rw [zero_add]; infer_instance
  -- `⟪grad f, grad u⟫ = df(grad u)` is continuous and vanishes off the support of `f`.
  have hgrad : Integrable (fun x ↦ inner ℝ (mgradient I f x) (mgradient I u x))
      (riemannianVolume I M) := by
    -- The bundle argument of `ContMDiff.inner_bundle` is not inferred through `TangentSpace`.
    have hcont : CMDiff 0 fun x ↦ inner ℝ (mgradient I f x) (mgradient I u x) :=
      ContMDiff.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id)
        (contMDiff_mgradient (n := 0) (by rwa [zero_add]))
        (contMDiff_mgradient (n := 0) (by simpa using hu.of_le one_le_two))
    refine hcont.continuous.integrable_of_hasCompactSupport
      (hfc.mono' fun x hx ↦ by_contra fun h ↦ hx ?_)
    dsimp only
    rw [inner_mgradient, (notMem_tsupport_iff_eventuallyEq.1 h).mvfderiv_eq, mvfderiv_zero,
      zero_apply]
  rw [integral_mul_conformalLaplacian_eq_sub hf.continuous hfc hu,
    integral_add (hgrad.const_mul _) (integrable_scalarCurvature_mul hf.continuous hfc
      hu.continuous), integral_const_mul, integral_mul_laplaceBeltrami hf hfc hu]
  ring

/-- **The conformal Laplacian is formally self-adjoint** on a manifold without boundary: for a
compactly supported `C²` function `f` and a `C²` function `u`, `∫ f L_g u dV = ∫ (L_g f) u dV`. -/
theorem integral_mul_conformalLaplacian_right_eq_left {f u : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hfc : HasCompactSupport f) (hu : ContMDiff I 𝓘(ℝ) 2 u) :
    ∫ x, f x * conformalLaplacian I u x ∂riemannianVolume I M =
      ∫ x, conformalLaplacian I f x * u x ∂riemannianVolume I M := by
  -- `Δf = div (grad f)` vanishes off the support of `f`, since `grad f` does.
  have hgradc : HasCompactSupport (β := E) (mgradient I f) :=
    hfc.mono' fun x hx ↦ by_contra fun h ↦ hx <| mgradient_eq_zero_iff.2 <|
      (notMem_tsupport_iff_eventuallyEq.1 h).mvfderiv_eq.trans mvfderiv_zero
  have hΔfc : HasCompactSupport (laplaceBeltrami I f) :=
    hgradc.mono' fun x hx ↦ by_contra fun h ↦ hx <| by
      rw [laplaceBeltrami_def]
      exact divergence_eq_zero_of_notMem_tsupport I h
  have hΔf : Integrable (fun x ↦ laplaceBeltrami I f x * u x) (riemannianVolume I M) :=
    ((contMDiff_laplaceBeltrami (n := 0) (m := 2) (k := 1) (by norm_num) (by norm_num)
      (by simpa using hf)).continuous.mul hu.continuous).integrable_of_hasCompactSupport
      hΔfc.mul_right
  have hpt (x : M) : conformalLaplacian I f x * u x =
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (f x * u x) -
        conformalCoefficient (finrank ℝ E) * (laplaceBeltrami I f x * u x) := by
    rw [conformalLaplacian_def]
    ring
  rw [integral_mul_conformalLaplacian_eq_sub hf.continuous hfc hu,
    integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub (integrable_scalarCurvature_mul hf.continuous hfc hu.continuous)
      (hΔf.const_mul _), integral_const_mul, integral_mul_laplaceBeltrami_right_eq_left hf hfc hu]

/-- **The energy identity for the conformal Laplacian** on a manifold without boundary: for a
compactly supported `C²` function `u`, `∫ u L_g u dV = ∫ (aₙ |grad u|² + Scal_g u²) dV`. -/
theorem integral_mul_conformalLaplacian_self {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (huc : HasCompactSupport u) :
    ∫ x, u x * conformalLaplacian I u x ∂riemannianVolume I M =
      ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
        ∂riemannianVolume I M := by
  simp only [integral_mul_conformalLaplacian (hu.of_le one_le_two) huc hu,
    real_inner_self_eq_norm_sq, sq]

end Energy

section Rescale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M]

/-- The energy identity for a smooth metric `g`, integrated against the volume of the
metric-indexed copy `WithMetric g`. -/
private theorem integral_energy_withMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {w : M → ℝ}
    (hw : ContMDiff I 𝓘(ℝ) 2 w) (hwc : HasCompactSupport w) :
    ∫ x, ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalCoefficient (finrank ℝ E) * ‖mgradient I w x.ofWithMetric‖ ^ 2) +
        g.scalarCurvature x.ofWithMetric * w x.ofWithMetric ^ 2)
        ∂riemannianVolume I (WithMetric g) =
      ∫ x, w x.ofWithMetric *
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          conformalLaplacian I w x.ofWithMetric) ∂riemannianVolume I (WithMetric g) := by
  borelize M
  rw [WithMetric.integral_comp_ofWithMetric g fun y ↦
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalCoefficient (finrank ℝ E) * ‖mgradient I w y‖ ^ 2) +
        g.scalarCurvature y * w y ^ 2,
    WithMetric.integral_comp_ofWithMetric g fun y ↦ w y *
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalLaplacian I w y)]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  rw [integral_mul_conformalLaplacian_self hw hwc]
  simp only [g.scalarCurvature_def]

/-- **Conformal invariance of the Yamabe energy.** In dimension `n ≠ 2`, let `u` be a positive
function such that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric on a manifold without boundary.
Then for every compactly supported `C²` function `v`,
`∫ (aₙ |grad_ĝ v|² + Scal_ĝ v²) dV_ĝ = ∫ (aₙ |grad_g (u v)|² + Scal_g (u v)²) dV_g`,
where `aₙ = 4 (n - 1) / (n - 2)`. -/
theorem integral_energy_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : finrank ℝ E ≠ 2) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} {v : M → ℝ}
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (hvc : HasCompactSupport v) :
    ∫ x, ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf
            hf_pos).toRiemannianMetric⟩;
        conformalCoefficient (finrank ℝ E) * ‖mgradient I v x.ofWithMetric‖ ^ 2) +
        (g.rescale _ hf hf_pos).scalarCurvature x.ofWithMetric * v x.ofWithMetric ^ 2)
        ∂riemannianVolume I (WithMetric (g.rescale _ hf hf_pos)) =
      ∫ x, ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalCoefficient (finrank ℝ E) * ‖mgradient I (u * v) x.ofWithMetric‖ ^ 2) +
        g.scalarCurvature x.ofWithMetric * (u * v) x.ofWithMetric ^ 2)
        ∂riemannianVolume I (WithMetric g) := by
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn)
  -- `u = (u ^ p) ^ p⁻¹` is smooth because the conformal factor `u ^ p` is.
  have hu : ContMDiff I 𝓘(ℝ) 2 u :=
    ((hf.rpow_const_of_ne (fun y ↦ (hf_pos y).ne') _).congr fun y ↦
      (Real.rpow_rpow_inv (hu_pos y).le (div_ne_zero four_ne_zero hn')).symm).of_le (by simp)
  rw [integral_energy_withMetric _ hv hvc, integral_energy_withMetric g (hu.mul hv) hvc.mul_left]
  exact integral_mul_conformalLaplacian_rescale g hn hu_pos hv

end Rescale

end TauCeti.Yamabe
