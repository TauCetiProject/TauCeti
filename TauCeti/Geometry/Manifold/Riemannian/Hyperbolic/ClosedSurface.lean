/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.CurvatureEquation
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.Volume
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.LiouvilleEnergy.Sobolev
import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Regularity
import TauCeti.Geometry.Manifold.Riemannian.TotalCurvature
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar

/-!
# Hyperbolic metrics in a conformal class of a closed surface

Let `g` be a smooth Riemannian metric on a closed connected surface `M`. A hyperbolic metric
conformal to `g` is a `TauCeti.HyperbolicMetric` whose metric is `f g` for a smooth positive
function `f`. This file identifies these hyperbolic metrics with the smooth solutions of the
curvature equation

`Δ⁺φ + K + e^(2φ) = 0`,

where `Δ⁺ = -div grad` is the nonnegative Laplacian of `g` and `K = Scal^g / 2` its Gaussian
curvature, the hyperbolic metric being `e^(2φ) g`. The only property of a hyperbolic metric
beyond its curvature, completeness, holds automatically on a closed surface, since the Riemannian
distance of a compact manifold is complete (`TauCeti.HyperbolicMetric.ofCompactSpace`). Finite
volume then follows separately (`TauCeti.HyperbolicMetric.hasFiniteVolume_of_compactSpace`).
So the existence of a hyperbolic metric in the conformal class of `g` is equivalent to the
solvability of the curvature equation, and by the maximum principle there is at most one such
metric.

When the total curvature `∫ K dV_g` is negative, the Liouville energy attains a minimum in
`H¹(M)` (`TauCeti.Manifold.SobolevH1.exists_forall_dirichletForm_eq_integral_neg_add_exp_mul`),
giving a weak solution of the curvature equation whose exponential nonlinearity is square
integrable by the Trudinger inequality (`TauCeti.Manifold.SobolevH1.memLp_exp_mul`). Semilinear
elliptic regularity
(`TauCeti.Manifold.SobolevH1.exists_ofSmooth_eq_and_neg_laplaceBeltrami_eq_mul_comp_add`)
bootstraps this weak solution to a smooth classical solution, yielding the existence and uniqueness
of a hyperbolic metric in the conformal class of `g` precisely when `∫ Scal^g dV_g < 0`. Since
total curvature is a conformal invariant of a closed surface, the area of this metric is
`-∫ K dV_g`.

## Main results

* `TauCeti.Manifold.existsUnique_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero`: on a closed
  connected smooth Riemannian surface, for every smooth function `K` with `∫ K dV < 0`, the
  curvature equation `Δ⁺φ + K + e^(2φ) = 0` has a unique smooth solution.
* `Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_metric_eq_rescale_iff`: a closed
  surface carries a hyperbolic metric conformal to `g` exactly when the curvature equation has a
  smooth solution.
* `TauCeti.HyperbolicMetric.eq_of_metric_eq_rescale`: two hyperbolic metrics conformal to `g`
  are equal.
* `Bundle.ContMDiffRiemannianMetric.existsUnique_hyperbolicMetric_metric_eq_rescale`: a closed
  connected surface with `∫ Scal^g dV_g < 0` carries a unique hyperbolic metric conformal to `g`.
* `Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_iff_integral_scalarCurvature_neg`:
  a nonempty closed connected surface carries a hyperbolic metric conformal to `g` if and only if
  `∫ Scal^g dV_g < 0`.
* `TauCeti.HyperbolicMetric.hypVolumeOfMetric_eq_of_metric_eq_rescale`: a hyperbolic metric
  conformal to `g` has area `-∫ K dV_g`.

## References

* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47.
* M. S. Berger, *Riemannian structures of prescribed Gaussian curvature for compact
  2-manifolds*, J. Differential Geom. 5 (1971), 325–332.
-/

public section

open Bundle Module TauCeti TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

section CurvatureEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Smooth solvability of the hyperbolic curvature equation on a closed surface.** On a closed
connected smooth Riemannian surface, for every smooth function `K` with `∫ K dV < 0`, the
curvature equation `Δ⁺φ + K + e^(2φ) = 0` has a unique smooth solution `φ`, where
`Δ⁺ = -div grad` is the nonnegative Laplacian. -/
theorem existsUnique_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero
    (hE : finrank ℝ E = 2) {K : M → ℝ} (hK : ContMDiff I 𝓘(ℝ) ∞ K)
    (hK_neg : ∫ x, K x ∂riemannianVolume I M < 0) :
    ∃! φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧
      ∀ x, -laplaceBeltrami I φ x + K x + Real.exp (2 * φ x) = 0 := by
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let KLp : MeasureTheory.Lp ℝ 2 (riemannianVolume I M) :=
    ContinuousMap.toLp 2 (riemannianVolume I M) ℝ ⟨K, hK.continuous⟩
  have hK_ae : (KLp : M → ℝ) =ᵐ[riemannianVolume I M] K :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (riemannianVolume I M) ⟨K, hK.continuous⟩
  have hKLp_neg : ∫ x, KLp x ∂riemannianVolume I M < 0 :=
    (MeasureTheory.integral_congr_ae hK_ae).symm ▸ hK_neg
  obtain ⟨w, hw⟩ :=
    SobolevH1.exists_forall_dirichletForm_eq_integral_neg_add_exp_mul hE KLp hKLp_neg
  have hF_lp : MeasureTheory.MemLp
      (fun x ↦ (-1 : ℝ) * Real.exp (2 * SobolevH1.toLp w x) + (-K x)) 2
      (riemannianVolume I M) := by
    have hexp : MeasureTheory.MemLp (fun x ↦ Real.exp (2 * SobolevH1.toLp w x)) 2
        (riemannianVolume I M) :=
      SobolevH1.memLp_exp_mul hE w 2 ENNReal.ofNat_ne_top
    have hK_lp : MeasureTheory.MemLp K 2 (riemannianVolume I M) :=
      MeasureTheory.MemLp.ae_eq hK_ae (MeasureTheory.Lp.memLp KLp)
    exact (hexp.const_mul (-1)).add hK_lp.neg
  have hΦ : ContDiff ℝ ∞ fun t : ℝ ↦ Real.exp (2 * t) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  obtain ⟨u, -, hu⟩ :=
    SobolevH1.exists_ofSmooth_eq_and_neg_laplaceBeltrami_eq_mul_comp_add (by omega)
      (A := fun _ ↦ (-1 : ℝ)) (C := fun x ↦ -K x) contMDiff_const hK.neg hΦ hF_lp fun v ↦ by
      rw [hw (SobolevH1.ofSmooth v)]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hK_ae, SobolevH1.toLp_ofSmooth_ae_eq v] with x hKx hvx
      rw [hKx, hvx]
      ring
  have hmono (x : M) : StrictMono fun t : ℝ ↦ K x + Real.exp (2 * t) :=
    fun _ _ hst ↦ by dsimp only; gcongr
  refine ⟨u, ⟨u.contMDiff, fun x ↦ by linarith [hu x]⟩, fun φ' ⟨hφ', hφ'_eq⟩ ↦ ?_⟩
  funext x
  exact le_antisymm
    (le_of_le_laplaceBeltrami_of_laplaceBeltrami_le hmono
      (hφ'.of_le (by simp)) (u.contMDiff.of_le (by simp))
      (fun y ↦ by linarith [hφ'_eq y]) (fun y ↦ by linarith [hu y]) x)
    (le_of_le_laplaceBeltrami_of_laplaceBeltrami_le hmono
      (u.contMDiff.of_le (by simp)) (hφ'.of_le (by simp))
      (fun y ↦ by linarith [hu y]) (fun y ↦ by linarith [hφ'_eq y]) x)

end CurvatureEquation

end TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

namespace Bundle.ContMDiffRiemannianMetric

variable (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- **Hyperbolic metrics in a conformal class and the curvature equation.** A closed surface
carries a hyperbolic metric conformal to `g`, that is of the form `f g` for a smooth positive
function `f`, exactly when the curvature equation `Δ⁺φ + K + e^(2φ) = 0` has a smooth solution
`φ`; here `Δ⁺ = -div grad` is the nonnegative Laplacian of `g` and `K = Scal^g / 2` its Gaussian
curvature. The hyperbolic metric is then `e^(2φ) g`. -/
theorem exists_hyperbolicMetric_metric_eq_rescale_iff (hE : finrank ℝ E = 2) :
    (∃ (G : HyperbolicMetric (I := I) (M := M)) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
        (hf_pos : ∀ x, 0 < f x), G.metric = g.rescale f hf hf_pos) ↔
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧
        ∀ x, -laplaceBeltrami I φ x + g.scalarCurvature x / 2 + Real.exp (2 * φ x) = 0 := by
  constructor
  · -- The exponent of the conformal factor `f = e^(2φ)` is `φ = log f / 2`.
    rintro ⟨G, f, hf, hf_pos, hG⟩
    have hfφ (x : M) : f x = Real.exp (2 * (Real.log (f x) / 2)) := by
      rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log (hf_pos x)]
    refine ⟨fun x ↦ Real.log (f x) / 2, (hf.log fun x ↦ (hf_pos x).ne').div_const 2, ?_⟩
    exact (g.isConstantCurvatureTensor_rescale_iff_of_finrank_eq_two hE hf hf_pos hfφ).1
      (hG ▸ G.curvature)
  · -- The metric `e^(2φ) g` has curvature `-1`, and completeness is automatic on a closed surface.
    rintro ⟨φ, hφ, h⟩
    have hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ Real.exp (2 * φ x) :=
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contMDiff.comp hφ
    have hf_pos (x : M) : 0 < Real.exp (2 * φ x) := Real.exp_pos _
    exact ⟨HyperbolicMetric.ofCompactSpace
      ((g.isConstantCurvatureTensor_rescale_iff_of_finrank_eq_two hE hf hf_pos
        fun _ ↦ rfl).2 h), _, hf, hf_pos, HyperbolicMetric.metric_ofCompactSpace _⟩

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.HyperbolicMetric

/-- **Uniqueness of the hyperbolic metric in a conformal class.** On a closed surface two
hyperbolic metrics conformal to the same metric `g` are equal. -/
theorem eq_of_metric_eq_rescale [I.Boundaryless] (hE : finrank ℝ E = 2)
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (G₁ G₂ : HyperbolicMetric (I := I) (M := M)) {f₁ f₂ : M → ℝ}
    {hf₁ : ContMDiff I 𝓘(ℝ) ∞ f₁} {hf₁_pos : ∀ x, 0 < f₁ x}
    {hf₂ : ContMDiff I 𝓘(ℝ) ∞ f₂} {hf₂_pos : ∀ x, 0 < f₂ x}
    (h₁ : G₁.metric = g.rescale f₁ hf₁ hf₁_pos) (h₂ : G₂.metric = g.rescale f₂ hf₂ hf₂_pos) :
    G₁ = G₂ := by
  -- Both conformal metrics have scalar curvature `-2`, so the maximum principle identifies the
  -- conformal factors.
  obtain rfl := g.eq_of_scalarCurvature_rescale_eq hE hf₁ hf₁_pos hf₂ hf₂_pos (by norm_num)
    (h₁ ▸ G₁.scalarCurvature_metric_of_finrank_eq_two hE)
    (h₂ ▸ G₂.scalarCurvature_metric_of_finrank_eq_two hE)
  exact HyperbolicMetric.ext (h₁.trans h₂.symm)

/-- **Area of the hyperbolic metric in a conformal class.** On a closed surface, a hyperbolic
metric conformal to `g` has area `-∫ K dV_g`, where `K = Scal^g / 2` is the Gaussian curvature of
`g`. -/
theorem hypVolumeOfMetric_eq_of_metric_eq_rescale [I.Boundaryless] [MeasurableSpace M]
    [BorelSpace M] (hE : finrank ℝ E = 2)
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (G : HyperbolicMetric (I := I) (M := M)) {f : M → ℝ} {hf : ContMDiff I 𝓘(ℝ) ∞ f}
    {hf_pos : ∀ x, 0 < f x} (h : G.metric = g.rescale f hf hf_pos) :
    hypVolumeOfMetric G =
      -(∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g)) / 2 := by
  -- The volume of `G` is that of the metric-indexed copy `WithMetric G.metric`.
  have hvol : hypVolumeOfMetric G = riemannianTotalVolume I (WithMetric G.metric) := by
    have h1 := WithMetric.integral_comp_ofWithMetric G.metric fun _ ↦ (1 : ℝ)
    simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one] at h1
    simp only [hypVolumeOfMetric_def, riemannianTotalVolume_def]
    exact h1.symm
  rw [hvol, h, ← g.mul_riemannianTotalVolume_rescale_of_finrank_eq_two hE hf hf_pos
    (h ▸ G.scalarCurvature_metric_of_finrank_eq_two hE)]
  ring

end TauCeti.HyperbolicMetric

namespace Bundle.ContMDiffRiemannianMetric

variable (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- **Existence and uniqueness of the hyperbolic metric in a conformal class.** On a closed
connected smooth surface with negative total scalar curvature `∫ Scal^g dV_g < 0`, there is a
unique hyperbolic metric conformal to `g`. -/
theorem existsUnique_hyperbolicMetric_metric_eq_rescale [I.Boundaryless] (hE : finrank ℝ E = 2)
    (hK : ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0) :
    ∃! G : HyperbolicMetric (I := I) (M := M),
      ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x),
        G.metric = g.rescale f hf hf_pos := by
  borelize M
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    instIsContMDiffRiemannianBundle g
  have hK' : ∫ x, g.scalarCurvature x / 2 ∂riemannianVolume I M < 0 := by
    rw [MeasureTheory.integral_div, ← WithMetric.integral_comp_ofWithMetric g g.scalarCurvature]
    linarith
  obtain ⟨φ, hφ, hφ_eq⟩ :=
    (existsUnique_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero hE
      (g.contMDiff_scalarCurvature.div_const 2) hK').exists
  obtain ⟨G, f, hf, hf_pos, hG⟩ :=
    (g.exists_hyperbolicMetric_metric_eq_rescale_iff hE).2 ⟨φ, hφ, hφ_eq⟩
  exact ⟨G, ⟨f, hf, hf_pos, hG⟩, fun G' ⟨f', hf', hf'_pos, hG'⟩ ↦
    HyperbolicMetric.eq_of_metric_eq_rescale hE G' G hG' hG⟩

/-- **Characterization of conformal classes admitting a hyperbolic metric.** A nonempty closed
connected smooth surface carries a hyperbolic metric conformal to `g` if and only if its total
scalar curvature `∫ Scal^g dV_g` is negative. -/
theorem exists_hyperbolicMetric_iff_integral_scalarCurvature_neg
    [I.Boundaryless] [Nonempty M] (hE : finrank ℝ E = 2) :
    (∃ (G : HyperbolicMetric (I := I) (M := M)) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
        (hf_pos : ∀ x, 0 < f x), G.metric = g.rescale f hf hf_pos) ↔
      ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0 := by
  refine ⟨fun ⟨G, f, hf, hf_pos, hG⟩ ↦ ?_, fun hK ↦ ?_⟩
  · exact g.integral_scalarCurvature_neg_of_scalarCurvature_rescale_eq hE hf hf_pos
      (by norm_num) (hG ▸ G.scalarCurvature_metric_of_finrank_eq_two hE)
  · obtain ⟨G, hG⟩ := (g.existsUnique_hyperbolicMetric_metric_eq_rescale hE hK).exists
    exact ⟨G, hG⟩

end Bundle.ContMDiffRiemannianMetric
