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
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Semilinear
import TauCeti.Geometry.Manifold.Riemannian.TotalCurvature
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization

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
metric. Since total curvature is a conformal invariant of a closed surface, the area of this
metric is `-∫ K dV_g`.

When `∫ K dV_g < 0`, minimizing the Liouville energy on `H¹(M)` produces a weak solution of
`Δ⁺w + K + e^(2w) = 0`
(`TauCeti.Manifold.SobolevH1.exists_forall_dirichletForm_eq_integral_neg_add_exp_mul`),
whose forcing `-e^(2w) - K` is square integrable by the Moser–Trudinger exponential integrability
of `H¹` on surfaces. Semilinear elliptic regularity on closed manifolds of dimension `< 4`
(`TauCeti.Manifold.SobolevH1.exists_contMDiff_of_forall_dirichletForm_eq`) upgrades this weak
solution to a smooth classical solution `φ`
(`TauCeti.Manifold.exists_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero`). Consequently, every
conformal class on a closed connected surface with negative total curvature contains a unique
hyperbolic metric.

## Main results

* `Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_metric_eq_rescale_iff`: a closed
  surface carries a hyperbolic metric conformal to `g` exactly when the curvature equation has a
  smooth solution.
* `TauCeti.HyperbolicMetric.eq_of_metric_eq_rescale`: two hyperbolic metrics conformal to `g`
  are equal.
* `TauCeti.HyperbolicMetric.hypVolumeOfMetric_eq_of_metric_eq_rescale`: a hyperbolic metric
  conformal to `g` has area `-∫ K dV_g`.
* `TauCeti.Manifold.exists_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero`: on a closed
  connected Riemannian surface, `Δ⁺φ + K + e^(2φ) = 0` admits a smooth solution for every smooth
  `K` with `∫ K dV < 0`.
* `Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_metric_eq_rescale` and
  `Bundle.ContMDiffRiemannianMetric.existsUnique_hyperbolicMetric_metric_eq_rescale`: existence
  and uniqueness of the hyperbolic metric conformal to `g` when `∫ Scal^g dV_g < 0`.
* `exists_hyperbolicMetric_metric_eq_rescale_iff_integral_scalarCurvature_neg` (in
  `Bundle.ContMDiffRiemannianMetric`): a nonempty closed connected surface carries a hyperbolic
  metric conformal to `g` if and only if `∫ Scal^g dV_g < 0`.
* `TauCeti.isHyperbolic_iff_exists_integral_scalarCurvature_neg`: a nonempty closed connected
  surface is hyperbolic if and only if it admits a smooth Riemannian metric of negative total
  scalar curvature.

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

section CurvatureEquationExistence

namespace TauCeti.Manifold

/-- **Smooth solvability of the curvature equation.** On a closed connected smooth Riemannian
surface, if `K : M → ℝ` is smooth and has negative integral `∫ K dV < 0`, then there exists a
smooth function `φ : M → ℝ` solving `Δ⁺φ + K + e^(2φ) = 0` everywhere, where `Δ⁺ = -div grad` is
the nonnegative Laplacian. -/
theorem exists_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M] [CompactSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hE : finrank ℝ E = 2) {K : M → ℝ} (hK : ContMDiff I 𝓘(ℝ) ∞ K)
    (hKint : ∫ x, K x ∂riemannianVolume I M < 0) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧
      ∀ x, -laplaceBeltrami I φ x + K x + Real.exp (2 * φ x) = 0 := by
  let KLp : MeasureTheory.Lp ℝ 2 (riemannianVolume I M) :=
    SobolevH1.toLp (SobolevH1.ofSmooth (⟨K, hK⟩ : C^∞⟮I, M; ℝ⟯))
  have hK_ae : (KLp : M → ℝ) =ᵐ[riemannianVolume I M] K :=
    SobolevH1.toLp_ofSmooth_ae_eq ⟨K, hK⟩
  have hKLp_int : ∫ x, KLp x ∂riemannianVolume I M < 0 := by
    rwa [MeasureTheory.integral_congr_ae hK_ae]
  obtain ⟨w, hw⟩ :=
    SobolevH1.exists_forall_dirichletForm_eq_integral_neg_add_exp_mul hE KLp hKLp_int
  have hE' : finrank ℝ E < 4 := by omega
  have hΦ : ContDiff ℝ ∞ (fun t : ℝ ↦ Real.exp (2 * t)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hf : MeasureTheory.MemLp
      (fun x ↦ (-1 : ℝ) * Real.exp (2 * SobolevH1.toLp w x) + -K x) 2 (riemannianVolume I M) :=
    ((SobolevH1.memLp_exp_mul hE w 2 (p := 2) ENNReal.ofNat_ne_top).const_mul (-1)).add
      ((MeasureTheory.Lp.memLp KLp).ae_eq hK_ae).neg
  obtain ⟨φ, hφ, -, hEq⟩ := SobolevH1.exists_contMDiff_of_forall_dirichletForm_eq hE'
      (A := fun _ ↦ (-1 : ℝ)) (C := fun x ↦ -K x) contMDiff_const hK.neg hΦ hf fun ψ ↦ by
    rw [hw (SobolevH1.ofSmooth ψ)]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hK_ae, SobolevH1.toLp_ofSmooth_ae_eq ψ] with x hxK hxψ
    rw [hxK, hxψ]
    ring
  exact ⟨φ, hφ, fun x ↦ by linarith [hEq x]⟩

end TauCeti.Manifold

end CurvatureEquationExistence

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

/-- **Existence of a hyperbolic metric in a conformal class.** Let `g` be a smooth Riemannian
metric on a closed connected surface `M` with negative total scalar curvature `∫ Scal^g dV_g < 0`.
Then there exists a hyperbolic metric `G` on `M` conformal to `g`, that is `G.metric = f g` for a
smooth positive function `f`. -/
theorem exists_hyperbolicMetric_metric_eq_rescale [I.Boundaryless] (hE : finrank ℝ E = 2)
    (hK : ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0) :
    ∃ (G : HyperbolicMetric (I := I) (M := M)) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
      (hf_pos : ∀ x, 0 < f x), G.metric = g.rescale f hf hf_pos := by
  rw [g.exists_hyperbolicMetric_metric_eq_rescale_iff hE]
  borelize M
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    instIsContMDiffRiemannianBundle g
  have hKint : ∫ x, g.scalarCurvature x / 2 ∂riemannianVolume I M < 0 := by
    rw [MeasureTheory.integral_div, ← WithMetric.integral_comp_ofWithMetric g g.scalarCurvature]
    linarith
  exact exists_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero hE
    (g.contMDiff_scalarCurvature.div_const 2) hKint

/-- **Existence and uniqueness of the hyperbolic metric in a conformal class.** Let `g` be a smooth
Riemannian metric on a closed connected surface `M` with negative total scalar curvature
`∫ Scal^g dV_g < 0`. Then there exists a unique hyperbolic metric `G` on `M` conformal to `g`. -/
theorem existsUnique_hyperbolicMetric_metric_eq_rescale [I.Boundaryless] (hE : finrank ℝ E = 2)
    (hK : ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0) :
    ∃! G : HyperbolicMetric (I := I) (M := M),
      ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x),
        G.metric = g.rescale f hf hf_pos := by
  obtain ⟨G, f, hf, hf_pos, hG⟩ := g.exists_hyperbolicMetric_metric_eq_rescale hE hK
  exact ⟨G, ⟨f, hf, hf_pos, hG⟩, fun G' ⟨_, _, _, hG'⟩ ↦
    HyperbolicMetric.eq_of_metric_eq_rescale hE G' G hG' hG⟩

/-- **Total-curvature characterization of conformal hyperbolic metrics.** A nonempty closed
connected surface `M` with smooth Riemannian metric `g` carries a hyperbolic metric conformal to
`g` if and only if its total scalar curvature `∫ Scal^g dV_g` is negative. -/
theorem exists_hyperbolicMetric_metric_eq_rescale_iff_integral_scalarCurvature_neg [I.Boundaryless]
    [Nonempty M] (hE : finrank ℝ E = 2) :
    (∃ (G : HyperbolicMetric (I := I) (M := M)) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
        (hf_pos : ∀ x, 0 < f x), G.metric = g.rescale f hf hf_pos) ↔
      ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0 := by
  refine ⟨?_, g.exists_hyperbolicMetric_metric_eq_rescale hE⟩
  rintro ⟨G, f, hf, hf_pos, hG⟩
  exact g.integral_scalarCurvature_neg_of_scalarCurvature_rescale_eq hE hf hf_pos (by norm_num)
    (hG ▸ G.scalarCurvature_metric_of_finrank_eq_two hE)

/-- **Hyperbolicity from negative total curvature.** A closed connected surface admitting a smooth
Riemannian metric of negative total scalar curvature is hyperbolic. -/
theorem isHyperbolic_of_integral_scalarCurvature_neg [I.Boundaryless] (hE : finrank ℝ E = 2)
    (hK : ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0) :
    IsHyperbolic (I := I) (M := M) :=
  isHyperbolic_iff.2 <|
    let ⟨G, _, _, _, _⟩ := g.exists_hyperbolicMetric_metric_eq_rescale hE hK
    ⟨G⟩

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

/-- **Total-curvature characterization of hyperbolic closed surfaces.** A nonempty closed connected
surface is hyperbolic if and only if it admits a smooth Riemannian metric of negative total scalar
curvature. -/
theorem isHyperbolic_iff_exists_integral_scalarCurvature_neg [I.Boundaryless] [Nonempty M]
    (hE : finrank ℝ E = 2) :
    IsHyperbolic (I := I) (M := M) ↔
      ∃ g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x),
        ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0 := by
  rw [isHyperbolic_iff]
  refine ⟨fun ⟨G⟩ ↦ ⟨G.metric, ?_⟩, fun ⟨g, hK⟩ ↦
    isHyperbolic_iff.1 (g.isHyperbolic_of_integral_scalarCurvature_neg hE hK)⟩
  have := (WithMetric.equiv G.metric).nonempty
  have hsc :
      ∫ x, G.metric.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric G.metric) =
        -2 * riemannianTotalVolume I (WithMetric G.metric) := by
    simp only [G.scalarCurvature_metric_of_finrank_eq_two hE, MeasureTheory.integral_const,
      smul_eq_mul, riemannianTotalVolume_def, mul_comm]
  rw [hsc]
  exact mul_neg_of_neg_of_pos (by norm_num) riemannianTotalVolume_pos

end TauCeti
