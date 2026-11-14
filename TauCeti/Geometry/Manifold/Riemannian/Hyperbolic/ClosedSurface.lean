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
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Trudinger
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
curvature, the hyperbolic metric being `e^(2φ) g`, and proves that such a conformal hyperbolic
metric exists (and is unique) if and only if the total curvature of `g` is negative.

Completeness holds automatically on a closed surface, since the Riemannian distance of a compact
manifold is complete (`TauCeti.HyperbolicMetric.ofCompactSpace`), and finite volume follows
separately (`TauCeti.HyperbolicMetric.hasFiniteVolume_of_compactSpace`). When `∫ K dV < 0`,
minimization of the Liouville energy on `H¹(M)` produces a weak solution `w ∈ H¹(M)` of
`Δ⁺w + K + e^(2w) = 0`
(`TauCeti.Manifold.SobolevH1.exists_forall_dirichletForm_eq_integral_neg_add_exp_mul`). By the
Moser–Trudinger inequality (`TauCeti.Manifold.SobolevH1.memLp_exp_mul`), `e^(2w)` lies in `L²(M)`,
so De Giorgi regularity (`TauCeti.Manifold.SobolevH1.exists_continuous_ae_eq_of_dirichletForm_eq`)
makes `w` continuous and the semilinear bootstrap
(`TauCeti.Manifold.SobolevH1.contMDiff_of_dirichletForm_eq_semilinear`) upgrades it to a unique
smooth classical solution
(`TauCeti.Manifold.existsUnique_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero`).
Conversely, conformal invariance of total curvature implies `∫ Scal^g dV_g < 0` whenever a nonempty
closed surface carries a conformal hyperbolic metric, and its area is `-∫ K dV_g`.

## Main results

* `TauCeti.Manifold.existsUnique_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero`: on a closed
  connected smooth Riemannian surface, for smooth `K` with `∫ K dV < 0`, the equation
  `-laplaceBeltrami I φ + K + e^(2φ) = 0` has a unique smooth solution.
* `Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_metric_eq_rescale_iff`: a closed
  surface carries a hyperbolic metric conformal to `g` exactly when the curvature equation has a
  smooth solution.
* `Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_metric_eq_rescale`: existence of a
  hyperbolic metric `f g` when `∫ Scal^g dV_g < 0`.
* `Bundle.ContMDiffRiemannianMetric.existsUnique_hyperbolicMetric_mem_conformalClass`: existence
  and uniqueness of a hyperbolic metric in `[g]` when `∫ Scal^g dV_g < 0`.
* `Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_mem_conformalClass_iff`: a nonempty
  closed surface carries a hyperbolic metric in `[g]` if and only if `∫ Scal^g dV_g < 0`.
* `TauCeti.HyperbolicMetric.eq_of_metric_eq_rescale`: two hyperbolic metrics conformal to `g`
  are equal.
* `TauCeti.HyperbolicMetric.hypVolumeOfMetric_eq_of_metric_eq_rescale`: a hyperbolic metric
  conformal to `g` has area `-∫ K dV_g`.

## References

* M. S. Berger, *Riemannian structures of prescribed Gaussian curvature for compact
  2-manifolds*, J. Differential Geom. 5 (1971), 325–332.
* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47.
-/

public section

open Bundle MeasureTheory Module TauCeti TauCeti.Manifold
open scoped ContDiff ENNReal Manifold NNReal

noncomputable section

section CurvaturePDE

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Smooth solvability and uniqueness of the constant negative curvature equation on a closed
surface.** On a closed connected smooth Riemannian surface, for every smooth function `K : M → ℝ`
with `∫ K dV < 0` there is a unique smooth function `φ : M → ℝ` solving
`-laplaceBeltrami I φ x + K x + Real.exp (2 * φ x) = 0` everywhere on `M`. -/
theorem existsUnique_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero
    (hE : finrank ℝ E = 2) {K : M → ℝ} (hK : ContMDiff I 𝓘(ℝ) ∞ K)
    (hK_neg : ∫ x, K x ∂riemannianVolume I M < 0) :
    ∃! φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧
      ∀ x, -laplaceBeltrami I φ x + K x + Real.exp (2 * φ x) = 0 := by
  let KLp : Lp ℝ 2 (riemannianVolume I M) :=
    ContinuousMap.toLp 2 (riemannianVolume I M) ℝ ⟨K, hK.continuous⟩
  have hKLp_ae : (KLp : M → ℝ) =ᵐ[riemannianVolume I M] K := ContinuousMap.coeFn_toLp _ _
  have hKLp_neg : ∫ x, KLp x ∂riemannianVolume I M < 0 := by rwa [integral_congr_ae hKLp_ae]
  obtain ⟨w, hw⟩ := SobolevH1.exists_forall_dirichletForm_eq_integral_neg_add_exp_mul
    hE KLp hKLp_neg
  -- By Moser–Trudinger, `-(K + e^(2w))` lies in `L²(M)`, so De Giorgi gives continuity of `w`.
  let f₀ : M → ℝ := fun x ↦ -(K x + Real.exp (2 * SobolevH1.toLp w x))
  have hf₀_memLp : MemLp f₀ (2 : ℝ≥0) (riemannianVolume I M) :=
    (((Lp.memLp KLp).ae_eq hKLp_ae).add
      (SobolevH1.memLp_exp_mul hE w 2 (p := (2 : ℝ≥0)) ENNReal.coe_ne_top)).neg
  have hw_f₀ : ∀ ψ : C^∞⟮I, M; ℝ⟯,
      SobolevH1.dirichletForm w (SobolevH1.ofSmooth ψ) =
        ∫ x, f₀ x * ψ x ∂riemannianVolume I M := fun ψ ↦ by
    rw [hw]
    refine integral_congr_ae ?_
    filter_upwards [hKLp_ae, SobolevH1.toLp_ofSmooth_ae_eq ψ] with x hxK hxψ
    dsimp only [f₀]
    rw [hxK, hxψ]
  obtain ⟨φ, hφ_cont, hwφ⟩ := SobolevH1.exists_continuous_ae_eq_of_dirichletForm_eq
    (r := 2) le_rfl (by rw [hE]; norm_num) hf₀_memLp hw_f₀
  -- Rewrite the weak right-hand side in terms of `φ` and bootstrap to `C^∞`.
  have hw_semi : ∀ ψ : C^∞⟮I, M; ℝ⟯,
      SobolevH1.dirichletForm w (SobolevH1.ofSmooth ψ) =
        ∫ x, ((-1 : ℝ) * Real.exp (2 * φ x) + -K x) * ψ x ∂riemannianVolume I M := fun ψ ↦ by
    rw [hw_f₀]
    refine integral_congr_ae ?_
    filter_upwards [hwφ] with x hx
    dsimp only [f₀]
    rw [hx]
    ring
  obtain ⟨hφ_smooth, hΔ⟩ := SobolevH1.contMDiff_of_dirichletForm_eq_semilinear
    (Φ := fun t ↦ Real.exp (2 * t)) (by omega) contMDiff_const hK.neg (by fun_prop)
    hφ_cont hwφ hw_semi
  have hφ_eq : ∀ x, -laplaceBeltrami I φ x + K x + Real.exp (2 * φ x) = 0 :=
    fun x ↦ by linarith [hΔ x]
  refine ⟨φ, ⟨hφ_smooth, hφ_eq⟩, fun φ' ⟨hφ'_smooth, hφ'_eq⟩ ↦ ?_⟩
  have hmono (x : M) : StrictMono fun t : ℝ ↦ K x + Real.exp (2 * t) := fun s t hst ↦ by
    have hexp := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hst two_pos)
    dsimp only
    linarith
  have hle₁ : φ' ≤ φ := le_of_le_laplaceBeltrami_of_laplaceBeltrami_le hmono
    (hφ'_smooth.of_le (by simp)) (hφ_smooth.of_le (by simp))
    (fun x ↦ by linarith [hφ'_eq x]) (fun x ↦ by linarith [hφ_eq x])
  have hle₂ : φ ≤ φ' := le_of_le_laplaceBeltrami_of_laplaceBeltrami_le hmono
    (hφ_smooth.of_le (by simp)) (hφ'_smooth.of_le (by simp))
    (fun x ↦ by linarith [hφ_eq x]) (fun x ↦ by linarith [hφ'_eq x])
  exact funext fun x ↦ le_antisymm (hle₁ x) (hle₂ x)

end TauCeti.Manifold

end CurvaturePDE

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

/-- **Existence of a conformal hyperbolic metric on a closed surface of negative total curvature.**
If a smooth Riemannian metric `g` on a closed connected surface satisfies `∫ Scal^g dV_g < 0`,
then its conformal class contains a hyperbolic metric `f g`. -/
theorem exists_hyperbolicMetric_metric_eq_rescale [I.Boundaryless]
    (hE : finrank ℝ E = 2)
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
  have hInt : ∫ x, g.scalarCurvature x / 2 ∂riemannianVolume I M < 0 := by
    rw [integral_div]
    rw [WithMetric.integral_comp_ofWithMetric g g.scalarCurvature] at hK
    linarith
  exact (existsUnique_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero hE
    (g.contMDiff_scalarCurvature.div_const 2) hInt).exists

/-- **Existence and uniqueness of a conformal hyperbolic metric on a closed surface.** Every
conformal class `[g]` of negative total curvature on a closed connected surface contains a unique
hyperbolic metric. -/
theorem existsUnique_hyperbolicMetric_mem_conformalClass [I.Boundaryless]
    (hE : finrank ℝ E = 2)
    (hK : ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0) :
    ∃! G : HyperbolicMetric (I := I) (M := M), G.metric ∈ g.conformalClass := by
  obtain ⟨G, f, hf, hf_pos, hGf⟩ := g.exists_hyperbolicMetric_metric_eq_rescale hE hK
  refine ⟨G, g.mem_conformalClass_iff.2 ⟨f, hf, hf_pos, hGf⟩, fun G' hG' ↦ ?_⟩
  obtain ⟨f', hf', hf'_pos, hG'f'⟩ := g.mem_conformalClass_iff.1 hG'
  exact HyperbolicMetric.eq_of_metric_eq_rescale hE G' G hG'f' hGf

/-- **Total-curvature characterization of conformal hyperbolic metrics on closed surfaces.** A
nonempty closed connected surface carries a hyperbolic metric in `[g]` if and only if
`∫ Scal^g dV_g < 0`. -/
theorem exists_hyperbolicMetric_mem_conformalClass_iff [I.Boundaryless] [Nonempty M]
    (hE : finrank ℝ E = 2) :
    (∃ G : HyperbolicMetric (I := I) (M := M), G.metric ∈ g.conformalClass) ↔
      ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0 := by
  refine ⟨?_, fun hK ↦ (g.existsUnique_hyperbolicMetric_mem_conformalClass hE hK).exists⟩
  rintro ⟨G, hG⟩
  obtain ⟨f, hf, hf_pos, hGf⟩ := g.mem_conformalClass_iff.1 hG
  exact g.integral_scalarCurvature_neg_of_scalarCurvature_rescale_eq hE hf hf_pos
    (c := -2) (by norm_num) (hGf ▸ G.scalarCurvature_metric_of_finrank_eq_two hE)

end Bundle.ContMDiffRiemannianMetric
