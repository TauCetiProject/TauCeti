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

Combining the variational existence of weak `H¹` solutions of the curvature equation
(`TauCeti.Manifold.SobolevH1.exists_forall_dirichletForm_eq_integral_neg_add_exp_mul`), the
Trudinger exponential integrability (`TauCeti.Manifold.SobolevH1.memLp_exp_mul`), and semilinear
elliptic regularity (`TauCeti.Manifold.SobolevH1.exists_contMDiff_of_forall_dirichletForm_eq`)
produces a unique smooth solution whenever `∫ K dV < 0`. Scaling the solution by a constant
yields a conformal metric of any prescribed constant negative scalar curvature `c < 0`, and in
particular a unique hyperbolic metric in the conformal class of `g` if and only if
`∫ Scal^g dV_g < 0`.

## Main results

* `TauCeti.Manifold.existsUnique_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero`: on a closed
  connected surface, `Δ⁺φ + K + e^(2φ) = 0` has a unique smooth solution whenever `K` is smooth
  with `∫ K dV < 0`.
* `Bundle.ContMDiffRiemannianMetric.existsUnique_scalarCurvature_rescale_eq`,
  `Bundle.ContMDiffRiemannianMetric.exists_scalarCurvature_rescale_eq_iff`: existence, uniqueness,
  and total-curvature characterization of a conformal metric of constant negative scalar curvature
  `c`.
* `Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_metric_eq_rescale_iff`: a closed
  surface carries a hyperbolic metric conformal to `g` exactly when the curvature equation has a
  smooth solution.
* `TauCeti.HyperbolicMetric.eq_of_metric_eq_rescale`: two hyperbolic metrics conformal to `g`
  are equal.
* `TauCeti.HyperbolicMetric.hypVolumeOfMetric_eq_of_metric_eq_rescale`: a hyperbolic metric
  conformal to `g` has area `-∫ K dV_g`.
* `Bundle.ContMDiffRiemannianMetric.existsUnique_hyperbolicMetric_metric_eq_rescale`,
  `Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_metric_eq_rescale_iff_integral_neg`:
  on a closed connected surface, the conformal class of `g` contains a unique hyperbolic metric
  if and only if `∫ Scal^g dV_g < 0`.

## References

* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47.
* M. S. Berger, *Riemannian structures of prescribed Gaussian curvature for compact
  2-manifolds*, J. Differential Geom. 5 (1971), 325–332.
-/

public section

open Bundle MeasureTheory Module TauCeti TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

section CurvatureEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

namespace TauCeti.Manifold

/-- **Existence and uniqueness for the curvature equation.** On a closed connected smooth
Riemannian surface, if `K` is smooth with `∫ K dV < 0`, then the curvature equation
`Δ⁺φ + K + e^(2φ) = 0` has a unique smooth solution `φ`. -/
theorem existsUnique_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero [I.Boundaryless]
    [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hE : finrank ℝ E = 2) {K : M → ℝ} (hK : ContMDiff I 𝓘(ℝ) ∞ K)
    (hKint : ∫ x, K x ∂riemannianVolume I M < 0) :
    ∃! φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧
      ∀ x, -laplaceBeltrami I φ x + K x + Real.exp (2 * φ x) = 0 := by
  -- Minimize the Liouville energy on `H¹(M)` to obtain a weak solution.
  have hK_memLp : MemLp K 2 (riemannianVolume I M) :=
    hK.continuous.memLp_of_hasCompactSupport (.of_compactSpace _)
  set KL2 : Lp ℝ 2 (riemannianVolume I M) := hK_memLp.toLp K
  have hKL2_ae : (KL2 : M → ℝ) =ᵐ[riemannianVolume I M] K := hK_memLp.coeFn_toLp
  have hKL2_int : ∫ x, KL2 x ∂riemannianVolume I M < 0 := by
    rwa [integral_congr_ae hKL2_ae]
  obtain ⟨w, hw⟩ :=
    SobolevH1.exists_forall_dirichletForm_eq_integral_neg_add_exp_mul hE KL2 hKL2_int
  -- Trudinger's inequality places `e^(2w)` in `L²(M)`, so semilinear regularity applies.
  have hweak (v : SobolevH1 I M) :
      SobolevH1.dirichletForm w v =
        ∫ x, ((-1) * Real.exp (2 * SobolevH1.toLp w x) + -K x) *
          SobolevH1.toLp v x ∂riemannianVolume I M :=
    (hw v).trans <| integral_congr_ae <| hKL2_ae.mono fun x hx ↦ by dsimp only; rw [hx]; ring
  have hmemLp : MemLp (fun x ↦ (-1) * Real.exp (2 * SobolevH1.toLp w x) + -K x) 2
      (riemannianVolume I M) :=
    ((SobolevH1.memLp_exp_mul hE w 2 (p := 2) ENNReal.ofNat_ne_top).const_mul (-1)).add
      hK_memLp.neg
  obtain ⟨u, -, hu⟩ := SobolevH1.exists_contMDiff_of_forall_dirichletForm_eq (by omega)
    contMDiff_const hK.neg (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)) hmemLp hweak
  -- Uniqueness follows from the comparison principle since `t ↦ K(x) + e^(2t)` is strictly
  -- increasing.
  have hu' (x : M) : -laplaceBeltrami I u x + K x + Real.exp (2 * u x) = 0 := by
    have h := hu x
    simp only [Function.comp_apply, id_eq] at h
    linarith
  refine ⟨u, ⟨u.contMDiff, hu'⟩, fun ψ ⟨hψ, hψeq⟩ ↦ ?_⟩
  have hmono (x : M) : StrictMono fun t : ℝ ↦ K x + Real.exp (2 * t) := fun _ _ hst ↦ by
    dsimp only
    linarith [Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hst two_pos)]
  have hle₁ := le_of_le_laplaceBeltrami_of_laplaceBeltrami_le hmono
    (hψ.of_le (by simp)) (u.contMDiff.of_le (by simp))
    (fun x ↦ by linarith [hψeq x]) (fun x ↦ by linarith [hu' x])
  have hle₂ := le_of_le_laplaceBeltrami_of_laplaceBeltrami_le hmono
    (u.contMDiff.of_le (by simp)) (hψ.of_le (by simp))
    (fun x ↦ by linarith [hu' x]) (fun x ↦ by linarith [hψeq x])
  exact funext fun x ↦ le_antisymm (hle₁ x) (hle₂ x)

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- **Existence and uniqueness of a conformal metric of constant negative scalar curvature.** On a
closed connected surface, if a smooth metric `g` has negative total scalar curvature, then for every
`c < 0` there is a unique smooth positive function `f` such that `f g` has constant scalar curvature
`c`. -/
theorem existsUnique_scalarCurvature_rescale_eq [I.Boundaryless] (hE : finrank ℝ E = 2) {c : ℝ}
    (hc : c < 0)
    (hg : ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0) :
    ∃! f : M → ℝ, ∃ (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x),
      ∀ x, (g.rescale f hf hf_pos).scalarCurvature x = c := by
  borelize M
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  let _ : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    instIsContMDiffRiemannianBundle g
  have hKint : ∫ x, g.scalarCurvature x / 2 ∂riemannianVolume I M < 0 := by
    rw [integral_div, ← WithMetric.integral_comp_ofWithMetric g g.scalarCurvature]
    exact div_neg_of_neg_of_pos hg two_pos
  obtain ⟨φ, ⟨hφ, hφeq⟩, -⟩ := existsUnique_contMDiff_neg_laplaceBeltrami_add_add_exp_eq_zero
    (I := I) hE (g.contMDiff_scalarCurvature.div_const 2) hKint
  -- Shift `φ` by `log (-2 / c) / 2` to scale the constant curvature from `-2` to `c`.
  let a : ℝ := Real.log (-2 / c) / 2
  let ψ : M → ℝ := fun x ↦ φ x + a
  have hψ : ContMDiff I 𝓘(ℝ) ∞ ψ := hφ.add contMDiff_const
  have hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ Real.exp (2 * ψ x) :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contMDiff.comp hψ
  have hsc : ∀ x,
      (g.rescale (fun x ↦ Real.exp (2 * ψ x)) hf (fun _ ↦ Real.exp_pos _)).scalarCurvature x =
        c := fun x ↦ by
    rw [scalarCurvature_rescale_eq_iff_of_finrank_eq_two g hE hf (fun _ ↦ Real.exp_pos _)
      (fun _ ↦ rfl)]
    have hψ_add : ψ = φ + fun _ ↦ a := rfl
    have hΔ : laplaceBeltrami I ψ x = laplaceBeltrami I φ x := by
      rw [hψ_add, laplaceBeltrami_add I (hφ.of_le (by simp)) contMDiff_const x,
        laplaceBeltrami_const I a x, add_zero]
    have hpos : 0 < -2 / c := div_pos_of_neg_of_neg (by norm_num) hc
    have hexp : Real.exp (2 * ψ x) = Real.exp (2 * φ x) * (-2 / c) := by
      dsimp only [ψ, a]
      rw [mul_add, Real.exp_add, mul_div_cancel₀ _ two_ne_zero, Real.exp_log hpos]
    have hmul : c / 2 * (Real.exp (2 * φ x) * (-2 / c)) = -Real.exp (2 * φ x) := by
      have hc0 : c ≠ 0 := hc.ne
      field_simp
    rw [hΔ, hexp, hmul]
    linarith [hφeq x]
  refine ⟨fun x ↦ Real.exp (2 * ψ x), ⟨hf, fun _ ↦ Real.exp_pos _, hsc⟩, ?_⟩
  rintro f' ⟨hf', hf'_pos, hsc'⟩
  exact g.eq_of_scalarCurvature_rescale_eq hE hf' hf'_pos hf (fun _ ↦ Real.exp_pos _) hc hsc' hsc

/-- **Total-curvature characterization of constant negative curvature conformal classes.** A smooth
metric `g` on a nonempty closed connected surface is conformal to a metric of constant scalar
curvature `c < 0` if and only if `∫ Scal^g dV_g < 0`. -/
theorem exists_scalarCurvature_rescale_eq_iff [I.Boundaryless] [Nonempty M] (hE : finrank ℝ E = 2)
    {c : ℝ} (hc : c < 0) :
    (∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x),
        ∀ x, (g.rescale f hf hf_pos).scalarCurvature x = c) ↔
      ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0 :=
  ⟨fun ⟨_, hf, hf_pos, h⟩ ↦ g.integral_scalarCurvature_neg_of_scalarCurvature_rescale_eq hE hf
    hf_pos hc h, fun hg ↦ (g.existsUnique_scalarCurvature_rescale_eq hE hc hg).exists⟩

end Bundle.ContMDiffRiemannianMetric

end CurvatureEquation

section Hyperbolic

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

end Hyperbolic

section HyperbolicExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

namespace Bundle.ContMDiffRiemannianMetric

variable (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- **Existence and uniqueness of a hyperbolic metric in a conformal class.** On a closed
connected surface, if a smooth metric `g` has negative total scalar curvature, then there is a
unique hyperbolic metric conformal to `g`. -/
theorem existsUnique_hyperbolicMetric_metric_eq_rescale [I.Boundaryless] (hE : finrank ℝ E = 2)
    (hg : ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0) :
    ∃! G : HyperbolicMetric (I := I) (M := M),
      ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x),
        G.metric = g.rescale f hf hf_pos := by
  obtain ⟨f, ⟨hf, hf_pos, hsc⟩, -⟩ :=
    g.existsUnique_scalarCurvature_rescale_eq hE (c := -2) (by norm_num) hg
  refine ⟨HyperbolicMetric.ofCompactSpace
      ((isConstantCurvatureTensor_iff_scalarCurvature_eq_of_finrank_eq_two _ hE (-1)).2
        fun x ↦ by norm_num; exact hsc x),
    ⟨f, hf, hf_pos, HyperbolicMetric.metric_ofCompactSpace _⟩, ?_⟩
  rintro G' ⟨f', hf', hf'_pos, hG'⟩
  exact HyperbolicMetric.eq_of_metric_eq_rescale hE G' _ hG'
    (HyperbolicMetric.metric_ofCompactSpace _)

/-- **Total-curvature characterization of hyperbolic conformal classes.** On a nonempty closed
connected surface, the conformal class of a smooth metric `g` contains a hyperbolic metric if
and only if `∫ Scal^g dV_g < 0`. -/
theorem exists_hyperbolicMetric_metric_eq_rescale_iff_integral_neg
    [I.Boundaryless] [Nonempty M] (hE : finrank ℝ E = 2) :
    (∃ (G : HyperbolicMetric (I := I) (M := M)) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
        (hf_pos : ∀ x, 0 < f x), G.metric = g.rescale f hf hf_pos) ↔
      ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0 := by
  constructor
  · rintro ⟨G, f, hf, hf_pos, hG⟩
    exact g.integral_scalarCurvature_neg_of_scalarCurvature_rescale_eq hE hf hf_pos
      (by norm_num) (hG ▸ G.scalarCurvature_metric_of_finrank_eq_two hE)
  · intro hg
    obtain ⟨G, ⟨f, hf, hf_pos, hG⟩, -⟩ :=
      g.existsUnique_hyperbolicMetric_metric_eq_rescale hE hg
    exact ⟨G, f, hf, hf_pos, hG⟩

end Bundle.ContMDiffRiemannianMetric

end HyperbolicExistence
