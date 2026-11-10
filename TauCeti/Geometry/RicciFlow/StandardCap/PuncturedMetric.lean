/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RicciFlow.StandardCap.Profile
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Scalar
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# The standard cap away from its tip

A standard cap profile `f` gives a smooth positive definite metric
`dr² + f(r)² g_(Sⁿ)` on `(0, ∞) × Sⁿ`. We construct this metric using the native
warped-product construction and compute its scalar curvature from the native
Levi-Civita connection. It is nonnegative, and on the cylindrical end equals
`n(n-1)/2`, hence equals one when `n = 2`.

This is the punctured cap: the origin has not been added, and no completeness
assertion is made. The same formula will identify the restriction of a smooth
cap metric in polar coordinates.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics
  Monographs 3 (2007), Definition 12.1.
* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7,
  Proposition 42 and Corollary 43 (warped-product curvature).
-/

public noncomputable section

open Bundle Set Real TopologicalSpace
open TauCeti.Manifold
open scoped ContDiff Manifold InnerProductSpace Topology

namespace TauCeti.IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : TauCeti.IsStandardCapProfile f)
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (Module.finrank ℝ V = n + 1)]

/-- The standard cap metric `dr² + f(r)² g_(Sⁿ)` away from the tip, with the
radial coordinate first. The sphere is the unit sphere in `V`. -/
def puncturedMetric :
    ContMDiffRiemannianMetric (𝓘(ℝ).prod (𝓡 n)) ∞ (ℝ × EuclideanSpace ℝ (Fin n))
      (fun p : (⟨Ioi (0 : ℝ), isOpen_Ioi⟩ : Opens ℝ) × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :=
  (((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace
    ⟨Ioi 0, isOpen_Ioi⟩).warpedProdTangentSpace (fun r ↦ f r)
      (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
      (fun r ↦ (hf.apply_pos r.property).ne')
      ((sphereRoundMetric (E := V)).ofLE (m := ∞) le_top)

variable {V}

/-- The punctured metric is the orthogonal sum of the radial metric and the
round sphere metric multiplied by `f(r)²`. -/
@[simp]
theorem puncturedMetric_inner
    (p : (⟨Ioi (0 : ℝ), isOpen_Ioi⟩ : Opens ℝ) × Metric.sphere (0 : V) 1)
    (v w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    (hf.puncturedMetric (n := n) V).inner p v w =
      (((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace
        ⟨Ioi 0, isOpen_Ioi⟩).inner p.1 (tangentSpaceProdEquiv p v).1
          (tangentSpaceProdEquiv p w).1 +
      f p.1 ^ 2 * ((sphereRoundMetric (E := V)).ofLE (m := ∞) le_top).inner p.2
        (tangentSpaceProdEquiv p v).2 (tangentSpaceProdEquiv p w).2 := by
  rw [puncturedMetric, ContMDiffRiemannianMetric.warpedProdTangentSpace_inner]

/-- Scalar curvature of the punctured standard cap, with `Δ = div grad`.
For a two-dimensional sphere fibre the two terms are
`2(1-f'²)/f² - 4f''/f`. -/
theorem scalarCurvature_puncturedMetric
    (p : (⟨Ioi (0 : ℝ), isOpen_Ioi⟩ : Opens ℝ) × Metric.sphere (0 : V) 1) :
    (hf.puncturedMetric (n := n) V).scalarCurvature p =
      (n : ℝ) * (n - 1) * (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 -
        2 * n * deriv (deriv f) p.1 / f p.1 := by
  let U : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  let gU := g.restrictOpenTangentSpace U
  have hg : g.scalarCurvature (p.1 : ℝ) = 0 := by
    rw [ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection g
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _).symm,
      scalarCurvature_leviCivitaConnection_model_space]
  let : RiemannianBundle (fun x : U ↦ TangentSpace 𝓘(ℝ) x) := ⟨gU.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ) x) := ⟨g.toRiemannianMetric⟩
  let := Bundle.instIsContMDiffRiemannianBundle gU
  let := Bundle.instIsContMDiffRiemannianBundle g
  have hgeq : g.toRiemannianMetric = (riemannianMetricVectorSpace ℝ).toRiemannianMetric :=
    ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _
  have hi := g.isLocalRiemannianIsometry_restrictOpenTangentSpace U
  have hΔ : laplaceBeltrami 𝓘(ℝ) (fun r : U ↦ f r) p.1 = deriv (deriv f) p.1 := by
    have h := hi.laplaceBeltrami_comp (u := f) (x := p.1)
      (hf.contDiff.contMDiff.contMDiffAt.of_le (by simp))
    simp only [Function.comp_def] at h
    rw [h, laplaceBeltrami_eq_laplacian_of_eq hgeq
        ((hf.contDiff.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).gradient_right
          (m := 1) (by norm_num) |>.differentiable (by norm_num) _),
      InnerProductSpace.laplacian_eq_iteratedDeriv_real]
    simp [iteratedDeriv_succ]
  have hgrad : ‖mgradient 𝓘(ℝ) (fun r : U ↦ f r) p.1‖ ^ 2 = deriv f p.1 ^ 2 := by
    obtain ⟨e, he⟩ := hi.exists_linearIsometryEquiv_eq_mfderiv p.1
    have h := hi.mfderiv_mgradient_comp (φ := f) (x := p.1)
      ((hf.differentiable (p.1 : ℝ)).mdifferentiableAt)
    simp only [Function.comp_def] at h
    rw [← e.norm_map, he, h, norm_mgradient_eq_norm_gradient_of_eq hgeq,
      gradient_eq_deriv', Real.norm_eq_abs, sq_abs]
  rw [puncturedMetric, ContMDiffRiemannianMetric.scalarCurvature_warpedProdTangentSpace,
    ContMDiffRiemannianMetric.scalarCurvature_restrictOpenTangentSpace,
    scalarCurvature_sphereRoundMetric_ofLE, hg, hΔ, hgrad]
  simp only [finrank_euclideanSpace_fin]
  ring

/-- The punctured standard cap has nonnegative scalar curvature in every
sphere dimension. -/
theorem scalarCurvature_puncturedMetric_nonneg
    (p : (⟨Ioi (0 : ℝ), isOpen_Ioi⟩ : Opens ℝ) × Metric.sphere (0 : V) 1) :
    0 ≤ (hf.puncturedMetric (n := n) V).scalarCurvature p := by
  rw [hf.scalarCurvature_puncturedMetric (n := n)]
  have h₀ := hf.deriv_nonneg p.1.property.le
  have h₁ := hf.deriv_le_one p.1.property.le
  have h₂ := hf.deriv_deriv_nonpos p.1.property.le
  have hpos := hf.apply_pos p.1.property
  cases n with
  | zero => simp
  | succ n =>
    have hn : (0 : ℝ) ≤ (n + 1 : ℕ) - 1 := by simp
    exact sub_nonneg.2 (le_trans (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) h₂) hpos.le)
      (div_nonneg (mul_nonneg (mul_nonneg (by positivity) hn) (by nlinarith)) (sq_nonneg _)))

/-- On a sufficiently far cylindrical end, scalar curvature is `n(n-1)/2`.
In particular it is one for the punctured three-dimensional cap. -/
theorem exists_scalarCurvature_puncturedMetric_eq_cylinder :
    ∃ R > 0, ∀ p : (⟨Ioi (0 : ℝ), isOpen_Ioi⟩ : Opens ℝ) × Metric.sphere (0 : V) 1,
      R ≤ (p.1 : ℝ) →
      (hf.puncturedMetric (n := n) V).scalarCurvature p = (n : ℝ) * (n - 1) / 2 := by
  obtain ⟨R, hR⟩ := hf.exists_eq_sqrt_two
  refine ⟨max R 0 + 1, by positivity, fun p hp ↦ ?_⟩
  have hr : R < (p.1 : ℝ) := by linarith [le_max_left R 0]
  have heq : f =ᶠ[𝓝 (p.1 : ℝ)] fun _ ↦ √2 := by
    filter_upwards [Ioi_mem_nhds hr] with s hs using hR s hs.le
  have hd : deriv f =ᶠ[𝓝 (p.1 : ℝ)] fun _ ↦ 0 := by
    filter_upwards [heq.deriv] with s hs
    simpa only [deriv_const] using hs
  rw [hf.scalarCurvature_puncturedMetric, heq.eq_of_nhds, hd.eq_of_nhds,
    hd.deriv_eq, deriv_const, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Near its missing tip, the punctured metric has scalar curvature `n(n+1)/4`,
the scalar curvature of a round sphere of sectional curvature `1/4`. -/
theorem exists_scalarCurvature_puncturedMetric_eq_round :
    ∃ r₀ > 0, ∀ p : (⟨Ioi (0 : ℝ), isOpen_Ioi⟩ : Opens ℝ) × Metric.sphere (0 : V) 1,
      (p.1 : ℝ) < r₀ →
      (hf.puncturedMetric (n := n) V).scalarCurvature p = (n : ℝ) * (n + 1) / 4 := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin
  refine ⟨r₀, hr₀, fun p hp ↦ ?_⟩
  have heq : f =ᶠ[𝓝 (p.1 : ℝ)] fun s ↦ 2 * sin (s / 2) := by
    filter_upwards [Ioo_mem_nhds p.1.property hp] with s hs using h s ⟨hs.1.le, hs.2⟩
  have hd : deriv f =ᶠ[𝓝 (p.1 : ℝ)] fun s ↦ cos (s / 2) := by
    filter_upwards [heq.deriv] with s hs
    rw [hs, (((hasDerivAt_id' s).div_const 2).sin.const_mul 2).deriv]
    ring
  have hdd : deriv (deriv f) (p.1 : ℝ) = -sin ((p.1 : ℝ) / 2) / 2 := by
    rw [hd.deriv_eq, (((hasDerivAt_id' (p.1 : ℝ)).div_const 2).cos).deriv]
    ring
  have hsin : sin ((p.1 : ℝ) / 2) ≠ 0 := by
    have := hf.apply_pos p.1.property
    rw [heq.eq_of_nhds] at this
    exact ne_of_gt (by linarith)
  have htrig : 1 - cos ((p.1 : ℝ) / 2) ^ 2 = sin ((p.1 : ℝ) / 2) ^ 2 := by
    nlinarith [sin_sq_add_cos_sq ((p.1 : ℝ) / 2)]
  rw [hf.scalarCurvature_puncturedMetric, heq.eq_of_nhds, hd.eq_of_nhds, hdd, htrig]
  field_simp
  ring

end TauCeti.IsStandardCapProfile
