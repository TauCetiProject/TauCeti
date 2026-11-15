/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Stereographic
public import TauCeti.Analysis.PDE.Yamabe.ConformalInvariance
public import TauCeti.Analysis.PDE.Yamabe.Sphere.Constant
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.PDE.Yamabe.Bubble.SobolevQuotient
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature

/-!
# The conformal Laplacian and Yamabe quotient of the round sphere

Let `E` be a real inner product space of dimension `n + 1` and let `Sⁿ` be its unit sphere with the
round metric (`TauCeti.sphereRoundMetric`), whose scalar curvature is `n (n - 1)` and whose total
Riemannian volume is `|Sⁿ| = TauCeti.roundSphereVolume n`. This file develops the Yamabe operator
and functional on `Sⁿ` and on the round sphere `Sⁿ(r)` of radius `r > 0`
(`TauCeti.sphereRoundMetricOfRadius`), and connects them to Euclidean space via stereographic
projection:

* **Conformal Laplacian.** On the unit sphere `Sⁿ`, `L u = aₙ (-Δ u) + n (n - 1) u`, so
  `L c = n (n - 1) c` for a constant `c`; on the sphere `Sⁿ(r)` of radius `r > 0` (metric `r² g`),
  `L_(r² g) c = (n (n - 1) / r²) c`. For instance, on `S³` of radius `r = 2` (`4 g`),
  `L_(4 g) 1 = 6 / 4`.
* **Constant unit-norm Yamabe solution.** For `n ≠ 2`, the positive constant
  `cₙ = |Sⁿ| ^ (-1 / pₙ)` solves the unit-norm Yamabe equation `L cₙ = Y(Sⁿ) cₙ ^ (pₙ - 1)`, where
  `Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)` (`TauCeti.Yamabe.sphereYamabeConstant`), and has unit
  `L^{pₙ}` norm on `Sⁿ` whenever `n ≠ 0, 2`.
* **Stereographic conformal covariance.** In dimension `n ≠ 2`, for `t > 0` the bubble-rescaled
  stereographic map `Φ(x) = σ⁻¹((2 / t) (x - b))` is a local Riemannian isometry from the
  metric-indexed copy of `ℝⁿ` carrying `U_{t,b} ^ (4 / (n - 2)) δ` into `Sⁿ`. Consequently, for
  every `t ≥ 0` and any function `u` that is `C²` at `Φ(x)`,
  `aₙ (-Δ (U_{t,b} · (u ∘ Φ)))(x) = U_{t,b}(x) ^ ((n + 2) / (n - 2)) (L u)(Φ(x))`.
  At `u = 1` this recovers the Euclidean bubble equation from `Scal(Sⁿ) = n (n - 1)`.
* **Yamabe quotient.** On the unit sphere `Sⁿ`, `Q(1) = Y(Sⁿ)` in every dimension `n ≥ 0`, and
  `Q(c) = Y(Sⁿ)` for every nonzero constant `c` when `n ≠ 2`. By homothety invariance of the
  Yamabe quotient (`Bundle.ContMDiffRiemannianMetric.yamabeQuotient_rescale_const`), the round
  sphere `Sⁿ(r)` of any radius `r > 0` has the same Yamabe quotient `Q_(r² g)(u) = Q_g(u)` for
  every function `u`, and in particular `Q_(r² g)(1) = Y(Sⁿ)` independently of `r`.

The sharp inequality `Q(u) ≥ Y(Sⁿ)` for general `H¹` functions (Aubin–Talenti / Obata) is not
proved here.

## Main results

All declarations are in the namespace `TauCeti.Yamabe`.

* `conformalLaplacian_sphere`, `conformalLaplacian_sphere_const`, and
  `conformalLaplacian_sphereRoundMetricOfRadius_const`: the conformal Laplacian on `Sⁿ` and on
  constants for `Sⁿ(r)`.
* `conformalLaplacian_sphere_roundSphereVolume_rpow_neg_inv` and
  `integral_abs_rpow_criticalExponent_roundSphereVolume_rpow_neg_inv`: the constant unit-`L^{pₙ}`
  solution `|Sⁿ| ^ (-1 / pₙ)` of `L u = Y(Sⁿ) u ^ (pₙ - 1)` on `Sⁿ`.
* `isLocalRiemannianIsometry_stereographic'_symm_smul_sub` and
  `conformalCoefficient_mul_neg_laplacian_bubble_mul_comp_stereographic'_symm_smul_sub`:
  stereographic local isometry and pointwise conformal covariance of `L`.
* `yamabeQuotient_sphere_one`, `yamabeQuotient_sphere_const`,
  `yamabeQuotient_sphereRoundMetricOfRadius`, and
  `yamabeQuotient_sphereRoundMetricOfRadius_one`: the Yamabe quotient on `Sⁿ` and `Sⁿ(r)`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2–§3.
-/

public section

open Bundle InnerProductSpace Laplacian MeasureTheory Metric Module TauCeti.Manifold
open scoped ContDiff Gradient Manifold Topology

noncomputable section

namespace TauCeti.Yamabe

section ConformalLaplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The conformal Laplacian on the unit round sphere**:
`L u = aₙ (-Δ u) + n (n - 1) u`. -/
theorem conformalLaplacian_sphere (u : sphere (0 : E) 1 → ℝ) (p : sphere (0 : E) 1) :
    conformalLaplacian (𝓡 n) u p =
      conformalCoefficient n * -laplaceBeltrami (𝓡 n) u p + n * ((n : ℝ) - 1) * u p := by
  rw [conformalLaplacian_def, finrank_euclideanSpace_fin, scalarCurvature_sphere]

/-- On the unit round sphere `Sⁿ`, the conformal Laplacian of a constant `c` is `n (n - 1) c`.
Not tagged `@[simp]`: `simp` already proves this via `conformalLaplacian_const` and
`scalarCurvature_sphere`. -/
theorem conformalLaplacian_sphere_const (c : ℝ) (p : sphere (0 : E) 1) :
    conformalLaplacian (𝓡 n) (fun _ : sphere (0 : E) 1 ↦ c) p = n * ((n : ℝ) - 1) * c := by
  rw [conformalLaplacian_const, scalarCurvature_sphere]

/-- **Conformal Laplacian of a constant on the round sphere of radius `r > 0`**:
`L_(r² g) c = (n (n - 1) / r²) c`. In particular, on `S³` at radius `r = 2` (`4 g`),
`L_(4 g) 1 = 6 / 4`. -/
@[simp 1100]
theorem conformalLaplacian_sphereRoundMetricOfRadius_const {r : ℝ} (hr : 0 < r) (c : ℝ)
    (p : sphere (0 : E) 1) :
    (letI : RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
       ⟨(sphereRoundMetricOfRadius r hr).toRiemannianMetric⟩;
     conformalLaplacian (𝓡 n) (fun _ ↦ c) p) =
      n * ((n : ℝ) - 1) / r ^ 2 * c := by
  rw [sphereRoundMetricOfRadius_def,
    conformalLaplacian_rescale_const _ (pow_pos hr 2) contMDiff_const p, conformalLaplacian_const,
    ← ContMDiffRiemannianMetric.scalarCurvature_def, scalarCurvature_sphereRoundMetric_ofLE]
  ring

/-- **Constant unit-norm Yamabe solution on `Sⁿ`.** In dimension `n ≠ 2`, the positive constant
`cₙ = |Sⁿ| ^ (-1 / pₙ)` solves `L cₙ = Y(Sⁿ) cₙ ^ (pₙ - 1)` on the unit round sphere. -/
theorem conformalLaplacian_sphere_roundSphereVolume_rpow_neg_inv (hn : n ≠ 2)
    (p : sphere (0 : E) 1) :
    conformalLaplacian (𝓡 n)
        (fun _ : sphere (0 : E) 1 ↦ roundSphereVolume n ^ (-(1 / criticalExponent n))) p =
      sphereYamabeConstant n *
        (roundSphereVolume n ^ (-(1 / criticalExponent n))) ^ (criticalExponent n - 1) := by
  rw [conformalLaplacian_sphere_const]
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp [sphereYamabeConstant_def]
  have hn₀' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn₀
  have hn₂' : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  rw [sphereYamabeConstant_def, mul_assoc (_ * _), ← Real.rpow_mul (roundSphereVolume_pos n).le,
    ← Real.rpow_add (roundSphereVolume_pos n)]
  congr 1
  congr 1
  rw [criticalExponent_def]
  field_simp
  ring

end ConformalLaplacian

section StereographicCovariance

/-- The conformal Laplacian at a point `x` depends only on the germ at `x` among functions that are
`C²` at `x`. -/
private theorem conformalLaplacian_congr_of_eventuallyEq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ F (fun x : M ↦ TangentSpace I x)]
    {u v : M → ℝ} {x : M} (hu : ContMDiffAt I 𝓘(ℝ) 2 u x) (hv : ContMDiffAt I 𝓘(ℝ) 2 v x)
    (h : u =ᶠ[𝓝 x] v) :
    conformalLaplacian I u x = conformalLaplacian I v x := by
  let _ : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hgrad {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
      MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) x :=
    (contMDiffAt_mgradient (I := I) (n := 1)
      (by simpa only [one_add_one_eq_two] using hf)).mdifferentiableAt (by simp)
  have hev : ∀ᶠ y in 𝓝 x, mgradient I u y = mgradient I v y := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    apply ext_inner_right ℝ
    intro w
    rw [inner_mgradient, inner_mgradient, hy.mvfderiv_eq]
  have hcov := (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv
  rw [conformalLaplacian_def, conformalLaplacian_def, laplaceBeltrami_def, laplaceBeltrami_def,
    divergence_def, divergence_def,
    hcov.congr_of_eventuallyEq (hgrad hu) (hgrad hv) Filter.univ_mem hev, h.eq_of_nhds]

/-- Transport of the conformal Laplacian from a metric-indexed copy `WithMetric g` to `M`. -/
private theorem conformalLaplacian_comp_ofWithMetric
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    (g : ContMDiffRiemannianMetric I ∞ F (fun x : M ↦ TangentSpace I x))
    {w : M → ℝ} {x : M} (hw : ContMDiffAt I 𝓘(ℝ) 2 w x) :
    conformalLaplacian I (w ∘ WithMetric.ofWithMetric) (WithMetric.toWithMetric g x) =
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
       conformalLaplacian I w x) := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have hiso : IsLocalRiemannianIsometry I I (WithMetric.ofWithMetric : WithMetric g → M) :=
    ⟨WithMetric.contMDiff_ofWithMetric,
      fun y ↦ by rw [WithMetric.mfderiv_ofWithMetric]; exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩,
      fun y a b ↦ (WithMetric.inner_def y a b).symm⟩
  rw [conformalLaplacian_def, conformalLaplacian_def,
    hiso.laplaceBeltrami_comp (x := WithMetric.toWithMetric g x) hw,
    ← hiso.scalarCurvature_map (WithMetric.toWithMetric g x),
    Function.comp_apply, WithMetric.ofWithMetric_toWithMetric]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **Rescaled inverse stereographic projection is a local Riemannian isometry.** In dimension
`n ≠ 2`, for `t > 0`, `x ↦ σ⁻¹((2 / t) (x - b))` is a smooth local Riemannian isometry from the
metric-indexed copy of `ℝⁿ` carrying the bubble conformal metric `U_{t,b} ^ (4 / (n - 2)) δ` into
the unit round sphere `Sⁿ`. -/
theorem isLocalRiemannianIsometry_stereographic'_symm_smul_sub (hn : n ≠ 2) (v : sphere (0 : E) 1)
    {t : ℝ} (ht : 0 < t) (b : EuclideanSpace ℝ (Fin n)) :
    let g₀ := (riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top
    let hf : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ fun y : EuclideanSpace ℝ (Fin n) ↦
        bubble t b y ^ (4 / ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 2)) :=
      (contDiff_bubble t b (m := ∞)).contMDiff.rpow_const_of_ne
        (fun y ↦ (bubble_pos ht b y).ne') _
    let hf_pos : ∀ y : EuclideanSpace ℝ (Fin n),
        0 < bubble t b y ^ (4 / ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 2)) :=
      fun y ↦ Real.rpow_pos_of_pos (bubble_pos ht b y) _
    IsLocalRiemannianIsometry (𝓡 n) (𝓡 n)
      (((stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)) ∘
        (WithMetric.ofWithMetric : WithMetric (g₀.rescale _ hf hf_pos) → _)) := by
  dsimp only
  let g₀ := (riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top
  let hf : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ fun y : EuclideanSpace ℝ (Fin n) ↦
      bubble t b y ^ (4 / ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 2)) :=
    (contDiff_bubble t b (m := ∞)).contMDiff.rpow_const_of_ne
      (fun y ↦ (bubble_pos ht b y).ne') _
  let hf_pos : ∀ y : EuclideanSpace ℝ (Fin n),
      0 < bubble t b y ^ (4 / ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 2)) :=
    fun y ↦ Real.rpow_pos_of_pos (bubble_pos ht b y) _
  let Φ : EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1 :=
    (stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)
  have hinner (y : WithMetric (g₀.rescale _ hf hf_pos)) (a c : TangentSpace (𝓡 n) y) :
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) (Φ ∘ WithMetric.ofWithMetric) y a)
          (mfderiv (𝓡 n) (𝓡 n) (Φ ∘ WithMetric.ofWithMetric) y c) =
        inner ℝ a c := by
    rw [WithMetric.mfderiv_comp_ofWithMetric Φ y, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, WithMetric.inner_def, ContMDiffRiemannianMetric.rescale_inner,
      ContMDiffRiemannianMetric.ofLE_inner]
    refine (inner_mfderiv_stereographic'_symm_smul_sub hn v ht b y.ofWithMetric _ _).trans ?_
    congr 3
    rw [finrank_euclideanSpace_fin]
  refine
    { contMDiff := ((isSmoothEmbedding_stereographic'_symm (k := ∞) v).contMDiff.comp
        (((contDiff_id.sub contDiff_const).const_smul (2 / t)).contMDiff)).comp
        WithMetric.contMDiff_ofWithMetric
      isInvertible_mfderiv := fun y ↦ ?_
      inner_mfderiv := hinner }
  set L := mfderiv (𝓡 n) (𝓡 n) (Φ ∘ WithMetric.ofWithMetric) y
  have hinj : Function.Injective L := by
    intro a c hac
    have h0 : inner ℝ (a - c) (a - c) = 0 := by
      rw [← hinner y (a - c) (a - c), map_sub, hac, sub_self, inner_zero_left]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)
  have hdim :
      finrank ℝ (TangentSpace (𝓡 n) y) =
        finrank ℝ (TangentSpace (𝓡 n) ((Φ ∘ WithMetric.ofWithMetric) y)) :=
    rfl
  let eL : TangentSpace (𝓡 n) y ≃ₗᵢ[ℝ] TangentSpace (𝓡 n) ((Φ ∘ WithMetric.ofWithMetric) y) :=
    (LinearEquiv.ofBijective L.toLinearMap
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
      ).isometryOfInner (hinner y)
  exact ⟨eL.toContinuousLinearEquiv, by ext w; rfl⟩

/-- On `ℝⁿ` with the smooth Euclidean metric `(riemannianMetricVectorSpace _).ofLE le_top`, the
conformal Laplacian of a `C²` function `f` is `aₙ (-Δ f)`. -/
private theorem conformalLaplacian_euclideanSpace {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : ContDiff ℝ 2 f) (x : EuclideanSpace ℝ (Fin m)) :
    (letI : RiemannianBundle (fun y : EuclideanSpace ℝ (Fin m) ↦ TangentSpace (𝓡 m) y) :=
       ⟨((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin m))).ofLE
         (m := ∞) le_top).toRiemannianMetric⟩;
     conformalLaplacian (𝓡 m) f x) = conformalCoefficient m * -Δ f x := by
  let g₀ := (riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin m))).ofLE (m := ∞) le_top
  have hgrad : DifferentiableAt ℝ (∇ f) x :=
    (((toDual ℝ (EuclideanSpace ℝ (Fin m))).symm.contDiff.comp
      (hf.fderiv_right (m := 1) (by norm_num))).differentiable one_ne_zero) x
  have hm := ContMDiffRiemannianMetric.toRiemannianMetric_ofLE
    (riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin m))) (le_top : (∞ : ℕ∞ω) ≤ ω)
  have hΔ :
      (letI : RiemannianBundle (fun y : EuclideanSpace ℝ (Fin m) ↦ TangentSpace (𝓡 m) y) :=
         ⟨g₀.toRiemannianMetric⟩;
       laplaceBeltrami (𝓡 m) f x) = Δ f x :=
    laplaceBeltrami_eq_laplacian_of_eq (inst := ⟨g₀.toRiemannianMetric⟩) hm hgrad
  have hS :
      (letI : RiemannianBundle (fun y : EuclideanSpace ℝ (Fin m) ↦ TangentSpace (𝓡 m) y) :=
         ⟨g₀.toRiemannianMetric⟩;
       (CovariantDerivative.leviCivitaConnection (𝓡 m)
         (EuclideanSpace ℝ (Fin m))).scalarCurvature x) = 0 := by
    rw [← g₀.scalarCurvature_def,
      ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection _
        hm.symm, scalarCurvature_leviCivitaConnection_model_space]
  rw [conformalLaplacian_def, finrank_euclideanSpace_fin, hΔ, hS, zero_mul, add_zero]

/-- **Stereographic conformal covariance of the conformal Laplacian.** In dimension `n ≠ 2`, let
`t ≥ 0` and `Φ(y) = σ⁻¹((2 / t) (y - b))`. For any `u : Sⁿ → ℝ` that is `C²` at `Φ(x)`,
`aₙ (-Δ (U_{t,b} · (u ∘ Φ)))(x) = U_{t,b}(x) ^ ((n + 2) / (n - 2)) (L u)(Φ(x))`. -/
theorem conformalCoefficient_mul_neg_laplacian_bubble_mul_comp_stereographic'_symm_smul_sub
    (hn : n ≠ 2) (v : sphere (0 : E) 1) {t : ℝ} (ht : 0 ≤ t)
    (b x : EuclideanSpace ℝ (Fin n)) {u : sphere (0 : E) 1 → ℝ}
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ) 2 u ((stereographic' n v).symm ((2 / t) • (x - b)))) :
    conformalCoefficient n *
        -Δ (fun y ↦ bubble t b y * u ((stereographic' n v).symm ((2 / t) • (y - b)))) x =
      bubble t b x ^ (((n : ℝ) + 2) / (n - 2)) *
        conformalLaplacian (𝓡 n) u ((stereographic' n v).symm ((2 / t) • (x - b))) := by
  have hn' : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  rcases ht.eq_or_lt with rfl | ht
  · have hb0 (y : EuclideanSpace ℝ (Fin n)) : bubble 0 b y = 0 := by
      rw [bubble_apply, finrank_euclideanSpace_fin, mul_zero, zero_div,
        Real.zero_rpow (div_ne_zero hn' two_ne_zero)]
    have hfun : (fun y ↦ bubble 0 b y * u ((stereographic' n v).symm ((2 / (0 : ℝ)) • (y - b)))) =
        fun _ ↦ (0 : ℝ) := funext fun y ↦ by rw [hb0, zero_mul]
    rw [hfun, laplacian_const, Pi.zero_apply, neg_zero, mul_zero, hb0,
      Real.zero_rpow (div_ne_zero (by positivity) hn'), zero_mul]
  let g₀ := (riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top
  let hf : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ fun y : EuclideanSpace ℝ (Fin n) ↦
      bubble t b y ^ (4 / ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 2)) :=
    (contDiff_bubble t b (m := ∞)).contMDiff.rpow_const_of_ne
      (fun y ↦ (bubble_pos ht b y).ne') _
  let hf_pos : ∀ y : EuclideanSpace ℝ (Fin n),
      0 < bubble t b y ^ (4 / ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 2)) :=
    fun y ↦ Real.rpow_pos_of_pos (bubble_pos ht b y) _
  set ĝ := g₀.rescale _ hf hf_pos
  let Φ : EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1 :=
    (stereographic' n v).symm ∘ fun y ↦ (2 / t) • (y - b)
  have hΦ : ContMDiff (𝓡 n) (𝓡 n) ∞ Φ :=
    (isSmoothEmbedding_stereographic'_symm (k := ∞) v).contMDiff.comp
      (((contDiff_id.sub contDiff_const).const_smul (2 / t)).contMDiff)
  have huΦ : ContMDiffAt (𝓡 n) 𝓘(ℝ) 2 (u ∘ Φ) x := hu.comp x (hΦ.of_le (by simp)).contMDiffAt
  obtain ⟨w, hw, -, hw_eq⟩ := huΦ.contDiffAt.exists_contDiff_eventuallyEq_of_finiteDimensional 2
  have hiso := isLocalRiemannianIsometry_stereographic'_symm_smul_sub hn v ht b
  have hiso_L :
      (letI : RiemannianBundle (fun y : EuclideanSpace ℝ (Fin n) ↦ TangentSpace (𝓡 n) y) :=
         ⟨ĝ.toRiemannianMetric⟩;
       conformalLaplacian (𝓡 n) w x) = conformalLaplacian (𝓡 n) u (Φ x) := by
    have hev_wm :
        (w ∘ WithMetric.ofWithMetric : WithMetric ĝ → ℝ) =ᶠ[𝓝 (WithMetric.toWithMetric ĝ x)]
          u ∘ (Φ ∘ WithMetric.ofWithMetric) :=
      WithMetric.continuous_ofWithMetric.continuousAt.eventually hw_eq
    rw [← conformalLaplacian_comp_ofWithMetric ĝ hw.contMDiff.contMDiffAt,
      conformalLaplacian_congr_of_eventuallyEq
        (hw.contMDiff.comp WithMetric.contMDiff_ofWithMetric).contMDiffAt
        (ContMDiffAt.comp (WithMetric.toWithMetric ĝ x) hu
          (hiso.contMDiff.of_le (by simp)).contMDiffAt) hev_wm,
      conformalLaplacian_def, conformalLaplacian_def,
      hiso.laplaceBeltrami_comp (x := WithMetric.toWithMetric ĝ x) hu,
      ← hiso.scalarCurvature_map (WithMetric.toWithMetric ĝ x)]
    rfl
  have hresc := conformalLaplacian_rescale g₀ (by simpa using hn) (bubble_pos ht b)
    (hf := hf) (hf_pos := hf_pos) (hv := hw.contMDiff) x
  have heq_prod : (bubble t b * w : EuclideanSpace ℝ (Fin n) → ℝ) =ᶠ[𝓝 x]
      fun y ↦ bubble t b y * u (Φ y) :=
    Filter.EventuallyEq.rfl.mul hw_eq
  rw [hiso_L, conformalLaplacian_euclideanSpace (f := bubble t b * w)
      ((contDiff_bubble t b (m := 2)).mul hw) x,
    (laplacian_congr_nhds heq_prod).eq_of_nhds, finrank_euclideanSpace_fin, neg_div,
    Real.rpow_neg (bubble_pos ht b x).le] at hresc
  exact (inv_mul_eq_iff_eq_mul₀ (Real.rpow_pos_of_pos (bubble_pos ht b x) _).ne').mp hresc.symm

end StereographicCovariance

section YamabeQuotient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **Unit-norm constant on `Sⁿ`.** In dimension `n ≠ 0, 2`, the constant `|Sⁿ| ^ (-1 / pₙ)` has
unit `L^{pₙ}` norm with respect to the Riemannian volume of the unit sphere. -/
theorem integral_abs_rpow_criticalExponent_roundSphereVolume_rpow_neg_inv
    [LindelofSpace (sphere (0 : E) 1)]
    [MeasurableSpace (sphere (0 : E) 1)] [BorelSpace (sphere (0 : E) 1)]
    (hn₀ : n ≠ 0) (hn₂ : n ≠ 2) :
    ∫ _ : sphere (0 : E) 1,
        |roundSphereVolume n ^ (-(1 / criticalExponent n))| ^ criticalExponent n
        ∂riemannianVolume (𝓡 n) (sphere (0 : E) 1) = 1 := by
  have : FiniteDimensional ℝ E :=
    Module.finite_of_finrank_pos ((Fact.out : finrank ℝ E = n + 1) ▸ Nat.succ_pos n)
  have hp : criticalExponent n ≠ 0 := by
    rw [criticalExponent_def]
    exact div_ne_zero (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hn₀))
      (sub_ne_zero.mpr (by exact_mod_cast hn₂))
  rw [integral_const, smul_eq_mul, ← riemannianTotalVolume_def, riemannianTotalVolume_sphere,
    abs_of_pos (Real.rpow_pos_of_pos (roundSphereVolume_pos n) _),
    ← Real.rpow_mul (roundSphereVolume_pos n).le, neg_mul, one_div_mul_cancel hp,
    Real.rpow_neg_one, mul_inv_cancel₀ (roundSphereVolume_pos n).ne']

/-- **The Yamabe quotient of `1` on the unit round sphere is `Y(Sⁿ)`.** This holds in every
dimension `n ≥ 0`. -/
@[simp 1100]
theorem yamabeQuotient_sphere_one
    [SigmaCompactSpace (sphere (0 : E) 1)]
    [MeasurableSpace (sphere (0 : E) 1)] [BorelSpace (sphere (0 : E) 1)] :
    yamabeQuotient (𝓡 n) (fun _ : sphere (0 : E) 1 ↦ (1 : ℝ)) = sphereYamabeConstant n := by
  have : FiniteDimensional ℝ E :=
    Module.finite_of_finrank_pos ((Fact.out : finrank ℝ E = n + 1) ▸ Nat.succ_pos n)
  rw [yamabeQuotient_one, finrank_euclideanSpace_fin]
  simp only [scalarCurvature_sphere, integral_const, smul_eq_mul, ← riemannianTotalVolume_def,
    riemannianTotalVolume_sphere, mul_comm (roundSphereVolume n), sphereYamabeConstant_eq_div]

/-- **The Yamabe quotient of any nonzero constant on `Sⁿ` (`n ≠ 2`) is `Y(Sⁿ)`.** -/
theorem yamabeQuotient_sphere_const
    [SigmaCompactSpace (sphere (0 : E) 1)]
    [MeasurableSpace (sphere (0 : E) 1)] [BorelSpace (sphere (0 : E) 1)]
    (hn : n ≠ 2) {c : ℝ} (hc : c ≠ 0) :
    yamabeQuotient (𝓡 n) (fun _ : sphere (0 : E) 1 ↦ c) = sphereYamabeConstant n := by
  rcases lt_or_ge 2 n with hn' | hn'
  · have hc1 : (fun _ : sphere (0 : E) 1 ↦ c) = c • fun _ ↦ (1 : ℝ) := by
      ext
      simp
    rw [hc1, yamabeQuotient_smul (by simpa using hn') hc, yamabeQuotient_sphere_one]
  · interval_cases n
    · simp [yamabeQuotient_def, mgradient_const, sphereYamabeConstant_def]
    · simp [yamabeQuotient_def, mgradient_const, sphereYamabeConstant_def]
    · exact absurd rfl hn

/-- **Radius invariance of the Yamabe quotient on the round sphere.** For any radius `r > 0` and
any function `u : Sⁿ → ℝ`, the Yamabe quotient of `u` for the round metric of radius `r` equals its
Yamabe quotient on the unit sphere, in every dimension `n ≥ 0`. -/
theorem yamabeQuotient_sphereRoundMetricOfRadius
    [SigmaCompactSpace (sphere (0 : E) 1)]
    [MeasurableSpace (sphere (0 : E) 1)] [BorelSpace (sphere (0 : E) 1)]
    {r : ℝ} (hr : 0 < r) (u : sphere (0 : E) 1 → ℝ) :
    (letI : RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
       ⟨(sphereRoundMetricOfRadius r hr).toRiemannianMetric⟩;
     letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
       (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
       instIsContinuousRiemannianBundle
         (sphereRoundMetricOfRadius r hr).toContinuousRiemannianMetric;
     yamabeQuotient (𝓡 n) u) =
      yamabeQuotient (𝓡 n) u := by
  rw [sphereRoundMetricOfRadius_def,
    ContMDiffRiemannianMetric.yamabeQuotient_rescale_const _ (pow_pos hr 2) u,
    ((sphereRoundMetric (E := E) (n := n)).ofLE le_top).yamabeQuotient_eq_of_riemannianBundle_eq
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _).symm u]

/-- **The Yamabe quotient of `1` on the round sphere of radius `r > 0` is `Y(Sⁿ)`.** -/
@[simp 1100]
theorem yamabeQuotient_sphereRoundMetricOfRadius_one
    [SigmaCompactSpace (sphere (0 : E) 1)]
    [MeasurableSpace (sphere (0 : E) 1)] [BorelSpace (sphere (0 : E) 1)]
    {r : ℝ} (hr : 0 < r) :
    (letI : RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
       ⟨(sphereRoundMetricOfRadius r hr).toRiemannianMetric⟩;
     letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
       (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
       instIsContinuousRiemannianBundle
         (sphereRoundMetricOfRadius r hr).toContinuousRiemannianMetric;
     yamabeQuotient (𝓡 n) (fun _ : sphere (0 : E) 1 ↦ (1 : ℝ))) =
      sphereYamabeConstant n := by
  rw [yamabeQuotient_sphereRoundMetricOfRadius hr, yamabeQuotient_sphere_one]

end YamabeQuotient

end TauCeti.Yamabe
