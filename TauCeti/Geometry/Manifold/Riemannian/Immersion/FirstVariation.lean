/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.FamilyVariation
public import TauCeti.Geometry.Manifold.Riemannian.Immersion.MeanCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Immersion.Weingarten
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface

/-!
# The first variation of volume of an immersion

Let `Φ t : M → N`, `t ∈ ℝ`, be a jointly smooth family of immersions into a manifold `N` whose
metric is compatible with a torsion-free connection `∇`, and let
`X = ∂_t Φ(t₀, ·)` (`TauCeti.familyVariationField`) be its variation field at `t₀`, a vector
field along `Φ t₀`. This file computes the derivative at `t₀` of the volume of `Φ t`, read as
the relative volume `V(t) = ∫ (J_t - 1) dV_{g_{t₀}}` of the induced metrics `g_t = Φ_t^* h`
(`Bundle.ContMDiffRiemannianMetric.relativeVolume`), whose derivative is already known to be
`∫ ∂_t J_t dV_{g_{t₀}}` (`Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback`).

* **The variation of the induced metric** (`TauCeti.hasDerivAt_inner_mfderiv_family`):
  `∂_t ⟪dΦ_t v, dΦ_t w⟫ = ⟪∇_v X, dΦ w⟫ + ⟪dΦ v, ∇_w X⟫` at `t₀`, where `∇_v X` is covariant
  differentiation along `Φ t₀` (`CovariantDerivative.alongMap`). Through a curve `c` with velocity
  `v`, `dΦ_t v` is the velocity of `s ↦ Φ t (c s)`; the symmetry lemma for the parametrized
  surface `(t, s) ↦ Φ t (c s)` (`CovariantDerivative.alongCurve_curveVelocity_comm`) turns the
  `t`-derivative of `dΦ_t v` into `∇_v X` (`TauCeti.alongCurve_mfderiv_family`), and metric
  compatibility along `t ↦ Φ t x` gives the product rule.
* **The variation of the relative volume density**: the variation `½ tr_{g_{t₀}} ∂_t g_t` of the
  relative volume density of a family of metrics
  (`Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolumeDensity`) is, for induced metrics,
  `∑ᵢ ⟪∇_{eᵢ} X, dΦ eᵢ⟫` in a `g_{t₀}`-orthonormal basis
  (`Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolumeDensity_pullback_family`).
* **Normal variations**: if `X` is normal to `Φ t₀`, the pointwise Weingarten equation
  `⟪∇_v X, dΦ w⟫ = -⟪B(v, w), X⟫` (`TauCeti.inner_alongMap_mfderiv_of_eventually_mem`) turns the
  sum into `-⟪∑ᵢ B(eᵢ, eᵢ), X⟫ = -m ⟪H, X⟫`, `m = dim M`, with `H` the mean curvature vector
  (`Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolumeDensity_pullback_family_of_normal`).
  Integrating gives the **first variation formula** `δVol = -m ∫ ⟪H, X⟫ dV` for normal
  variations of a compact boundaryless immersion
  (`Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback_of_normal`) and for
  compactly supported normal variations of a noncompact one
  (`Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback_of_isCompact_of_normal`).
  In particular a minimal immersion, `H = 0`, is stationary for these variations
  (`Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback_of_normal_of_minimal` and
  its compactly supported analogue
  `ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback_of_isCompact_of_normal_of_minimal`).

The metric of `M` used for the mean curvature vector is an arbitrary instance, assumed to be the
metric induced by `Φ t₀`, and the metric `h` of `N` that is pulled back is assumed to be the
inner product of the instance on `TN` with which `∇` is compatible.

## Main results

* `TauCeti.hasDerivAt_inner_mfderiv_family`: the variation of the induced metric.
* `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolumeDensity_pullback_family`,
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolumeDensity_pullback_family_of_normal`:
  the pointwise first variation for a family of immersions, and for a normal variation.
* `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback_of_normal`,
  `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback_of_isCompact_of_normal`:
  the first variation of volume `-m ∫ ⟪H, X⟫ dV` for normal variations.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8
  (the Weingarten equation and the mean curvature vector).
-/

public section

open Bundle Manifold Filter Function
open TauCeti.Manifold
open scoped ContDiff Manifold Topology InnerProductSpace

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {Φ : ℝ → M → N} {t₀ : ℝ} {x : M}

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-! ### The variation of the induced metric -/

variable [FiniteDimensional ℝ F] {cov : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)}

/-- **The `t`-derivative of `dΦ_t v`.** For a family which is `C²` at `(t₀, x)`, with `x` an
interior point, and a torsion-free connection on `N`, the covariant derivative of
`t ↦ dΦ_t v` along `t ↦ Φ t x` at `t₀` is the covariant derivative `∇_v X` of the variation field
along `Φ t₀`. -/
theorem alongCurve_mfderiv_family (ht : cov.IsTorsionFree)
    (hΦ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x)) (hx : I.IsInteriorPoint x)
    (v : TangentSpace I x) :
    CovariantDerivative.alongCurve cov (fun t ↦ Φ t x) (fun t ↦ mfderiv I J (Φ t) x v) t₀ =
      cov.alongMap I (Φ t₀) (familyVariationField J Φ t₀) x v := by
  obtain ⟨c, hc0, hc, hcv⟩ := exists_contMDiffAt_curveVelocity_eq (n := 2) x hx v (0 : ℝ)
  subst hc0 hcv
  have hc1 : MDifferentiableAt 𝓘(ℝ, ℝ) I c 0 := hc.mdifferentiableAt (by norm_num)
  have hσ := contMDiffAt_surface_family hΦ hc
  have hfield : CovariantDerivative.alongCurve cov (fun t ↦ Φ t (c 0))
      (fun t ↦ mfderiv I J (Φ t) (c 0) (curveVelocity I c 0)) t₀ =
      CovariantDerivative.alongCurve cov (fun t ↦ Φ t (c 0))
      (fun t ↦ curveVelocity J (fun s ↦ Φ t (c s)) 0) t₀ :=
    CovariantDerivative.alongCurve_congr cov _ _
      (eventually_mfderiv_family_apply_curveVelocity hΦ two_ne_zero hc1)
  rw [hfield]
  have : IsManifold J (minSmoothness ℝ 2) N := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hcomm := CovariantDerivative.alongCurve_curveVelocity_comm
    (f := fun t s ↦ Φ t (c s)) (u := t₀) (v := (0 : ℝ)) cov ht
    (by rwa [minSmoothness_of_isRCLikeNormedField])
  rw [← hcomm]
  have hX := (contMDiffAt_familyVariationField (Φ := Φ) (t₀ := t₀) (x := c 0) hΦ).mdifferentiableAt
    (by norm_num)
  have h := (CovariantDerivative.alongMap_curveVelocity (Φ t₀) cov (familyVariationField J Φ t₀)
    hc1 hX).symm
  simp only [familyVariationField_def] at h ⊢
  exact h

variable [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

/-- **The first variation of the induced metric.** For a family of maps `Φ t : M → N` which is
`C²` at `(t₀, x)`, with `x` an interior point, into a manifold with a torsion-free
metric-compatible connection, `∂_t ⟪dΦ_t v, dΦ_t w⟫ = ⟪∇_v X, dΦ w⟫ + ⟪dΦ v, ∇_w X⟫` at `t₀`, where
`X = ∂_t Φ(t₀, ·)` is the variation field and `∇` differentiates along `Φ t₀`. -/
theorem hasDerivAt_inner_mfderiv_family
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (ht : cov.IsTorsionFree)
    (hΦ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x)) (hx : I.IsInteriorPoint x)
    (v w : TangentSpace I x) :
    HasDerivAt (fun t ↦ ⟪mfderiv I J (Φ t) x v, mfderiv I J (Φ t) x w⟫_ℝ)
      (⟪cov.alongMap I (Φ t₀) (familyVariationField J Φ t₀) x v, mfderiv I J (Φ t₀) x w⟫_ℝ +
        ⟪mfderiv I J (Φ t₀) x v, cov.alongMap I (Φ t₀) (familyVariationField J Φ t₀) x w⟫_ℝ)
      t₀ := by
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) J (fun t ↦ Φ t x) t₀ :=
    hΦ.curry_left.mdifferentiableAt (by norm_num)
  have hbase := FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (Φ t₀ x)
  have h := hcov.hasDerivAt_inner_alongCurve hγ
    (differentiableAt_sectionCoord_mfderiv_family hΦ hx v _ hbase)
    (differentiableAt_sectionCoord_mfderiv_family hΦ hx w _ hbase)
  rwa [alongCurve_mfderiv_family ht hΦ hx, alongCurve_mfderiv_family ht hΦ hx] at h

end TauCeti

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 2 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {cov : CovariantDerivative J F (fun y : N ↦ TangentSpace J y)}
  {Φ : ℝ → M → N} {t₀ : ℝ} {x : M}
  {n : ℕ∞ω} (h : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))

/-- `2 ≤ n + 1` when `1 ≤ n`, so a `C^(n+1)` family with `n ≥ 1` is `C²`. -/
private theorem two_le_add_one (hn : 1 ≤ n) : (2 : ℕ∞ω) ≤ n + 1 :=
  calc (2 : ℕ∞ω) = 1 + 1 := by norm_num
    _ ≤ n + 1 := by gcongr

/-- **The first variation of the relative volume density of a family of immersions.** Let
`Φ t : M → N` be a jointly `C^(n+1)` family of immersions, `n ≥ 1`, into a manifold whose metric
`h` is the inner product of a torsion-free metric-compatible connection, and let `x` be an interior
point. In a basis `(eᵢ)` of `T_x M` orthonormal for `Φ_{t₀}^* h`, the relative volume density of
`Φ_t^* h` with respect to `Φ_{t₀}^* h` has derivative `∑ᵢ ⟪∇_{eᵢ} X, dΦ_{t₀} eᵢ⟫` at `t₀`, where
`X = ∂_t Φ(t₀, ·)` is the variation field. -/
theorem hasDerivAt_relativeVolumeDensity_pullback_family
    (hh : ∀ y (v w : TangentSpace J y), h.inner y v w = ⟪v, w⟫_ℝ)
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (ht : cov.IsTorsionFree) (hn : 1 ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) (hx : I.IsInteriorPoint x)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ (TangentSpace I x))
    (hb : ∀ i j, ⟪mfderiv I J (Φ t₀) x (b i), mfderiv I J (Φ t₀) x (b j)⟫_ℝ =
      if i = j then 1 else 0) :
    HasDerivAt (fun t ↦ ContMDiffRiemannianMetric.relativeVolumeDensity
        (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
        (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)) x)
      (∑ i, ⟪cov.alongMap I (Φ t₀) (familyVariationField J Φ t₀) x (b i),
        mfderiv I J (Φ t₀) x (b i)⟫_ℝ) t₀ := by
  have hΦ₂ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x) :=
    (hΦ _).of_le (two_le_add_one hn)
  have hd := hasDerivAt_relativeVolumeDensity
    (g := fun t ↦ h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)) (t₀ := t₀) b
    (by simpa only [ContMDiffRiemannianMetric.pullback_inner, hh] using hb)
    (fun v w ↦ by
      simpa only [ContMDiffRiemannianMetric.pullback_inner, hh] using
        hasDerivAt_inner_mfderiv_family hcov ht hΦ₂ hx v w)
  convert hd using 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm (mfderiv I J (Φ t₀) x (b i))]
  ring

/-- **The first variation of the relative volume density along a normal variation.** If moreover
the variation field `X` is normal to `Φ t₀` near `x` and the metric of `M` agrees at `x` with the
metric induced by `Φ t₀`, the relative volume density of `Φ_t^* h` with respect to `Φ_{t₀}^* h` has
derivative `-m ⟪H, X⟫` at `t₀`, where `m = dim M` and `H` is the mean curvature vector of
`Φ t₀`. -/
theorem hasDerivAt_relativeVolumeDensity_pullback_family_of_normal
    [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
    (hh : ∀ y (v w : TangentSpace J y), h.inner y v w = ⟪v, w⟫_ℝ)
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (ht : cov.IsTorsionFree) (hn : 1 ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x)) (hx : I.IsInteriorPoint x)
    (hM : ∀ v w : TangentSpace I x,
      ⟪v, w⟫_ℝ = ⟪mfderiv I J (Φ t₀) x v, mfderiv I J (Φ t₀) x w⟫_ℝ)
    (hX : ∀ᶠ y in 𝓝 x, familyVariationField J Φ t₀ y ∈ orthogonalNormalSpace I J (Φ t₀) y) :
    HasDerivAt (fun t ↦ ContMDiffRiemannianMetric.relativeVolumeDensity
        (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
        (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)) x)
      (-(Module.finrank ℝ E : ℝ) *
        ⟪immersionMeanCurvatureVector (I := I) cov (Φ t₀) x, familyVariationField J Φ t₀ x⟫_ℝ)
      t₀ := by
  have hΦ₂ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x) :=
    (hΦ _).of_le (two_le_add_one hn)
  have hf : ContMDiffAt I J 2 (Φ t₀) x := hΦ₂.curry_right
  let e := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hb : ∀ i j, ⟪mfderiv I J (Φ t₀) x (e.toBasis i), mfderiv I J (Φ t₀) x (e.toBasis j)⟫_ℝ =
      if i = j then 1 else 0 := fun i j ↦ by
    rw [OrthonormalBasis.coe_toBasis, ← hM]
    exact orthonormal_iff_ite.1 e.orthonormal i j
  convert hasDerivAt_relativeVolumeDensity_pullback_family h hh hcov ht hn hΦ hinj hx
    e.toBasis hb using 1
  simp only [OrthonormalBasis.coe_toBasis]
  rw [Finset.sum_congr rfl fun i _ ↦ inner_alongMap_mfderiv_of_eventually_mem hcov hf
    (mdifferentiableAt_sectionCoord_familyVariationField hΦ₂) hX (e i) (e i),
    immersionMeanCurvatureVector_eq_sum e, Finset.sum_neg_distrib, ← sum_inner,
    real_inner_smul_left]
  by_cases hm : (Module.finrank ℝ E : ℝ) = 0
  · have : IsEmpty (Fin (Module.finrank ℝ (TangentSpace I x))) := by
      rw [Fin.isEmpty_iff]
      exact_mod_cast hm
    simp [hm]
  · field_simp

/-- **The first variation of volume along a normal variation, compactly supported case.** Let
`Φ t : M → N` be a jointly `C^(n+1)` family of immersions, `n ≥ 1`, of a boundaryless manifold
`M`, not necessarily compact, into a manifold whose metric `h` is the inner product of a
torsion-free metric-compatible connection, with `Φ t = Φ t₀` outside a compact set `K` for `t`
near `t₀`. Suppose that the metric of `M` is the one induced by `Φ t₀` and that the variation field
`X = ∂_t Φ(t₀, ·)` is normal to `Φ t₀`. Then the relative volume of `Φ_t^* h` with respect to
`Φ_{t₀}^* h` has derivative `-m ∫ ⟪H, X⟫ dV` at `t₀`, where `m = dim M`, `H` is the mean
curvature vector of `Φ t₀` and `dV` is the Riemannian volume of `Φ_{t₀}^* h`. -/
theorem hasDerivAt_relativeVolume_pullback_of_isCompact_of_normal
    [LindelofSpace M] [T2Space M] [BoundarylessManifold I M]
    [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
    (hh : ∀ y (v w : TangentSpace J y), h.inner y v w = ⟪v, w⟫_ℝ)
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (ht : cov.IsTorsionFree) (hn : 1 ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x))
    (hM : ∀ y (v w : TangentSpace I y),
      ⟪v, w⟫_ℝ = ⟪mfderiv I J (Φ t₀) y v, mfderiv I J (Φ t₀) y w⟫_ℝ)
    (hX : ∀ y, familyVariationField J Φ t₀ y ∈ orthogonalNormalSpace I J (Φ t₀) y)
    {K : Set M} (hK : IsCompact K) (hΦK : ∀ᶠ t in 𝓝 t₀, ∀ y ∉ K, Φ t y = Φ t₀ y) :
    HasDerivAt (fun t ↦ ContMDiffRiemannianMetric.relativeVolume
        (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
        (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)))
      (-(Module.finrank ℝ E : ℝ) * ∫ y, ⟪immersionMeanCurvatureVector (I := I) cov (Φ t₀)
          y.ofWithMetric, familyVariationField J Φ t₀ y.ofWithMetric⟫_ℝ
        ∂riemannianVolume I (WithMetric (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀))
          (hinj t₀)))) t₀ := by
  convert ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback_of_isCompact h hn hΦ
    hinj hK hΦK using 1
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext y
  exact ((hasDerivAt_relativeVolumeDensity_pullback_family_of_normal h hh hcov ht hn hΦ hinj
    BoundarylessManifold.isInteriorPoint (hM _) (Eventually.of_forall hX)).deriv).symm

/-- **The first variation of volume along a normal variation, compact case.** Let `Φ t : M → N`
be a jointly `C^(n+1)` family of immersions, `n ≥ 1`, of a compact boundaryless manifold `M` into
a manifold whose metric `h` is the inner product of a torsion-free metric-compatible connection.
Suppose that the metric of `M` is the one induced by `Φ t₀` and that the variation field
`X = ∂_t Φ(t₀, ·)` is normal to `Φ t₀`. Then the relative volume of `Φ_t^* h` with respect to any
fixed metric `g₀` has derivative `-m ∫ ⟪H, X⟫ dV` at `t₀`, where `m = dim M`, `H` is the mean
curvature vector of `Φ t₀` and `dV` is the Riemannian volume of `Φ_{t₀}^* h`. -/
theorem hasDerivAt_relativeVolume_pullback_of_normal [CompactSpace M] [BoundarylessManifold I M]
    [RiemannianBundle (fun y : M ↦ TangentSpace I y)] {n₀ : ℕ∞ω}
    (g₀ : ContMDiffRiemannianMetric I n₀ E (fun x : M ↦ TangentSpace I x))
    (hh : ∀ y (v w : TangentSpace J y), h.inner y v w = ⟪v, w⟫_ℝ)
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (ht : cov.IsTorsionFree) (hn : 1 ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x))
    (hM : ∀ y (v w : TangentSpace I y),
      ⟪v, w⟫_ℝ = ⟪mfderiv I J (Φ t₀) y v, mfderiv I J (Φ t₀) y w⟫_ℝ)
    (hX : ∀ y, familyVariationField J Φ t₀ y ∈ orthogonalNormalSpace I J (Φ t₀) y) :
    HasDerivAt (fun t ↦ ContMDiffRiemannianMetric.relativeVolume g₀
        (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t)))
      (-(Module.finrank ℝ E : ℝ) * ∫ y, ⟪immersionMeanCurvatureVector (I := I) cov (Φ t₀)
          y.ofWithMetric, familyVariationField J Φ t₀ y.ofWithMetric⟫_ℝ
        ∂riemannianVolume I (WithMetric (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀))
          (hinj t₀)))) t₀ := by
  convert ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback (g₀ := g₀) h hn hΦ
    hinj t₀ using 1
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext y
  exact ((hasDerivAt_relativeVolumeDensity_pullback_family_of_normal h hh hcov ht hn hΦ hinj
    BoundarylessManifold.isInteriorPoint (hM _) (Eventually.of_forall hX)).deriv).symm

/-- **Minimal immersions are stationary for normal variations.** Under the hypotheses of
`Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback_of_normal`, if the mean
curvature vector of `Φ t₀` vanishes, the relative volume of `Φ_t^* h` has derivative `0` at `t₀`. -/
theorem hasDerivAt_relativeVolume_pullback_of_normal_of_minimal [CompactSpace M]
    [BoundarylessManifold I M] [RiemannianBundle (fun y : M ↦ TangentSpace I y)] {n₀ : ℕ∞ω}
    (g₀ : ContMDiffRiemannianMetric I n₀ E (fun x : M ↦ TangentSpace I x))
    (hh : ∀ y (v w : TangentSpace J y), h.inner y v w = ⟪v, w⟫_ℝ)
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (ht : cov.IsTorsionFree) (hn : 1 ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x))
    (hM : ∀ y (v w : TangentSpace I y),
      ⟪v, w⟫_ℝ = ⟪mfderiv I J (Φ t₀) y v, mfderiv I J (Φ t₀) y w⟫_ℝ)
    (hX : ∀ y, familyVariationField J Φ t₀ y ∈ orthogonalNormalSpace I J (Φ t₀) y)
    (hH : ∀ y, immersionMeanCurvatureVector (I := I) cov (Φ t₀) y = 0) :
    HasDerivAt (fun t ↦ ContMDiffRiemannianMetric.relativeVolume g₀
        (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t))) 0 t₀ := by
  simpa [hH] using hasDerivAt_relativeVolume_pullback_of_normal h g₀ hh hcov ht hn hΦ hinj hM hX

/-- **Minimal immersions are stationary for compactly supported normal variations.** Under the
hypotheses of
`Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolume_pullback_of_isCompact_of_normal`, if
the mean curvature vector of `Φ t₀` vanishes, the relative volume of `Φ_t^* h` with respect to
`Φ_{t₀}^* h` has derivative `0` at `t₀`. -/
theorem hasDerivAt_relativeVolume_pullback_of_isCompact_of_normal_of_minimal
    [LindelofSpace M] [T2Space M] [BoundarylessManifold I M]
    [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
    (hh : ∀ y (v w : TangentSpace J y), h.inner y v w = ⟪v, w⟫_ℝ)
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    (ht : cov.IsTorsionFree) (hn : 1 ≤ n)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) J (n + 1) (uncurry Φ))
    (hinj : ∀ t x, Injective (mfderiv I J (Φ t) x))
    (hM : ∀ y (v w : TangentSpace I y),
      ⟪v, w⟫_ℝ = ⟪mfderiv I J (Φ t₀) y v, mfderiv I J (Φ t₀) y w⟫_ℝ)
    (hX : ∀ y, familyVariationField J Φ t₀ y ∈ orthogonalNormalSpace I J (Φ t₀) y)
    {K : Set M} (hK : IsCompact K) (hΦK : ∀ᶠ t in 𝓝 t₀, ∀ y ∉ K, Φ t y = Φ t₀ y)
    (hH : ∀ y, immersionMeanCurvatureVector (I := I) cov (Φ t₀) y = 0) :
    HasDerivAt (fun t ↦ ContMDiffRiemannianMetric.relativeVolume
        (h.pullback (Φ t₀) (hΦ.curry_right (x := t₀)) (hinj t₀))
        (h.pullback (Φ t) (hΦ.curry_right (x := t)) (hinj t))) 0 t₀ := by
  simpa [hH] using
    hasDerivAt_relativeVolume_pullback_of_isCompact_of_normal h hh hcov ht hn hΦ hinj hM hX hK hΦK

end Bundle.ContMDiffRiemannianMetric
