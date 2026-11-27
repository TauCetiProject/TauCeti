/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.Matrix
public import TauCeti.Geometry.Manifold.Riemannian.Immersion.MeanCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Immersion.Weingarten
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface
import Mathlib.Analysis.SpecialFunctions.Sqrt

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
* **The variation of the relative volume density**
  (`Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolumeDensity`): if the inner products
  of `g_t` at `x` have parameter derivative `k`, then `∂_t J_t = ½ ∑ᵢ k(eᵢ, eᵢ)` at `t₀` in a
  `g_{t₀}`-orthonormal basis, by Jacobi's formula for the Gram determinant. For induced metrics
  this is `∑ᵢ ⟪∇_{eᵢ} X, dΦ eᵢ⟫` (`TauCeti.hasDerivAt_relativeVolumeDensity_pullback_family`).
* **Normal variations**: if `X` is normal to `Φ t₀`, the pointwise Weingarten equation
  `⟪∇_v X, dΦ w⟫ = -⟪B(v, w), X⟫` (`TauCeti.inner_alongMap_mfderiv_of_eventually_mem`) turns the
  sum into `-⟪∑ᵢ B(eᵢ, eᵢ), X⟫ = -m ⟪H, X⟫`, `m = dim M`, with `H` the mean curvature vector
  (`TauCeti.hasDerivAt_relativeVolumeDensity_pullback_family_of_normal`). Integrating gives the
  **first variation formula** `δVol = -m ∫ ⟪H, X⟫ dV` for normal variations of a compact
  boundaryless immersion (`TauCeti.hasDerivAt_relativeVolume_pullback_of_normal`) and for
  compactly supported normal variations of a noncompact one
  (`TauCeti.hasDerivAt_relativeVolume_pullback_of_isCompact_of_normal`). In particular a minimal
  immersion, `H = 0`, is stationary for these variations
  (`TauCeti.hasDerivAt_relativeVolume_pullback_of_normal_of_minimal`).

The metric of `M` used for the mean curvature vector is an arbitrary instance, assumed to be the
metric induced by `Φ t₀`, and the metric `h` of `N` that is pulled back is assumed to be the
inner product of the instance on `TN` with which `∇` is compatible.

## Main definitions

* `TauCeti.familyVariationField`: the variation field `X = ∂_t Φ(t₀, ·)` of a family of maps.

## Main results

* `TauCeti.hasDerivAt_inner_mfderiv_family`: the variation of the induced metric.
* `Bundle.ContMDiffRiemannianMetric.hasDerivAt_relativeVolumeDensity`: the variation of the
  relative volume density of a family of metrics.
* `TauCeti.hasDerivAt_relativeVolumeDensity_pullback_family`,
  `TauCeti.hasDerivAt_relativeVolumeDensity_pullback_family_of_normal`: the pointwise first
  variation for a family of immersions, and for a normal variation.
* `TauCeti.hasDerivAt_relativeVolume_pullback_of_normal`,
  `TauCeti.hasDerivAt_relativeVolume_pullback_of_isCompact_of_normal`: the first variation of
  volume `-m ∫ ⟪H, X⟫ dV` for normal variations.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8
  (the Weingarten equation and the mean curvature vector).
-/

public section

open Bundle Manifold Filter Function
open TauCeti.Manifold
open scoped ContDiff Manifold Topology InnerProductSpace

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n : ℕ∞ω}

/-- **The variation of the relative volume density.** Let `g_t` be a family of metrics whose inner
products at `x` have parameter derivative `h` at `t₀`. Then the relative volume density of `g_t`
with respect to `g_{t₀}` has derivative `½ ∑ᵢ h(eᵢ, eᵢ)` at `t₀`, for every `g_{t₀}`-orthonormal
basis `(eᵢ)` of `T_x M`: half the `g_{t₀}`-trace of `h`. -/
theorem hasDerivAt_relativeVolumeDensity {g : ℝ → ContMDiffRiemannianMetric I n E
    (fun x : M ↦ TangentSpace I x)} {x : M} {t₀ : ℝ}
    {h : TangentSpace I x → TangentSpace I x → ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I x))
    (hb : ∀ i j, (g t₀).inner x (b i) (b j) = if i = j then 1 else 0)
    (hg : ∀ v w, HasDerivAt (fun t ↦ (g t).inner x v w) (h v w) t₀) :
    HasDerivAt (fun t ↦ relativeVolumeDensity (g t₀) (g t) x) (2⁻¹ * ∑ i, h (b i) (b i)) t₀ := by
  let G : ℝ → Matrix ι ι ℝ := fun t ↦ Matrix.of fun i j ↦ (g t).inner x (b i) (b j)
  have hG : G t₀ = 1 := by
    ext i j
    simp [G, hb, Matrix.one_apply]
  have hdet := Matrix.hasDerivAt_det_of_entries (A := G)
    (A' := Matrix.of fun i j ↦ h (b i) (b j)) (fun i j ↦ hg _ _) (by simp [hG])
  have hsqrt := hdet.sqrt (by simp [hG])
  have heq : (fun t ↦ relativeVolumeDensity (g t₀) (g t) x) = fun t ↦ √(G t).det :=
    funext fun t ↦ b.relativeVolumeDensity_eq_sqrt_det_of_orthonormal hb
  rw [heq]
  convert hsqrt using 1
  simp [hG, Matrix.trace]
  ring

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {Φ : ℝ → M → N} {t₀ : ℝ} {x : M}

/-! ### The variation field -/

variable (J Φ t₀) in
/-- The **variation field** `X = ∂_t Φ(t₀, ·)` of a family of maps `Φ t : M → N` at `t₀`: at `y`,
the velocity at `t₀` of the curve `t ↦ Φ t y`. It is a vector field along `Φ t₀`. -/
def familyVariationField (y : M) : TangentSpace J (Φ t₀ y) :=
  curveVelocity J (fun t ↦ Φ t y) t₀

omit [TopologicalSpace M] in
/-- The definition of the variation field. -/
theorem familyVariationField_def (y : M) :
    familyVariationField J Φ t₀ y = curveVelocity J (fun t ↦ Φ t y) t₀ :=
  (rfl)

/-- The velocity of `f ∘ c` is `df` applied to the velocity of `c`. -/
private theorem curveVelocity_map {f : M → N} {c : ℝ → M} {s : ℝ}
    (hf : MDifferentiableAt I J f (c s)) (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c s) :
    curveVelocity J (fun r ↦ f (c r)) s = mfderiv I J f (c s) (curveVelocity I c s) := by
  have h := curveVelocityWithin_map (f := f) (γ := c) (s := Set.univ) hf
    uniqueDiffWithinAt_univ hc.mdifferentiableWithinAt
  rw [curveVelocityWithin_univ, curveVelocityWithin_univ] at h
  exact h

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- The variation field of a family which is `C²` at `(t₀, x)` is `C¹` at `x`, as a section of
the tangent bundle of `N` along `Φ t₀`. -/
theorem contMDiffAt_familyVariationField
    (hΦ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x)) :
    ContMDiffAt I J.tangent 1
      (fun y ↦ (⟨Φ t₀ y, familyVariationField J Φ t₀ y⟩ : TangentBundle J N)) x := by
  have hf : ContMDiffAt (I.prod 𝓘(ℝ)) J 2 (uncurry fun (y : M) (t : ℝ) ↦ Φ t y) (x, t₀) :=
    hΦ.comp (x, t₀) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have hϕ := hf.mfderiv (fun (y : M) (t : ℝ) ↦ Φ t y) (fun _ ↦ t₀) (m := 1) contMDiffAt_const
    (by norm_num)
  have hv : ContMDiffAt I 𝓘(ℝ).tangent 1
      (fun _ : M ↦ (⟨t₀, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ) ℝ)) x := contMDiffAt_const
  have hb : ContMDiffAt I J 1 (fun y ↦ Φ t₀ y) x :=
    (hΦ.comp x (contMDiffAt_const.prodMk contMDiffAt_id)).of_le (by norm_num)
  have := ContMDiffAt.clm_apply_of_inCoordinates hϕ hv hb
  simpa only [familyVariationField, curveVelocity_apply] using this

/-- The variation field of a family which is `C²` at `(t₀, x)` has a differentiable coordinate
reading at `x`. -/
theorem mdifferentiableAt_sectionCoord_familyVariationField
    (hΦ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x)) :
    MDifferentiableAt I 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) (Φ t₀) (familyVariationField J Φ t₀) (Φ t₀ x)) x :=
  mdifferentiableAt_sectionCoord (Φ t₀) _
    ((contMDiffAt_familyVariationField hΦ).mdifferentiableAt (by norm_num))
    (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (Φ t₀ x))

/-- Near `t₀`, the maps `Φ t` of a family which is `C²` at `(t₀, x)` are differentiable at `x`. -/
private theorem eventually_mdifferentiableAt_family
    (hΦ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x)) :
    ∀ᶠ t in 𝓝 t₀, MDifferentiableAt I J (Φ t) x := by
  have hcont : ContinuousAt (fun t : ℝ ↦ (t, x)) t₀ := by fun_prop
  filter_upwards [hcont.eventually ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hΦ)]
    with t ht
  exact (ht.comp x (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by norm_num)

omit [IsManifold I 2 M] [IsManifold J 2 N] in
/-- The parametrized surface `(t, s) ↦ Φ t (c s)` of a family `C²` at `(t₀, c 0)` and a curve
`C²` at `0` is `C²` at `(t₀, 0)`. -/
private theorem contMDiffAt_surface_family {c : ℝ → M}
    (hΦ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, c 0))
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) I 2 c 0) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) J 2 (fun z : ℝ × ℝ ↦ Φ z.1 (c z.2)) (t₀, 0) :=
  hΦ.comp (t₀, (0 : ℝ)) ((contDiffAt_fst.contMDiffAt (n := 2)).prodMk
    (hc.comp (t₀, (0 : ℝ)) contDiffAt_snd.contMDiffAt))

/-- The coordinate reading of `t ↦ dΦ_t v` along `t ↦ Φ t x` is differentiable at `t₀`. -/
private theorem differentiableAt_sectionCoord_mfderiv_family
    (hΦ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x)) (hx : I.IsInteriorPoint x)
    (v : TangentSpace I x) (y : N) (hy : Φ t₀ x ∈ (trivializationAt F (TangentSpace J) y).baseSet) :
    DifferentiableAt ℝ (sectionCoord ℝ (F := F) (fun t ↦ Φ t x)
      (fun t ↦ mfderiv I J (Φ t) x v) y) t₀ := by
  obtain ⟨c, hc0, hc, hcv⟩ := exists_contMDiffAt_curveVelocity_eq (n := 2) x hx v (0 : ℝ)
  subst hc0 hcv
  have hc1 : MDifferentiableAt 𝓘(ℝ, ℝ) I c 0 := hc.mdifferentiableAt (by norm_num)
  have hσ := contMDiffAt_surface_family hΦ hc
  have hd := ContMDiffAt.differentiableAt_sectionCoord_curveVelocity_snd
    (f := fun t s ↦ Φ t (c s)) hσ hy
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [eventually_mdifferentiableAt_family hΦ] with t ht
  simp only [sectionCoord_apply, curveVelocity_map ht hc1]

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
      ((eventually_mdifferentiableAt_family hΦ).mono fun t ht ↦
      (curveVelocity_map ht hc1).symm)
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
  exact (CovariantDerivative.alongMap_curveVelocity (Φ t₀) cov (familyVariationField J Φ t₀)
    hc1 hX).symm

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
    (hΦ.comp t₀ (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by norm_num)
  have hbase := FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (Φ t₀ x)
  have h := hcov.hasDerivAt_inner_alongCurve hγ
    (differentiableAt_sectionCoord_mfderiv_family hΦ hx v _ hbase)
    (differentiableAt_sectionCoord_mfderiv_family hΦ hx w _ hbase)
  rwa [alongCurve_mfderiv_family ht hΦ hx, alongCurve_mfderiv_family ht hΦ hx] at h

/-! ### Normal variations -/

variable [FiniteDimensional ℝ E]

/-- **The Weingarten equation, pointwise.** For a metric-compatible connection, a map `f` which is
`C²` at `x` and a field `ν` along `f` which is normal near `x` with differentiable reading at `x`,
`⟪∇_v ν, df w⟫ = -⟪B_x(v, w), ν⟫`. -/
theorem inner_alongMap_mfderiv_of_eventually_mem
    (hcov : CovariantDerivative.IsMetricCompatible (I := J) (V := fun y : N ↦ TangentSpace J y) cov)
    {f : M → N} (hf : ContMDiffAt I J 2 f x) {ν : Π y : M, TangentSpace J (f y)}
    (hν : MDifferentiableAt I 𝓘(ℝ, F) (sectionCoord ℝ (F := F) f ν (f x)) x)
    (hνn : ∀ᶠ y in 𝓝 x, ν y ∈ orthogonalNormalSpace I J f y) (v w : TangentSpace I x) :
    ⟪cov.alongMap I f ν x v, mfderiv I J f x w⟫_ℝ =
      -⟪immersionSecondFundamentalFormAt cov f x v w, ν x⟫_ℝ := by
  set V : Π y : M, TangentSpace I y := FiberBundle.extend E v
  set W : Π y : M, TangentSpace I y := FiberBundle.extend E w
  have hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E v
  have hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E w
  have hdW : MDifferentiableAt I 𝓘(ℝ, F)
      (sectionCoord ℝ (F := F) f (fun y ↦ mfderiv I J f y (W y)) (f x)) x := by
    have h := hf.contMDiffAt_tangentMap (X := (W x : TangentBundle I M)) (m := 1) (by norm_num)
    exact mdifferentiableAt_sectionCoord f _ ((h.mdifferentiableAt one_ne_zero).comp
      x hW) (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f x))
  have h0 : (fun y ↦ inner ℝ (ν y) (mfderiv I J f y (W y))) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
    hνn.mono fun y hy ↦ inner_coe_orthogonalNormalSpace_mfderiv ⟨_, hy⟩ (W y)
  have hd := hcov.mvfderiv_inner_alongMap (hf.mdifferentiableAt (by norm_num)) hν hdW v
  rw [h0.mvfderiv_eq, mvfderiv_const, zero_apply] at hd
  have hB : immersionSecondFundamentalFormAt cov f x v w =
      immersionSecondFundamentalForm cov f V W x := by
    simpa only [V, W, FiberBundle.extend_apply_self] using
      immersionSecondFundamentalFormAt_apply hf hV hW
  have hνx : ν x ∈ orthogonalNormalSpace I J f x := hνn.self_of_nhds
  rw [hB, inner_immersionSecondFundamentalForm_of_mem V W hνx]
  simp only [V, W, FiberBundle.extend_apply_self] at hd ⊢
  linarith [real_inner_comm (ν x)
    (cov.alongMap I f (fun y ↦ mfderiv I J f y (FiberBundle.extend E w y)) x v)]

section Pullback

variable {n : ℕ∞ω} (h : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))

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
  have hΦ₂ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x) := by
    refine (hΦ (t₀, x)).of_le ?_
    calc (2 : ℕ∞ω) = 1 + 1 := by norm_num
      _ ≤ n + 1 := by gcongr
  have hd := ContMDiffRiemannianMetric.hasDerivAt_relativeVolumeDensity
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
  have hΦ₂ : ContMDiffAt (𝓘(ℝ).prod I) J 2 (uncurry Φ) (t₀, x) := by
    refine (hΦ (t₀, x)).of_le ?_
    calc (2 : ℕ∞ω) = 1 + 1 := by norm_num
      _ ≤ n + 1 := by gcongr
  have hf : ContMDiffAt I J 2 (Φ t₀) x :=
    hΦ₂.comp x (contMDiffAt_const.prodMk contMDiffAt_id)
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
`TauCeti.hasDerivAt_relativeVolume_pullback_of_normal`, if the mean curvature vector of `Φ t₀`
vanishes, the relative volume of `Φ_t^* h` has derivative `0` at `t₀`. -/
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

end Pullback

end TauCeti
