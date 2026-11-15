/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Radial
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Normed.Affine.Isometry.StrictConvex
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Distance
import TauCeti.Topology.EMetricSpace.Component

/-!
# Distance-preserving maps are smooth

Let `f : M → N` preserve the Riemannian distances of two boundaryless Riemannian manifolds, with
`N` complete. The distances may be infinite (`EMetricSpace`), so the manifolds need not be
connected: points in different components are at infinite distance. The theorem of Myers and
Steenrod states that `f` is smooth and that its differential preserves the Riemannian metric; no
regularity of `f` is assumed. Consequently a distance-preserving bijection onto a complete
Riemannian manifold is a smooth Riemannian isometry. Conversely a smooth Riemannian isometry
preserves distances (the `IsometryClass` instance on `TauCeti.RiemannianIsometry`), so on
complete Riemannian manifolds the two notions of isometry agree.

The proof follows Palais. Distance-preserving maps send short radial geodesics to radial
geodesics (`Isometry.apply_riemannianExp_smul`), so the radial map
`A v = log_{f p} (f (exp_p v))` preserves norms and scales along rays. On small balls the
exponential map and the logarithm are Lipschitz with constants arbitrarily close to one, so near
the origin `A` changes distances by factors arbitrarily close to one; scaling along rays then
shows that `A` preserves distances on a ball. Hence `A` agrees there with a linear isometry `L`
(`TauCeti.exists_linearIsometry_eqOn_ball`), and `f = exp_{f p} ∘ L ∘ log_p` near `p`.

The normal-coordinate steps use the metric form of the radial lemmas of `Isometry/Radial.lean`, so
they are stated for metric spaces, where all distances are finite. Smoothness and differentials
are local, so the main theorems pass to extended distances by restricting `f` to the open
finite-distance components `Metric.eball p ∞` and `Metric.eball (f p) ∞`, which are metric spaces
and carry the restricted Riemannian metrics.

## Main results

* `Isometry.exists_linearIsometry_apply_riemannianExp_eq`: `f (exp_p v) = exp_{f p} (L v)` on a
  normal ball, for a linear isometry `L : T_p M →ₗᵢ[ℝ] T_{f p} N`.
* `Isometry.contMDiff`: a distance-preserving map into a complete manifold is smooth.
* `Isometry.inner_mfderiv`, `Isometry.norm_mfderiv`: its differential preserves inner products
  and norms.
* `IsometryEquiv.toRiemannianIsometry`: a distance-preserving bijection onto a complete
  Riemannian manifold as a smooth Riemannian isometry. With the `IsometryClass` coercion back to
  `M ≃ᵢ N` it is a bijection (`IsometryEquiv.toIsometryEquiv_toRiemannianIsometry`,
  `TauCeti.RiemannianIsometry.toRiemannianIsometry_toIsometryEquiv`), compatible with
  identities, inverses and composites.
* `TauCeti.RiemannianIsometry.isometryEquivMulEquiv`: on a complete manifold, the group of smooth
  Riemannian isometries is isomorphic to the group of isometries of the Riemannian distance.

## References

* S. B. Myers and N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of
  Math. 40 (1939), 400–416.
* R. S. Palais, *On the differentiability of isometries*, Proc. Amer. Math. Soc. 8 (1957),
  805–807.
* S. Kobayashi, *Transformation Groups in Differential Geometry*, Springer, 1972, Ch. II, §1.
-/

public section

open Bundle Filter Manifold Metric Set TauCeti.Manifold
open scoped ContDiff Manifold NNReal Topology

noncomputable section

namespace Isometry

section Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]

variable {f : M → N}

/-- Let `A` be a norm-preserving map between tangent spaces of `M` at `p` and `N` at `f p` with
`f ∘ exp_p = exp_{f p} ∘ A` on a ball. If `f` preserves distances, then near the origin `A`
changes distances by at most any factor `c > 1` in either direction. -/
private theorem exists_pos_norm_sub_bounds (hf : Isometry f) {p : M}
    {A : TangentSpace I p → TangentSpace J (f p)} {ρ : ℝ} (hρ : 0 < ρ)
    (hexp : ∀ v ∈ ball (0 : TangentSpace I p) ρ,
      f (riemannianExp I M p v) = riemannianExp J N (f p) (A v))
    (hnorm : ∀ v ∈ ball (0 : TangentSpace I p) ρ, ‖A v‖ = ‖v‖) {c : ℝ} (hc : 1 < c) :
    ∃ s > 0, ∀ v ∈ ball (0 : TangentSpace I p) s, ∀ w ∈ ball (0 : TangentSpace I p) s,
      ‖A v - A w‖ ≤ c * ‖v - w‖ ∧ ‖v - w‖ ≤ c * ‖A v - A w‖ := by
  -- Apply the exponential distance bounds with the constant `√c` at `p` and at `f p`.
  set c' : ℝ≥0 := (√c).toNNReal
  have hc'c : (c' : ℝ) * c' = c := by
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg c), Real.mul_self_sqrt (zero_le_one.trans hc.le)]
  have hc' : 1 < c' := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one, Real.coe_toNNReal _ (Real.sqrt_nonneg c)]
    exact Real.lt_sqrt_of_sq_lt (by simpa using hc)
  obtain ⟨sM, hsM, -, hM⟩ :=
    exists_isNormalDomain_ball_dist_riemannianExp_bounds (I := I) (M := M) p hc'
  obtain ⟨sN, hsN, -, hN⟩ :=
    exists_isNormalDomain_ball_dist_riemannianExp_bounds (I := J) (M := N) (f p) hc'
  refine ⟨min (min sM sN) ρ, lt_min (lt_min hsM hsN) hρ, fun v hv w hw ↦ ?_⟩
  have hsub (s : ℝ) (hs : min (min sM sN) ρ ≤ s) {u : TangentSpace I p}
      (hu : u ∈ ball (0 : TangentSpace I p) (min (min sM sN) ρ)) :
      u ∈ ball (0 : TangentSpace I p) s :=
    ball_subset_ball hs hu
  have hvρ := hsub ρ (min_le_right _ _) hv
  have hwρ := hsub ρ (min_le_right _ _) hw
  have hAN {u : TangentSpace I p} (hu : u ∈ ball (0 : TangentSpace I p) (min (min sM sN) ρ)) :
      A u ∈ ball (0 : TangentSpace J (f p)) sN := by
    rw [mem_ball_zero_iff, hnorm u (hsub ρ (min_le_right _ _) hu), ← mem_ball_zero_iff]
    exact hsub sN ((min_le_left _ _).trans (min_le_right _ _)) hu
  have hd : dist (riemannianExp J N (f p) (A v)) (riemannianExp J N (f p) (A w)) =
      dist (riemannianExp I M p v) (riemannianExp I M p w) := by
    rw [← hexp v hvρ, ← hexp w hwρ, hf.dist_eq]
  obtain ⟨hM₁, hM₂⟩ := hM v (hsub sM ((min_le_left _ _).trans (min_le_left _ _)) hv) w
    (hsub sM ((min_le_left _ _).trans (min_le_left _ _)) hw)
  obtain ⟨hN₁, hN₂⟩ := hN _ (hAN hv) _ (hAN hw)
  rw [hd] at hN₁ hN₂
  rw [← hc'c]
  constructor
  · calc ‖A v - A w‖ ≤ c' * dist (riemannianExp I M p v) (riemannianExp I M p w) := hN₁
      _ ≤ c' * (c' * ‖v - w‖) := by gcongr
      _ = c' * c' * ‖v - w‖ := by ring
  · calc ‖v - w‖ ≤ c' * dist (riemannianExp I M p v) (riemannianExp I M p w) := hM₁
      _ ≤ c' * (c' * ‖A v - A w‖) := by gcongr
      _ = c' * c' * ‖A v - A w‖ := by ring

variable [CompleteSpace N]

/-- **A distance-preserving map is a linear isometry in normal coordinates.** Let `f` preserve
the Riemannian distances, with `N` complete. Then there are a normal ball of some radius `ρ > 0`
at `p` and a linear isometry `L` from `T_p M` to `T_{f p} N` such that
`f (exp_p v) = exp_{f p} (L v)` for every `v` in that ball. -/
theorem exists_linearIsometry_apply_riemannianExp_eq (hf : Isometry f) (p : M) :
    ∃ ρ > 0, IsNormalDomain I M p (ball 0 ρ) ∧
      ∃ L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p),
        ∀ v ∈ ball (0 : TangentSpace I p) ρ,
          f (riemannianExp I M p v) = riemannianExp J N (f p) (L v) := by
  obtain ⟨r₁, hr₁, hn₁⟩ := exists_isNormalDomain_ball (I := J) (M := N) (f p)
  obtain ⟨r₂, hr₂, hn₂⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  have hρ : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  -- Short radial geodesics at `p` are minimizing and shorter than `r₁`.
  have hmin (v : TangentSpace I p) (hv : v ∈ ball 0 (min r₁ r₂)) :
      ‖v‖ ≤ dist p (riemannianExp I M p v) :=
    (hn₂.dist_riemannianExp_eq_of_mem_ball subset_rfl
      (ball_subset_ball (min_le_right _ _) hv)).ge
  have hlt (v : TangentSpace I p) (hv : v ∈ ball 0 (min r₁ r₂)) : ‖v‖ < r₁ :=
    (mem_ball_zero_iff.1 hv).trans_le (min_le_left _ _)
  -- The radial map `A v = log_{f p} (f (exp_p v))`.
  set A : TangentSpace I p → TangentSpace J (f p) :=
    fun v ↦ riemannianLog J N (f p) (ball 0 r₁) (f (riemannianExp I M p v)) with hA
  have hexp (v : TangentSpace I p) (hv : v ∈ ball 0 (min r₁ r₂)) :
      f (riemannianExp I M p v) = riemannianExp J N (f p) (A v) := by
    simpa using hf.apply_riemannianExp_smul hn₁ subset_rfl (hmin v hv) (hlt v hv)
      (t := 1) ⟨zero_le_one, le_rfl⟩
  have hA0 : A 0 = 0 := by simp [hA, hn₁.riemannianLog_self]
  have hdist (v : TangentSpace I p) (hv : v ∈ ball 0 (min r₁ r₂)) (w : TangentSpace I p)
      (hw : w ∈ ball 0 (min r₁ r₂)) : dist (A v) (A w) = dist v w :=
    TauCeti.dist_eq_of_forall_norm_sub_bounds
      (fun v hv t ht ↦ hf.riemannianLog_apply_riemannianExp_smul hn₁ subset_rfl (hmin v hv)
        (hlt v hv) ht)
      (fun c hc ↦ hf.exists_pos_norm_sub_bounds hρ hexp
        (fun v hv ↦ hf.norm_riemannianLog_apply_riemannianExp hn₁ subset_rfl (hmin v hv)
          (hlt v hv)) hc) hv hw
  obtain ⟨L, hL⟩ := TauCeti.exists_linearIsometry_eqOn_ball hρ hA0 hdist
  exact ⟨min r₁ r₂, hρ, hn₂.ball (ball_subset_ball (min_le_right _ _)) hρ, L,
    fun v hv ↦ by rw [hexp v hv, hL hv]⟩

/-- A distance-preserving map between Riemannian manifolds with finite distances, into a complete
manifold, is smooth. `Isometry.contMDiff` extends this to extended distances. -/
private theorem contMDiff_of_metricSpace (hf : Isometry f) : ContMDiff I J ∞ f := by
  intro p
  obtain ⟨ρ, -, hn, L, hL⟩ := hf.exists_linearIsometry_apply_riemannianExp_eq (I := I) (J := J) p
  -- Near `p`, `f` is `exp_{f p} ∘ L ∘ log_p`.
  have heq : f =ᶠ[𝓝 p]
      riemannianExp J N (f p) ∘ L ∘ riemannianLog I M p (ball 0 ρ) := by
    filter_upwards [hn.image_mem_nhds] with q hq
    obtain ⟨v, hv, rfl⟩ := hq
    simp only [Function.comp_apply, hn.riemannianLog_riemannianExp hv, hL v hv]
  have hlog : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ (riemannianLog I M p (ball 0 ρ)) p :=
    hn.contMDiffOn_riemannianLog.contMDiffAt hn.image_mem_nhds
  have hexp : ContMDiffAt 𝓘(ℝ, TangentSpace J (f p)) J ∞ (riemannianExp J N (f p))
      (L (riemannianLog I M p (ball 0 ρ) p)) := by
    rw [hn.riemannianLog_self, map_zero]
    exact contMDiffAt_riemannianExp (zero_mem_expDomain _)
  have hL' := L.toContinuousLinearMap.contMDiff.contMDiffAt.comp p hlog
  exact (hexp.comp p hL').congr_of_eventuallyEq heq

/-- The differential of a distance-preserving map between Riemannian manifolds with finite
distances, into a complete manifold, preserves inner products. `Isometry.inner_mfderiv` extends
this to extended distances. -/
private theorem inner_mfderiv_of_metricSpace (hf : Isometry f) (x : M) (v w : TangentSpace I x) :
    inner ℝ (mfderiv I J f x v) (mfderiv I J f x w) = inner ℝ v w := by
  obtain ⟨ρ, hρ, -, L, hL⟩ := hf.exists_linearIsometry_apply_riemannianExp_eq (I := I) (J := J) x
  have heq : f ∘ riemannianExp I M x =ᶠ[𝓝 (0 : TangentSpace I x)]
      riemannianExp J N (f x) ∘ L :=
    eventually_of_mem (ball_mem_nhds 0 hρ) fun v hv ↦ hL v hv
  -- Differentiating `f ∘ exp_x = exp_{f x} ∘ L` at the origin identifies `d f_x` with `L`.
  have hmf (u : TangentSpace I x) : mfderiv I J f x u = L u := by
    have h1 : HasMFDerivAt I J f (riemannianExp I M x 0)
        (mfderiv I J f (riemannianExp I M x 0)) :=
      ((hf.contMDiff_of_metricSpace (I := I) (J := J) _).mdifferentiableAt
        (by simp)).hasMFDerivAt
    have h2 := ((contMDiffAt_riemannianExp (I := I) (M := M)
      (zero_mem_expDomain x)).mdifferentiableAt (by simp)).hasMFDerivAt
    have h3 : HasMFDerivAt 𝓘(ℝ, TangentSpace J (f x)) J (riemannianExp J N (f x)) (L 0)
        (mfderiv 𝓘(ℝ, TangentSpace J (f x)) J (riemannianExp J N (f x)) (L 0)) := by
      refine ((contMDiffAt_riemannianExp ?_).mdifferentiableAt (by simp)).hasMFDerivAt
      rw [map_zero]
      exact zero_mem_expDomain (f x)
    have huniq := hasMFDerivAt_unique (h1.comp 0 h2)
      ((h3.comp 0 (L.toContinuousLinearMap.hasMFDerivAt (x := 0))).congr_of_eventuallyEq_abuse
        heq)
    have hu : mfderiv I J f (riemannianExp I M x 0)
        (mfderiv 𝓘(ℝ, TangentSpace I x) I (riemannianExp I M x) 0 u) =
        mfderiv 𝓘(ℝ, TangentSpace J (f x)) J (riemannianExp J N (f x)) (L 0) (L u) :=
      congr($huniq u)
    rw [mfderiv_riemannianExp_apply_zero] at hu
    -- Move the base points `exp_x 0 = x` and `L 0 = 0` of the two differentials.
    have hexp0 (a : TangentSpace J (f x)) (ha : a = 0) (z : TangentSpace J (f x)) :
        mfderiv 𝓘(ℝ, TangentSpace J (f x)) J (riemannianExp J N (f x)) a z = z := by
      subst ha
      exact mfderiv_riemannianExp_apply_zero (f x) z
    have hf0 (y : M) (hy : y = x) (z : TangentSpace I x) :
        mfderiv I J f y z = mfderiv I J f x z := by
      subst hy
      rfl
    rw [hf0 _ (riemannianExp_zero x), hexp0 _ (map_zero L)] at hu
    exact hu
  rw [hmf, hmf, L.inner_map_map]

end Metric

section Component

/-! ### Finite-distance components

Distances in a Riemannian manifold may be infinite, between points of different components. The
points at finite distance from `p` form an open submanifold whose distance is finite, so the
results above apply to it, and they transfer back since smoothness and differentials are local.
-/

open TopologicalSpace
open scoped ENNReal TauCeti

/-- The finite-distance component of `p`, as an open subset. -/
private def component {X : Type*} [EMetricSpace X] (p : X) : Opens X :=
  ⟨Metric.eball p ∞, Metric.isOpen_eball⟩

@[simp]
private theorem coe_component {X : Type*} [EMetricSpace X] (p : X) :
    (component p : Set X) = Metric.eball p ∞ :=
  rfl

@[simp]
private theorem mem_component_iff {X : Type*} [EMetricSpace X] {p x : X} :
    x ∈ component p ↔ edist x p < ⊤ := by
  rw [← SetLike.mem_coe, coe_component, Metric.mem_eball]

private theorem mem_component {X : Type*} [EMetricSpace X] (p : X) : p ∈ component p :=
  mem_component_iff.2 (by simp)

/-- The metric of a finite-distance component. It is built with `EMetricSpace.toMetricSpace`
rather than taken from `TauCeti.instMetricSpaceEBallTop`, so that its topology unfolds reducibly
to the subtype topology carrying the charts of the open subset. -/
private instance {X : Type*} [EMetricSpace X] (p : X) : MetricSpace (component p) :=
  EMetricSpace.toMetricSpace fun x y ↦ ((edist_triangle_right (x : X) y p).trans_lt
    (ENNReal.add_lt_top.2 ⟨mem_component_iff.1 x.2, mem_component_iff.1 y.2⟩)).ne

/-- A finite-distance component of a complete space is complete. -/
private instance {X : Type*} [EMetricSpace X] [CompleteSpace X] (p : X) :
    CompleteSpace (component p) :=
  -- The subtype of `component p` is that of `Metric.eball p ∞` (`coe_component`).
  TauCeti.instCompleteSpaceEBallTop p

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- The distance of a finite-distance component is its own Riemannian distance. -/
private instance (p : M) : IsRiemannianManifold I (component p) := by
  refine ⟨fun x y ↦ ((component p).riemannianEDist_open_eq_edist_of_eball_subset x y ?_
    (edist_lt_top x y)).symm⟩
  rw [coe_component, TauCeti.eball_top_eq_of_edist_ne_top (mem_component_iff.1 x.2).ne]

variable {N : Type*} [EMetricSpace N] {f : M → N}

/-- A distance-preserving map restricts to the finite-distance components of `p` and `f p`. -/
private def componentMap (hf : Isometry f) (p : M) : component p → component (f p) :=
  fun x ↦ ⟨f x, by rw [mem_component_iff, hf.edist_eq]; exact mem_component_iff.1 x.2⟩

@[simp]
private theorem coe_componentMap (hf : Isometry f) (p : M) (x : component p) :
    (componentMap hf p x : N) = f x :=
  rfl

private theorem val_comp_componentMap (hf : Isometry f) (p : M) :
    Subtype.val ∘ componentMap hf p = f ∘ Subtype.val :=
  funext (coe_componentMap hf p)

/-- The restriction of a distance-preserving map to finite-distance components preserves
distances. -/
private theorem isometry_componentMap (hf : Isometry f) (p : M) :
    Isometry (componentMap hf p) :=
  fun x y ↦ by simp only [Subtype.edist_eq, coe_componentMap, hf.edist_eq]

end Component

section EMetric

open scoped TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [CompleteSpace N]

variable {f : M → N}

/-- **Myers–Steenrod: a distance-preserving map between Riemannian manifolds is smooth.** The
manifolds are finite-dimensional and without boundary, their extended distances are the
Riemannian distances, and the target is complete; no connectedness, completeness, compactness or
surjectivity is needed on the source. -/
theorem contMDiff (hf : Isometry f) : ContMDiff I J ∞ f := by
  intro p
  have h : ContMDiffAt I J ∞ (Subtype.val ∘ componentMap hf p)
      (⟨p, mem_component p⟩ : component p) :=
    (contMDiff_subtype_val.comp (isometry_componentMap hf p).contMDiff_of_metricSpace) _
  rw [val_comp_componentMap] at h
  exact contMDiffAt_subtype_iff.1 h

/-- **The differential of a distance-preserving map preserves inner products.** -/
theorem inner_mfderiv (hf : Isometry f) (p : M) (v w : TangentSpace I p) :
    inner ℝ (mfderiv I J f p v) (mfderiv I J f p w) = inner ℝ v w := by
  set x : component p := ⟨p, mem_component p⟩
  have hcomp := val_comp_componentMap hf p
  set e := tangentSpaceOpenEquiv (I := I) x
  have h := (isometry_componentMap hf p).inner_mfderiv_of_metricSpace (I := I) (J := J) x
    (e.symm v) (e.symm w)
  -- Inner products on the components are those of `M` and `N`, and the differential of the
  -- restriction of `f` is that of `f`.
  rw [inner_tangentSpace_open (I := J), inner_tangentSpace_open (I := I),
    tangentSpaceOpenEquiv_mfderiv_apply hcomp, tangentSpaceOpenEquiv_mfderiv_apply hcomp,
    e.apply_symm_apply, e.apply_symm_apply] at h
  -- `RiemannianBundle` installs `RiemannianBundle.g.inner` as the fibre `Inner.inner`.
  exact h

/-- The differential of a distance-preserving map preserves norms. -/
theorem norm_mfderiv (hf : Isometry f) (p : M) (v : TangentSpace I p) :
    ‖mfderiv I J f p v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, hf.inner_mfderiv]

end EMetric

end Isometry

namespace IsometryEquiv

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ F H') [J.Boundaryless]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [CompleteSpace N]

/-- **Myers–Steenrod: a bijective distance-preserving map is a smooth Riemannian isometry.** An
isometry `e : M ≃ᵢ N` of the Riemannian extended distances between finite-dimensional Riemannian
manifolds without boundary, with complete target (equivalently, since `e` transfers completeness,
complete source), is a diffeomorphism whose differential preserves the Riemannian inner
products. -/
def toRiemannianIsometry (e : M ≃ᵢ N) : TauCeti.RiemannianIsometry I J M N :=
  haveI : CompleteSpace M := e.completeSpace
  { toEquiv := e.toEquiv
    contMDiff_toFun := e.isometry.contMDiff
    contMDiff_invFun := e.symm.isometry.contMDiff
    inner_mfderiv' := e.isometry.inner_mfderiv }

/-- The smooth Riemannian isometry underlying a bijective distance-preserving map is that map. -/
@[simp]
theorem coe_toRiemannianIsometry (e : M ≃ᵢ N) : ⇑(e.toRiemannianIsometry I J) = e :=
  (rfl)

/-- The underlying equivalence of `e.toRiemannianIsometry I J` is that of `e`. -/
@[simp]
theorem toEquiv_toRiemannianIsometry (e : M ≃ᵢ N) :
    (e.toRiemannianIsometry I J).toEquiv = e.toEquiv :=
  (rfl)

/-- The inverse of `e.toRiemannianIsometry I J` is the inverse of `e`. -/
@[simp]
theorem coe_toRiemannianIsometry_symm (e : M ≃ᵢ N) :
    ⇑(e.toRiemannianIsometry I J).symm = e.symm := by
  funext y
  apply e.injective
  rw [apply_symm_apply, ← coe_toRiemannianIsometry I J e,
    TauCeti.RiemannianIsometry.apply_symm_apply]

/-- Forgetting the smooth structure of `e.toRiemannianIsometry I J` recovers `e`. -/
@[simp]
theorem toIsometryEquiv_toRiemannianIsometry (e : M ≃ᵢ N) :
    ((e.toRiemannianIsometry I J : TauCeti.RiemannianIsometry I J M N) : M ≃ᵢ N) = e := by
  ext x
  simp

/-- The smooth Riemannian isometry of the identity is the identity. -/
@[simp]
theorem toRiemannianIsometry_refl [CompleteSpace M] :
    (IsometryEquiv.refl M).toRiemannianIsometry I I = TauCeti.RiemannianIsometry.refl I M := by
  ext x
  rw [coe_toRiemannianIsometry, TauCeti.RiemannianIsometry.refl_apply]
  rfl

/-- The smooth Riemannian isometry of the inverse is the inverse smooth Riemannian isometry. The
completeness of `M` it needs is transferred from `N` by `e`. -/
@[simp]
theorem toRiemannianIsometry_symm (e : M ≃ᵢ N) :
    haveI : CompleteSpace M := e.completeSpace
    e.symm.toRiemannianIsometry J I = (e.toRiemannianIsometry I J).symm := by
  ext x
  simp

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {H'' : Type*} [TopologicalSpace H''] (K : ModelWithCorners ℝ G H'') [K.Boundaryless]
  {P : Type*} [EMetricSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]
  [IsContMDiffRiemannianBundle K ∞ G (fun z : P ↦ TangentSpace K z)] [IsRiemannianManifold K P]
  [CompleteSpace P]

omit [CompleteSpace N] in
/-- The smooth Riemannian isometry of a composite is the composite of the smooth Riemannian
isometries. The completeness of `N` it needs is transferred from `P` by `e₂`. -/
theorem toRiemannianIsometry_trans (e₁ : M ≃ᵢ N) (e₂ : N ≃ᵢ P) :
    haveI : CompleteSpace N := e₂.completeSpace
    (e₁.trans e₂).toRiemannianIsometry I K =
      (e₁.toRiemannianIsometry I J).trans (e₂.toRiemannianIsometry J K) := by
  ext x
  simp

/-- The smooth Riemannian isometry of the unit of `M ≃ᵢ M` is the unit of `Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_one [CompleteSpace M] :
    (1 : M ≃ᵢ M).toRiemannianIsometry I I = 1 :=
  toRiemannianIsometry_refl I

/-- The smooth Riemannian isometry of a product in `M ≃ᵢ M` is the product in `Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_mul [CompleteSpace M] (e₁ e₂ : M ≃ᵢ M) :
    (e₁ * e₂).toRiemannianIsometry I I =
      e₁.toRiemannianIsometry I I * e₂.toRiemannianIsometry I I :=
  toRiemannianIsometry_trans I I I e₂ e₁

/-- The smooth Riemannian isometry of an inverse in `M ≃ᵢ M` is the inverse in `Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_inv [CompleteSpace M] (e : M ≃ᵢ M) :
    e⁻¹.toRiemannianIsometry I I = (e.toRiemannianIsometry I I)⁻¹ :=
  toRiemannianIsometry_symm I I e

end IsometryEquiv

namespace TauCeti.RiemannianIsometry

section Group

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- The metric equivalence of the unit of `Isom I M` is the unit of `M ≃ᵢ M`. -/
@[simp]
theorem toIsometryEquiv_one : ((1 : Isom I M) : M ≃ᵢ M) = 1 :=
  toIsometryEquiv_refl

/-- The metric equivalence of a product in `Isom I M` is the product in `M ≃ᵢ M`. -/
@[simp]
theorem toIsometryEquiv_mul (Φ Ψ : Isom I M) :
    ((Φ * Ψ : Isom I M) : M ≃ᵢ M) = (Φ : M ≃ᵢ M) * (Ψ : M ≃ᵢ M) :=
  toIsometryEquiv_trans Ψ Φ

/-- The metric equivalence of an inverse in `Isom I M` is the inverse in `M ≃ᵢ M`. -/
@[simp]
theorem toIsometryEquiv_inv (Φ : Isom I M) :
    ((Φ⁻¹ : Isom I M) : M ≃ᵢ M) = (Φ : M ≃ᵢ M)⁻¹ :=
  toIsometryEquiv_symm Φ

end Group

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

section Map

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [CompleteSpace N]

/-- A smooth Riemannian isometry is recovered from its underlying distance-preserving
bijection. -/
@[simp]
theorem toRiemannianIsometry_toIsometryEquiv (Φ : RiemannianIsometry I J M N) :
    (Φ : M ≃ᵢ N).toRiemannianIsometry I J = Φ := by
  ext x
  simp

end Map

variable (I M) [CompleteSpace M]

/-- **The smooth and the metric isometry groups agree.** On a complete finite-dimensional
Riemannian manifold without boundary, forgetting the smooth structure is a group isomorphism from
the smooth Riemannian isometries onto the isometries of the Riemannian extended distance. -/
def isometryEquivMulEquiv : Isom I M ≃* (M ≃ᵢ M) where
  toFun Φ := Φ
  invFun e := e.toRiemannianIsometry I I
  left_inv := toRiemannianIsometry_toIsometryEquiv
  right_inv := IsometryEquiv.toIsometryEquiv_toRiemannianIsometry I I
  map_mul' := toIsometryEquiv_mul

/-- The isomorphism of isometry groups forgets the smooth structure. -/
@[simp]
theorem isometryEquivMulEquiv_apply (Φ : Isom I M) :
    isometryEquivMulEquiv I M Φ = (Φ : M ≃ᵢ M) :=
  (rfl)

/-- The inverse isomorphism of isometry groups is `IsometryEquiv.toRiemannianIsometry`. -/
@[simp]
theorem isometryEquivMulEquiv_symm_apply (e : M ≃ᵢ M) :
    (isometryEquivMulEquiv I M).symm e = e.toRiemannianIsometry I I :=
  (rfl)

end TauCeti.RiemannianIsometry
