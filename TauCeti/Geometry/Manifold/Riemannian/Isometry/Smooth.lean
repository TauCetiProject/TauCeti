/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Radial
public import TauCeti.Topology.MetricSpace.Isometry.Group
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Calculus.FDeriv.NormComparison
import TauCeti.Analysis.Normed.Affine.Isometry.StrictConvex
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.DistanceChart
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Distortion
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Distance
import TauCeti.Topology.MetricSpace.Isometry.Restrict

/-!
# Smoothness of distance-preserving maps of Riemannian manifolds

Every distance-preserving map `f : M → N` between smooth boundaryless Riemannian manifolds into a
complete manifold is smooth and preserves the Riemannian metric (`Isometry.contMDiff`,
`Isometry.inner_mfderiv`), and without completeness or connectedness assumptions every map that
restricts locally to an open-image distance-preserving map — in particular every metric equivalence
`M ≃ᵢ N` between extended-metric Riemannian manifolds — is smooth and a smooth local or global
Riemannian isometry
(`TauCeti.Manifold.isLocalRiemannianIsometry_of_forall_exists_isometry_domRestrict`,
`IsometryEquiv.toRiemannianIsometry`).

Two complementary arguments are combined:

1. **Palais's radial-geodesic argument for complete targets of arbitrary codimension.** When `N` is
   a complete Riemannian manifold with finite distances, distance-preserving maps send short radial
   geodesics to radial geodesics (`Isometry.apply_riemannianExp_smul`), so
   `A v = log_{f p} (f (exp_p v))` preserves norms and scales along rays. Exponential and
   logarithmic distortion bounds near the origin
   (`exists_isNormalDomain_ball_dist_riemannianExp_bounds`) together with ray scaling show that `A`
   preserves distances on a ball, hence agrees there with a linear isometry `L`
   (`TauCeti.exists_linearIsometry_eqOn_ball`), giving `f = exp_{f p} ∘ L ∘ log_p` near `p`. For
   extended distances, `f` restricts to the finite-distance components of `p` and `f p`, which are
   open submanifolds with finite distances to which this argument applies.

2. **Squared-distance coordinate charts without completeness.** Near `p ∈ M` at which `f` restricts
   to an isometry on an open neighbourhood `U` with `f '' U ∈ 𝓝 (f p)`, choosing a squared-distance
   chart `Φ` around `f p` (`exists_partialDiffeomorph_pi_toReal_edist_sq`) whose centres
   `y i = f (a i)` come from points `a i` inside a uniformly normal ball around `p` expresses `f`
   locally as `Φ.symm (fun i ↦ (edist (a i) ·).toReal ^ 2)`, a composition of smooth maps. Applying
   the same argument to the local inverse yields a smooth local diffeomorphism, and comparing the
   germ in normal coordinates along radial rays shows `‖df_p v‖ = ‖v‖`, hence `df_p` preserves inner
   products by polarization. This requires neither completeness nor finite distance across
   disconnected components (`EMetricSpace`).

## Main definitions

* `IsometryEquiv.toRiemannianIsometry`: a metric equivalence `M ≃ᵢ N` between smooth boundaryless
  Riemannian manifolds promoted to a smooth `TauCeti.RiemannianIsometry`.
* `Isometry.riemannianIsometryOfCompactSpace`: a distance-preserving self-map of a compact
  boundaryless Riemannian manifold promoted to an element of `TauCeti.Isom I M`.
* `TauCeti.RiemannianIsometry.isometryEquivEquiv`: the equivalence
  `RiemannianIsometry I J M N ≃ (M ≃ᵢ N)`.
* `TauCeti.RiemannianIsometry.isometryEquivMulEquiv`: the group isomorphism
  `Isom I M ≃* (M ≃ᵢ M)`.

## Main results

* `Isometry.exists_linearIsometry_apply_riemannianExp_eq`: `f (exp_p v) = exp_{f p} (L v)` on a
  normal ball for a linear isometry `L : T_p M →ₗᵢ[ℝ] T_{f p} N`, when `N` is complete.
* `Isometry.contMDiff`, `Isometry.inner_mfderiv`: a distance-preserving map between
  extended-metric Riemannian manifolds into a complete one is smooth and its differential preserves
  inner products; no connectedness, completeness or surjectivity is needed on the source.
* `Isometry.norm_mfderiv`, `Isometry.exists_linearIsometry_mfderiv_eq`: its differential preserves
  norms and is a linear isometry of tangent spaces.
* `Isometry.exists_apply_riemannianExp_eq_mfderiv`: near `p`, a distance-preserving map into a
  complete manifold is determined by its value and differential at `p`, as
  `f (exp_p v) = exp_{f p} (d f_p v)`.
* `MDifferentiableAt.norm_mfderiv_eq_of_eventually_edist_eq`,
  `MDifferentiableAt.inner_mfderiv_eq_of_eventually_edist_eq`: a map differentiable at `p` that
  preserves extended distances from `p` near `p` preserves norms and inner products on `T_p M`.
* `TauCeti.Manifold.contMDiffAt_of_isometry_domRestrict`,
  `TauCeti.Manifold.isLocalDiffeomorphAt_of_isometry_domRestrict`,
  `TauCeti.Manifold.isLocalRiemannianIsometry_of_forall_exists_isometry_domRestrict`: local
  smoothness, local diffeomorphism, and local Riemannian isometry from local open-image metric
  isometries without completeness.
* `Isometry.isLocalRiemannianIsometry_of_isOpen_range`: a metric isometry with open range is a
  smooth local Riemannian isometry.
* `IsometryEquiv.contMDiff`: every metric equivalence `M ≃ᵢ N` is smooth.
* `TauCeti.RiemannianIsometry.exists_coe_eq_iff_isometry_and_surjective`,
  `TauCeti.RiemannianIsometry.exists_isom_coe_eq_iff_isometry`: smooth Riemannian isometries are
  characterized among maps by preserving the Riemannian distance (and surjectivity, automatic for
  self-maps of compact manifolds).

## References

* S. B. Myers and N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of
  Math. (2) 40 (1939), 400–416.
* R. S. Palais, *On the differentiability of isometries*, Proc. Amer. Math. Soc. 8 (1957),
  805–807.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Ch. IV, Theorem 3.10.
* S. Kobayashi, *Transformation Groups in Differential Geometry*, Springer, 1972, Ch. II, §1.
* M. Taylor, *Measure Theory and Integration*, Graduate Studies in Mathematics 76, AMS, 2006,
  Appendix E; and *Finsler structures and smoothness of isometries*, Proc. Amer. Math. Soc. 134
  (2006), no. 8, 2419–2423.
* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171, 2016, §5.6.2.
-/

public section

open Bundle Filter Function Manifold Metric Set TauCeti.Manifold
open scoped ContDiff ENNReal Manifold NNReal Topology

noncomputable section

/-! ### Differentiable maps preserving distance preserve the Riemannian metric -/

section MetricDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [IsRiemannianManifold J N]

namespace MDifferentiableAt

/-- If `f : M → N` is differentiable at `p` and preserves extended distances from `p` on a
neighbourhood of `p`, then `df_p` preserves tangent-vector norms. -/
theorem norm_mfderiv_eq_of_eventually_edist_eq {f : M → N} {p : M}
    (hf : MDifferentiableAt I J f p) (hedist : ∀ᶠ x in 𝓝 p, edist (f p) (f x) = edist p x)
    (v : TangentSpace I p) :
    ‖mfderiv I J f p v‖ = ‖v‖ := by
  obtain ⟨rM, hrM, hM⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  obtain ⟨rN, hrN, hN⟩ := exists_isNormalDomain_ball (I := J) (M := N) (f p)
  have hΨ := hf.hasFDerivAt_riemannianLog_comp_riemannianExp_zero hN
  -- Near `0 ∈ T_p M`, `exp_p u` stays in the normal ball at `p`, lands in the normal ball at
  -- `f p`, and lies where `f` preserves distance from `p`, so `‖log_{f p} (f (exp_p u))‖ = ‖u‖`.
  have hexp_cont : ContinuousAt (riemannianExp I M p) 0 :=
    continuousAt_riemannianExp (zero_mem_expDomain p)
  have hnorm_ev : ∀ᶠ u : TangentSpace I p in 𝓝 0,
      ‖riemannianLog J N (f p) (Metric.ball 0 rN) (f (riemannianExp I M p u))‖ = ‖u‖ := by
    have h1 : ∀ᶠ u in 𝓝 (0 : TangentSpace I p), u ∈ Metric.ball (0 : TangentSpace I p) rM :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrM)
    have h2 : ∀ᶠ u in 𝓝 (0 : TangentSpace I p),
        edist (f p) (f (riemannianExp I M p u)) = edist p (riemannianExp I M p u) :=
      hexp_cont.eventually (by rwa [riemannianExp_zero])
    have h3 : ∀ᶠ u in 𝓝 (0 : TangentSpace I p),
        f (riemannianExp I M p u) ∈ eball (f p) (ENNReal.ofReal rN) := by
      have hballN : eball (f p) (ENNReal.ofReal rN) ∈ 𝓝 (f p) :=
        Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self (ENNReal.ofReal_pos.2 hrN))
      exact (hf.continuousAt.comp_of_eq hexp_cont (riemannianExp_zero p)).preimage_mem_nhds
        (by simpa only [comp_apply, riemannianExp_zero] using hballN)
    filter_upwards [h1, h2, h3] with u hu1 hu2 hu3
    rw [← hN.toReal_edist_eq_norm_riemannianLog_of_mem_eball subset_rfl hu3, hu2,
      hM.edist_riemannianExp_eq_of_mem_ball subset_rfl hu1, ← ofReal_norm,
      ENNReal.toReal_ofReal (norm_nonneg u)]
  exact hΨ.norm_apply_eq_of_eventually_norm_sub_eq
    (by simpa [riemannianExp_zero, hN.riemannianLog_self] using hnorm_ev) v

/-- If `f : M → N` is differentiable at `p` and preserves extended distances from `p` on a
neighbourhood of `p`, then `df_p` preserves inner products of tangent vectors. -/
theorem inner_mfderiv_eq_of_eventually_edist_eq {f : M → N} {p : M}
    (hf : MDifferentiableAt I J f p) (hedist : ∀ᶠ x in 𝓝 p, edist (f p) (f x) = edist p x)
    (v w : TangentSpace I p) :
    inner ℝ (mfderiv I J f p v) (mfderiv I J f p w) = inner ℝ v w := by
  let L : TangentSpace I p →ₗᵢ[ℝ] TangentSpace J (f p) :=
    { toLinearMap := (mfderiv I J f p).toLinearMap
      norm_map' := hf.norm_mfderiv_eq_of_eventually_edist_eq hedist }
  exact L.inner_map_map v w

end MDifferentiableAt

end MetricDerivative

/-! ### Palais's smoothness theorem for distance-preserving maps into complete manifolds -/

section CompleteTarget

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

namespace Isometry

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

end Isometry

end CompleteTarget

/-! ### Palais's smoothness theorem for extended distances -/

section CompleteTargetEMetric

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

namespace Isometry

variable {f : M → N}

/-- **Myers–Steenrod: a distance-preserving map between Riemannian manifolds is smooth.** The
manifolds are finite-dimensional and without boundary, their extended distances are the
Riemannian distances, and the target is complete; no connectedness, completeness, compactness or
surjectivity is needed on the source. -/
theorem contMDiff (hf : Isometry f) : ContMDiff I J ∞ f := by
  intro p
  -- Restrict `f` to the finite-distance components of `p` and `f p`, open submanifolds with
  -- finite distances (`TauCeti.eballTopOpens`).
  let g : TauCeti.eballTopOpens p → TauCeti.eballTopOpens (f p) :=
    (hf.mapsTo_eball p ∞).restrict _ _ _
  have h : ContMDiffAt I J ∞ (Subtype.val ∘ g)
      (⟨p, Metric.mem_eball_self ENNReal.zero_lt_top⟩ : TauCeti.eballTopOpens p) :=
    (contMDiff_subtypeVal.comp (hf.mapsToRestrict _).contMDiff_of_metricSpace) _
  rw [show Subtype.val ∘ g = f ∘ Subtype.val from Set.MapsTo.restrict_commutes ..] at h
  exact contMDiffAt_subtype_iff.1 h

/-- **A distance-preserving map preserves the Riemannian metric.** The differential of a map
between Riemannian manifolds which preserves their Riemannian distances, into a complete
manifold, preserves inner products of tangent vectors. -/
theorem inner_mfderiv (hf : Isometry f) (x : M) (v w : TangentSpace I x) :
    inner ℝ (mfderiv I J f x v) (mfderiv I J f x w) = inner ℝ v w :=
  ((hf.contMDiff (I := I) (J := J) x).mdifferentiableAt (by simp))
    |>.inner_mfderiv_eq_of_eventually_edist_eq (.of_forall (hf.edist_eq x)) v w

/-- **The differential of a distance-preserving map preserves norms** of tangent vectors, when
the target is complete. -/
theorem norm_mfderiv (hf : Isometry f) (x : M) (v : TangentSpace I x) :
    ‖mfderiv I J f x v‖ = ‖v‖ :=
  ((hf.contMDiff (I := I) (J := J) x).mdifferentiableAt (by simp))
    |>.norm_mfderiv_eq_of_eventually_edist_eq (.of_forall (hf.edist_eq x)) v

/-- **The differential of a distance-preserving map is a linear isometry.** The differential at
`x` of a map between Riemannian manifolds which preserves their Riemannian distances, into a
complete manifold, is a linear isometry of tangent spaces. -/
theorem exists_linearIsometry_mfderiv_eq (hf : Isometry f) (x : M) :
    ∃ L : TangentSpace I x →ₗᵢ[ℝ] TangentSpace J (f x),
      ∀ v : TangentSpace I x, mfderiv I J f x v = L v :=
  ⟨{ toLinearMap := (mfderiv I J f x).toLinearMap
     norm_map' := hf.norm_mfderiv x }, fun _ ↦ rfl⟩

end Isometry

end CompleteTargetEMetric

/-! ### Distance-preserving maps in normal coordinates -/

section CompleteTargetExp

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
  [CompleteSpace N]

namespace Isometry

variable {f : M → N}

/-- The differential of a distance-preserving map at `x` is the linear isometry through which it
acts in normal coordinates. -/
private theorem mfderiv_apply_eq_of_apply_riemannianExp (hf : Isometry f) {x : M}
    {L : TangentSpace I x →ₗᵢ[ℝ] TangentSpace J (f x)} {ρ : ℝ} (hρ : 0 < ρ)
    (hL : ∀ v ∈ ball (0 : TangentSpace I x) ρ,
      f (riemannianExp I M x v) = riemannianExp J N (f x) (L v))
    (u : TangentSpace I x) :
    mfderiv I J f x u = L u := by
  have heq : f ∘ riemannianExp I M x =ᶠ[𝓝 (0 : TangentSpace I x)]
      riemannianExp J N (f x) ∘ L :=
    eventually_of_mem (ball_mem_nhds 0 hρ) fun v hv ↦ hL v hv
  -- Differentiating `f ∘ exp_x = exp_{f x} ∘ L` at the origin identifies `d f_x` with `L`.
  have h1 : HasMFDerivAt I J f (riemannianExp I M x 0)
      (mfderiv I J f (riemannianExp I M x 0)) :=
    ((hf.contMDiff (I := I) (J := J) _).mdifferentiableAt (by simp)).hasMFDerivAt
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

/-- **A distance-preserving map is determined near `p` by its value and differential at `p`.**
If `f` preserves the Riemannian distances and `N` is complete, then there is a normal ball of some
radius `ρ > 0` at `p` such that `f (exp_p v) = exp_{f p} (d f_p v)` for every `v` in that ball. -/
theorem exists_apply_riemannianExp_eq_mfderiv (hf : Isometry f) (p : M) :
    ∃ ρ > 0, IsNormalDomain I M p (ball 0 ρ) ∧
      ∀ v ∈ ball (0 : TangentSpace I p) ρ,
        f (riemannianExp I M p v) = riemannianExp J N (f p) (mfderiv I J f p v) := by
  obtain ⟨ρ, hρ, hn, L, hL⟩ := hf.exists_linearIsometry_apply_riemannianExp_eq (I := I) (J := J) p
  refine ⟨ρ, hρ, hn, fun v hv ↦ ?_⟩
  rw [hf.mfderiv_apply_eq_of_apply_riemannianExp hρ hL]
  exact hL v hv

end Isometry

end CompleteTargetExp

/-! ### Local smoothness and metric equivalences without completeness -/

section ExtendedMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [IsRiemannianManifold J N]

namespace TauCeti.Manifold

/-- **Local smoothness of metric isometries.** If `f : M → N` restricts to a metric isometry on an
open neighbourhood `U` of `p` and `f '' U` is a neighbourhood of `f p`, then `f` is smooth at
`p`. -/
theorem contMDiffAt_of_isometry_domRestrict {f : M → N} {U : Set M} {p : M} (hU : IsOpen U)
    (hp : p ∈ U) (hf : Isometry (U.domRestrict f)) (hfU : f '' U ∈ 𝓝 (f p)) :
    ContMDiffAt I J ∞ f p := by
  obtain ⟨r, -, WM, hWM_nhds, hWM⟩ :=
    exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M) p
  obtain ⟨WM', hWM'_sub, hWM'o, hpWM'⟩ := mem_nhds_iff.1 hWM_nhds
  set VM : Set M := U ∩ WM'
  have hVMo : IsOpen VM := hU.inter hWM'o
  have hpVM : p ∈ VM := ⟨hp, hpWM'⟩
  -- Because `f` is isometric on `U`, the image of `VM` is still a neighbourhood of `f p`.
  obtain ⟨ε, hε, hε_sub⟩ := EMetric.mem_nhds_iff.1 (hVMo.mem_nhds hpVM)
  have hfVM : f '' VM ∈ 𝓝 (f p) := by
    refine mem_of_superset (inter_mem hfU (Metric.isOpen_eball.mem_nhds
      (Metric.mem_eball_self hε))) ?_
    rintro _ ⟨⟨x, hxU, rfl⟩, hdist⟩
    refine mem_image_of_mem f (hε_sub ?_)
    rw [Metric.mem_eball] at hdist ⊢
    exact (hf.edist_eq ⟨x, hxU⟩ ⟨p, hp⟩).symm.trans_lt hdist
  obtain ⟨yN, Φ, hyN_mem, hfp_src, _, hΦ_eq⟩ :=
    exists_partialDiffeomorph_pi_toReal_edist_sq (I := J) (M := N) (f p) hfVM
  choose a ha_VM hfa using fun i ↦ hyN_mem i
  have ha_norm (i : Fin (Module.finrank ℝ F)) : IsNormalDomain I M (a i) (Metric.ball 0 r) :=
    (hWM (a i) (hWM'_sub (ha_VM i).2)).1
  have hf_cont : ContinuousOn f U := continuousOn_iff_continuous_domRestrict.2 hf.continuous
  set O : Set M := VM ∩ f ⁻¹' Φ.source
  have hOo : IsOpen O :=
    (hf_cont.mono fun _ (hz : _ ∈ VM) ↦ hz.1).isOpen_inter_preimage hVMo Φ.open_source
  have hpO : p ∈ O := ⟨hpVM, hfp_src⟩
  -- Uniform normality puts all of `O ⊆ WM` inside the metric ball of radius `r` around each `a i`.
  have hO_balls : O ⊆ ⋂ i, eball (a i) (ENNReal.ofReal r) := fun z hz ↦
    mem_iInter.2 fun i ↦ by
      rw [← (ha_norm i).image_riemannianExp_ball subset_rfl]
      exact (hWM (a i) (hWM'_sub (ha_VM i).2)).2 (hWM'_sub hz.1.2)
  set coord : M → Fin (Module.finrank ℝ F) → ℝ :=
    fun z i ↦ (edist (a i) z).toReal ^ 2
  have hcoord_smooth : ContMDiffOn I 𝓘(ℝ, Fin (Module.finrank ℝ F) → ℝ) ∞ coord O :=
    (contMDiffOn_pi_toReal_edist_sq ha_norm fun _ ↦ subset_rfl).mono hO_balls
  have hcoord_eq (z : M) (hz : z ∈ O) : coord z = Φ (f z) := by
    rw [hΦ_eq (f z) hz.2]
    ext i
    have hiso := hf.edist_eq ⟨a i, (ha_VM i).1⟩ ⟨z, hz.1.1⟩
    simp only [Set.domRestrict_apply, Subtype.edist_mk_mk, hfa i] at hiso
    simp only [coord, ← hiso]
  have hmaps : MapsTo coord O Φ.symm.source := fun z hz ↦ hcoord_eq z hz ▸ Φ.map_source hz.2
  have hcongr : EqOn f (Φ.symm ∘ coord) O := fun z hz ↦ by
    simp only [comp_apply, hcoord_eq z hz]
    exact (Φ.left_inv hz.2).symm
  exact ((Φ.symm.contMDiffOn.comp hcoord_smooth hmaps).congr hcongr).contMDiffAt (hOo.mem_nhds hpO)

/-- If `f : M → N` restricts to a metric isometry on an open neighbourhood `U` of `p` and
`f '' U ∈ 𝓝 (f p)`, then `f` is a smooth local diffeomorphism at `p`. -/
theorem isLocalDiffeomorphAt_of_isometry_domRestrict {f : M → N} {U : Set M} {p : M}
    (hU : IsOpen U) (hp : p ∈ U) (hf : Isometry (U.domRestrict f)) (hfU : f '' U ∈ 𝓝 (f p)) :
    IsLocalDiffeomorphAt I J ∞ f p := by
  have : Nonempty M := ⟨p⟩
  have hinj : InjOn f U := fun x₁ hx₁ x₂ hx₂ hfx ↦
    congrArg Subtype.val (hf.injective (a₁ := ⟨x₁, hx₁⟩) (a₂ := ⟨x₂, hx₂⟩) hfx)
  have hf_cont : ContinuousOn f U := continuousOn_iff_continuous_domRestrict.2 hf.continuous
  set VN : Set N := interior (f '' U)
  set U' : Set M := U ∩ f ⁻¹' VN
  set g : N → M := invFunOn f U
  have hVNo : IsOpen VN := isOpen_interior
  have hU'o : IsOpen U' := hf_cont.isOpen_inter_preimage hU hVNo
  have hpU' : p ∈ U' := ⟨hp, mem_interior_iff_mem_nhds.2 hfU⟩
  have hg_mem {y : N} (hy : y ∈ VN) : g y ∈ U' :=
    ⟨invFunOn_mem (interior_subset hy),
      mem_preimage.2 (by simpa only [g, invFunOn_eq (interior_subset hy)] using hy)⟩
  have hg_isom : Isometry (VN.domRestrict g) := fun ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ ↦ by
    have h := (hf.edist_eq ⟨g y₁, (hg_mem hy₁).1⟩ ⟨g y₂, (hg_mem hy₂).1⟩).symm
    simpa only [Set.domRestrict_apply, Subtype.edist_mk_mk, g,
      invFunOn_eq (interior_subset hy₁), invFunOn_eq (interior_subset hy₂)] using h
  have hU'_sub_im : U' ⊆ g '' VN := fun x hx ↦ ⟨f x, hx.2, hinj.leftInvOn_invFunOn hx.1⟩
  let Ψ : PartialDiffeomorph I J M N ∞ :=
    { toFun := f
      invFun := g
      source := U'
      target := VN
      map_source' := fun _ hx ↦ hx.2
      map_target' := fun _ hy ↦ hg_mem hy
      left_inv' := fun _ hx ↦ hinj.leftInvOn_invFunOn hx.1
      right_inv' := fun _ hy ↦ invFunOn_eq (interior_subset hy)
      open_source := hU'o
      open_target := hVNo
      contMDiffOn_toFun := fun x hx ↦
        (contMDiffAt_of_isometry_domRestrict hU hx.1 hf
          (mem_interior_iff_mem_nhds.1 hx.2)).contMDiffWithinAt
      contMDiffOn_invFun := fun y hy ↦
        (contMDiffAt_of_isometry_domRestrict hVNo hy hg_isom
          (mem_of_superset (hU'o.mem_nhds (hg_mem hy)) hU'_sub_im)).contMDiffWithinAt }
  exact TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := Ψ) hpU' (eqOn_refl f U')

/-- If `f : M → N` restricts around each point `p : M` to a metric isometry on an open
neighbourhood `U` with `f '' U ∈ 𝓝 (f p)`, then `f` is a smooth local Riemannian isometry. -/
theorem isLocalRiemannianIsometry_of_forall_exists_isometry_domRestrict {f : M → N}
    (hf : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ Isometry (U.domRestrict f) ∧ f '' U ∈ 𝓝 (f p)) :
    TauCeti.IsLocalRiemannianIsometry I J f where
  contMDiff p :=
    let ⟨_, hUo, hpU, hfU_isom, hfU_nhds⟩ := hf p
    contMDiffAt_of_isometry_domRestrict hUo hpU hfU_isom hfU_nhds
  isInvertible_mfderiv p :=
    let ⟨_, hUo, hpU, hfU_isom, hfU_nhds⟩ := hf p
    (isLocalDiffeomorphAt_of_isometry_domRestrict (I := I) (J := J) hUo hpU hfU_isom hfU_nhds)
      |>.isInvertible_mfderiv (by simp)
  inner_mfderiv p :=
    let ⟨U, hUo, hpU, hfU_isom, hfU_nhds⟩ := hf p
    ((contMDiffAt_of_isometry_domRestrict (I := I) (J := J) hUo hpU hfU_isom hfU_nhds)
      |>.mdifferentiableAt (by simp))
      |>.inner_mfderiv_eq_of_eventually_edist_eq
        (eventually_of_mem (hUo.mem_nhds hpU) fun y hy ↦ hfU_isom.edist_eq ⟨p, hpU⟩ ⟨y, hy⟩)

end TauCeti.Manifold

namespace Isometry

/-- A metric isometry `f : M → N` whose range is a neighbourhood of `f p` is smooth at `p`. -/
theorem contMDiffAt_of_range_mem_nhds {f : M → N} (hf : Isometry f) {p : M}
    (hr : range f ∈ 𝓝 (f p)) : ContMDiffAt I J ∞ f p :=
  contMDiffAt_of_isometry_domRestrict isOpen_univ (mem_univ p)
    (hf.comp isometry_subtypeVal) (by simpa only [image_univ] using hr)

/-- A metric isometry `f : M → N` whose range is a neighbourhood of `f p` is a smooth local
diffeomorphism at `p`. -/
theorem isLocalDiffeomorphAt_of_range_mem_nhds {f : M → N} (hf : Isometry f) {p : M}
    (hr : range f ∈ 𝓝 (f p)) : IsLocalDiffeomorphAt I J ∞ f p :=
  isLocalDiffeomorphAt_of_isometry_domRestrict isOpen_univ (mem_univ p)
    (hf.comp isometry_subtypeVal) (by simpa only [image_univ] using hr)

/-- A metric isometry `f : M → N` with open range is smooth. -/
theorem contMDiff_of_isOpen_range {f : M → N} (hf : Isometry f) (hr : IsOpen (range f)) :
    ContMDiff I J ∞ f :=
  fun p ↦ hf.contMDiffAt_of_range_mem_nhds (hr.mem_nhds (mem_range_self p))

/-- A metric isometry `f : M → N` with open range is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_of_isOpen_range {f : M → N} (hf : Isometry f)
    (hr : IsOpen (range f)) : IsLocalDiffeomorph I J ∞ f :=
  fun p ↦ hf.isLocalDiffeomorphAt_of_range_mem_nhds (hr.mem_nhds (mem_range_self p))

/-- A metric isometry `f : M → N` with open range is a smooth local Riemannian isometry. -/
theorem isLocalRiemannianIsometry_of_isOpen_range {f : M → N} (hf : Isometry f)
    (hr : IsOpen (range f)) : TauCeti.IsLocalRiemannianIsometry I J f :=
  isLocalRiemannianIsometry_of_forall_exists_isometry_domRestrict fun p ↦
    ⟨univ, isOpen_univ, mem_univ p, hf.comp isometry_subtypeVal,
      by simpa only [image_univ] using hr.mem_nhds (mem_range_self p)⟩

/-- A surjective metric isometry `f : M → N` is smooth. -/
theorem contMDiff_of_surjective {f : M → N} (hf : Isometry f) (hsurj : Surjective f) :
    ContMDiff I J ∞ f :=
  hf.contMDiff_of_isOpen_range (hsurj.range_eq.symm ▸ isOpen_univ)

/-- A surjective metric isometry `f : M → N` is a smooth local Riemannian isometry. -/
theorem isLocalRiemannianIsometry_of_surjective {f : M → N} (hf : Isometry f)
    (hsurj : Surjective f) : TauCeti.IsLocalRiemannianIsometry I J f :=
  hf.isLocalRiemannianIsometry_of_isOpen_range (hsurj.range_eq.symm ▸ isOpen_univ)

end Isometry

namespace IsometryEquiv

variable (I J) in
/-- **Myers–Steenrod smoothness theorem.** Every metric equivalence `e : M ≃ᵢ N` between smooth
boundaryless Riemannian manifolds is smooth. -/
protected theorem contMDiff (e : M ≃ᵢ N) : ContMDiff I J ∞ e :=
  e.isometry.contMDiff_of_surjective e.surjective

variable (I J) in
/-- Promote a metric equivalence `e : M ≃ᵢ N` between smooth boundaryless Riemannian manifolds to a
smooth `TauCeti.RiemannianIsometry`. -/
def toRiemannianIsometry (e : M ≃ᵢ N) : TauCeti.RiemannianIsometry I J M N where
  toDiffeomorph :=
    { toEquiv := e.toEquiv
      contMDiff_toFun := e.contMDiff I J
      contMDiff_invFun := e.symm.contMDiff J I }
  inner_mfderiv' :=
    (e.isometry.isLocalRiemannianIsometry_of_surjective (I := I) (J := J) e.surjective)
      |>.inner_mfderiv

/-- Promoting a metric equivalence to a smooth Riemannian isometry preserves the underlying map. -/
@[simp]
theorem coe_toRiemannianIsometry (e : M ≃ᵢ N) : ⇑(e.toRiemannianIsometry I J) = ⇑e :=
  (rfl)

/-- The underlying equivalence of `e.toRiemannianIsometry I J` is that of `e`. -/
@[simp]
theorem toEquiv_toRiemannianIsometry (e : M ≃ᵢ N) :
    (e.toRiemannianIsometry I J).toEquiv = e.toEquiv :=
  (rfl)

/-- Applying `e.toRiemannianIsometry I J` evaluates `e`. -/
@[simp]
theorem toRiemannianIsometry_apply (e : M ≃ᵢ N) (x : M) : e.toRiemannianIsometry I J x = e x :=
  (rfl)

/-- Promoting the inverse metric equivalence gives the inverse smooth Riemannian isometry. -/
@[simp]
theorem toRiemannianIsometry_symm (e : M ≃ᵢ N) :
    e.symm.toRiemannianIsometry J I = (e.toRiemannianIsometry I J).symm := by
  ext y
  apply (EquivLike.injective (e.toRiemannianIsometry I J))
  simp

/-- Evaluating `(e.toRiemannianIsometry I J).symm` agrees with `e.symm`. -/
@[simp]
theorem coe_toRiemannianIsometry_symm (e : M ≃ᵢ N) :
    ⇑(e.toRiemannianIsometry I J).symm = ⇑e.symm := by
  rw [← toRiemannianIsometry_symm, coe_toRiemannianIsometry]

/-- Promoting the identity metric equivalence gives the identity smooth Riemannian isometry. -/
@[simp]
theorem toRiemannianIsometry_refl :
    (IsometryEquiv.refl M).toRiemannianIsometry I I = TauCeti.RiemannianIsometry.refl I M := by
  ext x
  simp only [toRiemannianIsometry_apply, TauCeti.RiemannianIsometry.refl_apply,
    IsometryEquiv.coe_eq_toEquiv, IsometryEquiv.refl, Equiv.refl_apply]

/-- Forgetting smoothness after `toRiemannianIsometry` recovers the original metric equivalence. -/
@[simp]
theorem toIsometryEquiv_toRiemannianIsometry (e : M ≃ᵢ N) :
    ((e.toRiemannianIsometry I J : TauCeti.RiemannianIsometry I J M N) : M ≃ᵢ N) = e := by
  ext x
  simp

/-- Promoting `1 : M ≃ᵢ M` gives `1 : TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_one :
    (1 : M ≃ᵢ M).toRiemannianIsometry I I = (1 : TauCeti.Isom I M) := by
  ext x
  simp

/-- Promoting a product in `M ≃ᵢ M` gives the product in `TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_mul (e₁ e₂ : M ≃ᵢ M) :
    (e₁ * e₂).toRiemannianIsometry I I =
      e₁.toRiemannianIsometry I I * e₂.toRiemannianIsometry I I := by
  ext x
  simp

/-- Promoting an inverse in `M ≃ᵢ M` gives the inverse in `TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_inv (e : M ≃ᵢ M) :
    e⁻¹.toRiemannianIsometry I I = (e.toRiemannianIsometry I I)⁻¹ :=
  eq_inv_of_mul_eq_one_left
    (by rw [← toRiemannianIsometry_mul, inv_mul_cancel, toRiemannianIsometry_one])

/-- Promoting a quotient in `M ≃ᵢ M` gives the quotient in `TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_div (e₁ e₂ : M ≃ᵢ M) :
    (e₁ / e₂).toRiemannianIsometry I I =
      e₁.toRiemannianIsometry I I / e₂.toRiemannianIsometry I I := by
  simp [div_eq_mul_inv]

/-- Promoting a natural power in `M ≃ᵢ M` gives the natural power in `TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_pow (e : M ≃ᵢ M) (n : ℕ) :
    (e ^ n).toRiemannianIsometry I I = e.toRiemannianIsometry I I ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- Promoting an integer power in `M ≃ᵢ M` gives the integer power in `TauCeti.Isom I M`. -/
@[simp]
theorem toRiemannianIsometry_zpow (e : M ≃ᵢ M) (n : ℤ) :
    (e ^ n).toRiemannianIsometry I I = e.toRiemannianIsometry I I ^ n := by
  cases n with
  | ofNat n => simp
  | negSucc n => simp

variable
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''} [K.Boundaryless]
  {P : Type*} [EMetricSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)] [IsManifold K ∞ P]
  [IsContMDiffRiemannianBundle K ∞ G (fun z : P ↦ TangentSpace K z)]
  [IsRiemannianManifold K P]

variable (J) in
/-- Promoting a composite of metric equivalences agrees with composing the promoted smooth
Riemannian isometries. -/
theorem toRiemannianIsometry_trans (e₁ : M ≃ᵢ N) (e₂ : N ≃ᵢ P) :
    (e₁.trans e₂).toRiemannianIsometry I K =
      (e₁.toRiemannianIsometry I J).trans (e₂.toRiemannianIsometry J K) := by
  ext x
  simp

end IsometryEquiv

namespace Isometry

variable (I) in
/-- Every distance-preserving self-map of a compact smooth boundaryless Riemannian manifold is a
smooth Riemannian self-isometry. -/
def riemannianIsometryOfCompactSpace [CompactSpace M] {f : M → M} (hf : Isometry f) :
    TauCeti.Isom I M :=
  hf.isometryEquivOfCompactSpace.toRiemannianIsometry I I

/-- `hf.riemannianIsometryOfCompactSpace I` is `hf.isometryEquivOfCompactSpace` promoted via
`IsometryEquiv.toRiemannianIsometry`. -/
theorem riemannianIsometryOfCompactSpace_def [CompactSpace M] {f : M → M} (hf : Isometry f) :
    hf.riemannianIsometryOfCompactSpace I =
      hf.isometryEquivOfCompactSpace.toRiemannianIsometry I I :=
  (rfl)

/-- The underlying map of `hf.riemannianIsometryOfCompactSpace I` is `f`. -/
@[simp]
theorem coe_riemannianIsometryOfCompactSpace [CompactSpace M] {f : M → M} (hf : Isometry f) :
    ⇑(hf.riemannianIsometryOfCompactSpace I) = f := by
  simp [riemannianIsometryOfCompactSpace_def]

/-- Forgetting smoothness on `hf.riemannianIsometryOfCompactSpace I` recovers
`hf.isometryEquivOfCompactSpace`. -/
@[simp]
theorem toIsometryEquiv_riemannianIsometryOfCompactSpace [CompactSpace M] {f : M → M}
    (hf : Isometry f) :
    ((hf.riemannianIsometryOfCompactSpace I : TauCeti.Isom I M) : M ≃ᵢ M) =
      hf.isometryEquivOfCompactSpace := by
  simp [riemannianIsometryOfCompactSpace_def]

end Isometry

namespace TauCeti.RiemannianIsometry

/-- Promoting the underlying metric equivalence of a smooth Riemannian isometry recovers it. -/
@[simp]
theorem toRiemannianIsometry_toIsometryEquiv (Φ : RiemannianIsometry I J M N) :
    (Φ : M ≃ᵢ N).toRiemannianIsometry I J = Φ := by
  ext x
  simp

variable (I J M N) in
/-- **Equivalence between smooth Riemannian isometries and metric equivalences.** -/
def isometryEquivEquiv : RiemannianIsometry I J M N ≃ (M ≃ᵢ N) where
  toFun Φ := (Φ : M ≃ᵢ N)
  invFun e := e.toRiemannianIsometry I J
  left_inv := toRiemannianIsometry_toIsometryEquiv
  right_inv := IsometryEquiv.toIsometryEquiv_toRiemannianIsometry

/-- `isometryEquivEquiv` sends a smooth Riemannian isometry to its underlying metric equivalence. -/
@[simp]
theorem isometryEquivEquiv_apply (Φ : RiemannianIsometry I J M N) :
    isometryEquivEquiv I J M N Φ = (Φ : M ≃ᵢ N) :=
  (rfl)

/-- `isometryEquivEquiv.symm` promotes a metric equivalence via `toRiemannianIsometry`. -/
@[simp]
theorem isometryEquivEquiv_symm_apply (e : M ≃ᵢ N) :
    (isometryEquivEquiv I J M N).symm e = e.toRiemannianIsometry I J :=
  (rfl)

/-- A map `f : M → N` between smooth boundaryless Riemannian manifolds is the underlying map of a
smooth Riemannian isometry if and only if it is a surjective metric isometry. -/
theorem exists_coe_eq_iff_isometry_and_surjective {f : M → N} :
    (∃ Φ : RiemannianIsometry I J M N, ⇑Φ = f) ↔ Isometry f ∧ Surjective f := by
  refine ⟨?_, fun ⟨hf, hsurj⟩ ↦ ?_⟩
  · rintro ⟨Φ, rfl⟩
    exact ⟨IsometryClass.isometry Φ, Φ.toDiffeomorph.surjective⟩
  · let e : M ≃ᵢ N :=
      { toEquiv := Equiv.ofBijective f ⟨hf.injective, hsurj⟩
        isometry_toFun := hf }
    exact ⟨e.toRiemannianIsometry I J,
      (IsometryEquiv.coe_toRiemannianIsometry e).trans <|
        (IsometryEquiv.coe_mk _ _).trans (Equiv.coe_ofBijective f _)⟩

/-- On a compact smooth boundaryless Riemannian manifold, a self-map `f : M → M` is the underlying
map of a smooth Riemannian self-isometry if and only if it preserves the Riemannian distance. -/
theorem exists_isom_coe_eq_iff_isometry [CompactSpace M] {f : M → M} :
    (∃ Φ : Isom I M, ⇑Φ = f) ↔ Isometry f :=
  exists_coe_eq_iff_isometry_and_surjective.trans
    ⟨And.left, fun hf ↦ ⟨hf, hf.surjective_of_compactSpace⟩⟩

/-- On a compact smooth boundaryless Riemannian manifold, the underlying maps of `Isom I M` are
precisely the metric isometries `M → M`. -/
theorem range_coe_isom [CompactSpace M] :
    range ((⇑) : Isom I M → M → M) = {f : M → M | Isometry f} :=
  Set.ext fun _ ↦ exists_isom_coe_eq_iff_isometry

variable (I M) in
/-- **Group isomorphism between `Isom I M` and `M ≃ᵢ M`.** -/
def isometryEquivMulEquiv : Isom I M ≃* (M ≃ᵢ M) where
  toEquiv := isometryEquivEquiv I I M M
  map_mul' _ _ := by
    ext x
    simp

/-- The underlying equivalence of `isometryEquivMulEquiv` is `isometryEquivEquiv`. -/
@[simp]
theorem toEquiv_isometryEquivMulEquiv :
    (isometryEquivMulEquiv I M : Isom I M ≃ (M ≃ᵢ M)) = isometryEquivEquiv I I M M :=
  (rfl)

-- See note [hom simp lemma priority]
/-- `isometryEquivMulEquiv` sends an element of `Isom I M` to its metric equivalence. -/
@[simp low]
theorem isometryEquivMulEquiv_apply (Φ : Isom I M) :
    isometryEquivMulEquiv I M Φ = (Φ : M ≃ᵢ M) :=
  isometryEquivEquiv_apply Φ

-- See note [hom simp lemma priority]
/-- `isometryEquivMulEquiv.symm` promotes a self-metric equivalence via `toRiemannianIsometry`. -/
@[simp low]
theorem isometryEquivMulEquiv_symm_apply (e : M ≃ᵢ M) :
    (isometryEquivMulEquiv I M).symm e = e.toRiemannianIsometry I I :=
  isometryEquivEquiv_symm_apply e

end TauCeti.RiemannianIsometry

end ExtendedMetric

end
