/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Uniqueness
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Segment
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Uniform
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Reparametrization
import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# Strongly geodesically convex neighbourhoods and radial contractions

A subset `U` of a Riemannian manifold `M` is *strongly geodesically convex*
(`TauCeti.Manifold.IsStronglyGeodesicallyConvex`) if every pair of points `x, y ∈ U` is joined by a
minimizing geodesic segment on `[0, 1]` whose image lies in `U` and which is unique among **all**
minimizing geodesics between `x` and `y` in `M`. It is *uniformly normal*
(`TauCeti.Manifold.IsUniformlyNormal`) if each point `q ∈ U` admits a positive normal radius `r`
such that `U` lies in the normal ball `exp_q '' B(0, r)`.

Following Whitehead's argument in the presentation of Lee (Lemma 6.16 and Theorem 6.17), this file
proves that sufficiently small Riemannian balls around any point are both strongly geodesically
convex and uniformly normal, with locally uniform positive normal and strong-convexity radii, and
consequently uniform positive radii over any compact set:

1. **Strict convexity of squared radial distance**
   (`exists_isOpen_mem_strictConvexOn_toReal_edist_sq`): near any point `p₀`, the two-point squared
   logarithmic distance `(p, y) ↦ ‖log_p y‖²` is jointly smooth, and at `(p₀, p₀)` its second
   derivative along the geodesic in direction `v` is `2 ‖v‖²`. By continuity on the compact unit
   tangent sphere at `p₀`, there is an open neighbourhood `W` of `p₀` such that for every `p ∈ W`
   and every nonconstant geodesic `γ` in `W`, the squared distance
   `t ↦ (edist p (γ t)).toReal ^ 2` has strictly positive second derivative and is therefore
   strictly convex.
2. **Strong geodesic convexity of small balls**
   (`exists_mem_nhds_isStronglyGeodesicallyConvex_eball`): for `p` near `p₀` and sufficiently small
   `ε > 0`, any `x, y` in the ball of radius `ε` around `p` lie at distance `< 2 ε`, well within
   the uniform normal radius `R` at `x`. Every minimizing geodesic in `M` from `x` to `y` stays
   within distance `< 2 ε ≤ R` of `x` and so coincides with the radial geodesic
   `t ↦ exp_x (t • log_x y)`, while convexity of squared distance from `p` keeps that radial
   geodesic strictly inside the `ε`-ball.
3. **Intersections and smooth contractions**: finite intersections preserve both uniform normality
   and strong geodesic convexity. On any open set `W` enjoying both properties, the radial homotopy
   `H(s, x) = exp_q (s • log_q x)` from a chosen centre `q ∈ W` is smooth on an open domain
   containing `[0, 1] × W` and maps `[0, 1] × W` into `W`; reparametrizing time by
   `Real.smoothTransition` yields a globally smooth contraction `ℝ × W → W` fixing `q`, together
   with its cylinder restriction `W × [0, 1] → W` modelled on `I.prod (𝓡∂ 1)`.

All results are developed over an extended metric space
`[EMetricSpace M] [IsRiemannianManifold I M]` so that disconnected and empty manifolds are covered
without assuming finite distances between components; specializations to `[MetricSpace M]` are
provided alongside.

## Main definitions and results

* `TauCeti.Manifold.IsUniformlyNormal`: every point of a set has a normal tangent ball covering it;
  monotone under inclusion (`IsUniformlyNormal.mono`) and closed under nonempty intersections.
* `TauCeti.Manifold.IsStronglyGeodesicallyConvex`: unique globally minimizing geodesics in `M`
  staying in `U`; closed under intersections (`IsStronglyGeodesicallyConvex.inter`,
  `IsStronglyGeodesicallyConvex.biInter`) and implying path-connectedness when nonempty.
* `TauCeti.Manifold.exists_isOpen_mem_strictConvexOn_toReal_edist_sq`: strict convexity of squared
  distance along nonconstant short geodesics (Lee, Lemma 6.16).
* `TauCeti.Manifold.exists_mem_nhds_isStronglyGeodesicallyConvex_eball`,
  `TauCeti.Manifold.exists_pos_isStronglyGeodesicallyConvex_eball`, and
  `IsCompact.exists_pos_isNormalDomain_and_isStronglyGeodesicallyConvex_eball`: locally uniform and
  compact-set uniform normal and strong-convexity radii (Lee, Theorem 6.17).
* `TauCeti.Manifold.radialGeodesicHomotopy`, `TauCeti.Manifold.radialGeodesicHomotopyDomain`,
  `TauCeti.Manifold.geodesicOpenContract`, and `TauCeti.Manifold.geodesicOpenCylinderContract`:
  the raw radial geodesic contraction on its natural open domain, its `Real.smoothTransition`
  reparametrization on an open submanifold, and its cylinder restriction on `W × [0, 1]`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Ch. 6,
  Lemma 6.16 and Theorem 6.17.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §4, Theorem 4.2 (Whitehead).
-/

public section

noncomputable section

open Bundle Filter Function Manifold Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-! ### Uniformly normal subsets -/

section UniformlyNormal

variable
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- A subset `U` of a Riemannian manifold is *uniformly normal* if every point `q ∈ U` admits a
normal tangent ball `B(0, r)` of positive radius whose exponential image contains `U`. Note that
`r` may depend on `q`, so this property passes to arbitrary subsets. -/
def IsUniformlyNormal (U : Set M) : Prop :=
  ∀ ⦃q⦄, q ∈ U → ∃ r > 0, IsNormalDomain I M q (Metric.ball 0 r) ∧
    U ⊆ riemannianExp I M q '' Metric.ball 0 r

theorem isUniformlyNormal_def {U : Set M} :
    IsUniformlyNormal I U ↔
      ∀ ⦃q⦄, q ∈ U → ∃ r > 0, IsNormalDomain I M q (Metric.ball 0 r) ∧
        U ⊆ riemannianExp I M q '' Metric.ball 0 r := by
  rw [IsUniformlyNormal]

@[simp]
theorem isUniformlyNormal_empty : IsUniformlyNormal I (∅ : Set M) := by
  rw [isUniformlyNormal_def]
  intro _ hq
  exact hq.elim

/-- Uniform normality passes to arbitrary subsets. -/
theorem IsUniformlyNormal.mono {U V : Set M} (hU : IsUniformlyNormal I U) (hVU : V ⊆ U) :
    IsUniformlyNormal I V := by
  rw [isUniformlyNormal_def] at hU ⊢
  intro q hq
  obtain ⟨r, hr, hdom, hsub⟩ := hU (hVU hq)
  exact ⟨r, hr, hdom, hVU.trans hsub⟩

theorem IsUniformlyNormal.inter_left {U V : Set M} (hU : IsUniformlyNormal I U) :
    IsUniformlyNormal I (U ∩ V) :=
  hU.mono inter_subset_left

theorem IsUniformlyNormal.inter_right {U V : Set M} (hV : IsUniformlyNormal I V) :
    IsUniformlyNormal I (U ∩ V) :=
  hV.mono inter_subset_right

/-- Every nonempty intersection of uniformly normal sets is uniformly normal. -/
theorem IsUniformlyNormal.biInter {ι : Type*} {s : Set ι} {U : ι → Set M} (hs : s.Nonempty)
    (hU : ∀ i ∈ s, IsUniformlyNormal I (U i)) : IsUniformlyNormal I (⋂ i ∈ s, U i) :=
  (hU hs.some hs.some_mem).mono (biInter_subset_of_mem hs.some_mem)

/-- Chosen positive normal radius at a point `q` of a uniformly normal set `U`. -/
def IsUniformlyNormal.normalRadius {U : Set M} (hU : IsUniformlyNormal I U) {q : M}
    (hq : q ∈ U) : ℝ :=
  (isUniformlyNormal_def.1 hU hq).choose

theorem IsUniformlyNormal.normalRadius_pos {U : Set M} (hU : IsUniformlyNormal I U) {q : M}
    (hq : q ∈ U) : 0 < hU.normalRadius hq :=
  (isUniformlyNormal_def.1 hU hq).choose_spec.1

theorem IsUniformlyNormal.isNormalDomain_ball {U : Set M} (hU : IsUniformlyNormal I U) {q : M}
    (hq : q ∈ U) : IsNormalDomain I M q (Metric.ball 0 (hU.normalRadius hq)) :=
  (isUniformlyNormal_def.1 hU hq).choose_spec.2.1

theorem IsUniformlyNormal.subset_image_riemannianExp_ball {U : Set M}
    (hU : IsUniformlyNormal I U) {q : M} (hq : q ∈ U) :
    U ⊆ riemannianExp I M q '' Metric.ball 0 (hU.normalRadius hq) :=
  (isUniformlyNormal_def.1 hU hq).choose_spec.2.2

/-- Every point has an open uniformly normal neighbourhood. -/
theorem exists_isOpen_mem_isUniformlyNormal [I.Boundaryless] [T2Space M] (p : M) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ IsUniformlyNormal I W := by
  obtain ⟨r, hr, W, hW, hnorm⟩ := exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M) p
  refine ⟨interior W, isOpen_interior, mem_interior_iff_mem_nhds.2 hW, ?_⟩
  rw [isUniformlyNormal_def]
  intro q hq
  obtain ⟨hqdom, hqsub⟩ := hnorm q (interior_subset hq)
  exact ⟨r, hr, hqdom, interior_subset.trans hqsub⟩

end UniformlyNormal

/-! ### Strict convexity of squared radial distance along short geodesics -/

section StrictConvexDistance

variable
  [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- On a tube of uniformly normal balls of radius `R` over an open set `W₀`, the two-point
squared logarithmic distance `(p, y) ↦ ‖log_p y‖²` is jointly smooth on `W₀ ×ˢ W₀` whenever
`W₀` lies in every normal neighbourhood `exp_p '' B(0, R)`. -/
private theorem contMDiffOn_norm_riemannianLog_sq {W₀ : Set M} {R : ℝ} (hW₀ : IsOpen W₀)
    (hnorm : ∀ p ∈ W₀, IsNormalDomain I M p (Metric.ball 0 R) ∧
      W₀ ⊆ riemannianExp I M p '' Metric.ball 0 R) :
    ContMDiffOn (I.prod I) 𝓘(ℝ) ∞
      (fun x : M × M ↦ ‖riemannianLog I M x.1 (Metric.ball 0 R) x.2‖ ^ 2) (W₀ ×ˢ W₀) := by
  have hsq : ContMDiff I.tangent 𝓘(ℝ) ∞ (fun z : TangentBundle I M ↦ ‖z.2‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using
      (contMDiff_id (I := I.tangent) (n := ∞)).inner_bundle contMDiff_id
  have hlog := contMDiffOn_totalSpaceMk_riemannianLog hW₀ fun q hq ↦ (hnorm q hq).1
  refine (hsq.comp_contMDiffOn hlog).mono ?_
  rintro ⟨p, y⟩ ⟨hp, hy⟩
  exact ⟨hp, (hnorm p hp).2 hy⟩

/-- Joint smoothness at `(((p₀, p₀), w₀), 0)` of `((p, q, w), τ) ↦ ‖log_p (exp_q (τ • v))‖²`
with `v = e.symmL ℝ q w` in the preferred trivialization `e` at `p₀`. -/
private theorem contMDiffAt_norm_riemannianLog_sq_riemannianExp {p₀ : M} {W₀ : Set M} {R : ℝ}
    (hW₀ : IsOpen W₀) (hp₀ : p₀ ∈ W₀)
    (hnorm : ∀ p ∈ W₀, IsNormalDomain I M p (Metric.ball 0 R) ∧
      W₀ ⊆ riemannianExp I M p '' Metric.ball 0 R)
    (w₀ : E) :
    let e := trivializationAt E (TangentSpace I) p₀
    ContMDiffAt (((I.prod I).prod 𝓘(ℝ, E)).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun u : ((M × M) × E) × ℝ ↦
        ‖riemannianLog I M u.1.1.1 (Metric.ball 0 R)
          (riemannianExp I M u.1.1.2 (u.2 • e.symmL ℝ u.1.1.2 u.1.2))‖ ^ 2)
      (((p₀, p₀), w₀), 0) := by
  intro e
  let pt : ((M × M) × E) × ℝ := (((p₀, p₀), w₀), 0)
  have hp₀e : p₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p₀
  have hbase : ContMDiffAt (((I.prod I).prod 𝓘(ℝ, E)).prod 𝓘(ℝ)) I ∞
      (fun u : ((M × M) × E) × ℝ ↦ u.1.1.2) pt :=
    contMDiffAt_snd.comp pt (contMDiffAt_fst.comp pt contMDiffAt_fst)
  have hsymm : ContMDiffAt (((I.prod I).prod 𝓘(ℝ, E)).prod 𝓘(ℝ)) I.tangent ∞
      (fun u : ((M × M) × E) × ℝ ↦
        (⟨u.1.1.2, u.2 • e.symmL ℝ u.1.1.2 u.1.2⟩ : TangentBundle I M)) pt := by
    refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hbase, ?_⟩
    have hvec : ContMDiffAt (((I.prod I).prod 𝓘(ℝ, E)).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞
        (fun u : ((M × M) × E) × ℝ ↦ u.2 • u.1.2) pt :=
      contMDiffAt_snd.smul (contMDiffAt_snd.comp pt contMDiffAt_fst)
    refine hvec.congr_of_eventuallyEq ?_
    filter_upwards [hbase.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hp₀e)] with u hu
    rw [← map_smul, e.symmL_apply hu, e.apply_mk_symm hu]
  have hexp : ContMDiffAt (((I.prod I).prod 𝓘(ℝ, E)).prod 𝓘(ℝ)) I ∞
      (fun u : ((M × M) × E) × ℝ ↦ riemannianExp I M u.1.1.2 (u.2 • e.symmL ℝ u.1.1.2 u.1.2))
      pt := by
    have hz : (⟨p₀, (0 : ℝ) • e.symmL ℝ p₀ w₀⟩ : TangentBundle I M) ∈
        {z : TangentBundle I M | z.2 ∈ expDomain I M z.proj} := by
      simp
    exact (contMDiffOn_riemannianExp_tangentBundle.contMDiffAt
      (isOpen_setOfPred_mem_expDomain.mem_nhds hz)).comp pt hsymm
  have hp_fst : ContMDiffAt (((I.prod I).prod 𝓘(ℝ, E)).prod 𝓘(ℝ)) I ∞
      (fun u : ((M × M) × E) × ℝ ↦ u.1.1.1) pt :=
    contMDiffAt_fst.comp pt (contMDiffAt_fst.comp pt contMDiffAt_fst)
  have hpt : (p₀, riemannianExp I M p₀ ((0 : ℝ) • e.symmL ℝ p₀ w₀)) ∈ W₀ ×ˢ W₀ := by simp [hp₀]
  exact ((contMDiffOn_norm_riemannianLog_sq hW₀ hnorm).contMDiffAt
    ((hW₀.prod hW₀).mem_nhds hpt)).comp pt (hp_fst.prodMk hexp)

/-- Along an exponential ray `τ ↦ exp_q (τ • v)` read through the preferred trivialization at `p₀`,
the second `τ`-derivative at `0` of `(p, y) ↦ ‖log_p y‖²` varies continuously in `(p, q, w)` near
`(p₀, p₀, w₀)`. -/
private theorem continuousAt_iteratedDeriv_two_riemannianLog_sq {p₀ : M} {W₀ : Set M} {R : ℝ}
    (hW₀ : IsOpen W₀) (hp₀ : p₀ ∈ W₀)
    (hnorm : ∀ p ∈ W₀, IsNormalDomain I M p (Metric.ball 0 R) ∧
      W₀ ⊆ riemannianExp I M p '' Metric.ball 0 R)
    (w₀ : E) :
    let e := trivializationAt E (TangentSpace I) p₀
    ContinuousAt
      (fun z : (M × M) × E ↦
        iteratedDeriv 2
          (fun τ : ℝ ↦
            ‖riemannianLog I M z.1.1 (Metric.ball 0 R)
              (riemannianExp I M z.1.2 (τ • e.symmL ℝ z.1.2 z.2))‖ ^ 2) 0)
      ((p₀, p₀), w₀) := by
  intro e
  set F : (M × M) × E → ℝ → ℝ := fun z τ ↦
    ‖riemannianLog I M z.1.1 (Metric.ball 0 R)
      (riemannianExp I M z.1.2 (τ • e.symmL ℝ z.1.2 z.2))‖ ^ 2
  set c := extChartAt I p₀
  let toM : ((E × E) × E) → (M × M) × E := fun x ↦ ((c.symm x.1.1, c.symm x.1.2), x.2)
  let fromM : (M × M) × E → (E × E) × E := fun z ↦ ((c z.1.1, c z.1.2), z.2)
  let x₀ : (E × E) × E := fromM ((p₀, p₀), w₀)
  have hc_src : p₀ ∈ c.source := mem_extChartAt_source p₀
  have htoM : ContMDiffAt 𝓘(ℝ, (E × E) × E) ((I.prod I).prod 𝓘(ℝ, E)) ∞ toM x₀ := by
    have hcs := (contMDiffOn_extChartAt_symm (I := I) (n := ∞) p₀).contMDiffAt
      ((isOpen_extChartAt_target (I := I) p₀).mem_nhds (mem_extChartAt_target (I := I) p₀))
    exact ((hcs.comp x₀ (contDiffAt_fst.comp x₀ contDiffAt_fst).contMDiffAt).prodMk
      (hcs.comp x₀ (contDiffAt_snd.comp x₀ contDiffAt_fst).contMDiffAt)).prodMk
        contDiffAt_snd.contMDiffAt
  set g : ((E × E) × E) × ℝ → ℝ := fun y ↦ F (toM y.1) y.2
  have htoM_x₀ : toM x₀ = ((p₀, p₀), w₀) := by simp [toM, x₀, fromM, c.left_inv hc_src]
  have hg : ContDiffAt ℝ 2 g (x₀, 0) := by
    rw [← contMDiffAt_iff_contDiffAt]
    have hF := contMDiffAt_norm_riemannianLog_sq_riemannianExp hW₀ hp₀ hnorm w₀
    exact ((htoM_x₀ ▸ hF).comp (x₀, 0)
      ((htoM.comp (x₀, 0) contDiffAt_fst.contMDiffAt).prodMk contDiffAt_snd.contMDiffAt)).of_le
        (by simp)
  have hcont_x : ContinuousAt (fun x ↦ iteratedDeriv 2 (fun τ ↦ g (x, τ)) 0) x₀ := by
    have hfd : ContinuousAt (fun x ↦ fderiv ℝ (fderiv ℝ g) (x, 0) (0, 1) (0, 1)) x₀ :=
      (((hg.continuousAt_fderiv_fderiv le_rfl).comp (x := x₀)
        (continuousAt_id.prodMk continuousAt_const)).clm_apply continuousAt_const).clm_apply
          continuousAt_const
    refine hfd.congr_of_eventuallyEq ?_
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually
      (hg.eventually (by simp))] with x hgx
    dsimp only [id] at hgx
    rw [← TauCeti.fderiv_fderiv_slice_right_apply hgx 1 1,
      TauCeti.fderiv_fderiv_apply_eq_smul_iteratedDeriv]
    simp
  have hfromM : ContinuousAt fromM ((p₀, p₀), w₀) :=
    ((ContinuousAt.comp (x := ((p₀, p₀), w₀)) (continuousAt_extChartAt (I := I) p₀)
      (continuous_fst.comp continuous_fst).continuousAt).prodMk
      (ContinuousAt.comp (x := ((p₀, p₀), w₀)) (continuousAt_extChartAt (I := I) p₀)
        (continuous_snd.comp continuous_fst).continuousAt)).prodMk continuous_snd.continuousAt
  refine (ContinuousAt.comp (x := ((p₀, p₀), w₀)) hcont_x hfromM).congr_of_eventuallyEq ?_
  filter_upwards [(((isOpen_extChartAt_source p₀).prod (isOpen_extChartAt_source p₀)).prod
    isOpen_univ).mem_nhds ⟨⟨hc_src, hc_src⟩, mem_univ w₀⟩] with z hz
  have hleft : toM (fromM z) = z :=
    Prod.ext (Prod.ext (c.left_inv hz.1.1) (c.left_inv hz.1.2)) rfl
  dsimp only [Function.comp_apply, g]
  rw [hleft]

omit [I.Boundaryless] in
/-- At the base point `p₀`, `τ ↦ ‖log_{p₀} (exp_{p₀} (τ • v₀))‖²` agrees near `0` with
`τ² ‖v₀‖²`, so its second derivative at `0` is `2 ‖v₀‖²`. -/
private theorem iteratedDeriv_two_riemannianLog_sq_self {p₀ : M} {R : ℝ} (hR : 0 < R)
    (hdom₀ : IsNormalDomain I M p₀ (Metric.ball 0 R)) (v₀ : TangentSpace I p₀) :
    iteratedDeriv 2
      (fun τ : ℝ ↦ ‖riemannianLog I M p₀ (Metric.ball 0 R) (riemannianExp I M p₀ (τ • v₀))‖ ^ 2)
      0 = 2 * ‖v₀‖ ^ 2 := by
  have hev : (fun τ : ℝ ↦
      ‖riemannianLog I M p₀ (Metric.ball 0 R) (riemannianExp I M p₀ (τ • v₀))‖ ^ 2) =ᶠ[𝓝 0]
      fun τ : ℝ ↦ τ ^ 2 * ‖v₀‖ ^ 2 := by
    have hpre : IsOpen ((fun τ : ℝ ↦ τ • v₀) ⁻¹' Metric.ball (0 : TangentSpace I p₀) R) :=
      Metric.isOpen_ball.preimage (continuous_id.smul continuous_const)
    filter_upwards [hpre.mem_nhds (by simp [Metric.mem_ball_self hR])] with τ hτ
    rw [hdom₀.riemannianLog_riemannianExp hτ, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hderiv_quad : iteratedDeriv 2 (fun τ : ℝ ↦ τ ^ 2 * ‖v₀‖ ^ 2) 0 = 2 * ‖v₀‖ ^ 2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hd1 : deriv (fun τ : ℝ ↦ τ ^ 2 * ‖v₀‖ ^ 2) = fun τ : ℝ ↦ (2 * τ) * ‖v₀‖ ^ 2 :=
      funext fun τ ↦ (((hasDerivAt_pow 2 τ).mul_const (‖v₀‖ ^ 2)).deriv).trans (by simp)
    rw [hd1]
    exact (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (‖v₀‖ ^ 2)).deriv.trans (by ring)
  exact (hev.iteratedDeriv_eq 2).trans hderiv_quad

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Continuity at `((p₀, p₀), w)` of the squared fibre norm `z ↦ ‖e.symmL ℝ z.1.2 z.2‖²` read
through the preferred trivialization `e` at `p₀`. -/
private theorem continuousAt_norm_symmL_sq (p₀ : M) (w : E) :
    let e := trivializationAt E (TangentSpace I) p₀
    ContinuousAt (fun z : (M × M) × E ↦ ‖e.symmL ℝ z.1.2 z.2‖ ^ 2) ((p₀, p₀), w) := by
  intro e
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hp₀e : p₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p₀
  have hbase : ContinuousAt (fun z : (M × M) × E ↦ z.1.2) ((p₀, p₀), w) :=
    (continuous_snd.comp continuous_fst).continuousAt
  have hsec : ContinuousAt (fun z : (M × M) × E ↦
      (⟨z.1.2, e.symmL ℝ z.1.2 z.2⟩ : TangentBundle I M)) ((p₀, p₀), w) := by
    refine (FiberBundle.continuousAt_totalSpace E _).2 ⟨hbase, ?_⟩
    refine continuous_snd.continuousAt.congr_of_eventuallyEq ?_
    filter_upwards [hbase.preimage_mem_nhds (e.open_baseSet.mem_nhds hp₀e)] with z hz
    rw [e.symmL_apply hz, e.apply_mk_symm hz]
  exact ((TauCeti.continuous_norm_bundle E (TangentSpace I)).continuousAt.comp hsec).pow 2

/-- Compactness on the unit sphere in `E` yields an open neighbourhood `W ⊆ W₀` of `p₀` on which
`‖e.symmL ℝ q u‖²` is bounded above by the second `τ`-derivative at `0` for all `u ∈ sphere 0 1`. -/
private theorem exists_isOpen_mem_le_iteratedDeriv_two_on_sphere {p₀ : M} {W₀ : Set M} {R : ℝ}
    (hR : 0 < R) (hW₀ : IsOpen W₀) (hp₀ : p₀ ∈ W₀)
    (hW₀_base : W₀ ⊆ (trivializationAt E (TangentSpace I) p₀).baseSet)
    (hnorm : ∀ p ∈ W₀, IsNormalDomain I M p (Metric.ball 0 R) ∧
      W₀ ⊆ riemannianExp I M p '' Metric.ball 0 R) :
    let e := trivializationAt E (TangentSpace I) p₀
    ∃ W : Set M, IsOpen W ∧ p₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ p ∈ W, ∀ q ∈ W, ∀ u ∈ sphere (0 : E) 1,
        ‖e.symmL ℝ q u‖ ^ 2 ≤
          iteratedDeriv 2
            (fun τ : ℝ ↦
              ‖riemannianLog I M p (Metric.ball 0 R)
                (riemannianExp I M q (τ • e.symmL ℝ q u))‖ ^ 2) 0 := by
  intro e
  set Q : (M × M) × E → ℝ := fun z ↦
    iteratedDeriv 2
      (fun τ : ℝ ↦
        ‖riemannianLog I M z.1.1 (Metric.ball 0 R)
          (riemannianExp I M z.1.2 (τ • e.symmL ℝ z.1.2 z.2))‖ ^ 2) 0
  set N : (M × M) × E → ℝ := fun z ↦ ‖e.symmL ℝ z.1.2 z.2‖ ^ 2
  have hopen_lt : ∀ w ∈ sphere (0 : E) 1,
      ∃ U : Set (M × M), IsOpen U ∧ (p₀, p₀) ∈ U ∧ U ⊆ W₀ ×ˢ W₀ ∧
        ∃ V : Set E, IsOpen V ∧ w ∈ V ∧ ∀ z ∈ U ×ˢ V, N z ≤ Q z := by
    intro w hw
    have hw_ne : w ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hw
      exact norm_ne_zero_iff.1 (by simp [hw])
    have hv_ne : e.symmL ℝ p₀ w ≠ 0 := fun hv0 ↦
      hw_ne (by simpa [e.continuousLinearMapAt_symmL (hW₀_base hp₀)] using
        congrArg (e.continuousLinearMapAt ℝ p₀) hv0)
    have hpos : N ((p₀, p₀), w) < Q ((p₀, p₀), w) := by
      have hQN : Q ((p₀, p₀), w) = 2 * N ((p₀, p₀), w) :=
        iteratedDeriv_two_riemannianLog_sq_self hR (hnorm p₀ hp₀).1 (e.symmL ℝ p₀ w)
      have hNpos : 0 < N ((p₀, p₀), w) := sq_pos_of_ne_zero (norm_ne_zero_iff.2 hv_ne)
      linarith
    have hcontQ := continuousAt_iteratedDeriv_two_riemannianLog_sq hW₀ hp₀ hnorm w
    have hcontN := continuousAt_norm_symmL_sq (I := I) p₀ w
    have hev : ∀ᶠ z in 𝓝 ((p₀, p₀), w), N z ≤ Q z :=
      (tendsto_order.1 (hcontQ.sub hcontN)).1 0 (sub_pos.2 hpos) |>.mono fun _ hz ↦
        (sub_pos.1 hz).le
    obtain ⟨U₁, hU₁, V₁, hV₁, hUV⟩ := mem_nhds_prod_iff.1 hev
    obtain ⟨U, hUU₁, hUopen, hp₀U⟩ := _root_.mem_nhds_iff.1
      (inter_mem hU₁ ((hW₀.prod hW₀).mem_nhds ⟨hp₀, hp₀⟩))
    obtain ⟨V, hVV₁, hVopen, hwV⟩ := _root_.mem_nhds_iff.1 hV₁
    exact ⟨U, hUopen, hp₀U, fun _ hx ↦ (hUU₁ hx).2, V, hVopen, hwV,
      fun _ hz ↦ hUV ⟨(hUU₁ hz.1).1, hVV₁ hz.2⟩⟩
  choose! U_w hU_open hp₀U _ V_w hV_open hwV hNQ using hopen_lt
  obtain ⟨s, hs_sub, hs_cov⟩ := (isCompact_sphere (0 : E) 1).elim_nhds_subcover V_w
    fun w hw ↦ (hV_open w hw).mem_nhds (hwV w hw)
  set U_all : Set (M × M) := (W₀ ×ˢ W₀) ∩ ⋂ w ∈ s, U_w w
  have hU_all_open : IsOpen U_all :=
    (hW₀.prod hW₀).inter (isOpen_biInter_finset fun w hw ↦ hU_open w (hs_sub w hw))
  have hp₀_all : (p₀, p₀) ∈ U_all :=
    ⟨⟨hp₀, hp₀⟩, mem_iInter₂.2 fun w hw ↦ hp₀U w (hs_sub w hw)⟩
  obtain ⟨A₁, hA₁, A₂, hA₂, hAA⟩ := mem_nhds_prod_iff.1 (hU_all_open.mem_nhds hp₀_all)
  refine ⟨interior (A₁ ∩ A₂) ∩ W₀, isOpen_interior.inter hW₀,
    ⟨mem_interior_iff_mem_nhds.2 (inter_mem hA₁ hA₂), hp₀⟩, inter_subset_right,
    fun p hp q hq u hu ↦ ?_⟩
  obtain ⟨w₁, hw₁s, huV⟩ := mem_iUnion₂.1 (hs_cov hu)
  have hpq_all : (p, q) ∈ U_all := hAA ⟨(interior_subset hp.1).1, (interior_subset hq.1).2⟩
  exact hNQ w₁ (hs_sub w₁ hw₁s) ((p, q), u) ⟨(mem_iInter₂.1 hpq_all.2) w₁ hw₁s, huV⟩

/-- Quadratic homogeneity in the tangent vector of the second `τ`-derivative at `0` of
`τ ↦ ‖log_p (exp_q (τ • v))‖²`. -/
private theorem iteratedDeriv_two_riemannianLog_sq_smul {p q : M} {R : ℝ}
    (hdom_p : IsNormalDomain I M p (Metric.ball 0 R))
    (hq_mem : q ∈ riemannianExp I M p '' Metric.ball 0 R)
    (c : ℝ) (u : TangentSpace I q) :
    iteratedDeriv 2
      (fun τ : ℝ ↦
        ‖riemannianLog I M p (Metric.ball 0 R) (riemannianExp I M q (τ • (c • u)))‖ ^ 2) 0 =
      c ^ 2 * iteratedDeriv 2
        (fun τ : ℝ ↦
          ‖riemannianLog I M p (Metric.ball 0 R) (riemannianExp I M q (τ • u))‖ ^ 2) 0 := by
  let φ : ℝ → ℝ := fun τ ↦
    ‖riemannianLog I M p (Metric.ball 0 R) (riemannianExp I M q (τ • u))‖ ^ 2
  have hφ_smooth : ContDiffAt ℝ 2 φ 0 := by
    have hexp_u := contMDiffAt_riemannianExp_smul_zero (I := I) (M := M) q u
    have hF_q : ContMDiffAt I 𝓘(ℝ) ∞
        (fun y : M ↦ ‖riemannianLog I M p (Metric.ball 0 R) y‖ ^ 2) q :=
      ((contDiff_norm_sq ℝ).contMDiff.comp_contMDiffOn
        hdom_p.contMDiffOn_riemannianLog).contMDiffAt (hdom_p.isOpen_image.mem_nhds hq_mem)
    have hexp0 : riemannianExp I M q ((0 : ℝ) • u) = q := by simp
    rw [← contMDiffAt_iff_contDiffAt]
    exact ((hexp0 ▸ hF_q).comp 0 hexp_u).of_le (by simp)
  have hcomp := TauCeti.iteratedDeriv_two_comp (f := φ) (γ := fun τ : ℝ ↦ c * τ) (t := 0)
    (by simpa using hφ_smooth) (contDiffAt_const.mul contDiffAt_id)
  have hd1 : deriv (fun τ : ℝ ↦ c * τ) 0 = c := by simp
  have hd2 : iteratedDeriv 2 (fun τ : ℝ ↦ c * τ) 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hc_fn : deriv (fun τ : ℝ ↦ c * τ) = fun _ ↦ c := funext fun _ ↦ by simp
    simp [hc_fn]
  have hfun : (fun τ : ℝ ↦
      ‖riemannianLog I M p (Metric.ball 0 R) (riemannianExp I M q (τ • (c • u)))‖ ^ 2) =
      φ ∘ fun τ : ℝ ↦ c * τ := funext fun _ ↦ by simp [φ, smul_smul, mul_comm]
  rw [hfun, hcomp, hd1, hd2, mul_zero, map_zero, add_zero,
    TauCeti.fderiv_fderiv_apply_eq_smul_iteratedDeriv, smul_eq_mul, ← sq]

/-- Lower bound on the second derivative of squared logarithmic distance along exponential rays
near a point `p₀`: there is an open neighbourhood `W` of `p₀` such that for all `p, q ∈ W` and
every `v : TangentSpace I q`, the second `τ`-derivative at `0` of
`τ ↦ ‖log_p (exp_q (τ • v))‖²` is at least `‖v‖²`. -/
private theorem exists_isOpen_mem_le_iteratedDeriv_two_riemannianLog_sq (p₀ : M) :
    ∃ R > 0, ∃ W : Set M, IsOpen W ∧ p₀ ∈ W ∧
      (∀ p ∈ W, IsNormalDomain I M p (Metric.ball 0 R) ∧
        W ⊆ riemannianExp I M p '' Metric.ball 0 R) ∧
      ∀ p ∈ W, ∀ q ∈ W, ∀ v : TangentSpace I q,
        ‖v‖ ^ 2 ≤ iteratedDeriv 2
          (fun τ : ℝ ↦
            ‖riemannianLog I M p (Metric.ball 0 R) (riemannianExp I M q (τ • v))‖ ^ 2) 0 := by
  obtain ⟨R, hR, W', hW', hnorm'⟩ := exists_mem_nhds_forall_isNormalDomain_ball (I := I) (M := M) p₀
  let e := trivializationAt E (TangentSpace I) p₀
  set W₀ := interior W' ∩ e.baseSet
  have hW₀ : IsOpen W₀ := isOpen_interior.inter e.open_baseSet
  have hp₀ : p₀ ∈ W₀ :=
    ⟨mem_interior_iff_mem_nhds.2 hW', mem_baseSet_trivializationAt E (TangentSpace I) p₀⟩
  have hnorm : ∀ p ∈ W₀, IsNormalDomain I M p (Metric.ball 0 R) ∧
      W₀ ⊆ riemannianExp I M p '' Metric.ball 0 R := fun p hp ↦
    ⟨(hnorm' p (interior_subset hp.1)).1,
      (inter_subset_left.trans interior_subset).trans (hnorm' p (interior_subset hp.1)).2⟩
  obtain ⟨W, hW_open, hp₀W, hWW₀, hsphere⟩ :=
    exists_isOpen_mem_le_iteratedDeriv_two_on_sphere hR hW₀ hp₀ inter_subset_right hnorm
  refine ⟨R, hR, W, hW_open, hp₀W, fun p hp ↦ ⟨(hnorm p (hWW₀ hp)).1,
      hWW₀.trans (hnorm p (hWW₀ hp)).2⟩, fun p hp q hq v ↦ ?_⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · have hconst : (fun τ : ℝ ↦
        ‖riemannianLog I M p (Metric.ball 0 R) (riemannianExp I M q (τ • (0 : TangentSpace I q)))‖
          ^ 2) = fun _ ↦ ‖riemannianLog I M p (Metric.ball 0 R) q‖ ^ 2 :=
      funext fun _ ↦ by simp
    rw [hconst, iteratedDeriv_const]
    simp
  · set w : E := e.continuousLinearMapAt ℝ q v
    have hsymm_w : e.symmL ℝ q w = v := e.symmL_continuousLinearMapAt (hWW₀ hq).2 v
    have hw0 : w ≠ 0 := fun h0 ↦ hv0 (hsymm_w ▸ by simp [h0])
    set c : ℝ := ‖w‖
    have hc : 0 < c := norm_pos_iff.2 hw0
    set u : E := c⁻¹ • w
    have hu_sphere : u ∈ sphere (0 : E) 1 := by simp [u, c, norm_smul, inv_mul_cancel₀ hc.ne']
    have hv_eq : v = c • e.symmL ℝ q u := by
      rw [← hsymm_w]
      simp [u, smul_smul, mul_inv_cancel₀ hc.ne']
    have hnorm_eq : ‖v‖ ^ 2 = c ^ 2 * ‖e.symmL ℝ q u‖ ^ 2 := by
      simp [hv_eq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hv_eq, iteratedDeriv_two_riemannianLog_sq_smul (hnorm p (hWW₀ hp)).1
      ((hnorm p (hWW₀ hp)).2 (hWW₀ hq)) c (e.symmL ℝ q u), ← hv_eq, hnorm_eq]
    exact mul_le_mul_of_nonneg_left (hsphere p hp q hq u hu_sphere) (sq_nonneg c)

variable [IsRiemannianManifold I M]

/-- Positivity of the second ray-derivative of `‖log_p ·‖²` on `W` makes `t ↦ ‖log_p (γ t)‖²`
strictly convex along any nonconstant geodesic `γ` on `[a, b]` staying in `W`. -/
private theorem strictConvexOn_norm_riemannianLog_sq_comp_geodesic {W : Set M} {R : ℝ} {p : M}
    (hdom_p : IsNormalDomain I M p (Metric.ball 0 R))
    (hW_sub : W ⊆ riemannianExp I M p '' Metric.ball 0 R)
    (hderiv2 : ∀ q ∈ W, ∀ v : TangentSpace I q,
      ‖v‖ ^ 2 ≤ iteratedDeriv 2
        (fun τ : ℝ ↦
          ‖riemannianLog I M p (Metric.ball 0 R) (riemannianExp I M q (τ • v))‖ ^ 2) 0)
    {a b : ℝ} {γ : ℝ → M} (hab : a < b) (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (hγW : MapsTo γ (Icc a b) W) (hnonconst : ∃ t ∈ Icc a b, γ t ≠ γ a) :
    StrictConvexOn ℝ (Icc a b)
      ((fun y : M ↦ ‖riemannianLog I M p (Metric.ball 0 R) y‖ ^ 2) ∘ γ) := by
  let f : M → ℝ := fun y ↦ ‖riemannianLog I M p (Metric.ball 0 R) y‖ ^ 2
  have hspeed_pos : 0 < ‖curveVelocityWithin I γ (Icc a b) a‖ := by
    by_contra hle
    have hzero : ‖curveVelocityWithin I γ (Icc a b) a‖ = 0 :=
      le_antisymm (not_lt.1 hle) (norm_nonneg _)
    obtain ⟨t, ht, hne⟩ := hnonconst
    have hlen0 : pathELength I γ a t = 0 := by
      rw [hγ.pathELength_eq isPreconnected_Icc (left_mem_Icc.2 hab.le) ht
        (left_mem_Icc.2 hab.le), ← ofReal_norm, hzero]
      simp
    have hed0 : edist (γ a) (γ t) = 0 :=
      nonpos_iff_eq_zero.1 <| (IsRiemannianManifold.edist_le_pathELength
        ((hγ.contMDiffOn.mono (Icc_subset_Icc le_rfl ht.2)).of_le (by norm_num)) ht.1).trans
          hlen0.le
    exact hne (edist_eq_zero.1 hed0).symm
  have hcont : ContinuousOn (f ∘ γ) (Icc a b) :=
    ((contDiff_norm_sq ℝ (n := 0)).continuous.comp_continuousOn
      hdom_p.continuousOn_riemannianLog).comp hγ.continuousOn fun t ht ↦ hW_sub (hγW ht)
  refine strictConvexOn_of_deriv2_pos (convex_Icc a b) hcont ?_
  rw [interior_Icc]
  intro t₀ ht₀
  have hfrom := (hγ.mono (uniqueDiffOn_Ioo a b)
    Ioo_subset_Icc_self).isGeodesicCurveOnFrom_comp_add_const ht₀
  have hloc_eq : (fun u : ℝ ↦ (f ∘ γ) (u + t₀)) =ᶠ[𝓝 0]
      fun u : ℝ ↦ f (riemannianExp I M (γ t₀) (u • curveVelocity I γ t₀)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨sub_neg.2 ht₀.1, sub_pos.2 ht₀.2⟩] with u hu
    exact congrArg f ((hfrom.eqOn_maximalGeodesic hu).symm.trans
      (riemannianExp_smul (I := I) (M := M) (γ t₀) (curveVelocity I γ t₀) u).symm)
  have hd2_eq : (deriv^[2] (f ∘ γ)) t₀ =
      iteratedDeriv 2
        (fun u : ℝ ↦ f (riemannianExp I M (γ t₀) (u • curveVelocity I γ t₀))) 0 := by
    rw [← congrFun (iteratedDeriv_eq_iterate (n := 2) (f := f ∘ γ)) t₀]
    have htr := congrFun (iteratedDeriv_comp_add_const 2 (f ∘ γ) t₀) 0
    rw [zero_add] at htr
    exact htr.symm.trans (hloc_eq.iteratedDeriv_eq 2)
  have hvel_eq : ‖curveVelocity I γ t₀‖ = ‖curveVelocityWithin I γ (Icc a b) a‖ := by
    rw [← curveVelocityWithin_of_mem_nhds
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht₀) Ioo_subset_Icc_self)]
    exact hγ.norm_curveVelocityWithin_eq isPreconnected_Icc (Ioo_subset_Icc_self ht₀)
      (left_mem_Icc.2 hab.le)
  rw [hd2_eq]
  calc 0 < ‖curveVelocityWithin I γ (Icc a b) a‖ ^ 2 := sq_pos_of_pos hspeed_pos
    _ = ‖curveVelocity I γ t₀‖ ^ 2 := by rw [hvel_eq]
    _ ≤ iteratedDeriv 2
          (fun u : ℝ ↦ f (riemannianExp I M (γ t₀) (u • curveVelocity I γ t₀))) 0 :=
        hderiv2 (γ t₀) (hγW (Ioo_subset_Icc_self ht₀)) (curveVelocity I γ t₀)

/-- **Strict convexity of squared radial distance along short geodesics (Lee, Lemma 6.16).**
Every point `p₀` has a radius `R > 0` and an open neighbourhood `W` such that at each `p ∈ W` the
tangent ball `B(0, R)` is a normal domain and `W ⊆ Metric.eball p (ENNReal.ofReal R)`, and along
any nonconstant geodesic `γ` on `[a, b]` staying in `W` the squared distance
`t ↦ (edist p (γ t)).toReal ^ 2` is strictly convex on `[a, b]`. -/
theorem exists_isOpen_mem_strictConvexOn_toReal_edist_sq (p₀ : M) :
    ∃ R > 0, ∃ W : Set M, IsOpen W ∧ p₀ ∈ W ∧
      (∀ p ∈ W, IsNormalDomain I M p (Metric.ball 0 R) ∧
        W ⊆ Metric.eball p (ENNReal.ofReal R)) ∧
      ∀ p ∈ W, ∀ {a b : ℝ} {γ : ℝ → M}, a < b → IsGeodesicCurveOn I γ (Icc a b) →
        MapsTo γ (Icc a b) W → (∃ t ∈ Icc a b, γ t ≠ γ a) →
        StrictConvexOn ℝ (Icc a b) (fun t ↦ (edist p (γ t)).toReal ^ 2) := by
  obtain ⟨R, hR, W, hW_open, hp₀W, hnorm, hderiv2⟩ :=
    exists_isOpen_mem_le_iteratedDeriv_two_riemannianLog_sq (I := I) p₀
  refine ⟨R, hR, W, hW_open, hp₀W, fun p hp ↦ ?_, fun p hp {a b γ} hab hγ hγW hnonconst ↦ ?_⟩
  · refine ⟨(hnorm p hp).1, ?_⟩
    rw [← (hnorm p hp).1.image_riemannianExp_ball subset_rfl]
    exact (hnorm p hp).2
  · have hdom_p := (hnorm p hp).1
    let f : M → ℝ := fun y ↦ ‖riemannianLog I M p (Metric.ball 0 R) y‖ ^ 2
    have hf_eq : EqOn (fun t ↦ (edist p (γ t)).toReal ^ 2) (f ∘ γ) (Icc a b) := fun t ht ↦ by
      have hmem : γ t ∈ riemannianExp I M p '' Metric.ball 0 R := (hnorm p hp).2 (hγW ht)
      simp only [Function.comp_apply, f, hdom_p.edist_eq_enorm_riemannianLog_of_mem_ball
        subset_rfl hmem, toReal_eNorm]
    have hstrict := strictConvexOn_norm_riemannianLog_sq_comp_geodesic hdom_p (hnorm p hp).2
      (hderiv2 p hp) hab hγ hγW hnonconst
    refine ⟨convex_Icc a b, fun x hx y hy hxy α β hα hβ hαβ ↦ ?_⟩
    rw [hf_eq ((convex_Icc a b) hx hy hα.le hβ.le hαβ), hf_eq hx, hf_eq hy]
    exact hstrict.2 hx hy hxy hα hβ hαβ

end StrictConvexDistance

section StrictConvexMetricSpace

variable
  [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- Metric-space form of `exists_isOpen_mem_strictConvexOn_toReal_edist_sq`: near any point `p₀`,
`t ↦ dist p (γ t) ^ 2` is strictly convex along nonconstant geodesics in `W`. -/
theorem exists_isOpen_mem_strictConvexOn_dist_sq (p₀ : M) :
    ∃ R > 0, ∃ W : Set M, IsOpen W ∧ p₀ ∈ W ∧
      (∀ p ∈ W, IsNormalDomain I M p (Metric.ball 0 R) ∧ W ⊆ Metric.ball p R) ∧
      ∀ p ∈ W, ∀ {a b : ℝ} {γ : ℝ → M}, a < b → IsGeodesicCurveOn I γ (Icc a b) →
        MapsTo γ (Icc a b) W → (∃ t ∈ Icc a b, γ t ≠ γ a) →
        StrictConvexOn ℝ (Icc a b) (fun t ↦ dist p (γ t) ^ 2) := by
  obtain ⟨R, hR, W, hWo, hp₀W, hnorm, hconv⟩ :=
    exists_isOpen_mem_strictConvexOn_toReal_edist_sq (I := I) p₀
  refine ⟨R, hR, W, hWo, hp₀W, fun p hp ↦ ?_, fun p hp {a b γ} hab hγ hγW hne ↦ ?_⟩
  · refine ⟨(hnorm p hp).1, ?_⟩
    simpa only [Metric.eball_ofReal] using (hnorm p hp).2
  · simpa only [← dist_edist] using hconv p hp hab hγ hγW hne

end StrictConvexMetricSpace

/-! ### Strong geodesic convexity and Whitehead–Lee Theorem 6.17 -/

section StronglyGeodesicallyConvex

variable
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- A subset `U` of a Riemannian manifold `M` is *strongly geodesically convex* if every pair of
points `x, y ∈ U` is joined by a globally minimizing geodesic segment `γ` on `[0, 1]` whose image
lies in `U`, and every minimizing geodesic segment in `M` from `x` to `y` agrees with `γ` on
`[0, 1]` (without assuming the competitor stays in `U`). -/
def IsStronglyGeodesicallyConvex (U : Set M) : Prop :=
  ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U →
    ∃ γ : ℝ → M, IsGeodesicCurveOn I γ (Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧
      pathELength I γ 0 1 = edist x y ∧ MapsTo γ (Icc 0 1) U ∧
      ∀ ⦃γ' : ℝ → M⦄, IsGeodesicCurveOn I γ' (Icc 0 1) → γ' 0 = x → γ' 1 = y →
        pathELength I γ' 0 1 ≤ edist x y → EqOn γ' γ (Icc 0 1)

theorem isStronglyGeodesicallyConvex_def {U : Set M} :
    IsStronglyGeodesicallyConvex I U ↔
      ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U →
        ∃ γ : ℝ → M, IsGeodesicCurveOn I γ (Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧
          pathELength I γ 0 1 = edist x y ∧ MapsTo γ (Icc 0 1) U ∧
          ∀ ⦃γ' : ℝ → M⦄, IsGeodesicCurveOn I γ' (Icc 0 1) → γ' 0 = x → γ' 1 = y →
            pathELength I γ' 0 1 ≤ edist x y → EqOn γ' γ (Icc 0 1) := by
  rw [IsStronglyGeodesicallyConvex]

@[simp]
theorem isStronglyGeodesicallyConvex_empty : IsStronglyGeodesicallyConvex I (∅ : Set M) := by
  rw [isStronglyGeodesicallyConvex_def]
  intro _ hx
  exact hx.elim

/-- Every nonempty strongly geodesically convex set is path-connected. -/
theorem IsStronglyGeodesicallyConvex.isPathConnected {U : Set M}
    (hU : IsStronglyGeodesicallyConvex I U) (hne : U.Nonempty) : IsPathConnected U := by
  refine ⟨hne.some, hne.some_mem, fun {y} hy ↦ ?_⟩
  obtain ⟨γ, hγ, h0, h1, -, hmaps, -⟩ := isStronglyGeodesicallyConvex_def.1 hU hne.some_mem hy
  refine ⟨{ toFun := fun t : unitInterval ↦ γ t.1
            continuous_toFun := hγ.continuousOn.comp_continuous continuous_subtype_val fun t ↦ t.2
            source' := h0
            target' := h1 }, fun t ↦ hmaps t.2⟩

/-- Every nonempty strongly geodesically convex set is connected. -/
theorem IsStronglyGeodesicallyConvex.isConnected {U : Set M}
    (hU : IsStronglyGeodesicallyConvex I U) (hne : U.Nonempty) : IsConnected U :=
  (hU.isPathConnected hne).isConnected

/-- The intersection of two strongly geodesically convex sets is strongly geodesically convex:
global uniqueness forces the minimizing geodesic in `U` and the minimizing geodesic in `V` between
two points of `U ∩ V` to coincide. -/
theorem IsStronglyGeodesicallyConvex.inter {U V : Set M}
    (hU : IsStronglyGeodesicallyConvex I U) (hV : IsStronglyGeodesicallyConvex I V) :
    IsStronglyGeodesicallyConvex I (U ∩ V) := by
  rw [isStronglyGeodesicallyConvex_def] at hU hV ⊢
  rintro x ⟨hxU, hxV⟩ y ⟨hyU, hyV⟩
  obtain ⟨γU, hγU, h0U, h1U, hlenU, hmapsU, huniqU⟩ := hU hxU hyU
  obtain ⟨γV, hγV, h0V, h1V, hlenV, hmapsV, -⟩ := hV hxV hyV
  have heq : EqOn γV γU (Icc 0 1) := huniqU hγV h0V h1V hlenV.le
  exact ⟨γU, hγU, h0U, h1U, hlenU, fun t ht ↦ ⟨hmapsU ht, heq ht ▸ hmapsV ht⟩, huniqU⟩

/-- Every nonempty finite intersection of strongly geodesically convex sets is strongly
geodesically convex. -/
theorem IsStronglyGeodesicallyConvex.biInter {ι : Type*} {s : Finset ι} {U : ι → Set M}
    (hs : s.Nonempty) (hU : ∀ i ∈ s, IsStronglyGeodesicallyConvex I (U i)) :
    IsStronglyGeodesicallyConvex I (⋂ i ∈ s, U i) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    simpa using hU i (Finset.mem_singleton_self i)
  | cons i t hit _ ih =>
    have hcons : (⋂ j ∈ Finset.cons i t hit, U j) = U i ∩ ⋂ j ∈ t, U j := by
      simp [Finset.cons_eq_insert]
    rw [hcons]
    exact (hU i (Finset.mem_cons_self i t)).inter
      (ih fun j hj ↦ hU j (Finset.mem_cons_of_mem hj))

/-- Any two points of a strongly geodesically convex set lie at finite Riemannian distance. -/
theorem IsStronglyGeodesicallyConvex.edist_ne_top {U : Set M}
    (hU : IsStronglyGeodesicallyConvex I U) {x y : M} (hx : x ∈ U) (hy : y ∈ U) :
    edist x y ≠ ⊤ := by
  obtain ⟨γ, hγ, _, _, hlen, -, -⟩ := isStronglyGeodesicallyConvex_def.1 hU hx hy
  rw [← hlen, hγ.pathELength_eq isPreconnected_Icc (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one), ← ofReal_norm]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

variable [I.Boundaryless]

variable [IsRiemannianManifold I M]

/-- If `U` is strongly geodesically convex and contained in the normal ball `exp_q '' B(0, r)`
around `q ∈ U`, then for every `x ∈ U` the radial geodesic segment
`t ↦ exp_q (t • log_q x)` stays inside `U` for `t ∈ [0, 1]`. -/
theorem IsStronglyGeodesicallyConvex.mapsTo_riemannianExp_smul_riemannianLog {U : Set M}
    (hU : IsStronglyGeodesicallyConvex I U) {q : M} (hqU : q ∈ U) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : U ⊆ riemannianExp I M q '' Metric.ball 0 r) {x : M} (hx : x ∈ U) :
    MapsTo (fun t : ℝ ↦ riemannianExp I M q (t • riemannianLog I M q (Metric.ball 0 r) x))
      (Icc 0 1) U := by
  set v := riemannianLog I M q (Metric.ball 0 r) x
  have hv : v ∈ Metric.ball (0 : TangentSpace I q) r := riemannianLog_mem (hsub hx)
  have hIcc_sub : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M q v := fun _ ht ↦
    hq.mem_geodesicInterval hv ht.1 ht.2
  have hgeo_rad : IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M q (t • v)) (Icc 0 1) :=
    ((isGeodesicCurveOnFrom_maximalGeodesic q v).isGeodesicCurveOn.mono
      (uniqueDiffOn_Icc zero_lt_one) hIcc_sub).congr fun t _ ↦ riemannianExp_smul q v t
  have h0 : riemannianExp I M q ((0 : ℝ) • v) = q := by simp
  have h1 : riemannianExp I M q ((1 : ℝ) • v) = x := by
    simpa [v] using riemannianExp_riemannianLog (hsub hx)
  have hlen : pathELength I (fun t : ℝ ↦ riemannianExp I M q (t • v)) 0 1 = edist q x := by
    rw [hq.pathELength_riemannianExp_smul_eq_edist_of_mem_ball subset_rfl hv,
      riemannianExp_riemannianLog (hsub hx)]
  obtain ⟨γ, -, -, -, -, hmaps, huniq⟩ := isStronglyGeodesicallyConvex_def.1 hU hqU hx
  have heq := huniq hgeo_rad h0 h1 hlen.le
  exact fun t ht ↦ (heq ht).symm ▸ hmaps ht

/-- On a strongly geodesically convex open set `U` whose points all have normal tangent ball
`B(0, r)` covering `U`, the two-endpoint geodesic segment map `(x, y, t) ↦ exp_x (t • log_x y)`
is smooth on `(U ×ˢ U) ×ˢ Icc 0 1` and maps `(U ×ˢ U) ×ˢ Icc 0 1` into `U`. -/
theorem IsStronglyGeodesicallyConvex.contMDiffOn_and_mapsTo_segment {U : Set M} {r : ℝ}
    (hUo : IsOpen U) (hU : IsStronglyGeodesicallyConvex I U)
    (hnorm : ∀ x ∈ U, IsNormalDomain I M x (Metric.ball 0 r) ∧
      U ⊆ riemannianExp I M x '' Metric.ball 0 r) :
    ContMDiffOn ((I.prod I).prod 𝓘(ℝ)) I ∞
      (fun p : (M × M) × ℝ ↦
        riemannianExp I M p.1.1 (p.2 • riemannianLog I M p.1.1 (Metric.ball 0 r) p.1.2))
      ((U ×ˢ U) ×ˢ Icc (0 : ℝ) 1) ∧
      MapsTo
        (fun p : (M × M) × ℝ ↦
          riemannianExp I M p.1.1 (p.2 • riemannianLog I M p.1.1 (Metric.ball 0 r) p.1.2))
        ((U ×ˢ U) ×ˢ Icc (0 : ℝ) 1) U := by
  refine ⟨(contMDiffOn_riemannianExp_smul_riemannianLog hUo fun q hq ↦ (hnorm q hq).1).mono ?_, ?_⟩
  · rintro ⟨⟨x, y⟩, t⟩ ⟨⟨hx, hy⟩, ht⟩
    exact ⟨⟨hx, (hnorm x hx).2 hy⟩, ht⟩
  · rintro ⟨⟨x, y⟩, t⟩ ⟨⟨hx, hy⟩, ht⟩
    exact hU.mapsTo_riemannianExp_smul_riemannianLog hx (hnorm x hx).1 (hnorm x hx).2 hy ht

omit [I.Boundaryless] [IsRiemannianManifold I M] in
/-- Convexity of `(edist p (γ t)).toReal ^ 2` along `[0, 1]` keeps a geodesic segment `γ` with
endpoints in `eball p (ofReal ε)` inside `eball p (ofReal ε)` whenever all points of `γ` have
finite distance from `p`. -/
private theorem mapsTo_eball_of_strictConvexOn_edist_sq {W₁ : Set M} {p : M} {ε : ℝ} {γ : ℝ → M}
    (hε0 : 0 < ε)
    (hconv : ∀ {a b : ℝ} {γ : ℝ → M}, a < b → IsGeodesicCurveOn I γ (Icc a b) →
      MapsTo γ (Icc a b) W₁ → (∃ t ∈ Icc a b, γ t ≠ γ a) →
      StrictConvexOn ℝ (Icc a b) (fun t ↦ (edist p (γ t)).toReal ^ 2))
    (hγ_geo : IsGeodesicCurveOn I γ (Icc 0 1)) (hγ_W₁ : MapsTo γ (Icc 0 1) W₁)
    (h0_mem : γ 0 ∈ Metric.eball p (ENNReal.ofReal ε))
    (h1_mem : γ 1 ∈ Metric.eball p (ENNReal.ofReal ε))
    (hfin : ∀ t ∈ Icc (0 : ℝ) 1, edist p (γ t) ≠ ⊤) :
    MapsTo γ (Icc 0 1) (Metric.eball p (ENNReal.ofReal ε)) := by
  by_cases hconst : ∀ t ∈ Icc (0 : ℝ) 1, γ t = γ 0
  · intro t ht
    rwa [hconst t ht]
  · push Not at hconst
    have hsc := hconv zero_lt_one hγ_geo hγ_W₁ hconst
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | _
    · exact h0_mem
    rcases eq_or_lt_of_le ht.2 with rfl | ht1
    · exact h1_mem
    have hineq := hsc.convexOn.2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
      (sub_nonneg.2 ht.2) ht.1 (by ring)
    dsimp only [smul_eq_mul] at hineq
    have ht_comb : (1 - t) * 0 + t * 1 = t := by ring
    rw [ht_comb] at hineq
    have h0_sq : (edist p (γ 0)).toReal ^ 2 < ε ^ 2 := by
      have h := ENNReal.toReal_lt_of_lt_ofReal (mem_eball'.1 h0_mem)
      nlinarith [ENNReal.toReal_nonneg (a := edist p (γ 0))]
    have h1_sq : (edist p (γ 1)).toReal ^ 2 < ε ^ 2 := by
      have h := ENNReal.toReal_lt_of_lt_ofReal (mem_eball'.1 h1_mem)
      nlinarith [ENNReal.toReal_nonneg (a := edist p (γ 1))]
    have ht_sq : (edist p (γ t)).toReal ^ 2 < ε ^ 2 := by
      nlinarith [sub_pos.2 ht1]
    have ht_lt : (edist p (γ t)).toReal < ε := lt_of_pow_lt_pow_left₀ 2 hε0.le ht_sq
    exact mem_eball'.2 ((ENNReal.lt_ofReal_iff_toReal_lt (hfin t ht)).2 ht_lt)

/-- A radial exponential ray `t ↦ exp_x (t • v)` on `[0, 1]` starting at `x ∈ eball p (ofReal ε)`
with `‖v‖ₑ < ofReal (2 * ε)` stays inside `eball p (ofReal (3 * ε))`. -/
private theorem mapsTo_riemannianExp_smul_eball_three_mul {p x : M} {ε : ℝ} (hε0 : 0 < ε)
    (hx : x ∈ Metric.eball p (ENNReal.ofReal ε)) {v : TangentSpace I x}
    (hv : ‖v‖ₑ < ENNReal.ofReal (2 * ε)) :
    MapsTo (fun t : ℝ ↦ riemannianExp I M x (t • v)) (Icc 0 1)
      (Metric.eball p (ENNReal.ofReal (3 * ε))) := fun t ht ↦ by
  have hed_xt : edist x (riemannianExp I M x (t • v)) < ENNReal.ofReal (2 * ε) :=
    calc edist x (riemannianExp I M x (t • v)) ≤ ‖t • v‖ₑ := edist_riemannianExp_le x (t • v)
      _ = ENNReal.ofReal t * ‖v‖ₑ := by rw [eNorm_smul, Real.eNorm_eq_ofReal ht.1]
      _ ≤ 1 * ‖v‖ₑ := by gcongr; simpa using ENNReal.ofReal_le_ofReal ht.2
      _ = ‖v‖ₑ := one_mul _
      _ < ENNReal.ofReal (2 * ε) := hv
  refine mem_eball'.2 ?_
  calc edist p (riemannianExp I M x (t • v))
      ≤ edist p x + edist x (riemannianExp I M x (t • v)) := edist_triangle p x _
    _ < ENNReal.ofReal ε + ENNReal.ofReal (2 * ε) := ENNReal.add_lt_add (mem_eball'.1 hx) hed_xt
    _ = ENNReal.ofReal (3 * ε) := by rw [← ENNReal.ofReal_add hε0.le (by positivity)]; ring_nf

/-- Core ball-convexity step of Lee Theorem 6.17: if `W₁` satisfies strict convexity of squared
distance with normal radius `R`, and `eball p (ofReal (3 * ε)) ⊆ W₁` with `0 < ε` and `2 * ε ≤ R`,
then `eball p (ofReal ε)` is strongly geodesically convex. -/
private theorem isStronglyGeodesicallyConvex_eball_of_strictConvex {W₁ : Set M} {R : ℝ} {p : M}
    {ε : ℝ} (hε0 : 0 < ε) (h2εR : 2 * ε ≤ R)
    (h3ε_W₁ : Metric.eball p (ENNReal.ofReal (3 * ε)) ⊆ W₁)
    (hnorm₁ : ∀ q ∈ W₁, IsNormalDomain I M q (Metric.ball 0 R) ∧
      W₁ ⊆ Metric.eball q (ENNReal.ofReal R))
    (hconv₁ : ∀ q ∈ W₁, ∀ {a b : ℝ} {γ : ℝ → M}, a < b → IsGeodesicCurveOn I γ (Icc a b) →
      MapsTo γ (Icc a b) W₁ → (∃ t ∈ Icc a b, γ t ≠ γ a) →
      StrictConvexOn ℝ (Icc a b) (fun t ↦ (edist q (γ t)).toReal ^ 2)) :
    IsStronglyGeodesicallyConvex I (Metric.eball p (ENNReal.ofReal ε)) := by
  rw [isStronglyGeodesicallyConvex_def]
  intro x hx y hy
  have hpW₁ : p ∈ W₁ := h3ε_W₁ (Metric.mem_eball_self (ENNReal.ofReal_pos.2 (by positivity)))
  have hxW₁ : x ∈ W₁ := h3ε_W₁ (Metric.eball_subset_eball (by gcongr; linarith) hx)
  have hdom_x := (hnorm₁ x hxW₁).1
  have hed_xy : edist x y < ENNReal.ofReal (2 * ε) := by
    calc edist x y ≤ edist x p + edist p y := edist_triangle x p y
      _ = edist p x + edist p y := by rw [edist_comm x p]
      _ < ENNReal.ofReal ε + ENNReal.ofReal ε :=
          ENNReal.add_lt_add (mem_eball'.1 hx) (mem_eball'.1 hy)
      _ = ENNReal.ofReal (2 * ε) := by rw [← ENNReal.ofReal_add hε0.le hε0.le]; ring_nf
  have hed_xy_R : edist x y < ENNReal.ofReal R :=
    hed_xy.trans_le (ENNReal.ofReal_le_ofReal h2εR)
  have hy_exp : y ∈ riemannianExp I M x '' Metric.ball 0 R := by
    rw [hdom_x.image_riemannianExp_ball subset_rfl, mem_eball']
    exact hed_xy_R
  set v := riemannianLog I M x (Metric.ball 0 R) y
  have hv_ball : v ∈ Metric.ball (0 : TangentSpace I x) R := riemannianLog_mem hy_exp
  have hv_norm : ‖v‖ₑ = edist x y :=
    (hdom_x.edist_eq_enorm_riemannianLog_of_mem_ball subset_rfl hy_exp).symm
  let γ : ℝ → M := fun t ↦ riemannianExp I M x (t • v)
  have hγ_geo : IsGeodesicCurveOn I γ (Icc 0 1) :=
    ((isGeodesicCurveOnFrom_maximalGeodesic x v).isGeodesicCurveOn.mono
      (uniqueDiffOn_Icc zero_lt_one) fun _ ht ↦ hdom_x.mem_geodesicInterval hv_ball ht.1 ht.2
    ).congr fun t _ ↦ riemannianExp_smul x v t
  have hγ0 : γ 0 = x := by simp [γ]
  have hγ1 : γ 1 = y := by simpa [γ, v] using riemannianExp_riemannianLog hy_exp
  have hγ_len : pathELength I γ 0 1 = edist x y := by
    rw [hdom_x.pathELength_riemannianExp_smul_eq_edist_of_mem_ball subset_rfl hv_ball,
      riemannianExp_riemannianLog hy_exp]
  have hγ_3ε := mapsTo_riemannianExp_smul_eball_three_mul (I := I) hε0 hx (hv_norm.trans_lt hed_xy)
  have hγ_maps := mapsTo_eball_of_strictConvexOn_edist_sq hε0 (hconv₁ p hpW₁) hγ_geo
    (hγ_3ε.mono_right h3ε_W₁) (hγ0.symm ▸ hx) (hγ1.symm ▸ hy)
    fun t ht ↦ (mem_eball'.1 (hγ_3ε ht)).ne_top
  refine ⟨γ, hγ_geo, hγ0, hγ1, hγ_len, hγ_maps, fun γ' hγ' h0' h1' hlen' ↦ ?_⟩
  have hγ'_in_R : MapsTo γ' (Icc 0 1) (riemannianExp I M x '' Metric.ball 0 R) := fun t ht ↦ by
    rw [hdom_x.image_riemannianExp_ball subset_rfl, mem_eball']
    calc edist x (γ' t) = edist (γ' 0) (γ' t) := by rw [h0']
      _ ≤ pathELength I γ' 0 t :=
          IsRiemannianManifold.edist_le_pathELength
            ((hγ'.contMDiffOn.mono (Icc_subset_Icc le_rfl ht.2)).of_le (by norm_num)) ht.1
      _ ≤ pathELength I γ' 0 1 := pathELength_mono le_rfl ht.2
      _ ≤ edist x y := hlen'
      _ < ENNReal.ofReal R := hed_xy_R
  exact hdom_x.eqOn_riemannianExp_smul_of_geodesic_pathELength_le hv_ball hγ' hγ'_in_R h0'
    (h1'.trans (riemannianExp_riemannianLog hy_exp).symm) (hlen'.trans_eq hγ_len.symm)

/-- If every point `q ∈ eball p (ofReal ε)` has normal domain `B(0, 2 * r)` with `0 < r` and
`0 < ε ≤ r`, then `eball p (ofReal ε)` is uniformly normal. -/
private theorem isUniformlyNormal_eball_of_forall_isNormalDomain {p : M} {r ε : ℝ} (hr : 0 < r)
    (hε : ε ∈ Ioc 0 r)
    (hdom : ∀ q ∈ Metric.eball p (ENNReal.ofReal ε), IsNormalDomain I M q (Metric.ball 0 (2 * r))) :
    IsUniformlyNormal I (Metric.eball p (ENNReal.ofReal ε)) := by
  rw [isUniformlyNormal_def]
  intro q hq
  refine ⟨2 * r, by positivity, hdom q hq, ?_⟩
  rw [(hdom q hq).image_riemannianExp_ball subset_rfl]
  intro y hy
  refine mem_eball'.2 ?_
  calc edist q y ≤ edist q p + edist p y := edist_triangle q p y
    _ = edist p q + edist p y := by rw [edist_comm q p]
    _ < ENNReal.ofReal ε + ENNReal.ofReal ε :=
        ENNReal.add_lt_add (mem_eball'.1 hq) (mem_eball'.1 hy)
    _ ≤ ENNReal.ofReal (2 * r) := by
        rw [← ENNReal.ofReal_add hε.1.le hε.1.le]
        exact ENNReal.ofReal_le_ofReal (by linarith [hε.2])

/-- **Locally uniform strong geodesic convexity of Riemannian balls (Lee, Theorem 6.17).**
Every point `p₀` has a radius `r > 0` and an open neighbourhood `W` such that for each `p ∈ W`,
the tangent ball `B(0, 2 * r)` is a normal domain at `p`, and for every `ε ∈ (0, r]` the open
ball `Metric.eball p (ENNReal.ofReal ε)` is both strongly geodesically convex and uniformly
normal. -/
theorem exists_mem_nhds_isStronglyGeodesicallyConvex_eball (p₀ : M) :
    ∃ r > 0, ∃ W : Set M, IsOpen W ∧ p₀ ∈ W ∧
      (∀ p ∈ W, IsNormalDomain I M p (Metric.ball 0 (2 * r))) ∧
      ∀ p ∈ W, ∀ ε ∈ Ioc 0 r,
        IsStronglyGeodesicallyConvex I (Metric.eball p (ENNReal.ofReal ε)) ∧
          IsUniformlyNormal I (Metric.eball p (ENNReal.ofReal ε)) := by
  obtain ⟨R, hR, W₁, hW₁_open, hp₀W₁, hnorm₁, hconv₁⟩ :=
    exists_isOpen_mem_strictConvexOn_toReal_edist_sq (I := I) p₀
  obtain ⟨δ, hδ, hδW₁⟩ := EMetric.isOpen_iff.1 hW₁_open p₀ hp₀W₁
  set δ_real : ℝ := min R ((min δ 1).toReal)
  have hδ_real_pos : 0 < δ_real :=
    lt_min hR (ENNReal.toReal_pos (lt_min hδ zero_lt_one).ne'
      ((min_le_right δ 1).trans_lt ENNReal.one_lt_top).ne)
  set r : ℝ := δ_real / 4
  have hr : 0 < r := by positivity
  have h4r_eq : 4 * r = δ_real := by ring
  have h4r_le_R : 4 * r ≤ R := h4r_eq.symm ▸ min_le_left R (min δ 1).toReal
  have h2r_le_R : 2 * r ≤ R := by linarith
  have h4r_sub_W₁ : Metric.eball p₀ (ENNReal.ofReal (4 * r)) ⊆ W₁ := fun q hq ↦ by
    apply hδW₁ (mem_eball'.2 ?_)
    have hle : ENNReal.ofReal δ_real ≤ δ :=
      (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans <|
        (ENNReal.ofReal_toReal ((min_le_right δ 1).trans_lt ENNReal.one_lt_top).ne).trans_le
          (min_le_left _ _)
    exact (mem_eball'.1 hq).trans_le (h4r_eq.symm ▸ hle)
  have hdom_4r : ∀ q ∈ Metric.eball p₀ (ENNReal.ofReal (4 * r)),
      IsNormalDomain I M q (Metric.ball 0 (2 * r)) := fun q hq ↦
    (hnorm₁ q (h4r_sub_W₁ hq)).1.ball (Metric.ball_subset_ball h2r_le_R) (by positivity)
  refine ⟨r, hr, Metric.eball p₀ (ENNReal.ofReal r), Metric.isOpen_eball,
    Metric.mem_eball_self (ENNReal.ofReal_pos.2 hr),
    fun p hp ↦ hdom_4r p (Metric.eball_subset_eball (by gcongr; linarith) hp),
    fun p hp ε hε ↦ ?_⟩
  have h3ε_sub : Metric.eball p (ENNReal.ofReal (3 * ε)) ⊆
      Metric.eball p₀ (ENNReal.ofReal (4 * r)) := fun q hq ↦ mem_eball'.2 <|
    calc edist p₀ q ≤ edist p₀ p + edist p q := edist_triangle p₀ p q
      _ < ENNReal.ofReal r + ENNReal.ofReal (3 * ε) :=
          ENNReal.add_lt_add (mem_eball'.1 hp) (mem_eball'.1 hq)
      _ ≤ ENNReal.ofReal (4 * r) := by
          rw [← ENNReal.ofReal_add hr.le (by linarith [hε.1])]
          exact ENNReal.ofReal_le_ofReal (by linarith [hε.2])
  refine ⟨isStronglyGeodesicallyConvex_eball_of_strictConvex hε.1 (by linarith [hε.2])
    (h3ε_sub.trans h4r_sub_W₁) hnorm₁ hconv₁,
    isUniformlyNormal_eball_of_forall_isNormalDomain hr hε fun q hq ↦ hdom_4r q (h3ε_sub ?_)⟩
  exact Metric.eball_subset_eball (ENNReal.ofReal_le_ofReal (by linarith [hε.1])) hq

/-- Pointwise strong-convexity radius: every point `p` admits `r > 0` such that `B(0, 2 * r)` is a
normal domain at `p` and every open ball `Metric.eball p (ENNReal.ofReal ε)` of radius
`0 < ε ≤ r` is strongly geodesically convex and uniformly normal. -/
theorem exists_pos_isStronglyGeodesicallyConvex_eball (p : M) :
    ∃ r > 0, IsNormalDomain I M p (Metric.ball 0 (2 * r)) ∧
      ∀ ε ∈ Ioc 0 r,
        IsStronglyGeodesicallyConvex I (Metric.eball p (ENNReal.ofReal ε)) ∧
          IsUniformlyNormal I (Metric.eball p (ENNReal.ofReal ε)) := by
  obtain ⟨r, hr, W, -, hpW, hdom, hconv⟩ :=
    exists_mem_nhds_isStronglyGeodesicallyConvex_eball (I := I) p
  exact ⟨r, hr, hdom p hpW, hconv p hpW⟩

/-- **Uniform normal and strong-convexity radii over a compact set.** For any compact subset `K`
of a Riemannian manifold `M`, there exist a positive normal radius `r_norm` and a positive
strong-convexity radius `r_conv` with `2 * r_conv ≤ r_norm` such that at every `p ∈ K`, the
tangent ball `B(0, r_norm)` (and hence `B(0, r_conv)`) is a normal domain and every ball
`Metric.eball p (ENNReal.ofReal ε)` for `0 < ε ≤ r_conv` is strongly geodesically convex and
uniformly normal. -/
theorem _root_.IsCompact.exists_pos_isNormalDomain_and_isStronglyGeodesicallyConvex_eball
    {K : Set M} (hK : IsCompact K) :
    ∃ r_norm > 0, ∃ r_conv > 0, 2 * r_conv ≤ r_norm ∧
      (∀ p ∈ K, IsNormalDomain I M p (Metric.ball 0 r_norm)) ∧
      ∀ p ∈ K, ∀ ε ∈ Ioc 0 r_conv,
        IsStronglyGeodesicallyConvex I (Metric.eball p (ENNReal.ofReal ε)) ∧
          IsUniformlyNormal I (Metric.eball p (ENNReal.ofReal ε)) := by
  choose R hR W hW_open hpW hdom hconv using
    exists_mem_nhds_isStronglyGeodesicallyConvex_eball (I := I) (M := M)
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover W fun p _ ↦ (hW_open p).mem_nhds (hpW p)
  rcases t.eq_empty_or_nonempty with rfl | ht
  · refine ⟨2, by positivity, 1, by positivity, by norm_num, fun _ hp ↦ ?_, fun _ hp ↦ ?_⟩ <;>
      exact False.elim (by simpa using hKt hp)
  set r_conv : ℝ := t.inf' ht R
  have hr_conv : 0 < r_conv := (Finset.lt_inf'_iff ht).2 fun p _ ↦ hR p
  refine ⟨2 * r_conv, by positivity, r_conv, hr_conv, le_rfl, fun p hp ↦ ?_, fun p hp ε hε ↦ ?_⟩
  · obtain ⟨q, hqt, hpW_q⟩ := mem_iUnion₂.1 (hKt hp)
    have hle : 2 * r_conv ≤ 2 * R q := mul_le_mul_of_nonneg_left (Finset.inf'_le R hqt) zero_le_two
    exact (hdom q p hpW_q).ball (Metric.ball_subset_ball hle) (by positivity)
  · obtain ⟨q, hqt, hpW_q⟩ := mem_iUnion₂.1 (hKt hp)
    exact hconv q p hpW_q ε ⟨hε.1, hε.2.trans (Finset.inf'_le R hqt)⟩

end StronglyGeodesicallyConvex

section StronglyGeodesicallyConvexMetricSpace

variable
  [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- Metric-space form of `exists_pos_isStronglyGeodesicallyConvex_eball`: small metric balls
`Metric.ball p ε` are strongly geodesically convex and uniformly normal. -/
theorem exists_pos_isStronglyGeodesicallyConvex_ball (p : M) :
    ∃ r > 0, IsNormalDomain I M p (Metric.ball 0 (2 * r)) ∧
      ∀ ε ∈ Ioc 0 r,
        IsStronglyGeodesicallyConvex I (Metric.ball p ε) ∧
          IsUniformlyNormal I (Metric.ball p ε) := by
  obtain ⟨r, hr, hdom, hconv⟩ := exists_pos_isStronglyGeodesicallyConvex_eball (I := I) p
  refine ⟨r, hr, hdom, fun ε hε ↦ ?_⟩
  simpa only [Metric.eball_ofReal] using hconv ε hε

/-- Metric-space form of
`IsCompact.exists_pos_isNormalDomain_and_isStronglyGeodesicallyConvex_eball`. -/
theorem _root_.IsCompact.exists_pos_isNormalDomain_and_isStronglyGeodesicallyConvex_ball
    {K : Set M} (hK : IsCompact K) :
    ∃ r_norm > 0, ∃ r_conv > 0, 2 * r_conv ≤ r_norm ∧
      (∀ p ∈ K, IsNormalDomain I M p (Metric.ball 0 r_norm)) ∧
      ∀ p ∈ K, ∀ ε ∈ Ioc 0 r_conv,
        IsStronglyGeodesicallyConvex I (Metric.ball p ε) ∧
          IsUniformlyNormal I (Metric.ball p ε) := by
  obtain ⟨rn, hrn, rc, hrc, hle, hdom, hconv⟩ :=
    hK.exists_pos_isNormalDomain_and_isStronglyGeodesicallyConvex_eball (I := I) (M := M)
  refine ⟨rn, hrn, rc, hrc, hle, hdom, fun p hp ε hε ↦ ?_⟩
  simpa only [Metric.eball_ofReal] using hconv p hp ε hε

end StronglyGeodesicallyConvexMetricSpace

/-! ### Smooth radial geodesic contractions and smooth step reparametrization -/

section RadialContraction

variable
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The natural domain of the raw radial geodesic homotopy centred at `q` on the normal tangent
ball `B(0, r)`: pairs `(s, x) ∈ ℝ × M` with `x ∈ exp_q '' B(0, r)` and `s • log_q x ∈ expDomain`. -/
def radialGeodesicHomotopyDomain (q : M) (r : ℝ) : Set (ℝ × M) :=
  {p : ℝ × M | p.2 ∈ riemannianExp I M q '' Metric.ball 0 r ∧
    p.1 • riemannianLog I M q (Metric.ball 0 r) p.2 ∈ expDomain I M q}

theorem mem_radialGeodesicHomotopyDomain_iff {q : M} {r : ℝ} {p : ℝ × M} :
    p ∈ radialGeodesicHomotopyDomain I M q r ↔
      p.2 ∈ riemannianExp I M q '' Metric.ball 0 r ∧
        p.1 • riemannianLog I M q (Metric.ball 0 r) p.2 ∈ expDomain I M q := by
  rw [radialGeodesicHomotopyDomain]
  rfl

variable (I M) in
/-- The raw radial geodesic contraction `H(s, x) = exp_q (s • log_q x)` centred at `q` using the
normal tangent ball `B(0, r)`. -/
def radialGeodesicHomotopy (q : M) (r : ℝ) (p : ℝ × M) : M :=
  riemannianExp I M q (p.1 • riemannianLog I M q (Metric.ball 0 r) p.2)

theorem radialGeodesicHomotopy_def (q : M) (r : ℝ) (p : ℝ × M) :
    radialGeodesicHomotopy I M q r p =
      riemannianExp I M q (p.1 • riemannianLog I M q (Metric.ball 0 r) p.2) := by
  rw [radialGeodesicHomotopy]

theorem radialGeodesicHomotopy_one_left {q : M} {r : ℝ} {x : M}
    (hx : x ∈ riemannianExp I M q '' Metric.ball 0 r) :
    radialGeodesicHomotopy I M q r (1, x) = x := by
  simp [radialGeodesicHomotopy, riemannianExp_riemannianLog hx]

/-- For any subset `W ⊆ exp_q '' B(0, r)`, the cylinder `[0, 1] ×ˢ W` lies in
`radialGeodesicHomotopyDomain I M q r`. -/
theorem IsNormalDomain.Icc_prod_subset_radialGeodesicHomotopyDomain {q : M} {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r)) {W : Set M}
    (hW : W ⊆ riemannianExp I M q '' Metric.ball 0 r) :
    Icc (0 : ℝ) 1 ×ˢ W ⊆ radialGeodesicHomotopyDomain I M q r := by
  rintro ⟨s, x⟩ ⟨hs, hx⟩
  rw [mem_radialGeodesicHomotopyDomain_iff]
  exact ⟨hW hx, hq.subset_expDomain (hq.smul_mem (riemannianLog_mem (hW hx)) hs.1 hs.2)⟩

variable [I.Boundaryless]

@[simp]
theorem radialGeodesicHomotopy_zero_left (q : M) (r : ℝ) (x : M) :
    radialGeodesicHomotopy I M q r (0, x) = q := by
  simp [radialGeodesicHomotopy]

@[simp]
theorem IsNormalDomain.radialGeodesicHomotopy_self_right {q : M} {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r)) (s : ℝ) :
    radialGeodesicHomotopy I M q r (s, q) = q := by
  simp [radialGeodesicHomotopy, hq.riemannianLog_self]

/-- When `B(0, r)` is a normal domain at `q`, the natural domain of `radialGeodesicHomotopy` is
open in `ℝ × M`. -/
theorem IsNormalDomain.isOpen_radialGeodesicHomotopyDomain {q : M} {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r)) :
    IsOpen (radialGeodesicHomotopyDomain I M q r) := by
  let V := riemannianExp I M q '' Metric.ball 0 r
  have hcont : ContinuousOn
      (fun p : ℝ × M ↦ p.1 • riemannianLog I M q (Metric.ball 0 r) p.2) (univ ×ˢ V) :=
    continuousOn_fst.smul (hq.continuousOn_riemannianLog.comp continuousOn_snd fun _ hp ↦ hp.2)
  have hopen := hcont.isOpen_inter_preimage (isOpen_univ.prod hq.isOpen_image) (isOpen_expDomain q)
  have heq : (univ ×ˢ V) ∩
      (fun p : ℝ × M ↦ p.1 • riemannianLog I M q (Metric.ball 0 r) p.2) ⁻¹' expDomain I M q =
      radialGeodesicHomotopyDomain I M q r := by
    ext ⟨s, x⟩
    simp [radialGeodesicHomotopyDomain, V]
  rwa [← heq]

/-- On a normal ball `B(0, r)` at `q`, the raw radial geodesic homotopy is smooth on its open
domain `radialGeodesicHomotopyDomain I M q r`. -/
theorem IsNormalDomain.contMDiffOn_radialGeodesicHomotopy {q : M} {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r)) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) I ∞ (radialGeodesicHomotopy I M q r)
      (radialGeodesicHomotopyDomain I M q r) := by
  intro p hp
  rw [mem_radialGeodesicHomotopyDomain_iff] at hp
  have hlog : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, TangentSpace I q) ∞
      (fun u : ℝ × M ↦ riemannianLog I M q (Metric.ball 0 r) u.2) p :=
    (hq.contMDiffOn_riemannianLog.contMDiffAt
      (hq.isOpen_image.mem_nhds hp.1)).comp p contMDiffAt_snd
  have hsmul : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, TangentSpace I q) ∞
      (fun u : ℝ × M ↦ u.1 • riemannianLog I M q (Metric.ball 0 r) u.2) p :=
    contMDiffAt_fst.smul hlog
  exact ((contMDiffAt_riemannianExp hp.2).comp p hsmul).contMDiffWithinAt

variable [IsRiemannianManifold I M]

/-- When `W` is strongly geodesically convex and contained in the normal ball `exp_q '' B(0, r)`
around `q ∈ W`, the raw radial geodesic homotopy maps `[0, 1] ×ˢ W` into `W`. -/
theorem IsStronglyGeodesicallyConvex.mapsTo_radialGeodesicHomotopy {W : Set M}
    (hW : IsStronglyGeodesicallyConvex I W) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : W ⊆ riemannianExp I M q '' Metric.ball 0 r) :
    MapsTo (radialGeodesicHomotopy I M q r) (Icc (0 : ℝ) 1 ×ˢ W) W := by
  rintro ⟨s, x⟩ ⟨hs, hx⟩
  exact hW.mapsTo_riemannianExp_smul_riemannianLog hqW hq hsub hx hs

variable (I) in
/-- Smooth geodesic contraction `ℝ × W → W` of a strongly geodesically convex open submanifold
`W : Opens M` to a centre `q ∈ W`, obtained by reparametrizing the radial geodesic homotopy with
`Real.smoothTransition`. -/
def geodesicOpenContract (W : Opens M) (hW : IsStronglyGeodesicallyConvex I (W : Set M))
    {q : M} (hqW : q ∈ W) {r : ℝ} (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) (p : ℝ × ↥W) : ↥W :=
  ⟨radialGeodesicHomotopy I M q r (Real.smoothTransition p.1, p.2.1),
    hW.mapsTo_radialGeodesicHomotopy hqW hq hsub
      ⟨⟨Real.smoothTransition.nonneg p.1, Real.smoothTransition.le_one p.1⟩, p.2.2⟩⟩

theorem coe_geodesicOpenContract (W : Opens M) (hW : IsStronglyGeodesicallyConvex I (W : Set M))
    {q : M} (hqW : q ∈ W) {r : ℝ} (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) (p : ℝ × ↥W) :
    (geodesicOpenContract I W hW hqW hq hsub p : M) =
      radialGeodesicHomotopy I M q r (Real.smoothTransition p.1, p.2.1) :=
  (rfl)

/-- The smooth-transition-reparametrized radial geodesic contraction `ℝ × W → W` is `C^∞`. -/
theorem contMDiff_geodesicOpenContract (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I) I ∞ (geodesicOpenContract I W hW hqW hq hsub) := by
  have hcoe : Subtype.val ∘ geodesicOpenContract I W hW hqW hq hsub =
      radialGeodesicHomotopy I M q r ∘ fun u : ℝ × ↥W ↦ (Real.smoothTransition u.1, (u.2 : M)) :=
    funext (coe_geodesicOpenContract W hW hqW hq hsub)
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff W, hcoe]
  intro p
  have hmem : (Real.smoothTransition p.1, (p.2 : M)) ∈ radialGeodesicHomotopyDomain I M q r :=
    hq.Icc_prod_subset_radialGeodesicHomotopyDomain hsub
      ⟨⟨Real.smoothTransition.nonneg p.1, Real.smoothTransition.le_one p.1⟩, p.2.2⟩
  have hstep : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun u : ℝ × ↥W ↦ (Real.smoothTransition u.1, (u.2 : M))) p :=
    (Real.smoothTransition.contDiff.contMDiff.contMDiffAt.comp p contMDiffAt_fst).prodMk
      (contMDiff_subtype_val.contMDiffAt.comp p contMDiffAt_snd)
  exact (hq.contMDiffOn_radialGeodesicHomotopy.contMDiffAt
    (hq.isOpen_radialGeodesicHomotopyDomain.mem_nhds hmem)).comp p hstep

theorem geodesicOpenContract_of_nonpos (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) {t : ℝ} (ht : t ≤ 0) (x : ↥W) :
    geodesicOpenContract I W hW hqW hq hsub (t, x) = ⟨q, hqW⟩ := by
  ext
  rw [coe_geodesicOpenContract, Real.smoothTransition.zero_of_nonpos ht,
    radialGeodesicHomotopy_zero_left]

theorem geodesicOpenContract_of_one_le (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) {t : ℝ} (ht : 1 ≤ t) (x : ↥W) :
    geodesicOpenContract I W hW hqW hq hsub (t, x) = x := by
  ext
  rw [coe_geodesicOpenContract, Real.smoothTransition.one_of_one_le ht,
    radialGeodesicHomotopy_one_left (hsub x.2)]

@[simp]
theorem geodesicOpenContract_zero_left (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) (x : ↥W) :
    geodesicOpenContract I W hW hqW hq hsub (0, x) = ⟨q, hqW⟩ :=
  geodesicOpenContract_of_nonpos W hW hqW hq hsub le_rfl x

@[simp]
theorem geodesicOpenContract_one_left (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) (x : ↥W) :
    geodesicOpenContract I W hW hqW hq hsub (1, x) = x :=
  geodesicOpenContract_of_one_le W hW hqW hq hsub le_rfl x

@[simp]
theorem geodesicOpenContract_centre (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) (t : ℝ) :
    geodesicOpenContract I W hW hqW hq hsub (t, ⟨q, hqW⟩) = ⟨q, hqW⟩ := by
  ext
  rw [coe_geodesicOpenContract, hq.radialGeodesicHomotopy_self_right]

variable (I) in
/-- Cylinder-ordered smooth geodesic contraction `W × [0, 1] → W` modelled on `I.prod (𝓡∂ 1)`,
matching the factor order expected by `TauCeti.homotopyOperator`. -/
def geodesicOpenCylinderContract (W : Opens M) (hW : IsStronglyGeodesicallyConvex I (W : Set M))
    {q : M} (hqW : q ∈ W) {r : ℝ} (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r)
    (p : ↥W × Icc (0 : ℝ) 1) : ↥W :=
  geodesicOpenContract I W hW hqW hq hsub (p.2.1, p.1)

theorem geodesicOpenCylinderContract_apply (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) (p : ↥W × Icc (0 : ℝ) 1) :
    geodesicOpenCylinderContract I W hW hqW hq hsub p =
      geodesicOpenContract I W hW hqW hq hsub (p.2.1, p.1) :=
  (rfl)

/-- The cylinder-ordered geodesic contraction `W × [0, 1] → W` is `C^∞` for `I.prod (𝓡∂ 1)`. -/
theorem contMDiff_geodesicOpenCylinderContract (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) :
    ContMDiff (I.prod (𝓡∂ 1)) I ∞ (geodesicOpenCylinderContract I W hW hqW hq hsub) :=
  (contMDiff_geodesicOpenContract W hW hqW hq hsub).comp
    (((contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp contMDiff_snd).prodMk contMDiff_fst)

@[simp]
theorem geodesicOpenCylinderContract_zero (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) (x : ↥W) :
    geodesicOpenCylinderContract I W hW hqW hq hsub (x, 0) = ⟨q, hqW⟩ :=
  geodesicOpenContract_zero_left W hW hqW hq hsub x

@[simp]
theorem geodesicOpenCylinderContract_one (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) (x : ↥W) :
    geodesicOpenCylinderContract I W hW hqW hq hsub (x, 1) = x :=
  geodesicOpenContract_one_left W hW hqW hq hsub x

@[simp]
theorem geodesicOpenCylinderContract_centre (W : Opens M)
    (hW : IsStronglyGeodesicallyConvex I (W : Set M)) {q : M} (hqW : q ∈ W) {r : ℝ}
    (hq : IsNormalDomain I M q (Metric.ball 0 r))
    (hsub : (W : Set M) ⊆ riemannianExp I M q '' Metric.ball 0 r) (t : Icc (0 : ℝ) 1) :
    geodesicOpenCylinderContract I W hW hqW hq hsub (⟨q, hqW⟩, t) = ⟨q, hqW⟩ :=
  geodesicOpenContract_centre W hW hqW hq hsub t.1

end RadialContraction

end TauCeti.Manifold

end
