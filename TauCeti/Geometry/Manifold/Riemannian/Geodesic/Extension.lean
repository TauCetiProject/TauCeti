/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
import TauCeti.Geometry.Manifold.IntegralCurve.Extension
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed

/-!
# Extending geodesics and smooth geodesic segments

The velocity lift of a geodesic is an integral curve of the geodesic spray, which is a `C¹`
vector field on the tangent bundle of a `C³` manifold with a `C²` metric. The finite-endpoint
extension criterion for integral curves therefore applies: a geodesic on `(a, b)` whose velocity
lift accumulates at a point of the tangent bundle as `t → a⁺` is the restriction of a geodesic on
a strictly longer interval `(c, b)`, and similarly at `b`.

If the geodesic itself converges to a point `p` at an endpoint, its velocity lift does
accumulate there. A geodesic has constant speed, and the tangent vectors of bounded norm over a
compact neighbourhood of `p` form a compact subset of the tangent bundle. Consequently a geodesic
on `(a, b)` which is continuous on `[a, b]` agrees on `[a, b]` with a geodesic defined on an open
interval containing `[a, b]`. This gives, for instance, the endpoint velocities of a curve which
is only known to be a geodesic in the interior of its parameter interval, such as a
length-minimizing curve whose endpoints lie on the boundary of a domain.

The finite-endpoint geodesic extensions need a `C²` metric on a `C³` manifold without boundary.
The globally smooth curve extensions require a smooth metric and manifold without boundary.
No completeness assumption is needed.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.exists_lt_isGeodesicCurveOn_Ioo` and
  `TauCeti.Manifold.IsGeodesicCurveOn.exists_gt_isGeodesicCurveOn_Ioo`: a geodesic on `(a, b)`
  extends past `a`, respectively `b`, when its velocity lift has a cluster point there.
* `TauCeti.Manifold.IsGeodesicCurveOn.exists_lt_isGeodesicCurveOn_Ioo_of_tendsto` and
  `TauCeti.Manifold.IsGeodesicCurveOn.exists_gt_isGeodesicCurveOn_Ioo_of_tendsto`: a geodesic on
  `(a, b)` converging to a point at an endpoint extends past that endpoint through that point.
* `TauCeti.Manifold.IsGeodesicCurveOn.exists_isGeodesicCurveOn_Ioo_of_continuousOn_Icc`: a
  geodesic on `(a, b)` which is continuous on `[a, b]` agrees on `[a, b]` with a geodesic on an
  open interval containing `[a, b]`.
* `TauCeti.Manifold.IsGeodesicCurveOn.exists_contMDiff_eventuallyEq`: a geodesic on an open
  preconnected set `U` agrees near any set closed in `ℝ` and contained in `U` with a globally
  smooth curve.
* `TauCeti.Manifold.IsGeodesicCurveOn.exists_contMDiff_isGeodesicCurveOn_comp_affine`: an affine
  reparametrization on a nondegenerate closed interval mapped into `U` has a globally smooth
  extension preserving its germs and affine velocity formula.
* `TauCeti.Manifold.IsGeodesicCurveOn.exists_contMDiff_isGeodesicCurveOn_Icc`: a geodesic on a
  nondegenerate closed interval has a globally smooth extension preserving its endpoint velocities.
* `TauCeti.Manifold.exists_contMDiff_eventuallyEq_maximalGeodesic`: a maximal geodesic agrees near
  any set closed in `ℝ` and contained in its maximal interval with a globally smooth curve.
* `TauCeti.Manifold.exists_contMDiff_isGeodesicCurveOn_maximalGeodesic`: the same for an affine
  reparametrization on a nondegenerate closed interval mapped into the maximal interval,
  preserving its germs and affine velocity formula.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Lemma 9.19 (the escape
  lemma for integral curves).
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 4 (existence and
  uniqueness of geodesics).
-/

public section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {a b : ℝ}

section SmoothExtension

variable [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A geodesic on an open preconnected set `U` agrees near any set closed in `ℝ` and contained
in `U` with a curve smooth on the whole line. -/
theorem IsGeodesicCurveOn.exists_contMDiff_eventuallyEq {γ : ℝ → M} {U K : Set ℝ}
    (hγ : IsGeodesicCurveOn I γ U) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hK : IsClosed K) (hKU : K ⊆ U) :
    ∃ f : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ f ∧ ∀ t ∈ K, f =ᶠ[𝓝 t] γ := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · exact ⟨fun _ ↦ γ 0, contMDiff_const, fun t ht ↦ (hKU ht).elim⟩
  exact hγ.contMDiffOn_infty.exists_contMDiff_eventuallyEq_of_starConvex hU
    (hconn.ordConnected.convex.starConvex hc) hK hKU

/-- An affine reparametrization of a geodesic on an open preconnected set `U`, restricted to a
nondegenerate closed interval mapped into `U`, has a globally smooth extension agreeing near
each parameter, which is geodesic on the interval and has the affinely rescaled velocity. -/
theorem IsGeodesicCurveOn.exists_contMDiff_isGeodesicCurveOn_comp_affine
    {γ : ℝ → M} {U : Set ℝ} {m k t₀ t₁ : ℝ} (hγ : IsGeodesicCurveOn I γ U)
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (ht : t₀ < t₁) (hG : ∀ u ∈ Icc t₀ t₁, m * u + k ∈ U) :
    ∃ f : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ f ∧
      (∀ u ∈ Icc t₀ t₁, f =ᶠ[𝓝 u] fun x ↦ γ (m * x + k)) ∧
      IsGeodesicCurveOn I f (Icc t₀ t₁) ∧ ∀ u ∈ Icc t₀ t₁,
        curveVelocity I f u = m • curveVelocity I γ (m * u + k) := by
  have hφ : Continuous fun u : ℝ ↦ m * u + k := by fun_prop
  obtain ⟨g, hg, hev⟩ := hγ.exists_contMDiff_eventuallyEq hU hconn
    (isCompact_Icc.image hφ).isClosed (image_subset_iff.2 hG)
  have hev' (u : ℝ) (hu : u ∈ Icc t₀ t₁) :
      (fun x ↦ g (m * x + k)) =ᶠ[𝓝 u] fun x ↦ γ (m * x + k) :=
    (hev _ (mem_image_of_mem _ hu)).comp_tendsto hφ.continuousAt
  have heq : EqOn (fun x ↦ g (m * x + k)) (fun x ↦ γ (m * x + k))
      (Icc t₀ t₁) := fun u hu ↦ (hev' u hu).self_of_nhds
  refine ⟨fun x ↦ g (m * x + k), hg.comp (contDiff_const.mul contDiff_id |>.add
    contDiff_const).contMDiff, hev', ?_, fun u hu ↦ ?_⟩
  · exact (hγ.comp_affine m k (uniqueDiffOn_Icc ht) hG).congr heq
  · have hd : HasDerivAt (fun x : ℝ ↦ m * x + k) m u := by
      simpa using ((hasDerivAt_id u).const_mul m).add_const k
    have hdiff : MDifferentiableAt 𝓘(ℝ) I γ (m * u + k) :=
      (hγ.contMDiffAt_infty (hU.mem_nhds (hG u hu))).mdifferentiableAt (by simp)
    have hvel : curveVelocity I (fun x ↦ g (m * x + k)) u =
        curveVelocity I (γ ∘ fun x ↦ m * x + k) u :=
      (hev' u hu).curveVelocity_eq
    rw [hvel, curveVelocity_comp hd hdiff]

end SmoothExtension

namespace IsGeodesicCurveOn

section ConstantSpeed

variable [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The velocity lift of a geodesic on a preconnected parameter set `s` accumulates at a point of
the tangent bundle along any nontrivial filter which is eventually in `s` and along which the
geodesic converges. -/
theorem exists_mapClusterPt_curveVelocityLiftWithin {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s)
    (hs : IsPreconnected s) {l : Filter ℝ} [l.NeBot] (hl : s ∈ l) {p : M}
    (hp : Tendsto γ l (𝓝 p)) :
    ∃ z : TangentBundle I M, MapClusterPt z l (curveVelocityLiftWithin I γ s) := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  obtain ⟨τ, hτ⟩ := l.nonempty_of_mem hl
  obtain ⟨K, hK, hpK⟩ := exists_compact_mem_nhds p
  have hmem : Tendsto (curveVelocityLiftWithin I γ s) l
      (𝓟 {z : TangentBundle I M | z.proj ∈ K ∧ ‖z.2‖ ≤ ‖curveVelocityWithin I γ s τ‖}) := by
    refine tendsto_principal.2 ?_
    filter_upwards [hp.eventually hpK, hl] with t ht hts
    rw [curveVelocityLiftWithin_apply]
    exact ⟨ht, (hγ.norm_curveVelocityWithin_eq hs hts hτ).le⟩
  obtain ⟨z, -, hz⟩ := (hK.norm_le_bundle _).exists_mapClusterPt hmem
  exact ⟨z, hz⟩

end ConstantSpeed

variable [I.Boundaryless] [T2Space M] [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]

/-- **Extension of a geodesic past a finite left endpoint.** A geodesic on `(a, b)` whose velocity
lift accumulates at a point of the tangent bundle as `t → a⁺` agrees on `(a, b)` with a geodesic
on a strictly longer interval `(c, b)`. -/
theorem exists_lt_isGeodesicCurveOn_Ioo (hγ : IsGeodesicCurveOn I γ (Ioo a b)) (hab : a < b)
    {z : TangentBundle I M}
    (hz : MapClusterPt z (𝓝[>] a) (curveVelocityLiftWithin I γ (Ioo a b))) :
    ∃ c < a, ∃ δ : ℝ → M, IsGeodesicCurveOn I δ (Ioo c b) ∧ EqOn δ γ (Ioo a b) := by
  obtain ⟨c, hc, δ, hδ, heq⟩ := ((isMIntegralCurveOn_curveVelocityLiftWithin_iff
    isOpen_Ioo.uniqueDiffOn hγ.contMDiffOn).2 hγ).exists_lt_isMIntegralCurveOn_Ioo hab
    contMDiff_one_geodesicSpray hz
  exact ⟨c, hc, fun t ↦ (δ t).proj,
    isGeodesicCurveOn_proj_of_isMIntegralCurveOn isOpen_Ioo.uniqueDiffOn hδ,
    fun t ht ↦ (congrArg TotalSpace.proj (heq ht)).trans (curveVelocityLiftWithin_proj γ _ t)⟩

/-- **Extension of a geodesic past a finite right endpoint.** A geodesic on `(a, b)` whose
velocity lift accumulates at a point of the tangent bundle as `t → b⁻` agrees on `(a, b)` with a
geodesic on a strictly longer interval `(a, d)`. -/
theorem exists_gt_isGeodesicCurveOn_Ioo (hγ : IsGeodesicCurveOn I γ (Ioo a b)) (hab : a < b)
    {z : TangentBundle I M}
    (hz : MapClusterPt z (𝓝[<] b) (curveVelocityLiftWithin I γ (Ioo a b))) :
    ∃ d > b, ∃ δ : ℝ → M, IsGeodesicCurveOn I δ (Ioo a d) ∧ EqOn δ γ (Ioo a b) := by
  obtain ⟨d, hd, δ, hδ, heq⟩ := ((isMIntegralCurveOn_curveVelocityLiftWithin_iff
    isOpen_Ioo.uniqueDiffOn hγ.contMDiffOn).2 hγ).exists_gt_isMIntegralCurveOn_Ioo hab
    contMDiff_one_geodesicSpray hz
  exact ⟨d, hd, fun t ↦ (δ t).proj,
    isGeodesicCurveOn_proj_of_isMIntegralCurveOn isOpen_Ioo.uniqueDiffOn hδ,
    fun t ht ↦ (congrArg TotalSpace.proj (heq ht)).trans (curveVelocityLiftWithin_proj γ _ t)⟩

/-- A geodesic on `(a, b)` which converges to a point `p` as `t → a⁺` agrees on `(a, b)` with a
geodesic on a strictly longer interval `(c, b)`, whose value at `a` is `p`. -/
theorem exists_lt_isGeodesicCurveOn_Ioo_of_tendsto (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    (hab : a < b) {p : M} (hp : Tendsto γ (𝓝[>] a) (𝓝 p)) :
    ∃ c < a, ∃ δ : ℝ → M, IsGeodesicCurveOn I δ (Ioo c b) ∧ EqOn δ γ (Ioo a b) ∧ δ a = p := by
  obtain ⟨z, hz⟩ :=
    hγ.exists_mapClusterPt_curveVelocityLiftWithin isPreconnected_Ioo (Ioo_mem_nhdsGT hab) hp
  obtain ⟨c, hc, δ, hδ, heq⟩ := hγ.exists_lt_isGeodesicCurveOn_Ioo hab hz
  refine ⟨c, hc, δ, hδ, heq, tendsto_nhds_unique ?_ hp⟩
  refine ((hδ.continuousOn.continuousAt (Ioo_mem_nhds hc hab)).tendsto.mono_left
    nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with t ht using heq ht

/-- A geodesic on `(a, b)` which converges to a point `p` as `t → b⁻` agrees on `(a, b)` with a
geodesic on a strictly longer interval `(a, d)`, whose value at `b` is `p`. -/
theorem exists_gt_isGeodesicCurveOn_Ioo_of_tendsto (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    (hab : a < b) {p : M} (hp : Tendsto γ (𝓝[<] b) (𝓝 p)) :
    ∃ d > b, ∃ δ : ℝ → M, IsGeodesicCurveOn I δ (Ioo a d) ∧ EqOn δ γ (Ioo a b) ∧ δ b = p := by
  obtain ⟨z, hz⟩ :=
    hγ.exists_mapClusterPt_curveVelocityLiftWithin isPreconnected_Ioo (Ioo_mem_nhdsLT hab) hp
  obtain ⟨d, hd, δ, hδ, heq⟩ := hγ.exists_gt_isGeodesicCurveOn_Ioo hab hz
  refine ⟨d, hd, δ, hδ, heq, tendsto_nhds_unique ?_ hp⟩
  refine ((hδ.continuousOn.continuousAt (Ioo_mem_nhds hab hd)).tendsto.mono_left
    nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht using heq ht

/-- **Extension of a geodesic past both endpoints.** A geodesic on `(a, b)` which is continuous
on `[a, b]` agrees on `[a, b]` with a geodesic on an open interval `(c, d)` containing
`[a, b]`. -/
theorem exists_isGeodesicCurveOn_Ioo_of_continuousOn_Icc (hγ : IsGeodesicCurveOn I γ (Ioo a b))
    (hab : a < b) (hcont : ContinuousOn γ (Icc a b)) :
    ∃ c < a, ∃ d > b, ∃ δ : ℝ → M, IsGeodesicCurveOn I δ (Ioo c d) ∧ EqOn δ γ (Icc a b) := by
  have ha : Tendsto γ (𝓝[>] a) (𝓝 (γ a)) := by
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hab] using
      (hcont a (left_mem_Icc.2 hab.le)).mono Ioo_subset_Icc_self
  have hb : Tendsto γ (𝓝[<] b) (𝓝 (γ b)) := by
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hab] using
      (hcont b (right_mem_Icc.2 hab.le)).mono Ioo_subset_Icc_self
  obtain ⟨c, hc, δ₁, hδ₁, heq₁, hδ₁a⟩ := hγ.exists_lt_isGeodesicCurveOn_Ioo_of_tendsto hab ha
  have hcb : c < b := hc.trans hab
  have hδ₁b : Tendsto δ₁ (𝓝[<] b) (𝓝 (γ b)) := by
    refine hb.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht using (heq₁ ht).symm
  obtain ⟨d, hd, δ, hδ, heq, hδb⟩ := hδ₁.exists_gt_isGeodesicCurveOn_Ioo_of_tendsto hcb hδ₁b
  refine ⟨c, hc, d, hd, δ, hδ, fun t ht ↦ ?_⟩
  rcases ht.2.eq_or_lt with rfl | htb
  · exact hδb
  · rw [heq ⟨hc.trans_le ht.1, htb⟩]
    rcases ht.1.eq_or_lt with rfl | hat
    · exact hδ₁a
    · exact heq₁ ⟨hat, htb⟩

end IsGeodesicCurveOn

variable [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A geodesic on a nondegenerate closed interval has a globally smooth extension agreeing on
that interval, with the same velocity lift, including at the endpoints. -/
theorem IsGeodesicCurveOn.exists_contMDiff_isGeodesicCurveOn_Icc
    (hγ : IsGeodesicCurveOn I γ (Icc a b)) (hab : a < b) :
    ∃ f : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ f ∧ EqOn f γ (Icc a b) ∧
      IsGeodesicCurveOn I f (Icc a b) ∧ ∀ u ∈ Icc a b,
        curveVelocityLift I f u = curveVelocityLiftWithin I γ (Icc a b) u := by
  have hγopen := hγ.mono (uniqueDiffOn_Ioo a b) Ioo_subset_Icc_self
  obtain ⟨c, hc, d, hd, δ, hδ, hδγ⟩ :=
    hγopen.exists_isGeodesicCurveOn_Ioo_of_continuousOn_Icc hab hγ.continuousOn
  have hsub : Icc a b ⊆ Ioo c d := fun u hu ↦ ⟨hc.trans_le hu.1, hu.2.trans_lt hd⟩
  obtain ⟨f, hf, hevent⟩ := hδ.exists_contMDiff_eventuallyEq isOpen_Ioo isPreconnected_Ioo
    isClosed_Icc hsub
  have heq : EqOn f γ (Icc a b) := fun u hu ↦ (hevent u hu).self_of_nhds.trans (hδγ hu)
  refine ⟨f, hf, heq, hγ.congr heq, fun u hu ↦ ?_⟩
  have hev : f =ᶠ[𝓝[Icc a b] u] γ := by
    filter_upwards [self_mem_nhdsWithin] with t ht using heq ht
  calc
    curveVelocityLift I f u = curveVelocityLiftWithin I f (Icc a b) u := by
      rw [curveVelocityLiftWithin_apply, curveVelocityLift_apply,
        curveVelocityWithin_subset (subset_univ _) ((uniqueDiffOn_Icc hab) u hu)
          ((hf.mdifferentiable (by simp)) u).mdifferentiableWithinAt,
        curveVelocityWithin_univ]
    _ = curveVelocityLiftWithin I γ (Icc a b) u := hev.curveVelocityLiftWithin_eq (heq hu)

variable {p : M} {v : TangentSpace I p}

/-- **Smooth extension of a geodesic segment.** Near a set `K` closed in `ℝ` and contained in its
maximal interval, the maximal geodesic from `p` with initial velocity `v` agrees with a curve
which is smooth on the whole line. -/
theorem exists_contMDiff_eventuallyEq_maximalGeodesic {K : Set ℝ} (hK : IsClosed K)
    (hKG : K ⊆ geodesicInterval I M p v) :
    ∃ f : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ f ∧ ∀ t ∈ K, f =ᶠ[𝓝 t] maximalGeodesic I M p v := by
  exact (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn
    |>.exists_contMDiff_eventuallyEq isOpen_geodesicInterval isPreconnected_geodesicInterval
      hK hKG

/-- **An affinely reparametrized geodesic segment as a smooth geodesic piece.** If `t₀ < t₁` and
`m * u + k` lies in the maximal interval of `v` for `u ∈ [t₀, t₁]`, there is a curve smooth on
the whole line which agrees near each point of `[t₀, t₁]` with `u ↦ γ_v (m * u + k)`, is a
geodesic there and has the corresponding affinely rescaled velocity. -/
theorem exists_contMDiff_isGeodesicCurveOn_maximalGeodesic {m k t₀ t₁ : ℝ}
    (ht : t₀ < t₁) (hG : ∀ u ∈ Icc t₀ t₁, m * u + k ∈ geodesicInterval I M p v) :
    ∃ f : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ f ∧
      (∀ u ∈ Icc t₀ t₁, f =ᶠ[𝓝 u] fun x ↦ maximalGeodesic I M p v (m * x + k)) ∧
      IsGeodesicCurveOn I f (Icc t₀ t₁) ∧ ∀ u ∈ Icc t₀ t₁,
        curveVelocity I f u = m • curveVelocity I (maximalGeodesic I M p v) (m * u + k) := by
  exact (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn
    |>.exists_contMDiff_isGeodesicCurveOn_comp_affine isOpen_geodesicInterval
      isPreconnected_geodesicInterval ht hG

end TauCeti.Manifold
