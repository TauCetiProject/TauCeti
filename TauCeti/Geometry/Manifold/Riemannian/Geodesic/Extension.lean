/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
import Mathlib.Topology.Order.IntermediateValue
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

Applying this two-sided extension to the closed subinterval between any two parameters identifies
every geodesic on a preconnected parameter set — open, closed, half-open, or unbounded — with a
time-translated restriction of the maximal integral curve of the geodesic spray (and, for a smooth
metric, of the maximal geodesic) determined by its value and velocity at any chosen parameter. In
particular, already for a `C²` metric on a `C³` Hausdorff manifold without boundary, every geodesic
on a preconnected parameter set agrees there with a geodesic defined on an open preconnected
superset. For a smooth metric, near any closed subset of an open preconnected geodesic domain it
also agrees with a curve smooth on the whole line.

The finite-endpoint and open-superset geodesic extensions need a `C²` metric on a `C³` Hausdorff
manifold without boundary. The smooth extensions on open preconnected sets require only a smooth
metric and manifold; the closed-interval and maximal-geodesic smooth extensions and the
maximal-geodesic identifications also assume a Hausdorff manifold without boundary. No completeness
assumption is needed.

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
* `TauCeti.Manifold.IsGeodesicCurveOn.sub_mem_geodesicInterval_of_isPreconnected` and
  `TauCeti.Manifold.IsGeodesicCurveOn.maximalGeodesic_sub_eq_of_isPreconnected`: on any
  preconnected parameter set, a geodesic is a time-translated piece of the maximal geodesic from
  any of its parameters.
* `TauCeti.Manifold.IsGeodesicCurveOnFrom.subset_geodesicInterval_of_isPreconnected`,
  `TauCeti.Manifold.IsGeodesicCurveOn.subset_geodesicInterval_of_maximalGeodesic`, and
  `TauCeti.Manifold.IsGeodesicCurveOnFrom.eqOn_maximalGeodesic_of_isPreconnected`: any geodesic
  with initial data `(p, v)` on a preconnected parameter set is defined inside
  `geodesicInterval I M p v` and agrees there with `maximalGeodesic I M p v`.
* `TauCeti.Manifold.IsGeodesicCurveOn.exists_isOpen_isPreconnected_superset`: every geodesic on a
  preconnected parameter set extends to an open preconnected superset.
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

variable [IsManifold I ∞ M]
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
      (𝓟 {z : TangentBundle I M | z.proj ∈ K ∧ ‖z.snd‖ ≤ ‖curveVelocityWithin I γ s τ‖}) := by
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

/-- Extending the closed subinterval between any two parameters of a preconnected geodesic
identifies it with the base projection of the maximal integral curve of the geodesic spray started
at the velocity lift at the first parameter. -/
private theorem sub_mem_and_maximalIntegralCurve_sub_eq_of_isPreconnected
    {s : Set ℝ} {τ t : ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    (hτ : τ ∈ s) (ht : t ∈ s) :
    t - τ ∈ maximalIntegralCurveInterval (geodesicSpray I M) (curveVelocityLiftWithin I γ s τ) ∧
      (maximalIntegralCurve (geodesicSpray I M) (curveVelocityLiftWithin I γ s τ) (t - τ)).proj =
        γ t := by
  rcases eq_or_ne t τ with rfl | hne
  · rw [sub_self, maximalIntegralCurve_zero, curveVelocityLiftWithin_proj]
    exact ⟨zero_mem_maximalIntegralCurveInterval contMDiff_one_geodesicSpray.contMDiffAt, rfl⟩
  have hlr : min τ t < max τ t := min_lt_max.2 hne.symm
  have hmin : min τ t ∈ s := min_rec' (· ∈ s) hτ ht
  have hmax : max τ t ∈ s := max_rec' (· ∈ s) hτ ht
  have hsub : Icc (min τ t) (max τ t) ⊆ s := hs.ordConnected.out hmin hmax
  obtain ⟨c, hc, d, hd, δ, hδ, heq⟩ :=
    (hγ.mono isOpen_Ioo.uniqueDiffOn
      (Ioo_subset_Icc_self.trans hsub)).exists_isGeodesicCurveOn_Ioo_of_continuousOn_Icc
      hlr (hγ.continuousOn.mono hsub)
  have hτ_Icc : τ ∈ Icc (min τ t) (max τ t) := ⟨min_le_left _ _, le_max_left _ _⟩
  have ht_Icc : t ∈ Icc (min τ t) (max τ t) := ⟨min_le_right _ _, le_max_right _ _⟩
  have hIcc_Ioo : Icc (min τ t) (max τ t) ⊆ Ioo c d :=
    fun r hr ↦ ⟨hc.trans_le hr.1, hr.2.trans_lt hd⟩
  have hτ_Ioo : τ ∈ Ioo c d := hIcc_Ioo hτ_Icc
  have ht_Ioo : t ∈ Ioo c d := hIcc_Ioo ht_Icc
  have hlift : curveVelocityLift I δ τ = curveVelocityLiftWithin I γ s τ := by
    have h1 : curveVelocityLift I δ τ =
        curveVelocityLiftWithin I δ (Icc (min τ t) (max τ t)) τ := by
      rw [curveVelocityLift_apply, curveVelocityLiftWithin_apply,
        curveVelocityWithin_subset hIcc_Ioo (uniqueDiffOn_Icc hlr τ hτ_Icc)
          (hδ.mdifferentiableOn τ hτ_Ioo),
        curveVelocityWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hτ_Ioo)]
    have h2 : curveVelocityLiftWithin I δ (Icc (min τ t) (max τ t)) τ =
        curveVelocityLiftWithin I γ (Icc (min τ t) (max τ t)) τ :=
      (heq.eventuallyEq_of_mem self_mem_nhdsWithin).curveVelocityLiftWithin_eq (heq hτ_Icc)
    have h3 : curveVelocityLiftWithin I γ (Icc (min τ t) (max τ t)) τ =
        curveVelocityLiftWithin I γ s τ := by
      rw [curveVelocityLiftWithin_apply, curveVelocityLiftWithin_apply,
        curveVelocityWithin_subset hsub (uniqueDiffOn_Icc hlr τ hτ_Icc) (hγ.mdifferentiableOn τ hτ)]
    exact h1.trans (h2.trans h3)
  have hshift := hδ.isGeodesicCurveOnFrom_comp_add_const hτ_Ioo
  let z := curveVelocityLiftWithin I (δ ∘ fun u : ℝ ↦ u + τ) (Ioo (c - τ) (d - τ))
  have hz : IsMIntegralCurveOn z (geodesicSpray I M) (Ioo (c - τ) (d - τ)) :=
    (isMIntegralCurveOn_curveVelocityLiftWithin_iff isOpen_Ioo.uniqueDiffOn
      hshift.isGeodesicCurveOn.contMDiffOn).2 hshift.isGeodesicCurveOn
  have hz0 : z 0 = curveVelocityLiftWithin I γ s τ :=
    ((curveVelocityLiftWithin_apply _ _ 0).trans
      (hshift.initial_eq.trans (curveVelocityLift_apply δ τ).symm)).trans hlift
  have ht_shift : t - τ ∈ Ioo (c - τ) (d - τ) :=
    ⟨sub_lt_sub_right ht_Ioo.1 τ, sub_lt_sub_right ht_Ioo.2 τ⟩
  refine ⟨hz.subset_maximalIntegralCurveInterval hshift.zero_mem hz0 ht_shift, ?_⟩
  have heq_int := hz.eqOn_maximalIntegralCurve contMDiff_one_geodesicSpray hshift.zero_mem hz0
    ht_shift
  have hproj : (z (t - τ)).proj = γ t := by
    rw [curveVelocityLiftWithin_proj, Function.comp_apply, sub_add_cancel]
    exact heq ht_Icc
  exact (congrArg TotalSpace.proj heq_int).trans hproj

/-- **Extension of a geodesic from any preconnected parameter set to an open interval.** Every
geodesic on a preconnected parameter set agrees on that set with a geodesic defined on an open
preconnected superset. -/
theorem exists_isOpen_isPreconnected_superset
    {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s) :
    ∃ U : Set ℝ, IsOpen U ∧ IsPreconnected U ∧ s ⊆ U ∧
      ∃ δ : ℝ → M, IsGeodesicCurveOn I δ U ∧ EqOn δ γ s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨τ, hτ⟩
  · exact ⟨∅, isOpen_empty, isPreconnected_empty, Subset.rfl, γ, hγ, eqOn_refl γ ∅⟩
  let z₀ := curveVelocityLiftWithin I γ s τ
  let I₀ := maximalIntegralCurveInterval (geodesicSpray I M) z₀
  let U : Set ℝ := (fun t : ℝ ↦ 1 * t + (-τ)) ⁻¹' I₀
  have hU_open : IsOpen U := isOpen_maximalIntegralCurveInterval.preimage (by fun_prop)
  have hU_conn : IsPreconnected U := by
    have himg : U = (fun r : ℝ ↦ r + τ) '' I₀ := by
      ext t
      simp [U]
    rw [himg]
    exact isPreconnected_maximalIntegralCurveInterval.image _ (by fun_prop)
  have hgeo₀ : IsGeodesicCurveOn I
      (fun r ↦ (maximalIntegralCurve (geodesicSpray I M) z₀ r).proj) I₀ :=
    isGeodesicCurveOn_proj_of_isMIntegralCurveOn isOpen_maximalIntegralCurveInterval.uniqueDiffOn
      (isMIntegralCurveOn_maximalIntegralCurve contMDiff_one_geodesicSpray)
  refine ⟨U, hU_open, hU_conn, fun t ht ↦ ?_,
    fun t ↦ (maximalIntegralCurve (geodesicSpray I M) z₀ (1 * t + (-τ))).proj,
    hgeo₀.comp_affine 1 (-τ) hU_open.uniqueDiffOn (fun _ hr ↦ hr),
    fun t ht ↦ ?_⟩
  · simpa only [U, mem_preimage, one_mul, ← sub_eq_add_neg] using
      (hγ.sub_mem_and_maximalIntegralCurve_sub_eq_of_isPreconnected hs hτ ht).1
  · simpa only [one_mul, ← sub_eq_add_neg] using
      (hγ.sub_mem_and_maximalIntegralCurve_sub_eq_of_isPreconnected hs hτ ht).2

end IsGeodesicCurveOn

section Maximal

variable [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Extending the closed subinterval between any two parameters of a preconnected geodesic
identifies it with the maximal geodesic started at the first parameter. -/
private theorem IsGeodesicCurveOn.sub_mem_and_maximalGeodesic_sub_eq_of_isPreconnected
    {s : Set ℝ} {τ t : ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    (hτ : τ ∈ s) (ht : t ∈ s) :
    t - τ ∈ geodesicInterval I M (γ τ) (curveVelocityWithin I γ s τ) ∧
      maximalGeodesic I M (γ τ) (curveVelocityWithin I γ s τ) (t - τ) = γ t := by
  have h := hγ.sub_mem_and_maximalIntegralCurve_sub_eq_of_isPreconnected hs hτ ht
  rw [curveVelocityLiftWithin_apply, maximalIntegralCurveInterval_geodesicSpray,
    ← maximalGeodesic_def] at h
  exact h

/-- For a geodesic `γ` on any preconnected parameter set `s` and `τ, t ∈ s`, the shifted time
`t - τ` lies in the maximal geodesic interval for the initial data `(γ τ, γ'(τ))`. -/
theorem IsGeodesicCurveOn.sub_mem_geodesicInterval_of_isPreconnected
    {s : Set ℝ} {τ t : ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    (hτ : τ ∈ s) (ht : t ∈ s) :
    t - τ ∈ geodesicInterval I M (γ τ) (curveVelocityWithin I γ s τ) :=
  (hγ.sub_mem_and_maximalGeodesic_sub_eq_of_isPreconnected hs hτ ht).1

/-- **Every geodesic on a preconnected parameter set is a translate of a maximal geodesic.**
For a geodesic `γ` on a preconnected set `s` and `τ, t ∈ s`, the maximal geodesic with initial
data `(γ τ, γ'(τ))` takes the value `γ t` at time `t - τ`. -/
theorem IsGeodesicCurveOn.maximalGeodesic_sub_eq_of_isPreconnected
    {s : Set ℝ} {τ t : ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    (hτ : τ ∈ s) (ht : t ∈ s) :
    maximalGeodesic I M (γ τ) (curveVelocityWithin I γ s τ) (t - τ) = γ t :=
  (hγ.sub_mem_and_maximalGeodesic_sub_eq_of_isPreconnected hs hτ ht).2

/-- Every geodesic with initial data `(p, v)` on a preconnected parameter set is defined inside
`geodesicInterval I M p v`. -/
theorem IsGeodesicCurveOnFrom.subset_geodesicInterval_of_isPreconnected
    {p : M} {v : TangentSpace I p} {s : Set ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ s p v) (hs : IsPreconnected s) :
    s ⊆ geodesicInterval I M p v := by
  intro t ht
  have hdom := congrArg (fun z : TangentBundle I M ↦ geodesicInterval I M z.proj z.snd)
      hγ.initial_eq
  dsimp only at hdom
  have hmem := hγ.isGeodesicCurveOn.sub_mem_geodesicInterval_of_isPreconnected hs hγ.zero_mem ht
  rw [sub_zero, hdom] at hmem
  exact hmem

/-- If `maximalGeodesic I M p v` is a geodesic on a preconnected parameter set containing `0`, then
that parameter set lies inside `geodesicInterval I M p v`. -/
theorem IsGeodesicCurveOn.subset_geodesicInterval_of_maximalGeodesic
    {p : M} {v : TangentSpace I p} {s : Set ℝ}
    (hγ : IsGeodesicCurveOn I (maximalGeodesic I M p v) s) (hs : IsPreconnected s)
    (h0 : (0 : ℝ) ∈ s) :
    s ⊆ geodesicInterval I M p v := by
  refine IsGeodesicCurveOnFrom.subset_geodesicInterval_of_isPreconnected ⟨hγ, h0, ?_⟩ hs
  have hmax := isGeodesicCurveOnFrom_maximalGeodesic (I := I) p v
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) I (maximalGeodesic I M p v) 0 :=
    (hmax.isGeodesicCurveOn.mdifferentiableOn 0 zero_mem_geodesicInterval).mdifferentiableAt
      (isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval)
  have hvel : curveVelocityWithin I (maximalGeodesic I M p v) s 0 =
      curveVelocityWithin I (maximalGeodesic I M p v) (geodesicInterval I M p v) 0 :=
    (curveVelocityWithin_eq_of_hasMFDerivWithinAt
      (hasMFDerivAt_curveVelocity hd).hasMFDerivWithinAt (hγ.uniqueDiffOn 0 h0)).trans
      (curveVelocityWithin_of_mem_nhds
        (isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval)).symm
  rw [hvel]
  exact hmax.initial_eq

/-- Every geodesic with initial data `(p, v)` on a preconnected parameter set agrees there with
`maximalGeodesic I M p v`. -/
theorem IsGeodesicCurveOnFrom.eqOn_maximalGeodesic_of_isPreconnected
    {p : M} {v : TangentSpace I p} {s : Set ℝ}
    (hγ : IsGeodesicCurveOnFrom I γ s p v) (hs : IsPreconnected s) :
    EqOn (maximalGeodesic I M p v) γ s := by
  intro t ht
  have hval := congrArg (fun z : TangentBundle I M ↦ maximalGeodesic I M z.proj z.snd t)
      hγ.initial_eq
  dsimp only at hval
  refine hval.symm.trans ?_
  simpa only [sub_zero] using
    hγ.isGeodesicCurveOn.maximalGeodesic_sub_eq_of_isPreconnected hs hγ.zero_mem ht

end Maximal

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
