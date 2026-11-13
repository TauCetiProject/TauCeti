/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
import TauCeti.Geometry.Manifold.IntegralCurve.Extension
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed

/-!
# Extending a geodesic past a finite endpoint

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

The extension theorems need a `C²` metric on a `C³` manifold without boundary, and nothing is
assumed about the completeness of the manifold.

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

end TauCeti.Manifold
