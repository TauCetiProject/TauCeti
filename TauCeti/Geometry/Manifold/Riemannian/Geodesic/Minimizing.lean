/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ProperSpace
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Corner
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import Mathlib.Analysis.Normed.Module.Ray
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Minimizing geodesics from an everywhere-defined exponential map

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and suppose that the
exponential map at `p` is defined on all of `T_p M`.  Then every point `q` is reached from `p` by
a *minimizing* geodesic: there is a tangent vector `v` with `exp_p v = q` and
`‖v‖ = dist p q`, so that the geodesic `t ↦ exp_p (t • v)` on `[0, 1]` joins `p` to `q`, has
length `dist p q`, and each of its subsegments realizes the distance between its endpoints.

Combined with `properSpace_of_expDomain_eq_univ_of_exists_riemannianExp_eq_and_norm_le_dist`,
this shows that an everywhere-defined exponential map at a single point makes the manifold proper,
and, through `expDomain_eq_univ_of_completeSpace`, that a complete Riemannian manifold is proper.

## Main results

In the namespace `TauCeti.Manifold`:

* `exists_riemannianExp_eq_and_norm_eq_dist`: **if `exp_p` is everywhere defined, every point is
  `exp_p v` for a tangent vector `v` with `‖v‖ = dist p q`.**
* `dist_riemannianExp_smul_riemannianExp_smul`: along such a minimizing initial velocity, the
  radial geodesic on `[0, 1]` travels at constant speed `dist p q` in the metric sense.
* `exists_isGeodesicCurveOn_Icc_pathELength_eq_edist`: **a minimizing geodesic segment joins `p`
  to every point**, and each of its subsegments realizes the distance between its endpoints.
* `properSpace_of_expDomain_eq_univ`: an everywhere-defined exponential map at one point makes
  the manifold proper.
* `properSpace_of_completeSpace`: a complete Riemannian manifold is proper.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8, the implication
  from assertion (a) to assertion (f), and the implications (a) ⇒ (b) and (c) ⇒ (b).
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6, Lemma 6.18 and
  Thm. 6.19.
-/

public section

open Bundle Manifold Metric Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)] [IsRiemannianManifold I M]

/- The argument is do Carmo's. Put `r = dist p q`. On a small geodesic sphere about `p`, choose a
point nearest to `q`, and follow its radial direction as `γ`. The closed set of times
`s ∈ [0, r]` with `dist (γ s) q ≤ r - s` has largest element `r`: otherwise the local sphere
lemma above produces a minimizing broken geodesic extension. The corner lemma makes that extension
a later point of `γ`, contradicting maximality. -/

/-- **A minimizing broken geodesic does not break.**  Let `γ` be the all-time maximal geodesic
from `p` with unit initial velocity, let `s > 0`, and let `w` be a tangent vector at `γ s` in the
domain of the exponential map.  If `exp_{γ s} w` is at distance at least `s + ‖w‖` from `p`, it is
`γ (s + ‖w‖)`. -/
private theorem riemannianExp_eq_maximalGeodesic_add {p : M} {u : TangentSpace I p}
    (hu : geodesicInterval I M p u = univ) (hu1 : ‖u‖ = 1) {s : ℝ} (hs : 0 < s)
    {w : TangentSpace I (maximalGeodesic I M p u s)}
    (hw : w ∈ expDomain I M (maximalGeodesic I M p u s))
    (hdist : s + ‖w‖ ≤ dist p (riemannianExp I M (maximalGeodesic I M p u s) w)) :
    riemannianExp I M (maximalGeodesic I M p u s) w = maximalGeodesic I M p u (s + ‖w‖) := by
  set V := curveVelocityWithin I (maximalGeodesic I M p u) (geodesicInterval I M p u) s
  have hsJ : s ∈ geodesicInterval I M p u := hu ▸ mem_univ s
  -- The geodesic restarted at `γ s` with velocity `V` is `γ` translated by `s`.
  have hexp (τ : ℝ) :
      riemannianExp I M (maximalGeodesic I M p u s) (τ • V) = maximalGeodesic I M p u (s + τ) := by
    rw [riemannianExp_smul, ← maximalGeodesic_add hsJ (hu ▸ mem_univ _)]
  have hV : ‖V‖ = 1 := (norm_curveVelocityWithin_maximalGeodesic hsJ).trans hu1
  have hback : (-s) • V ∈ expDomain I M (maximalGeodesic I M p u s) := by
    rw [← mem_geodesicInterval_iff_smul_mem_expDomain,
      mem_geodesicInterval_maximalGeodesic_iff hsJ, hu]
    exact mem_univ _
  -- Otherwise the path from `p` back along `γ` to `γ s` and out to `exp_{γ s} w` has a corner at
  -- `γ s`, and it would be shorter than the distance between its endpoints.
  have hray : SameRay ℝ ((-s) • V) (-w) := by
    by_contra h
    have hlt := dist_riemannianExp_lt_norm_add_norm hback hw h
    rw [hexp, add_neg_cancel, maximalGeodesic_zero, norm_smul, hV, mul_one, Real.norm_eq_abs,
      abs_neg, abs_of_pos hs] at hlt
    linarith
  have hVw : SameRay ℝ V w := by
    rw [neg_smul, sameRay_neg_iff] at hray
    simpa [inv_smul_smul₀ hs.ne'] using hray.pos_smul_left (inv_pos.2 hs)
  have hw' : w = ‖w‖ • V := by
    simpa [hV] using hVw.norm_smul_eq
  rw [hw', hexp, norm_smul, hV, mul_one, norm_norm]

/-- **The minimizing direction propagates.**  Let `γ` be the all-time maximal geodesic from `p`
with unit initial velocity, and let `0 < s < dist p q` be a time at which `γ s` lies on a minimizing
path to `q`, in the sense that `dist (γ s) q ≤ dist p q - s`.  Then some later time `s' ≤ dist p q`
has the same property. -/
private theorem exists_gt_dist_maximalGeodesic_le {p q : M} {u : TangentSpace I p}
    (hu : geodesicInterval I M p u = univ) (hu1 : ‖u‖ = 1) {s : ℝ} (hs : 0 < s)
    (hsr : s < dist p q) (hsq : dist (maximalGeodesic I M p u s) q ≤ dist p q - s) :
    ∃ s' > s, s' ≤ dist p q ∧ dist (maximalGeodesic I M p u s') q ≤ dist p q - s' := by
  set γ := maximalGeodesic I M p u
  have hpγ : dist p (γ s) ≤ s := by
    simpa [γ, ← riemannianExp_smul, norm_smul, hu1, abs_of_nonneg hs.le] using
      dist_riemannianExp_le p (s • u)
  have hxq : dist (γ s) q = dist p q - s :=
    le_antisymm hsq (by linarith [dist_triangle p (γ s) q])
  -- The point of a small geodesic sphere about `γ s` nearest to `q` lies on `γ`.
  obtain ⟨ε, hε, hstep⟩ := exists_dist_riemannianExp_eq_dist_sub (I := I) (γ s) q
  set δ := min (ε / 2) (dist p q - s)
  have hδ : 0 < δ := lt_min (half_pos hε) (sub_pos.2 hsr)
  obtain ⟨w, hw, hwn, hwq⟩ := hstep δ hδ.le (min_lt_of_left_lt (half_lt_self hε))
    (hxq ▸ min_le_right _ _)
  have hfar : s + ‖w‖ ≤ dist p (riemannianExp I M (γ s) w) := by
    linarith [dist_triangle p (riemannianExp I M (γ s) w) q]
  have heq : riemannianExp I M (γ s) w = γ (s + ‖w‖) :=
    riemannianExp_eq_maximalGeodesic_add hu hu1 hs hw hfar
  refine ⟨s + δ, by linarith, by linarith [min_le_right (ε / 2) (dist p q - s)], ?_⟩
  rw [← hwn, ← heq, hwq, hxq, hwn]
  linarith

variable {p : M}

/-- **An everywhere-defined exponential map reaches every point minimally.**  If the exponential
map at `p` is defined on all of `T_p M`, then every point `q` is `exp_p v` for a tangent vector `v`
with `‖v‖ = dist p q`. -/
theorem exists_riemannianExp_eq_and_norm_eq_dist (ha : expDomain I M p = univ) (q : M) :
    ∃ v : TangentSpace I p, riemannianExp I M p v = q ∧ ‖v‖ = dist p q := by
  set r := dist p q
  rcases (dist_nonneg : 0 ≤ r).eq_or_lt with hr | hr
  · exact ⟨0, by rw [riemannianExp_zero, dist_eq_zero.1 hr.symm], by rw [norm_zero]; exact hr⟩
  -- The first step: the point of a small geodesic sphere about `p` nearest to `q`.
  obtain ⟨ε, hε, hstep⟩ := exists_dist_riemannianExp_eq_dist_sub (I := I) p q
  set δ := min (ε / 2) r
  have hδ : 0 < δ := lt_min (half_pos hε) hr
  obtain ⟨w₀, -, hw₀, hw₀q⟩ :=
    hstep δ hδ.le (min_lt_of_left_lt (half_lt_self hε)) (min_le_right _ _)
  have hw₀0 : w₀ ≠ 0 := norm_ne_zero_iff.1 (hw₀ ▸ hδ.ne')
  set u := ‖w₀‖⁻¹ • w₀
  have hu1 : ‖u‖ = 1 := norm_smul_inv_norm hw₀0
  have hJ : geodesicInterval I M p u = univ := by
    rw [geodesicInterval_eq_preimage_expDomain, ha, preimage_univ]
  set γ := maximalGeodesic I M p u
  have hγexp (t : ℝ) : riemannianExp I M p (t • u) = γ t := riemannianExp_smul p u t
  have hγδ : γ δ = riemannianExp I M p w₀ := by
    rw [← hγexp, ← hw₀, smul_inv_smul₀ (norm_ne_zero_iff.2 hw₀0)]
  have hγcont : Continuous γ := by
    rw [← continuousOn_univ, ← hJ]
    exact lipschitzOnWith_maximalGeodesic.continuousOn
  -- The times `s ∈ [0, r]` at which `γ s` lies on a minimizing path to `q`; its largest element
  -- is `r`, since otherwise the minimizing path extends past it.
  set A := {s ∈ Icc 0 r | dist (γ s) q ≤ r - s}
  have hAclosed : IsClosed A :=
    isClosed_Icc.inter (isClosed_le (hγcont.dist continuous_const)
      (continuous_const.sub continuous_id))
  have hAbdd : BddAbove A := ⟨r, fun s hs ↦ hs.1.2⟩
  have hδA : δ ∈ A := ⟨⟨hδ.le, min_le_right _ _⟩, by rw [hγδ, hw₀q]⟩
  have hsA : sSup A ∈ A := hAclosed.csSup_mem ⟨δ, hδA⟩ hAbdd
  have hsr : sSup A = r := by
    refine hsA.1.2.eq_or_lt.resolve_right fun hlt ↦ ?_
    obtain ⟨s', hs', hs'r, hs'q⟩ := exists_gt_dist_maximalGeodesic_le hJ hu1
      (hδ.trans_le (le_csSup hAbdd hδA)) hlt hsA.2
    exact (le_csSup hAbdd ⟨⟨by linarith [hsA.1.1], hs'r⟩, hs'q⟩).not_gt hs'
  refine ⟨r • u, ?_, by rw [norm_smul, hu1, mul_one, Real.norm_of_nonneg hr.le]⟩
  have hγr := hsA.2
  rw [hsr, sub_self] at hγr
  rw [hγexp]
  exact dist_le_zero.1 hγr

/-- **Minimizing radial geodesics travel at constant metric speed.**  If `v` lies in the domain
of `exp_p` and `‖v‖ ≤ dist p (exp_p v)` (so that equality holds, by `dist_riemannianExp_le`),
then for all `s, t ∈ [0, 1]` the points `exp_p (s • v)`
and `exp_p (t • v)` are at distance `|s - t| * ‖v‖`. -/
theorem dist_riemannianExp_smul_riemannianExp_smul {v : TangentSpace I p}
    (hv : v ∈ expDomain I M p) (hmin : ‖v‖ ≤ dist p (riemannianExp I M p v)) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (riemannianExp I M p (s • v)) (riemannianExp I M p (t • v)) = |s - t| * ‖v‖ := by
  have hsub : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.1 hv)
  have hlip (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
      dist (riemannianExp I M p (a • v)) (riemannianExp I M p (b • v)) ≤ ‖v‖ * |a - b| := by
    rw [riemannianExp_smul, riemannianExp_smul, ← Real.dist_eq]
    exact lipschitzOnWith_maximalGeodesic.dist_le_mul _ (hsub ha) _ (hsub hb)
  -- Going from `p` to `exp_p v` through the two points cannot beat the distance `‖v‖`.
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, abs_sub_comm]
    exact this ht hs (le_of_not_ge hst)
  refine le_antisymm ((hlip s t hs ht).trans_eq (mul_comm _ _)) ?_
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have hps : dist p (riemannianExp I M p (s • v)) ≤ s * ‖v‖ := by
    simpa [abs_of_nonneg hs.1, mul_comm] using hlip 0 s h0 hs
  have htq : dist (riemannianExp I M p (t • v)) (riemannianExp I M p v) ≤ (1 - t) * ‖v‖ := by
    simpa [abs_sub_comm t 1, abs_of_nonneg (sub_nonneg.2 ht.2), mul_comm] using hlip t 1 ht h1
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hst)]
  linarith [dist_triangle4 p (riemannianExp I M p (s • v)) (riemannianExp I M p (t • v))
    (riemannianExp I M p v)]

/-- **An everywhere-defined exponential map yields minimizing geodesics.**  If the exponential map
at `p` is defined on all of `T_p M`, then every point `q` is joined to `p` by a geodesic segment
`γ` on `[0, 1]` whose length is the distance from `p` to `q`; moreover each of its subsegments
realizes the distance between its endpoints. -/
theorem exists_isGeodesicCurveOn_Icc_pathELength_eq_edist (ha : expDomain I M p = univ) (q : M) :
    ∃ γ : ℝ → M, IsGeodesicCurveOn I γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q ∧
      pathELength I γ 0 1 = edist p q ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
        pathELength I γ s t = edist (γ s) (γ t) := by
  obtain ⟨v, hvq, hv⟩ := exists_riemannianExp_eq_and_norm_eq_dist ha q
  have hJ : geodesicInterval I M p v = univ := by
    rw [geodesicInterval_eq_preimage_expDomain, ha, preimage_univ]
  have hmin : ‖v‖ ≤ dist p (riemannianExp I M p v) := (hvq ▸ hv).le
  have hγ (t : ℝ) : maximalGeodesic I M p v t = riemannianExp I M p (t • v) :=
    (riemannianExp_smul p v t).symm
  -- Every subsegment of the radial geodesic has length `(t - s) * ‖v‖`, its endpoint distance.
  have hsub : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
      pathELength I (maximalGeodesic I M p v) s t =
        edist (maximalGeodesic I M p v s) (maximalGeodesic I M p v t) := by
    intro s hs t ht hst
    rw [pathELength_maximalGeodesic (hJ ▸ mem_univ s) (hJ ▸ mem_univ t), edist_dist, hγ, hγ,
      dist_riemannianExp_smul_riemannianExp_smul (ha ▸ mem_univ v) hmin hs ht,
      abs_of_nonpos (sub_nonpos.2 hst), neg_sub, ENNReal.ofReal_mul (sub_nonneg.2 hst),
      ofReal_norm, mul_comm]
  refine ⟨maximalGeodesic I M p v, ?_, maximalGeodesic_zero p v, ?_, ?_, hsub⟩
  · exact (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.mono
      (uniqueDiffOn_Icc zero_lt_one) (hJ ▸ subset_univ _)
  · rw [← riemannianExp_def, hvq]
  · rw [hsub 0 (left_mem_Icc.2 zero_le_one) 1 (right_mem_Icc.2 zero_le_one) zero_le_one,
      maximalGeodesic_zero, ← riemannianExp_def, hvq]

/-- **An everywhere-defined exponential map makes the manifold proper.**  If the exponential map
at a single point `p` is defined on all of `T_p M`, every closed bounded subset of `M` is
compact. -/
theorem properSpace_of_expDomain_eq_univ (ha : expDomain I M p = univ) : ProperSpace M :=
  properSpace_of_expDomain_eq_univ_of_exists_riemannianExp_eq_and_norm_le_dist ha fun q ↦
    (exists_riemannianExp_eq_and_norm_eq_dist ha q).imp fun _ h ↦ ⟨h.1, h.2.le⟩

variable (I) in
include I in
/-- **A complete Riemannian manifold is proper**: its closed bounded subsets are compact.  The
model `I` cannot be inferred from the conclusion, so it is an explicit argument. -/
theorem properSpace_of_completeSpace [CompleteSpace M] : ProperSpace M := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨p⟩⟩
  · infer_instance
  · have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
      (V := fun x : M ↦ TangentSpace I x)
    exact properSpace_of_expDomain_eq_univ (expDomain_eq_univ_of_completeSpace (I := I) p)

end TauCeti.Manifold

end
