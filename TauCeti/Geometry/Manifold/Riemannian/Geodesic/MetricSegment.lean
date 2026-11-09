/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing
public import TauCeti.Topology.MetricSpace.Length
import Mathlib.Analysis.Normed.Module.Ray
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Corner
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance

/-!
# Minimizing geodesics and metric geodesic segments

A metric geodesic segment from `x` to `y` is a curve on `[0, 1]` with
`dist (γ s) (γ t) = |s - t| * dist x y`, and a geodesic space is one in which every pair of points
is joined by such a segment. On a Riemannian manifold the segments are the minimizing radial
geodesics: if `v` is a tangent vector at `p` whose norm is the distance from `p` to `exp_p v`, the
maximal geodesic `t ↦ exp_p (t • v)` is a metric geodesic segment.

When `M` is complete, `TauCeti.Manifold.expDomain_eq_univ_of_completeSpace` makes `exp_p` defined
on all of `T_p M` and `TauCeti.Manifold.exists_riemannianExp_eq_and_norm_eq_dist` then produces
such a `v` for every pair of points, so a complete Riemannian manifold is a geodesic space. That
the manifold is a *length* space needs no completeness; it is `TauCeti.Manifold.isLengthSpace`.

Conversely, a curve that realizes distances is a geodesic, with no regularity assumed. If
`dist (γ s) (γ t) = |s - t|` near `0`, then the logarithms at `γ 0` of the points of `γ` before and
after `0` point in opposite directions, since a broken radial path through `γ 0` is strictly longer
than the distance between its endpoints. Hence `γ` agrees near `0` with a unit-speed radial
geodesic from `γ 0`. In particular a metric geodesic segment is smooth at its interior parameters.

## Main results

In the namespace `TauCeti.Manifold`:

* `isGeodesicSegment_maximalGeodesic`: a geodesic whose initial velocity has the norm of the
  distance travelled is a metric geodesic segment.
* `exists_isGeodesicSegment_of_expDomain_eq_univ`: an everywhere-defined exponential map at `p`
  joins `p` to every point by a metric geodesic segment.
* `isGeodesicSpace_of_completeSpace`: **a complete Riemannian manifold is a geodesic space.**
* `exists_eventuallyEq_riemannianExp_smul_of_dist_eq_abs`: a curve with
  `dist (γ s) (γ t) = |s - t|` near `0` agrees near `0` with the radial geodesic
  `t ↦ exp_{γ 0} (t • v)` of a unit vector `v`; consequently it is smooth at `0`
  (`contMDiffAt_of_dist_eq_abs`) with unit speed (`norm_curveVelocity_eq_one_of_dist_eq_abs`).
* `contMDiffAt_of_dist_eq_mul_abs`: a curve with `dist (γ s) (γ t) = |s - t| * c` near `t₀` is
  smooth at `t₀`.
* `TauCeti.IsGeodesicSegment.contMDiffAt`: **a metric geodesic segment is smooth at its interior
  parameters.**

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8, assertion (f).
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 6, for the fact
  that minimizing curves with unit-speed parametrizations are geodesics, which is proved here for
  curves without any regularity assumption.
* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, AMS, 2001, Section 2.5.
-/

public section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

variable {p : M}

/-- **A minimizing geodesic is a metric geodesic segment.** Let `v` lie in the domain of `exp_p`
and satisfy `‖v‖ ≤ dist p (exp_p v)`, so that equality holds by `dist_riemannianExp_le`. Then the
maximal geodesic from `p` with initial velocity `v`, read on `[0, 1]`, is a geodesic segment from
`p` to `exp_p v` in the metric sense. -/
theorem isGeodesicSegment_maximalGeodesic {v : TangentSpace I p} (hv : v ∈ expDomain I M p)
    (hmin : ‖v‖ ≤ dist p (riemannianExp I M p v)) :
    IsGeodesicSegment (maximalGeodesic I M p v) p (riemannianExp I M p v) where
  source := maximalGeodesic_zero p v
  target := (riemannianExp_def p v).symm
  dist_eq s hs t ht := by
    rw [← riemannianExp_smul p v s, ← riemannianExp_smul p v t,
      dist_riemannianExp_smul_riemannianExp_smul hv hmin hs ht,
      le_antisymm (dist_riemannianExp_le p v) hmin]

/-- **An everywhere-defined exponential map yields metric geodesic segments.** If `exp_p` is
defined on all of `T_p M`, every point `q` is joined to `p` by a metric geodesic segment. For the
segment as an explicit geodesic of the Riemannian connection, combine
`exists_riemannianExp_eq_and_norm_eq_dist` with `isGeodesicSegment_maximalGeodesic`. -/
theorem exists_isGeodesicSegment_of_expDomain_eq_univ (ha : expDomain I M p = univ) (q : M) :
    ∃ γ : ℝ → M, IsGeodesicSegment γ p q := by
  obtain ⟨v, hvq, hv⟩ := exists_riemannianExp_eq_and_norm_eq_dist ha q
  refine ⟨maximalGeodesic I M p v, ?_⟩
  rw [← hvq]
  exact isGeodesicSegment_maximalGeodesic (ha ▸ mem_univ v) (le_of_eq (by rw [hvq, hv]))

variable (I) in
include I in
/-- **A complete Riemannian manifold is a geodesic space**: any two of its points are joined by a
curve on `[0, 1]` that is parametrised proportionally to arclength and realises their distance.
The model `I` cannot be inferred from the conclusion, so it is an explicit argument. -/
theorem isGeodesicSpace_of_completeSpace [CompleteSpace M] : IsGeodesicSpace M := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  exact ⟨fun x y ↦ exists_isGeodesicSegment_of_expDomain_eq_univ
    (expDomain_eq_univ_of_completeSpace (I := I) x) y⟩

/-! ### Metric geodesic segments are geodesics -/

/-- **A curve realizing distances is locally a radial geodesic.** If
`dist (γ s) (γ t) = |s - t|` for all `s, t ∈ [-ε, ε]`, then near `0` the curve `γ` agrees with the
radial geodesic `t ↦ exp_{γ 0} (t • v)` for a unit vector `v` at `γ 0`.

No differentiability of `γ` is assumed. Inside a normal ball at `γ 0`, the logarithms of `γ s` and
`γ t` for `s ≤ 0 ≤ t` must point in opposite directions: otherwise the strict inequality for
broken radial paths, `dist_riemannianExp_lt_norm_add_norm`, would make `dist (γ s) (γ t)` smaller
than `|s| + |t| = |s - t|`. -/
theorem exists_eventuallyEq_riemannianExp_smul_of_dist_eq_abs {γ : ℝ → M} {ε : ℝ} (hε : 0 < ε)
    (hdist : ∀ s ∈ Icc (-ε) ε, ∀ t ∈ Icc (-ε) ε, dist (γ s) (γ t) = |s - t|) :
    ∃ v : TangentSpace I (γ 0), ‖v‖ = 1 ∧
      γ =ᶠ[𝓝 0] fun t ↦ riemannianExp I M (γ 0) (t • v) := by
  obtain ⟨R, hR, hU⟩ := exists_isNormalDomain_ball (I := I) (γ 0)
  set δ := min (ε / 2) (R / 2)
  have hδ : 0 < δ := lt_min (half_pos hε) (half_pos hR)
  have hδε : δ ≤ ε := (min_le_left _ _).trans (half_le_self hε.le)
  have hδR : δ < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hsub : Icc (-δ) δ ⊆ Icc (-ε) ε := Icc_subset_Icc (neg_le_neg hδε) hδε
  have h0 : (0 : ℝ) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hdist0 : ∀ t ∈ Icc (-δ) δ, dist (γ 0) (γ t) = |t| := fun t ht ↦ by
    simpa only [zero_sub, abs_neg] using hdist 0 h0 t (hsub ht)
  have himage : ∀ t ∈ Icc (-δ) δ, γ t ∈ riemannianExp I M (γ 0) '' Metric.ball 0 R := by
    intro t ht
    rw [hU.image_riemannianExp_ball Subset.rfl, Metric.mem_eball', edist_dist, hdist0 t ht]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).2 ((abs_le.mpr ht).trans_lt hδR)
  set v : ℝ → TangentSpace I (γ 0) := fun t ↦ riemannianLog I M (γ 0) (Metric.ball 0 R) (γ t)
  have hv : ∀ t ∈ Icc (-δ) δ, v t ∈ Metric.ball 0 R :=
    fun t ht ↦ hU.riemannianLog_mem (himage t ht)
  have hexp : ∀ t ∈ Icc (-δ) δ, riemannianExp I M (γ 0) (v t) = γ t :=
    fun t ht ↦ hU.riemannianExp_riemannianLog (himage t ht)
  have hnorm : ∀ t ∈ Icc (-δ) δ, ‖v t‖ = |t| := by
    intro t ht
    have h := hU.dist_riemannianExp_eq_of_mem_ball Subset.rfl (hv t ht)
    rw [hexp t ht, hdist0 t ht] at h
    exact h.symm
  have hopposite : ∀ s ∈ Icc (-δ) δ, ∀ t ∈ Icc (-δ) δ,
      s ≤ 0 → 0 ≤ t → SameRay ℝ (v s) (-v t) := by
    intro s hs t ht hs0 ht0
    by_contra h
    have hlt := dist_riemannianExp_lt_norm_add_norm
      (hU.subset_expDomain (hv s hs)) (hU.subset_expDomain (hv t ht)) h
    rw [hexp s hs, hexp t ht, hdist s (hsub hs) t (hsub ht), hnorm s hs, hnorm t ht,
      abs_of_nonpos (by linarith), abs_of_nonpos hs0, abs_of_nonneg ht0] at hlt
    linarith
  have hleft : -δ ∈ Icc (-δ) δ := ⟨le_rfl, by linarith⟩
  have hright : δ ∈ Icc (-δ) δ := ⟨by linarith, le_rfl⟩
  have hvleft : v (-δ) = -v δ := by
    have heq := (hopposite (-δ) hleft δ hright (by linarith) hδ.le).norm_smul_eq
    rw [hnorm (-δ) hleft, norm_neg, hnorm δ hright, abs_neg, abs_of_pos hδ] at heq
    have h := congrArg (fun w : TangentSpace I (γ 0) ↦ δ⁻¹ • w) heq
    simpa only [smul_smul, inv_mul_cancel₀ hδ.ne', one_smul] using h.symm
  have hlinear : ∀ t ∈ Icc (-δ) δ, v t = t • (δ⁻¹ • v δ) := by
    intro t ht
    have heq : δ • v t = t • v δ := by
      by_cases ht0 : 0 ≤ t
      · have h := congrArg Neg.neg
          (hopposite (-δ) hleft t ht (by linarith) ht0).norm_smul_eq
        simpa only [hnorm (-δ) hleft, norm_neg, hnorm t ht, abs_neg, abs_of_pos hδ,
          abs_of_nonneg ht0, hvleft, smul_neg, neg_neg, hnorm δ hright] using h
      · have ht0' : t ≤ 0 := (not_le.mp ht0).le
        have h := (hopposite t ht δ hright ht0' hδ.le).norm_smul_eq
        simpa only [hnorm t ht, norm_neg, hnorm δ hright, abs_of_pos hδ,
          abs_of_nonpos ht0', neg_smul, smul_neg, neg_neg] using h.symm
    have h := congrArg (fun w : TangentSpace I (γ 0) ↦ δ⁻¹ • w) heq
    simpa only [smul_smul, inv_mul_cancel₀ hδ.ne', one_smul, mul_comm] using h
  refine ⟨δ⁻¹ • v δ, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hδ.le), hnorm δ hright,
      abs_of_pos hδ, inv_mul_cancel₀ hδ.ne']
  · filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδ] with t ht
    rw [← hexp t (Ioo_subset_Icc_self ht), hlinear t (Ioo_subset_Icc_self ht)]

/-- A curve with `dist (γ s) (γ t) = |s - t|` for all `s, t ∈ [-ε, ε]` is smooth at `0`. -/
theorem contMDiffAt_of_dist_eq_abs {γ : ℝ → M} {ε : ℝ} (hε : 0 < ε)
    (hdist : ∀ s ∈ Icc (-ε) ε, ∀ t ∈ Icc (-ε) ε, dist (γ s) (γ t) = |s - t|) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ 0 := by
  obtain ⟨v, -, heq⟩ := exists_eventuallyEq_riemannianExp_smul_of_dist_eq_abs (I := I) hε hdist
  exact (contMDiffAt_riemannianExp_smul_zero (γ 0) v).congr_of_eventuallyEq heq

/-- A curve with `dist (γ s) (γ t) = |s - t|` for all `s, t ∈ [-ε, ε]` has unit Riemannian speed
at `0`. -/
theorem norm_curveVelocity_eq_one_of_dist_eq_abs {γ : ℝ → M} {ε : ℝ} (hε : 0 < ε)
    (hdist : ∀ s ∈ Icc (-ε) ε, ∀ t ∈ Icc (-ε) ε, dist (γ s) (γ t) = |s - t|) :
    ‖curveVelocity I γ 0‖ = 1 := by
  obtain ⟨v, hv, heq⟩ := exists_eventuallyEq_riemannianExp_smul_of_dist_eq_abs (I := I) hε hdist
  rw [heq.norm_curveVelocity_eq (I := I), curveVelocity_riemannianExp_smul_zero]
  have hbase : riemannianExp I M (γ 0) ((0 : ℝ) • v) = γ 0 := by
    rw [zero_smul, riemannianExp_zero]
  exact (congrArg (fun x : M ↦ ‖(show TangentSpace I x from v)‖) hbase).trans hv

/-- **A curve realizing distances at constant speed is smooth.** If
`dist (γ s) (γ t) = |s - t| * c` for all `s, t` in `[t₀ - ε, t₀ + ε]`, with `c ≥ 0`, then `γ` is
smooth at `t₀`. -/
theorem contMDiffAt_of_dist_eq_mul_abs {γ : ℝ → M} {ε c t₀ : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    (hdist : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
      dist (γ s) (γ t) = |s - t| * c) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t₀ := by
  have ht₀ : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  rcases hc.eq_or_lt with rfl | hc
  · refine (contMDiffAt_const (c := γ t₀)).congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds (by linarith : t₀ - ε < t₀) (by linarith : t₀ < t₀ + ε)]
      with t ht
    rw [← dist_eq_zero, hdist t ht t₀ ht₀, mul_zero]
  set η : ℝ → M := fun s ↦ γ (t₀ + s / c)
  have hb : ∀ s ∈ Icc (-(ε * c)) (ε * c), t₀ + s / c ∈ Icc (t₀ - ε) (t₀ + ε) := by
    intro s hs
    constructor
    · have h : -ε ≤ s / c := (le_div_iff₀ hc).mpr (by nlinarith [hs.1])
      linarith
    · have h : s / c ≤ ε := (div_le_iff₀ hc).mpr hs.2
      linarith
  have hη : ∀ s ∈ Icc (-(ε * c)) (ε * c), ∀ t ∈ Icc (-(ε * c)) (ε * c),
      dist (η s) (η t) = |s - t| := by
    intro s hs t ht
    rw [hdist _ (hb s hs) _ (hb t ht), show t₀ + s / c - (t₀ + t / c) = (s - t) / c by ring,
      abs_div, abs_of_pos hc, div_mul_cancel₀ _ hc.ne']
  have hηsmooth : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ η (c * (t₀ - t₀)) := by
    simpa only [sub_self, mul_zero] using contMDiffAt_of_dist_eq_abs (mul_pos hε hc) hη
  have hψ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ c * (t - t₀)) t₀ :=
    contMDiffAt_iff_contDiffAt.mpr (by fun_prop)
  have heq : (fun t : ℝ ↦ η (c * (t - t₀))) = γ := by
    funext t
    simp only [η, mul_div_cancel_left₀ (t - t₀) hc.ne', add_sub_cancel]
  simpa only [Function.comp_def, heq] using hηsmooth.comp t₀ hψ

/-- **Metric geodesic segments are smooth.** A metric geodesic segment from `p` to `q` is smooth
at every interior parameter `t ∈ (0, 1)`. -/
theorem _root_.TauCeti.IsGeodesicSegment.contMDiffAt {γ : ℝ → M} {q : M}
    (hγ : IsGeodesicSegment γ p q) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t := by
  set ε := min (t / 2) ((1 - t) / 2)
  have hε : 0 < ε := lt_min (half_pos ht.1) (half_pos (sub_pos.mpr ht.2))
  have hsub : Icc (t - ε) (t + ε) ⊆ Icc (0 : ℝ) 1 := by
    intro s hs
    have hleft : ε ≤ t / 2 := min_le_left _ _
    have hright : ε ≤ (1 - t) / 2 := min_le_right _ _
    constructor <;> linarith [hs.1, hs.2]
  exact contMDiffAt_of_dist_eq_mul_abs hε dist_nonneg
    fun s hs u hu ↦ hγ.dist_eq s (hsub hs) u (hsub hu)

end TauCeti.Manifold
