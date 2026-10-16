/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Length
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Escape

/-!
# Metric completeness gives geodesic completeness

A maximal geodesic travels at constant speed, so on its maximal interval it is a Lipschitz curve
for the Riemannian distance.  If that interval had a finite endpoint, the image of the curve would
therefore be totally bounded, hence relatively compact once the manifold is metrically complete.
This contradicts the escape lemma for geodesics, `eventually_notMem_nhdsLT_maximalGeodesic`, so no
such endpoint exists and every geodesic is defined for all time.  The same Lipschitz bound,
read between the parameters `0` and `1`, says that the exponential map does not increase the
distance from the base point: `dist p (exp_p v) ≤ ‖v‖`.

## Main results

* `TauCeti.Manifold.lipschitzOnWith_maximalGeodesic`: consequently it is `‖v‖`-Lipschitz there.
* `TauCeti.Manifold.edist_riemannianExp_le` and `TauCeti.Manifold.dist_riemannianExp_le`: the
  distance from `p` to `exp_p v` is at most `‖v‖`.
* `TauCeti.Manifold.isGeodesicallyCompleteAt_of_completeSpace`: a complete Riemannian manifold is
  geodesically complete at every point, with
  `TauCeti.Manifold.isGeodesicCurveOnFrom_maximalGeodesic_univ` the resulting all-time geodesic
  and `TauCeti.Manifold.expDomain_eq_univ_of_completeSpace` the resulting everywhere-defined
  exponential map.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8, the implication
  from assertion (c), metric completeness, to assertion (d), geodesic completeness.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6, Thm. 6.19.
-/

public section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable {p : M} {v : TangentSpace I p}

/-! ### Lipschitz bound -/

variable [IsRiemannianManifold I M]

/-- **A maximal geodesic is Lipschitz on its maximal interval**, with its constant speed as
Lipschitz constant. -/
theorem lipschitzOnWith_maximalGeodesic :
    LipschitzOnWith ‖v‖₊ (maximalGeodesic I M p v) (geodesicInterval I M p v) := by
  have key : ∀ s ∈ geodesicInterval I M p v, ∀ t ∈ geodesicInterval I M p v, s ≤ t →
      edist (maximalGeodesic I M p v s) (maximalGeodesic I M p v t) ≤ ‖v‖₊ * edist s t := by
    intro s hs t ht hst
    have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (maximalGeodesic I M p v) (Icc s t) :=
      ((isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p
        v).isGeodesicCurveOn.contMDiffOn.mono
          (ordConnected_geodesicInterval.out hs ht)).of_le (by norm_num)
    calc edist (maximalGeodesic I M p v s) (maximalGeodesic I M p v t)
        ≤ pathELength I (maximalGeodesic I M p v) s t :=
          IsRiemannianManifold.edist_le_pathELength hsm hst
      _ = ‖v‖ₑ * ENNReal.ofReal (t - s) := pathELength_maximalGeodesic hs ht
      _ = ‖v‖₊ * edist s t := by
        rw [edist_dist, Real.dist_eq, abs_sub_comm,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s), enorm_eq_nnnorm]
  intro s hs t ht
  rcases le_total s t with h | h
  · exact key s hs t ht h
  · rw [edist_comm, edist_comm s t]
    exact key t ht s hs h

/-! ### The distance bound for the exponential map -/

/-- **The exponential map does not increase the distance from the base point.**  The extended
distance from `p` to `exp_p v` is at most `‖v‖ₑ`, for every tangent vector `v` at `p`. -/
theorem edist_riemannianExp_le (p : M) (v : TangentSpace I p) :
    edist p (riemannianExp I M p v) ≤ ‖v‖ₑ := by
  by_cases hv : v ∈ expDomain I M p
  · have h := lipschitzOnWith_maximalGeodesic (I := I) (M := M) (p := p) (v := v)
      zero_mem_geodesicInterval (mem_expDomain_iff.1 hv)
    rw [(isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v).base_eq] at h
    have h01 : edist (0 : ℝ) 1 = 1 := by simp [edist_dist, Real.dist_eq]
    simpa [riemannianExp_def, enorm_eq_nnnorm, h01] using h
  · simp [hv]

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- The distance from `p` to `exp_p v` is at most `‖v‖`; see `edist_riemannianExp_le`. -/
theorem dist_riemannianExp_le (p : M) (v : TangentSpace I p) :
    dist p (riemannianExp I M p v) ≤ ‖v‖ := by
  have h := edist_riemannianExp_le (I := I) (M := M) p v
  rwa [← ofReal_norm, edist_le_ofReal (norm_nonneg v)] at h

end Metric

/-! ### Completeness -/

variable (I M) in
/-- Over a bounded subinterval of its maximal interval, the image of a maximal geodesic in a
complete Riemannian manifold has compact closure. -/
private theorem isCompact_closure_image_maximalGeodesic [CompleteSpace M] {a b : ℝ}
    (p : M) (v : TangentSpace I p) (hab : Ioo a b ⊆ geodesicInterval I M p v) :
    IsCompact (closure (maximalGeodesic I M p v '' Ioo a b)) := by
  have htb : TotallyBounded (maximalGeodesic I M p v '' Ioo a b) := by
    have huniv : TotallyBounded (univ : Set (Ioo a b)) := by
      simpa using totallyBounded_preimage
        (f := (Subtype.val : Ioo a b → ℝ)) isUniformEmbedding_subtype_val.isUniformInducing
        ((isCompact_Icc (a := a) (b := b)).totallyBounded.subset Ioo_subset_Icc_self)
    have hlip : LipschitzWith ‖v‖₊ ((Ioo a b).domRestrict (maximalGeodesic I M p v)) :=
      ((lipschitzOnWith_maximalGeodesic (p := p) (v := v)).mono hab).to_restrict
    simpa using huniv.image hlip.uniformContinuous
  exact isCompact_iff_totallyBounded_isComplete.2 ⟨htb.closure, isClosed_closure.isComplete⟩

/-- **Metric completeness implies geodesic completeness.**  In a Riemannian manifold which is
complete for its Riemannian distance, every maximal geodesic is defined for all time.  This is the
implication from assertion (c) to assertion (d) of do Carmo's Hopf–Rinow theorem. -/
theorem isGeodesicallyCompleteAt_of_completeSpace [CompleteSpace M] (p : M) :
    IsGeodesicallyCompleteAt I M p := by
  rw [← expDomain_eq_univ_iff]
  apply eq_univ_of_forall
  intro v
  rw [mem_expDomain_iff]
  have h0 : (0 : ℝ) ∈ geodesicInterval I M p v := zero_mem_geodesicInterval
  have hup : ¬ BddAbove (geodesicInterval I M p v) := by
    intro hbdd
    have hlub := isLUB_csSup ⟨0, h0⟩ hbdd
    obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_geodesicInterval_of_isLUB hlub
    obtain ⟨t, ht1, ht2⟩ := ((eventually_notMem_nhdsLT_maximalGeodesic hlub
      (isCompact_closure_image_maximalGeodesic I M p v hsub)).and
        (Filter.eventually_iff.2 (Ioo_mem_nhdsLT (ha.trans hb0)))).exists
    exact ht1 (subset_closure (mem_image_of_mem _ ht2))
  have hlow : ¬ BddBelow (geodesicInterval I M p v) := by
    intro hbdd
    have hglb := isGLB_csInf ⟨0, h0⟩ hbdd
    obtain ⟨b, hb, ha0, hsub⟩ := exists_Ioo_subset_geodesicInterval_of_isGLB hglb
    obtain ⟨t, ht1, ht2⟩ := ((eventually_notMem_nhdsGT_maximalGeodesic hglb
      (isCompact_closure_image_maximalGeodesic I M p v hsub)).and
        (Filter.eventually_iff.2 (Ioo_mem_nhdsGT (ha0.trans hb)))).exists
    exact ht1 (subset_closure (mem_image_of_mem _ ht2))
  have hinterval : geodesicInterval I M p v = univ := by
    rw [← maximalIntegralCurveInterval_geodesicSpray] at h0 hup hlow ⊢
    exact maximalIntegralCurveInterval_eq_univ_of_not_bddAbove_not_bddBelow h0 hup hlow
  rw [hinterval]
  exact mem_univ 1

/-- In a complete Riemannian manifold the maximal geodesic with initial data `(p, v)` is a
geodesic on the whole real line. -/
theorem isGeodesicCurveOnFrom_maximalGeodesic_univ [CompleteSpace M] (p : M)
    (v : TangentSpace I p) :
    IsGeodesicCurveOnFrom I (maximalGeodesic I M p v) univ p v := by
  have h := isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v
  have hdomain : expDomain I M p = univ :=
    expDomain_eq_univ_iff.2 (isGeodesicallyCompleteAt_of_completeSpace p)
  have hinterval : geodesicInterval I M p v = univ := by
    rw [geodesicInterval_eq_preimage_expDomain, hdomain, preimage_univ]
  rwa [hinterval] at h

/-- **The exponential map of a complete Riemannian manifold is everywhere defined**, its domain
being the whole tangent space at every point. -/
theorem expDomain_eq_univ_of_completeSpace [CompleteSpace M] (p : M) : expDomain I M p = univ :=
  expDomain_eq_univ_iff.2 (isGeodesicallyCompleteAt_of_completeSpace p)

end TauCeti.Manifold

end
