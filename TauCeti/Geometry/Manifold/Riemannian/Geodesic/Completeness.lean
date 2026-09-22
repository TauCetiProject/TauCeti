/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Topology.VectorBundle.Riemannian

/-!
# Metric completeness gives geodesic completeness

A maximal geodesic travels at constant speed, so on its maximal interval it is a Lipschitz curve
for the Riemannian distance.  If that interval had a finite endpoint, the image of the curve would
therefore be totally bounded, hence relatively compact once the manifold is metrically complete;
the velocity lift would then stay in the part of the tangent bundle consisting of the vectors of
norm at most the speed over that compact set, which is compact.  An integral curve of the geodesic
spray cannot remain in a compact set as it approaches a finite endpoint of its maximal interval,
so no such endpoint exists and every geodesic is defined for all time.

The step about velocities is not implicit in constant speed: that bounds the velocity in the
fibrewise Riemannian norm, and it is the compactness of the norm-bounded part of a Riemannian
bundle over a compact set which converts such a bound into relative compactness in the total
space.

## Main results

* `TauCeti.Manifold.norm_curveVelocityWithin_maximalGeodesic` and
  `TauCeti.Manifold.pathELength_maximalGeodesic`: the maximal geodesic from `(p, v)` has speed
  `‖v‖` throughout its maximal interval, so its length over a parameter interval is `‖v‖` times
  the elapsed time.
* `TauCeti.Manifold.lipschitzOnWith_maximalGeodesic`: consequently it is `‖v‖`-Lipschitz there.
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
  [T2Space (TangentBundle I M)]

variable {p : M} {v : TangentSpace I p}

/-! ### Speed, length and the Lipschitz bound -/

/-- **A maximal geodesic has constant speed `‖v‖`.**  At every parameter of its maximal interval,
the maximal geodesic from `p` with initial velocity `v` has velocity of norm `‖v‖`. -/
theorem norm_curveVelocityWithin_maximalGeodesic {t : ℝ} (ht : t ∈ geodesicInterval I M p v) :
    ‖curveVelocityWithin I (maximalGeodesic I M p v) (geodesicInterval I M p v) t‖ = ‖v‖ := by
  rw [curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds ht),
    norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    inner_curveVelocity_maximalGeodesic_self ht]

/-- **The length of a maximal geodesic is its speed times the elapsed time.**  Between two
parameters of its maximal interval, the Riemannian length of the maximal geodesic from `p` with
initial velocity `v` is `‖v‖ * (t - s)`. -/
theorem pathELength_maximalGeodesic {s t : ℝ} (hs : s ∈ geodesicInterval I M p v)
    (ht : t ∈ geodesicInterval I M p v) :
    pathELength I (maximalGeodesic I M p v) s t = ‖v‖ₑ * ENNReal.ofReal (t - s) := by
  have hsub : Ioo s t ⊆ geodesicInterval I M p v :=
    Ioo_subset_Icc_self.trans (ordConnected_geodesicInterval.out hs ht)
  have key : ∀ u ∈ Ioo s t,
      ‖mfderiv 𝓘(ℝ, ℝ) I (maximalGeodesic I M p v) u 1‖ₑ = ‖v‖ₑ := by
    intro u hu
    have hmem := hsub hu
    have hvel : mfderiv 𝓘(ℝ, ℝ) I (maximalGeodesic I M p v) u 1 =
        curveVelocityWithin I (maximalGeodesic I M p v) (geodesicInterval I M p v) u :=
      ((curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds hmem)).trans
        (curveVelocity_apply (I := I))).symm
    rw [hvel, ← ofReal_norm, ← ofReal_norm, norm_curveVelocityWithin_maximalGeodesic hmem]
  rw [pathELength_eq_lintegral_mfderiv_Ioo, setLIntegral_congr_fun measurableSet_Ioo key,
    setLIntegral_const, Real.volume_Ioo]

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

/-! ### Completeness -/

variable [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- Over a bounded subinterval of its maximal interval, the velocity lift of a maximal geodesic in
a complete Riemannian manifold stays in a compact subset of the tangent bundle. -/
private theorem exists_isCompact_forall_mem_maximalIntegralCurve [CompleteSpace M] {a b : ℝ}
    (p : M) (v : TangentSpace I p) (hab : Ioo a b ⊆ geodesicInterval I M p v) :
    ∃ K : Set (TangentBundle I M), IsCompact K ∧
      ∀ t ∈ Ioo a b, maximalIntegralCurve (geodesicSpray I M) (TotalSpace.mk' E p v) t ∈ K := by
  have htb : TotallyBounded (maximalGeodesic I M p v '' Ioo a b) := by
    have huniv : TotallyBounded (univ : Set (Ioo a b)) := by
      simpa using totallyBounded_preimage
        (f := (Subtype.val : Ioo a b → ℝ)) isUniformEmbedding_subtype_val.isUniformInducing
        ((isCompact_Icc (a := a) (b := b)).totallyBounded.subset Ioo_subset_Icc_self)
    have hlip : LipschitzWith ‖v‖₊ ((Ioo a b).domRestrict (maximalGeodesic I M p v)) :=
      ((lipschitzOnWith_maximalGeodesic (p := p) (v := v)).mono hab).to_restrict
    simpa using huniv.image hlip.uniformContinuous
  have hbase : IsCompact (closure (maximalGeodesic I M p v '' Ioo a b)) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨htb.closure, isClosed_closure.isComplete⟩
  have hz : IsMIntegralCurveOn
      (maximalIntegralCurve (geodesicSpray I M) (TotalSpace.mk' E p v)) (geodesicSpray I M)
      (geodesicInterval I M p v) := by
    rw [← maximalIntegralCurveInterval_geodesicSpray (I := I) (M := M) p v]
    exact isMIntegralCurveOn_maximalIntegralCurve contMDiff_one_geodesicSpray
  refine ⟨{z : TangentBundle I M |
      z.proj ∈ closure (maximalGeodesic I M p v '' Ioo a b) ∧ ‖z.2‖ ≤ ‖v‖},
    hbase.norm_le_bundle ‖v‖, fun t ht ↦ ?_⟩
  have hproj : (fun r ↦ (maximalIntegralCurve (geodesicSpray I M) (TotalSpace.mk' E p v) r).proj)
      = maximalGeodesic I M p v := funext fun r ↦ (maximalGeodesic_def p v r).symm
  have hlift : maximalIntegralCurve (geodesicSpray I M) (TotalSpace.mk' E p v) t =
      curveVelocityLiftWithin I (maximalGeodesic I M p v) (geodesicInterval I M p v) t := by
    rw [← hproj]
    exact eq_curveVelocityLiftWithin_of_isMIntegralCurveOn
      (isOpen_geodesicInterval.uniqueDiffOn t (hab ht)) hz (hab ht)
  refine ⟨?_, le_of_eq ?_⟩
  · rw [← maximalGeodesic_def]
    exact subset_closure (mem_image_of_mem _ ht)
  calc ‖(maximalIntegralCurve (geodesicSpray I M) (TotalSpace.mk' E p v) t).2‖
      = ‖(TotalSpace.mk' E (maximalGeodesic I M p v t)
            (curveVelocityWithin I (maximalGeodesic I M p v)
              (geodesicInterval I M p v) t)).2‖ :=
        congrArg (fun z : TangentBundle I M ↦ ‖z.2‖)
          (hlift.trans (curveVelocityLiftWithin_apply _ _ _))
    _ = ‖v‖ := norm_curveVelocityWithin_maximalGeodesic (hab ht)

/-- **Metric completeness implies geodesic completeness.**  In a Riemannian manifold which is
complete for its Riemannian distance, every maximal geodesic is defined for all time.  This is the
implication from assertion (c) to assertion (d) of do Carmo's Hopf–Rinow theorem. -/
theorem isGeodesicallyCompleteAt_of_completeSpace [CompleteSpace M] (p : M) :
    IsGeodesicallyCompleteAt I M p := by
  rw [← expDomain_eq_univ_iff]
  apply eq_univ_of_forall
  intro v
  rw [mem_expDomain_iff]
  set x₀ : TangentBundle I M := TotalSpace.mk' E p v
  have hJ : maximalIntegralCurveInterval (geodesicSpray I M) x₀ = geodesicInterval I M p v :=
    maximalIntegralCurveInterval_geodesicSpray p v
  have h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval (geodesicSpray I M) x₀ := by
    rw [hJ]; exact zero_mem_geodesicInterval
  have hspray := contMDiff_one_geodesicSpray (I := I) (M := M)
  have hup : ¬ BddAbove (maximalIntegralCurveInterval (geodesicSpray I M) x₀) := by
    intro hbdd
    have hlub := isLUB_csSup ⟨0, h0⟩ hbdd
    obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB h0 hlub
    obtain ⟨K, hK, hmem⟩ :=
      exists_isCompact_forall_mem_maximalIntegralCurve I M p v
        (fun u hu ↦ hJ ▸ hsub hu)
    obtain ⟨t, ht1, ht2⟩ :=
      ((eventually_notMem_nhdsLT_maximalIntegralCurve hspray h0 hlub hK).and
        (Filter.eventually_iff.2 (Ioo_mem_nhdsLT (ha.trans hb0)))).exists
    exact ht1 (hmem t ht2)
  have hlow : ¬ BddBelow (maximalIntegralCurveInterval (geodesicSpray I M) x₀) := by
    intro hbdd
    have hglb := isGLB_csInf ⟨0, h0⟩ hbdd
    obtain ⟨b, hb, ha0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB h0 hglb
    obtain ⟨K, hK, hmem⟩ :=
      exists_isCompact_forall_mem_maximalIntegralCurve I M p v
        (fun u hu ↦ hJ ▸ hsub hu)
    obtain ⟨t, ht1, ht2⟩ :=
      ((eventually_notMem_nhdsGT_maximalIntegralCurve hspray h0 hglb hK).and
        (Filter.eventually_iff.2 (Ioo_mem_nhdsGT (ha0.trans hb)))).exists
    exact ht1 (hmem t ht2)
  have hinterval : geodesicInterval I M p v = univ := by
    rw [← hJ]
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
