/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.WithMetric
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness

/-!
# A metric dominating a complete metric is geodesically complete

Let `M` be a Riemannian manifold which is complete for its Riemannian distance, and let `g` be a
second Riemannian metric on `M` dominating the given one: `|v|² ≤ g(v, v)` for every tangent
vector `v`. Then `(M, g)` is geodesically complete.

Indeed, a maximal geodesic `γ` of `g` has constant `g`-speed `|γ'(0)|_g`, so its length for the
given metric between two times `s ≤ t` is at most `|γ'(0)|_g (t - s)`. Hence `γ` is Lipschitz on
its maximal interval for the given Riemannian distance. If that interval had a finite endpoint,
the image of `γ` near it would be totally bounded, hence relatively compact by completeness,
contradicting the escape lemma for geodesics of `g`.

The second metric is carried by the copy `TauCeti.WithMetric g` of `M`, so that the two metric
instances never live on the same type. No distance is needed on the copy.

## Main results

* `TauCeti.WithMetric.norm_mfderiv_ofWithMetric_le`: if `g` dominates the given metric, the
  identification of the copy with `M` does not increase the norms of tangent vectors.
* `TauCeti.WithMetric.lipschitzOnWith_ofWithMetric_maximalGeodesic`: a maximal geodesic of `g`
  is Lipschitz for the given Riemannian distance, with its `g`-speed as constant.
* `TauCeti.WithMetric.isGeodesicallyCompleteAt_of_sq_norm_le`: **a metric dominating a complete
  Riemannian metric is geodesically complete.**

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8, and Ch. 7, §3,
  Lemma 3.3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 6.
-/

public section

open Bundle Filter Manifold MeasureTheory Set TauCeti.Manifold
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

omit [I.Boundaryless] in
/-- If `g` dominates the given metric of `M`, the differential of the identification
`ofWithMetric` of the copy carrying `g` with `M` does not increase norms. -/
theorem norm_mfderiv_ofWithMetric_le (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ g.inner x v v)
    (x : WithMetric g) (v : TangentSpace I x) : ‖mfderiv I I ofWithMetric x v‖ ≤ ‖v‖ := by
  have h := hg x.ofWithMetric (mfderiv I I ofWithMetric x v)
  rw [← inner_def, real_inner_self_eq_norm_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

instance : T2Space (WithMetric g) :=
  (homeomorph g).isEmbedding.t2Space

variable [IsRiemannianManifold I M]

/-- **A maximal geodesic of a dominating metric is Lipschitz for the given distance.** If `g`
dominates the given metric of `M`, a maximal geodesic of `g`, read in `M`, is Lipschitz on its
maximal interval for the Riemannian distance of `M`, with its `g`-speed as constant. -/
theorem lipschitzOnWith_ofWithMetric_maximalGeodesic
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ g.inner x v v) (p : WithMetric g)
    (v : TangentSpace I p) :
    LipschitzOnWith ‖v‖₊ (ofWithMetric ∘ maximalGeodesic I (WithMetric g) p v)
      (geodesicInterval I (WithMetric g) p v) := by
  set γ := maximalGeodesic I (WithMetric g) p v
  have hγ := (isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := WithMetric g) p
    v).isGeodesicCurveOn
  have key : ∀ s ∈ geodesicInterval I (WithMetric g) p v,
      ∀ t ∈ geodesicInterval I (WithMetric g) p v, s ≤ t →
      edist ((ofWithMetric ∘ γ) s) ((ofWithMetric ∘ γ) t) ≤ ‖v‖₊ * edist s t := by
    intro s hs t ht hst
    have hst' : Icc s t ⊆ geodesicInterval I (WithMetric g) p v :=
      ordConnected_geodesicInterval.out hs ht
    have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (ofWithMetric ∘ γ) (Icc s t) :=
      contMDiff_ofWithMetric.comp_contMDiffOn ((hγ.contMDiffOn.mono hst').of_le (by norm_num))
    have hlen : pathELength I (ofWithMetric ∘ γ) s t ≤ pathELength I γ s t := by
      rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc]
      refine setLIntegral_mono' measurableSet_Icc fun τ hτ ↦ ?_
      have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ τ :=
        (hγ.contMDiffOn.contMDiffAt (isOpen_geodesicInterval.mem_nhds (hst' hτ))).mdifferentiableAt
          (by norm_num)
      rw [mfderiv_comp τ (hasMFDerivAt_ofWithMetric _).mdifferentiableAt hdiff,
        ContinuousLinearMap.comp_apply, ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_mfderiv_ofWithMetric_le hg _ _)
    calc edist ((ofWithMetric ∘ γ) s) ((ofWithMetric ∘ γ) t)
        ≤ pathELength I (ofWithMetric ∘ γ) s t :=
          IsRiemannianManifold.edist_le_pathELength hsm hst
      _ ≤ pathELength I γ s t := hlen
      _ = ‖v‖ₑ * ENNReal.ofReal (t - s) := by
        have hv : ‖curveVelocityWithin I γ (geodesicInterval I (WithMetric g) p v) 0‖ = ‖v‖ :=
          congrArg (fun z : TangentBundle I (WithMetric g) ↦ ‖z.2‖)
            (isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := WithMetric g) p v).initial_eq
        rw [hγ.pathELength_eq isPreconnected_geodesicInterval hs ht zero_mem_geodesicInterval,
          ← ofReal_norm, ← ofReal_norm, hv]
      _ = ‖v‖₊ * edist s t := by
        rw [edist_dist, Real.dist_eq, abs_sub_comm,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s), enorm_eq_nnnorm]
  intro s hs t ht
  rcases le_total s t with h | h
  · exact key s hs t ht h
  · rw [edist_comm, edist_comm s t]
    exact key t ht s hs h

/-- Over a bounded subinterval of its maximal interval, a maximal geodesic of a metric dominating
a complete metric stays in a compact set. -/
private theorem exists_isCompact_image_maximalGeodesic_subset [CompleteSpace M]
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ g.inner x v v) {a b : ℝ} (p : WithMetric g)
    (v : TangentSpace I p) (hab : Ioo a b ⊆ geodesicInterval I (WithMetric g) p v) :
    ∃ K : Set (WithMetric g), IsCompact K ∧
      maximalGeodesic I (WithMetric g) p v '' Ioo a b ⊆ K := by
  set c := ofWithMetric ∘ maximalGeodesic I (WithMetric g) p v
  have htb : TotallyBounded (c '' Ioo a b) := by
    have huniv : TotallyBounded (univ : Set (Ioo a b)) := by
      simpa using totallyBounded_preimage
        (f := (Subtype.val : Ioo a b → ℝ)) isUniformEmbedding_subtype_val.isUniformInducing
        ((isCompact_Icc (a := a) (b := b)).totallyBounded.subset Ioo_subset_Icc_self)
    have hlip : LipschitzWith ‖v‖₊ ((Ioo a b).domRestrict c) :=
      ((lipschitzOnWith_ofWithMetric_maximalGeodesic hg p v).mono hab).to_restrict
    simpa using huniv.image hlip.uniformContinuous
  have hK : IsCompact (closure (c '' Ioo a b)) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨htb.closure, isClosed_closure.isComplete⟩
  refine ⟨toWithMetric g '' closure (c '' Ioo a b), hK.image continuous_toWithMetric, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨c t, subset_closure (mem_image_of_mem _ ht), rfl⟩

/-- **A metric dominating a complete Riemannian metric is geodesically complete.** If `M` is
complete for its Riemannian distance and `g` is a Riemannian metric on `M` with
`|v|² ≤ g(v, v)` for every tangent vector `v`, then every maximal geodesic of `g` is defined for
all time. -/
theorem isGeodesicallyCompleteAt_of_sq_norm_le [CompleteSpace M]
    (hg : ∀ x (v : TangentSpace I x), ‖v‖ ^ 2 ≤ g.inner x v v) (p : WithMetric g) :
    IsGeodesicallyCompleteAt I (WithMetric g) p := by
  rw [← expDomain_eq_univ_iff]
  apply eq_univ_of_forall
  intro v
  rw [mem_expDomain_iff]
  have h0 : (0 : ℝ) ∈ geodesicInterval I (WithMetric g) p v := zero_mem_geodesicInterval
  have hup : ¬ BddAbove (geodesicInterval I (WithMetric g) p v) := by
    intro hbdd
    have hlub := isLUB_csSup ⟨0, h0⟩ hbdd
    obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_geodesicInterval_of_isLUB hlub
    obtain ⟨K, hK, hsubK⟩ := exists_isCompact_image_maximalGeodesic_subset hg p v hsub
    obtain ⟨t, ht1, ht2⟩ := ((eventually_notMem_nhdsLT_maximalGeodesic hlub hK).and
        (Filter.eventually_iff.2 (Ioo_mem_nhdsLT (ha.trans hb0)))).exists
    exact ht1 (hsubK (mem_image_of_mem _ ht2))
  have hlow : ¬ BddBelow (geodesicInterval I (WithMetric g) p v) := by
    intro hbdd
    have hglb := isGLB_csInf ⟨0, h0⟩ hbdd
    obtain ⟨b, hb, ha0, hsub⟩ := exists_Ioo_subset_geodesicInterval_of_isGLB hglb
    obtain ⟨K, hK, hsubK⟩ := exists_isCompact_image_maximalGeodesic_subset hg p v hsub
    obtain ⟨t, ht1, ht2⟩ := ((eventually_notMem_nhdsGT_maximalGeodesic hglb hK).and
        (Filter.eventually_iff.2 (Ioo_mem_nhdsGT (ha0.trans hb)))).exists
    exact ht1 (hsubK (mem_image_of_mem _ ht2))
  have hinterval : geodesicInterval I (WithMetric g) p v = univ := by
    rw [← maximalIntegralCurveInterval_geodesicSpray] at hup hlow ⊢
    exact maximalIntegralCurveInterval_eq_univ_of_not_bddAbove_not_bddBelow hup hlow
  rw [hinterval]
  exact mem_univ 1

end TauCeti.WithMetric

end
