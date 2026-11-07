/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Flow
public import TauCeti.Geometry.Manifold.IntegralCurve.SmoothFlow
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory

/-!
# The smooth geodesic flow

The geodesic spray of a smooth finite-dimensional Riemannian manifold has a family of integral
curves depending smoothly on the initial tangent vector and on time.  Projecting each spray
trajectory to the manifold gives the geodesic with that initial position and velocity, on one
common open time neighbourhood for all nearby initial data.

Globally, the maximal integral curves of the spray form the *geodesic flow* on the tangent bundle.
Its natural domain is the set of pairs `(z, t)` of a tangent vector `z ∈ T_x M` and a time `t` in
the maximal geodesic interval of `z`; this domain is open, the flow is jointly smooth on it, and so
is its base projection, the maximal geodesic regarded as a function of its initial data and time.
This is the smooth-dependence input for smoothness of the exponential map on its natural domain.

## Main results

* `TauCeti.Manifold.exists_contMDiffAt_localGeodesicFlow`: local spray trajectories form a
  jointly smooth family, and their base projections have the prescribed geodesic initial data.
* `TauCeti.Manifold.maximalIntegralCurveFlowDomain_geodesicSpray`: the domain of the
  geodesic flow consists of the pairs `(z, t)` with `t` in the maximal geodesic interval of `z`.
* `TauCeti.Manifold.isOpen_setOfPred_mem_geodesicInterval`: this domain is open in `TM × ℝ`.
* `TauCeti.Manifold.contMDiffOn_maximalIntegralCurve_geodesicSpray`: the maximal geodesic flow is
  smooth on its domain.
* `TauCeti.Manifold.contMDiffOn_maximalGeodesic`: maximal geodesics depend smoothly on their
  initial data and on time.
* `TauCeti.Manifold.contMDiffAt_maximalGeodesic_comp`: a curve of initial states gives a
  jointly Cⁿ geodesic variation at each point of the central maximal interval.
* `TangentBundle.exists_contMDiffOn_maximalGeodesic_of_isCompact`: nearby initial states
  share a smooth flow domain around any compact subset of a maximal geodesic interval.
* `TauCeti.Manifold.exists_contMDiffOn_maximalGeodesic_comp_of_isCompact`: a curve of initial
  states gives a geodesic variation on a common domain around a compact time subset.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapter 5.
-/

public section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The smooth local geodesic flow.**  Near every initial state `z : TM`, the integral curves
of the geodesic spray exist on a common open time neighbourhood and depend smoothly on the initial
state and time at `(z, 0)`.  Their base projections are geodesics with the position and velocity
encoded by each nearby initial state.
-/
theorem exists_contMDiffAt_localGeodesicFlow (z : TangentBundle I M) :
    ∃ U ∈ nhds z, ∃ s ∈ nhds (0 : ℝ), IsOpen s ∧
      ∃ Φ : TangentBundle I M → ℝ → TangentBundle I M,
        CMDiffAt ∞ (fun p : TangentBundle I M × ℝ ↦ Φ p.1 p.2) (z, 0) ∧
          ∀ w ∈ U, Φ w 0 = w ∧
            IsMIntegralCurveOn (Φ w) (geodesicSpray I M) s ∧
            (∀ t ∈ s, ∀ u, Φ w (t + u) = Φ (Φ w t) u) ∧
            IsGeodesicCurveOnFrom I (fun t ↦ (Φ w t).proj) s w.proj w.2 := by
  obtain ⟨U, hU, s, hs, hsopen, Φ, hΦsmooth, hΦ⟩ :=
    exists_contMDiffAt_localFlow (I := I.tangent) (V := univ)
      (v := geodesicSpray I M) z contMDiff_infty_geodesicSpray.contMDiffOn univ_mem
  refine ⟨U, hU, s, hs, hsopen, Φ, hΦsmooth, ?_⟩
  intro w hw
  obtain ⟨hΦ0, hΦcurve, hΦadd⟩ := hΦ w hw
  refine ⟨hΦ0, hΦcurve, hΦadd, ?_⟩
  exact hΦcurve.isGeodesicCurveOnFrom_proj hsopen.uniqueDiffOn (mem_of_mem_nhds hs) hΦ0

/-! ### The maximal geodesic flow -/

/-- The domain of the maximal flow of the geodesic spray consists of the pairs `(z, t)` for which
`t` lies in the maximal geodesic interval of the initial data encoded by `z`. -/
theorem maximalIntegralCurveFlowDomain_geodesicSpray :
    maximalIntegralCurveFlowDomain (geodesicSpray I M) =
      {q : TangentBundle I M × ℝ | q.2 ∈ geodesicInterval I M q.1.proj q.1.2} := by
  ext ⟨z, t⟩
  rw [mem_maximalIntegralCurveFlowDomain]
  simp only [Set.mem_ofPred_eq]
  rw [← maximalIntegralCurveInterval_geodesicSpray]

variable [T2Space M]

/-- **The domain of the geodesic flow is open**: the pairs `(z, t)` of a tangent vector and a
time of its maximal geodesic interval form an open subset of `TM × ℝ`. -/
theorem isOpen_setOfPred_mem_geodesicInterval :
    IsOpen {q : TangentBundle I M × ℝ | q.2 ∈ geodesicInterval I M q.1.proj q.1.2} := by
  rw [← maximalIntegralCurveFlowDomain_geodesicSpray]
  exact isOpen_maximalIntegralCurveFlowDomain contMDiff_one_geodesicSpray

/-- **The maximal geodesic flow is smooth.**  The maximal integral curves of the geodesic spray
depend smoothly, jointly in the initial tangent vector and in time, on the domain of the
geodesic flow. -/
theorem contMDiffOn_maximalIntegralCurve_geodesicSpray :
    ContMDiffOn (I.tangent.prod 𝓘(ℝ, ℝ)) I.tangent ∞
      (fun q : TangentBundle I M × ℝ ↦ maximalIntegralCurve (geodesicSpray I M) q.1 q.2)
      {q | q.2 ∈ geodesicInterval I M q.1.proj q.1.2} := by
  rw [← maximalIntegralCurveFlowDomain_geodesicSpray]
  exact contMDiffOn_maximalIntegralCurve (I := I.tangent) (n := (⊤ : ℕ∞)) (by simp)
    contMDiff_infty_geodesicSpray

/-- **Smooth dependence of maximal geodesics on initial data.**  The maximal geodesic with initial
point `z.proj` and initial velocity `z.2`, evaluated at time `t`, is a smooth function of
`(z, t)` on the domain of the geodesic flow. -/
theorem contMDiffOn_maximalGeodesic :
    ContMDiffOn (I.tangent.prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : TangentBundle I M × ℝ ↦ maximalGeodesic I M q.1.proj q.1.2 q.2)
      {q | q.2 ∈ geodesicInterval I M q.1.proj q.1.2} :=
  ((Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (n := ∞)).comp_contMDiffOn
    contMDiffOn_maximalIntegralCurve_geodesicSpray).congr fun _ _ ↦ maximalGeodesic_def _ _ _

/-- A Cⁿ curve of initial states gives a jointly Cⁿ geodesic variation at each point
of the central maximal geodesic interval, for every finite order `n`. -/
theorem contMDiffAt_maximalGeodesic_comp
    {σ : ℝ → TangentBundle I M} {n : ℕ} (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n σ 0) {t : ℝ}
    (ht : t ∈ geodesicInterval I M (σ 0).proj (σ 0).2) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n
      (fun z : ℝ × ℝ ↦ maximalGeodesic I M (σ z.1).proj (σ z.1).2 z.2) (0, t) := by
  have hfst : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) n Prod.fst ((0 : ℝ), t) :=
    (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffAt
  have hsnd : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) n Prod.snd ((0 : ℝ), t) :=
    (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffAt
  exact ((contMDiffOn_maximalGeodesic (I := I) (M := M)).contMDiffAt
    (isOpen_setOfPred_mem_geodesicInterval.mem_nhds ht)).of_le (by simp)
      |>.comp (0, t) ((hσ.comp (0, t) hfst).prodMk hsnd)

/-- Around a compact subset of a maximal geodesic interval there is one open time domain
valid for every nearby initial state, on which the geodesic flow is jointly smooth.
In particular a prescribed compact geodesic segment admits variations on a common time domain,
even when the metric is incomplete. -/
theorem _root_.TangentBundle.exists_contMDiffOn_maximalGeodesic_of_isCompact (z : TangentBundle I M)
    {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ geodesicInterval I M z.proj z.2) :
    ∃ (U : Set (TangentBundle I M)) (V : Set ℝ),
      IsOpen U ∧ IsOpen V ∧ z ∈ U ∧ K ⊆ V ∧
        (∀ w ∈ U, V ⊆ geodesicInterval I M w.proj w.2) ∧
        ContMDiffOn (I.tangent.prod 𝓘(ℝ, ℝ)) I ∞
          (fun q : TangentBundle I M × ℝ ↦ maximalGeodesic I M q.1.proj q.1.2 q.2)
          (U ×ˢ V) := by
  obtain ⟨U, V, hU, hV, hz, hKV, hUV⟩ := generalized_tube_lemma
    (isCompact_singleton (x := z)) hK
    (isOpen_setOfPred_mem_geodesicInterval (I := I) (M := M))
    (by rintro ⟨w, t⟩ ⟨hw, ht⟩; rcases mem_singleton_iff.mp hw with rfl; exact hsub ht)
  exact ⟨U, V, hU, hV, hz (mem_singleton z), hKV,
    fun w hw t ht ↦ hUV (a := (w, t)) ⟨hw, ht⟩,
    contMDiffOn_maximalGeodesic.mono hUV⟩

/-- A Cⁿ curve of initial states gives a Cⁿ geodesic variation on one product neighbourhood of
any compact subset of the central maximal interval, for every finite order `n`. Both the variation
parameter and the time domain are open, so derivatives at compact segment endpoints
are unrestricted. -/
theorem exists_contMDiffOn_maximalGeodesic_comp_of_isCompact
    {σ : ℝ → TangentBundle I M} {n : ℕ} (hσ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n σ 0)
    {K : Set ℝ} (hK : IsCompact K)
    (hsub : K ⊆ geodesicInterval I M (σ 0).proj (σ 0).2) :
    ∃ (U V : Set ℝ), IsOpen U ∧ IsOpen V ∧ 0 ∈ U ∧ K ⊆ V ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n
        (fun z : ℝ × ℝ ↦ maximalGeodesic I M (σ z.1).proj (σ z.1).2 z.2) (U ×ˢ V) ∧
      ∀ q ∈ U, IsGeodesicCurveOn I (maximalGeodesic I M (σ q).proj (σ q).2) V := by
  obtain ⟨A, V, hA, hV, hσA, hKV, hdom, hflow⟩ :=
    (σ 0).exists_contMDiffOn_maximalGeodesic_of_isCompact hK hsub
  obtain ⟨W, hW, hσW⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hσ
  let U := interior W ∩ interior (σ ⁻¹' A)
  have h0 : 0 ∈ U := ⟨mem_interior_iff_mem_nhds.2 hW,
    mem_interior_iff_mem_nhds.2 (hσ.continuousAt.preimage_mem_nhds (hA.mem_nhds hσA))⟩
  have hσU : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent n σ U :=
    hσW.mono fun _ hq ↦ interior_subset hq.1
  have hUA : MapsTo σ U A := fun _ hq ↦ (interior_subset (s := σ ⁻¹' A)) hq.2
  refine ⟨U, V, isOpen_interior.inter isOpen_interior, hV, h0, hKV, ?_, ?_⟩
  · have hfst : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) n Prod.fst :=
      contMDiff_iff_contDiff.mpr contDiff_fst
    have hsnd : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) n Prod.snd :=
      contMDiff_iff_contDiff.mpr contDiff_snd
    have hσfst : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I.tangent n
        (fun z : ℝ × ℝ ↦ σ z.1) (U ×ˢ V) :=
      hσU.comp hfst.contMDiffOn (fun _ h ↦ h.1)
    exact (hflow.of_le (by simp)).comp (hσfst.prodMk hsnd.contMDiffOn)
      (fun z hz ↦ ⟨hUA hz.1, hz.2⟩)
  · intro q hq
    exact (isGeodesicCurveOnFrom_maximalGeodesic (σ q).proj (σ q).2).isGeodesicCurveOn.mono
      hV.uniqueDiffOn (hdom (σ q) (hUA hq))

end TauCeti.Manifold

end
