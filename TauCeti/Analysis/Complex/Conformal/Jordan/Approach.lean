/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Inverse.BoundaryCluster
public import TauCeti.Analysis.Complex.Conformal.Jordan.Domain
import TauCeti.Analysis.Complex.Conformal.Caratheodory
import TauCeti.Analysis.Complex.PlaneSeparation.Basic
import TauCeti.Topology.JordanCurve.SmallArc
import TauCeti.Topology.Frontier
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Preconnected approach regions for Jordan domains

A Jordan domain has preconnected approach regions at every boundary point.
The proof uses Janiszewski's theorem (`TauCeti.janiszewski`) and one arc
lemma, avoiding the Jordan curve theorem and Schoenflies.

Given `a ∈ frontier U` with `U` a Jordan domain, take an open arc
`W ⊆ frontier U ∩ ball a r` through `a` whose complement `frontier U \ W`
is closed and preconnected.  Set `S := frontier U` and
`T := sphere a r ∪ (frontier U \ W)`.  Then `S ∩ T = frontier U \ W` is
preconnected, `S` does not separate points of `U`, and `T` does not
separate points of `ball a ρ` for small `ρ`; Janiszewski puts both in one
component of `(S ∪ T)ᶜ ⊆ U ∩ ball a r`.

Combined with `injOn_closedBall_of_isPreconnected_image_approach` from
`Inverse/BoundaryCluster.lean`, this gives injectivity on the closed disc
for the Riemann map of a Jordan domain, and with `closureHomeomorph` from
`BoundaryCorrespondence.lean`, the homeomorphism of closures.

## Input

* `TauCeti.IsJordanCurve.exists_isCompact_isPreconnected_notMem_sdiff_subset_ball`
  (`JordanCurve/SmallArc.lean`) — a Jordan curve admits a compact preconnected
  arc missing any given point, whose complement lies in a given ball.

## Main results

* `TauCeti.IsJordanDomain.isPreconnectedApproachAt`
  — a Jordan domain has preconnected approach regions at every boundary point.
* `TauCeti.injOn_closedBall_of_isJordanCurve_frontier`
  — injectivity on the closed disc for the Riemann map, Jordan case.
* `TauCeti.exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier`
  — the Riemann map extends to a homeomorphism of the closures;
  `TauCeti.exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier_of_mem` also sends the
  centre of the disc to a prescribed point of the domain.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
-/

public section

open Set Metric Topology Function Filter Bornology Real

namespace TauCeti

/-! ### Jordan domains -/

variable {U : Set ℂ} {a : ℂ}

/-- The connected component, in the complement of a set `F` containing the frontier of
`U` and the sphere `sphere a r`, of a point of `U ∩ ball a r` stays inside `U ∩ ball a r`. -/
private theorem connectedComponentIn_compl_subset_inter_ball {x₀ : ℂ} {r : ℝ}
    (hr : 0 < r) {F : Set ℂ} (hF : frontier U ∪ sphere a r ⊆ F)
    (hx₀U : x₀ ∈ U) (hx₀r : x₀ ∈ ball a r) :
    connectedComponentIn Fᶜ x₀ ⊆ U ∩ ball a r :=
  subset_inter (connectedComponentIn_subset_of_frontier_subset hx₀U fun z hz => hF (Or.inl hz))
    (connectedComponentIn_subset_of_frontier_subset hx₀r fun z hz =>
      hF (Or.inr (by rwa [frontier_ball _ hr.ne'] at hz)))

/-- **Janiszewski step.**  Given an open arc `W` of the boundary through `a`,
inside `ball a r`, with closed preconnected complement, the trace `U ∩ ball a δ`
lies in one preconnected subset of `U ∩ ball a r` for some `δ > 0`. -/
private theorem IsJordanDomain.exists_isPreconnected_inter_ball_subset_of_arc
    (hU : IsJordanDomain U) {r : ℝ} (hr : 0 < r) {W : Set ℂ}
    (hWJ : W ⊆ frontier U ∩ ball a r) (haW : a ∈ W)
    (hclosed : IsClosed (frontier U \ W)) (hpre : IsPreconnected (frontier U \ W)) :
    ∃ δ > 0, ∃ C ⊆ U ∩ ball a r, IsPreconnected C ∧ U ∩ ball a δ ⊆ C := by
  set J := frontier U
  -- a radius whose ball misses the complementary arc
  obtain ⟨ρ, hρ₀, hρr, hρdisj⟩ :
      ∃ ρ > 0, ρ ≤ r ∧ Disjoint (ball a ρ) (J \ W) := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl a fun h => h.2 haW
    exact ⟨min r ε, lt_min hr hε, min_le_left _ _,
      Set.disjoint_left.2 fun z hz hzE => hεsub (ball_subset_ball (min_le_right _ _) hz) hzE⟩
  refine ⟨ρ, hρ₀, ?_⟩
  rcases (U ∩ ball a ρ).eq_empty_or_nonempty with hne | ⟨x₀, hx₀U, hx₀a⟩
  · exact ⟨∅, empty_subset _, isPreconnected_empty, hne.subset⟩
  set S : Set ℂ := J
  set T : Set ℂ := sphere a r ∪ (J \ W)
  have hUJ : U ∩ J = ∅ := hU.isOpen.inter_frontier_eq
  refine ⟨connectedComponentIn (S ∪ T)ᶜ x₀,
    connectedComponentIn_compl_subset_inter_ball hr
      (fun z hz => hz.elim Or.inl fun h => Or.inr (Or.inl h)) hx₀U (ball_subset_ball hρr hx₀a),
    isPreconnected_connectedComponentIn, ?_⟩
  -- Janiszewski puts every point of `U ∩ ball a ρ` in the component of `x₀`
  rintro y ⟨hyU, hya⟩
  have hSb : IsBounded S := hU.isBounded.closure.subset frontier_subset_closure
  have hST : S ∩ T = J \ W := by
    ext z
    constructor
    · rintro ⟨hzJ, hz | hz⟩
      · refine ⟨hzJ, fun hzW => ?_⟩
        exact (ne_of_lt (mem_ball.mp (hWJ hzW).2)) (mem_sphere.mp hz)
      · exact hz
    · exact fun hz => ⟨hz.1, Or.inr hz⟩
  have hSsep : y ∈ connectedComponentIn Sᶜ x₀ :=
    hU.isConnected.isPreconnected.subset_connectedComponentIn (F := Sᶜ) hx₀U
      (fun z hz hzJ => (Set.eq_empty_iff_forall_notMem.mp hUJ) z ⟨hz, hzJ⟩) hyU
  have hTsep : y ∈ connectedComponentIn Tᶜ x₀ := by
    refine (convex_ball a ρ).isPreconnected.subset_connectedComponentIn hx₀a ?_ hya
    rintro z hz (h | h)
    · exact (ne_of_lt (mem_ball.mp (ball_subset_ball hρr hz))) (mem_sphere.mp h)
    · exact Set.disjoint_left.mp hρdisj hz h
  exact janiszewski isClosed_frontier (isClosed_sphere.union hclosed) hSb
    (isBounded_sphere.union (hSb.subset sdiff_subset)) (hST ▸ hpre) hSsep hTsep

/-- **A Jordan domain is locally connected from within at each point.** For every outer radius
`ε > 0` there is a smaller radius `δ > 0` and a preconnected subset of `U ∩ ball a ε` that contains
the trace `U ∩ ball a δ` of the domain on the smaller ball. -/
theorem IsJordanDomain.exists_isPreconnected_inter_ball_subset
    (hU : IsJordanDomain U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ C ⊆ U ∩ ball a ε, IsPreconnected C ∧ U ∩ ball a δ ⊆ C := by
  -- At a boundary point the arc lemma supplies the closed complementary arc and the Janiszewski
  -- step does the rest; elsewhere the point is interior to the domain or outside its closure.
  by_cases ha : a ∈ frontier U
  swap
  · -- off the frontier, `a` is an interior point of `U` or lies outside `closure U`
    by_cases haU : a ∈ U
    · obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hU.isOpen a haU
      exact ⟨min δ ε, lt_min hδ hε, ball a (min δ ε),
        fun z hz => ⟨hsub (ball_subset_ball (min_le_left _ _) hz),
          ball_subset_ball (min_le_right _ _) hz⟩,
        (convex_ball a _).isPreconnected, inter_subset_right⟩
    · obtain ⟨δ, hδ, hdisj⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl a
        fun h => ha ⟨h, by rwa [hU.isOpen.interior_eq]⟩
      exact ⟨min δ ε, lt_min hδ hε, ∅, empty_subset _, isPreconnected_empty, fun z hz =>
        absurd (subset_closure hz.1) (hdisj (ball_subset_ball (min_le_left _ _) hz.2))⟩
  obtain ⟨S, hSJ, hScompact, hSpre, haS, hball⟩ :=
    hU.isJordanCurve_frontier.exists_isCompact_isPreconnected_notMem_sdiff_subset_ball hε
  have hcancel : frontier U \ (frontier U \ S) = S := sdiff_sdiff_cancel_left hSJ
  refine hU.exists_isPreconnected_inter_ball_subset_of_arc hε (W := frontier U \ S)
    (fun z hz => ⟨hz.1, hball hz⟩) ⟨ha, haS⟩ ?_ ?_
  · rw [hcancel]; exact hScompact.isClosed
  · rw [hcancel]; exact hSpre

/-- **A Jordan domain has preconnected approach regions at every point.** -/
theorem IsJordanDomain.isPreconnectedApproachAt
    (hU : IsJordanDomain U) : IsPreconnectedApproachAt U a :=
  isPreconnectedApproachAt_of_forall_exists_isPreconnected_superset
    fun _ hε => hU.exists_isPreconnected_inter_ball_subset hε

variable {f F : ℂ → ℂ} {c : ℂ} {r : ℝ}

/-- **Conformal injectivity on the closed disc when the image is a Jordan
domain.**  Feeds `IsJordanDomain.isPreconnectedApproachAt` into
`injOn_closedBall_of_isPreconnected_image_approach`. -/
theorem IsJordanDomain.injOn_closedBall_of_conformal
    (hfd : DifferentiableOn ℂ f (ball c r))
    (hfi : InjOn f (ball c r))
    (hFc : ContinuousOn F (closedBall c r))
    (hFf : EqOn F f (ball c r))
    (hJ : IsJordanDomain (f '' ball c r)) :
    InjOn F (closedBall c r) :=
  injOn_closedBall_of_isPreconnected_image_approach hfd hfi hFc hFf
    fun _ _ => hJ.isPreconnectedApproachAt

/-- **Boundary injectivity, Jordan case**, in the hypothesis shape of
`TauCeti.exists_continuousOn_closedBall_eqOn_of_locallyConnectedSpace_frontier` with a Jordan-curve
boundary. -/
theorem injOn_closedBall_of_isJordanCurve_frontier
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hJf : IsJordanCurve (frontier (f '' ball c r)))
    (hFc : ContinuousOn F (closedBall c r)) (hFf : EqOn F f (ball c r)) :
    InjOn F (closedBall c r) := by
  -- a degenerate disc has at most one closed point
  rcases le_or_gt r 0 with hr | hr
  · exact (subsingleton_closedBall c hr).injOn F
  have hJ : IsJordanDomain (f '' ball c r) :=
    { isOpen := isOpen_image_of_differentiableOn_of_injOn isOpen_ball hf hinj
      isConnected := IsConnected.image ⟨nonempty_ball.mpr hr, (convex_ball c r).isPreconnected⟩
        f hf.continuousOn
      isBounded := hb
      isJordanCurve_frontier := hJf }
  exact hJ.injOn_closedBall_of_conformal hf hinj hFc hFf

/-- **The Riemann map of a Jordan domain extends to a homeomorphism of the
closures**, with the centre of the disc sent to any prescribed point `p` of the domain. -/
theorem exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier_of_mem {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω)) {p : ℂ} (hp : p ∈ Ω) :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn g (ball 0 1) Ω ∧ g 0 = p ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure Ω,
        ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = g z := by
  have := hΩJ.locallyConnectedSpace
  obtain ⟨g, hgc, hgd, hgbij, hg0⟩ :=
    exists_continuousOn_closedBall_bijOn_ball_of_locallyConnectedSpace_frontier_of_mem hΩo
      (IsJordanDomain.mk hΩo hΩc hΩb hΩJ).isSimplyConnected hΩb hp
  have himg : g '' ball 0 1 = Ω := hgbij.image_eq
  have hgi : InjOn g (closedBall 0 1) :=
    injOn_closedBall_of_isJordanCurve_frontier hgd hgbij.injOn (himg ▸ hΩb)
      (himg ▸ hΩJ) hgc fun _ _ => rfl
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hgc' : ContinuousOn g (closure (ball (0 : ℂ) 1)) := by rwa [hcl]
  have hgi' : InjOn g (closure (ball (0 : ℂ) 1)) := by rwa [hcl]
  have himg' : closure (g '' ball 0 1) = closure Ω := by rw [himg]
  refine ⟨g, hgc, hgd, hgbij, hg0, (Homeomorph.setCongr hcl.symm).trans
    ((closureHomeomorph isBounded_ball hgc' (fun _ _ => rfl) hgi').trans
      (Homeomorph.setCongr himg')), fun z => ?_⟩
  simp only [Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  exact coe_closureHomeomorph_apply isBounded_ball hgc' (fun _ _ => rfl) hgi' _

/-- **The Riemann map of a Jordan domain extends to a homeomorphism of the
closures.** -/
theorem exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω)) :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn g (ball 0 1) Ω ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure Ω,
        ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = g z :=
  have ⟨g, hgc, hgd, hgbij, _, he⟩ :=
    exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier_of_mem hΩo hΩc hΩb hΩJ
      hΩc.nonempty.some_mem
  ⟨g, hgc, hgd, hgbij, he⟩

end TauCeti
