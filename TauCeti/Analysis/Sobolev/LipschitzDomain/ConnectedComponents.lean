/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Topology.ConnectedComponents

/-!
# Connected components of a Lipschitz domain

Inside the cylinder of a Lipschitz chart, a Lipschitz domain is the region above the graph of a
Lipschitz function. When the graph stays below the top of the cylinder, this region is
preconnected: it is the continuous image of the convex set `(0, 1) × ball 0 r` under
`(s, y) ↦ (ℓ(y) + s (h - ℓ(y)), y)`, where `ℓ(y) = max (γ y) (-h)` is the lower end of the
vertical fibre over `y`. Shrinking the radius of a chart centred at a frontier point until
`K r < h` achieves this, so every frontier point of a Lipschitz domain `Ω` has an open
neighbourhood `N` with `Ω ∩ N` preconnected.

Consequently a Lipschitz domain with compact frontier, in particular a bounded one in a proper
space, has finitely many connected components. Finitely many such neighbourhoods cover the
frontier; each of them meets a single component of `Ω`; and every component meets one of them,
since a component that does not reaches no frontier point of `Ω`, so it has empty frontier and is
the whole ambient space. This is the count behind the Neumann problem: the `H¹` functions with
vanishing gradient on a bounded Lipschitz domain are the functions constant on each of its
finitely many components.

## Main declarations

* `TauCeti.isPreconnected_setOf_lt_fst_inter_normalCylinder`: the region above a continuous
  graph inside a cylinder whose top lies above the graph is preconnected.
* `Set.IsLipschitzChart.isPreconnected_inter_preimage_normalCylinder`: the part of `Ω` inside
  such a chart is preconnected.
* `Set.IsLipschitzDomain.exists_isOpen_isPreconnected_inter`: every frontier point of a Lipschitz
  domain has an open neighbourhood meeting it in a preconnected set.
* `Set.IsLipschitzDomain.finite_connectedComponents`: a Lipschitz domain with compact frontier has
  finitely many connected components.
* `Set.IsLipschitzDomain.finite_connectedComponents_of_isBounded`: the same for a bounded Lipschitz
  domain in a proper space.

## References

* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, Definition 1.2.1.1 (Lipschitz
  boundaries as local epigraphs).
-/

public section

open Metric Set TopologicalSpace
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace TauCeti

/-- **The region above a graph inside a cylinder is preconnected.** If `γ` is continuous on the
ball of radius `r` and stays below the top `h` of the cylinder there, the part of the cylinder
`normalCylinder h r` strictly above the graph of `γ` is preconnected. -/
theorem isPreconnected_setOf_lt_fst_inter_normalCylinder {γ : E → ℝ} {h r : ℝ}
    (hγc : ContinuousOn γ (ball 0 r)) (hγ : ∀ y ∈ ball (0 : E) r, γ y < h) :
    IsPreconnected ({x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} ∩ normalCylinder h r) := by
  rcases le_or_gt h 0 with hh | hh
  · -- For `h ≤ 0` the cylinder is empty.
    rw [eq_empty_of_forall_notMem fun x (hx : x ∈ _ ∩ normalCylinder h r) => by
      rw [mem_inter_iff, mem_normalCylinder] at hx
      linarith [hx.2.1, hx.2.2.1]]
    exact isPreconnected_empty
  -- The lower end of the vertical fibre of the region over `y`.
  set lo : E → ℝ := fun y => max (γ y) (-h)
  have hlo : ∀ y ∈ ball (0 : E) r, lo y < h := fun y hy => max_lt (hγ y hy) (by linarith)
  set f : ℝ × E → WithLp 2 (ℝ × E) := fun q =>
    WithLp.toLp 2 (lo q.snd + q.fst * (h - lo q.snd), q.snd)
  have himage : {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} ∩ normalCylinder h r =
      f '' (Ioo 0 1 ×ˢ ball 0 r) := by
    ext x
    constructor
    · rintro ⟨hx, hxC⟩
      rw [mem_normalCylinder] at hxC
      have hxr : x.snd ∈ ball (0 : E) r := mem_ball_zero_iff.2 hxC.2.2
      have h1 : lo x.snd < x.fst := max_lt hx hxC.1
      have := hlo x.snd hxr
      refine ⟨((x.fst - lo x.snd) / (h - lo x.snd), x.snd),
        ⟨⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩, hxr⟩,
        ?_⟩
      refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_) <;>
        simp [f, div_mul_cancel₀ _ (by linarith : h - lo x.snd ≠ 0)]
    · rintro ⟨⟨t, y⟩, ⟨⟨ht0, ht1⟩, hy⟩, rfl⟩
      have h2 := hlo y hy
      have h1 : lo y < lo y + t * (h - lo y) := by nlinarith
      have h3 : lo y + t * (h - lo y) < h := by nlinarith
      refine ⟨(le_max_left _ _).trans_lt h1, ?_⟩
      rw [mem_normalCylinder]
      exact ⟨(le_max_right _ _).trans_lt h1, h3, mem_ball_zero_iff.1 hy⟩
  rw [himage]
  have hloc : ContinuousOn lo (ball 0 r) := hγc.sup continuousOn_const
  refine (isPreconnected_Ioo.prod (convex_ball (0 : E) r).isPreconnected).image f ?_
  refine (WithLp.prod_continuous_toLp 2 ℝ E).comp_continuousOn (ContinuousOn.prodMk ?_
    continuousOn_snd)
  have hlo' : ContinuousOn (fun q : ℝ × E => lo q.snd) (Ioo 0 1 ×ˢ ball 0 r) :=
    hloc.comp continuousOn_snd fun q hq => hq.2
  exact hlo'.add (continuousOn_fst.mul (continuousOn_const.sub hlo'))

end TauCeti

namespace Set

open TauCeti

namespace IsLipschitzChart

variable {Ω : Set F} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {K : ℝ≥0} {h r : ℝ}

/-- **A Lipschitz domain is preconnected inside a chart whose graph stays below the top of the
cylinder.** -/
theorem isPreconnected_inter_preimage_normalCylinder (hc : IsLipschitzChart Ω e γ K h r)
    (hγ : ∀ y ∈ ball (0 : E) r, γ y < h) :
    IsPreconnected (Ω ∩ e ⁻¹' normalCylinder h r) := by
  have hpre := isPreconnected_setOf_lt_fst_inter_normalCylinder
    hc.lipschitzWith.continuous.continuousOn hγ
  rw [← hc.image_inter_normalCylinder] at hpre
  have himage : e.symm '' (e '' Ω ∩ normalCylinder h r) = Ω ∩ e ⁻¹' normalCylinder h r := by
    ext z
    constructor
    · rintro ⟨w, ⟨⟨u, hu, rfl⟩, hwC⟩, rfl⟩
      simpa [hu] using hwC
    · rintro ⟨hz, hzC⟩
      exact ⟨e z, ⟨⟨z, hz, rfl⟩, hzC⟩, e.symm_apply_apply z⟩
  exact himage ▸ hpre.image _ e.symm.continuous.continuousOn

end IsLipschitzChart

namespace IsLipschitzDomain

variable {Ω : Set F}

/-- **A Lipschitz domain is preconnected near each frontier point.** Every frontier point `x` of a
Lipschitz domain `Ω` has an open neighbourhood `N` such that `Ω ∩ N` is preconnected: the
preimage of a chart cylinder whose radius `r` satisfies `K r < h`. -/
theorem exists_isOpen_isPreconnected_inter (hΩ : Ω.IsLipschitzDomain E) {x : F}
    (hx : x ∈ frontier Ω) : ∃ N : Set F, IsOpen N ∧ x ∈ N ∧ IsPreconnected (Ω ∩ N) := by
  obtain ⟨e₀, γ₀, K, h₀, r₀, hc₀, hx₀⟩ :=
    isLipschitzDomain_iff_exists_mem_normalCylinder.1 hΩ x hx
  obtain ⟨e, γ, h, r, hc, hex⟩ := hc₀.exists_isLipschitzChart_eq_zero hx₀
  have hγ0 := hc.apply_zero_of_mem_frontier hx hex
  have hh := hc.height_pos
  set r' := min r (h / (K + 1))
  have hr' : 0 < r' := lt_min hc.radius_pos (by positivity)
  have hKr : (K : ℝ) * r' < h := by
    calc (K : ℝ) * r' ≤ K * (h / (K + 1)) := by gcongr; exact min_le_right _ _
      _ < h := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  refine ⟨e ⁻¹' normalCylinder h r', (isOpen_normalCylinder h r').preimage e.continuous,
    by simpa [hex] using zero_mem_normalCylinder (E := E) hh hr', ?_⟩
  refine (hc.mono hh hr' le_rfl (min_le_left _ _)).isPreconnected_inter_preimage_normalCylinder
    fun y hy => ?_
  have hy' : ‖y‖ < r' := mem_ball_zero_iff.1 hy
  have := hc.lipschitzWith.dist_le_mul y 0
  rw [hγ0, Real.dist_eq, sub_zero, dist_zero_right] at this
  calc γ y ≤ |γ y| := le_abs_self _
    _ ≤ K * ‖y‖ := this
    _ ≤ K * r' := by gcongr
    _ < h := hKr

/-- **A Lipschitz domain with compact frontier has finitely many connected components.** -/
theorem finite_connectedComponents (hΩ : Ω.IsLipschitzDomain E)
    (hcompact : IsCompact (frontier Ω)) : Finite (ConnectedComponents Ω) := by
  -- Finitely many open sets `N`, each meeting `Ω` in a preconnected set, cover the frontier;
  -- every component of `Ω` other than the whole space reaches the frontier, hence one of them.
  choose N hNo hxN hNc using fun x : frontier Ω => hΩ.exists_isOpen_isPreconnected_inter x.property
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover (fun x : frontier Ω => N x) hNo
    fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩
  rcases isEmpty_or_nonempty Ω with hΩe | hΩne
  · exact Finite.of_surjective _ ConnectedComponents.surjective_coe
  obtain ⟨a₀⟩ := hΩne
  -- Each of the covering sets meets `Ω`, at a point `b x`.
  have hmeet : ∀ x : frontier Ω, (Ω ∩ N x).Nonempty := fun x => by
    rw [inter_comm]
    exact mem_closure_iff.1 (frontier_subset_closure x.property) (N x) (hNo x) (hxN x)
  choose b hb using hmeet
  let ψ : Option t → ConnectedComponents Ω := fun o =>
    o.elim (ConnectedComponents.mk a₀) fun x => ConnectedComponents.mk ⟨b x, (hb x).1⟩
  refine Finite.of_surjective ψ fun c => ?_
  obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe c
  by_cases hC : ∃ x ∈ t, (connectedComponentIn Ω a ∩ N x).Nonempty
  · -- The component of `a` meets some `N x`, and so contains the whole preconnected `Ω ∩ N x`.
    obtain ⟨x, hxt, z, hzC, hzN⟩ := hC
    have hz : z ∈ Ω := connectedComponentIn_subset _ _ hzC
    refine ⟨some ⟨x, hxt⟩, ?_⟩
    calc ψ (some ⟨x, hxt⟩) = ConnectedComponents.mk ⟨z, hz⟩ :=
          (hNc x).connectedComponents_mk_eq inter_subset_left (hb x) ⟨hz, hzN⟩
      _ = ConnectedComponents.mk a :=
          ConnectedComponents.mk_eq_mk_iff_mem_connectedComponentIn.2 hzC
  · -- Otherwise the component of `a` has empty frontier, so it is the whole space.
    simp only [not_exists, not_and, not_nonempty_iff_eq_empty] at hC
    have hfr : frontier (connectedComponentIn Ω a) = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => ?_
      have hyΩ : y ∈ frontier Ω := ⟨closure_mono (connectedComponentIn_subset _ _) hy.1, by
        rw [hΩ.isOpen.interior_eq]
        exact frontier_connectedComponentIn_subset_compl hΩ.isOpen a hy⟩
      obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht hyΩ)
      obtain ⟨z, hzN, hzC⟩ := mem_closure_iff.1 hy.1 (N x) (hNo x) hyx
      exact (hC x hxt).subset ⟨hzC, hzN⟩
    have huniv : connectedComponentIn Ω a = univ :=
      (isClopen_iff_frontier_eq_empty.2 hfr).eq_univ ⟨a, mem_connectedComponentIn a.property⟩
    exact ⟨none, ConnectedComponents.mk_eq_mk_iff_mem_connectedComponentIn.2
      (huniv ▸ mem_univ _)⟩

/-- **A bounded Lipschitz domain in a proper space has finitely many connected components.** -/
theorem finite_connectedComponents_of_isBounded [ProperSpace F] (hΩ : Ω.IsLipschitzDomain E)
    (hb : Bornology.IsBounded Ω) : Finite (ConnectedComponents Ω) :=
  hΩ.finite_connectedComponents <| Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)

end IsLipschitzDomain

end Set
