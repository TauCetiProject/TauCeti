/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Images of closed sets under maps tending to infinity

Let `f` be continuous on a closed subset `A` of a proper metric space.  The image of each
bounded part of `A` is then bounded, since its closure in `A` is compact, so any choice of
preimages of points escaping to infinity escapes to infinity as well.  If moreover `f` tends to
infinity at infinity along `A`, then `f '' A` is closed, and when `f` is injective on `A` its
inverse on `f '' A` is continuous: `f` restricted to `A` is a closed embedding.

These facts let a map defined on a closed region, such as the closed upper half-plane, be
inverted continuously up to the boundary of its image.

## Main results

* `TauCeti.tendsto_invFunOn_cobounded`: chosen preimages of points escaping to infinity escape to
  infinity.
* `TauCeti.isClosed_image_of_tendsto_cobounded`: `f '' A` is closed when `f` tends to infinity
  at infinity along `A`.
* `TauCeti.continuousOn_of_leftInvOn_of_tendsto_cobounded`: any left inverse on `A` of such an
  `f`, for instance `invFunOn f A` when `f` is injective on `A`, is continuous on `f '' A`.
-/

public section

open Bornology Filter Function Metric Set Topology

namespace TauCeti

variable {α β : Type*} [PseudoMetricSpace α] [ProperSpace α] {f : α → β} {A : Set α}

/-- If `f` is continuous on a closed subset `A` of a proper space, then any choice of preimages in
`A` of points of `f '' A` escaping to infinity escapes to infinity. -/
theorem tendsto_invFunOn_cobounded [Nonempty α] [PseudoMetricSpace β] (hA : IsClosed A)
    (hf : ContinuousOn f A) :
    Tendsto (invFunOn f A) (cobounded β ⊓ 𝓟 (f '' A)) (cobounded α) := by
  obtain ⟨x₀⟩ := ‹Nonempty α›
  rw [(hasBasis_cobounded_compl_closedBall x₀).tendsto_right_iff]
  intro R _
  -- The compact part `A ∩ closedBall x₀ R` has bounded image, and points beyond that bound have
  -- their chosen preimages outside the ball.
  obtain ⟨M, -, hM⟩ := (((isCompact_closedBall x₀ R).inter_left hA).image_of_continuousOn
    (hf.mono inter_subset_left)).isBounded.subset_closedBall_lt 0 (f x₀)
  have hfar : (closedBall (f x₀) M)ᶜ ∈ cobounded β :=
    (hasBasis_cobounded_compl_closedBall (f x₀)).mem_of_mem (i := M) trivial
  refine mem_inf_of_inter hfar (mem_principal_self _) fun y ⟨hyM, hyA⟩ hyR => hyM ?_
  rw [← invFunOn_eq hyA]
  exact hM ⟨_, ⟨invFunOn_mem hyA, hyR⟩, rfl⟩

/-- **Images of closed sets under maps tending to infinity are closed.**  If `f` is continuous on
a closed subset `A` of a proper space and tends to infinity at infinity along `A`, then
`f '' A` is closed. -/
theorem isClosed_image_of_tendsto_cobounded [MetricSpace β] (hA : IsClosed A)
    (hf : ContinuousOn f A) (hp : Tendsto f (cobounded α ⊓ 𝓟 A) (cobounded β)) :
    IsClosed (f '' A) := by
  refine isClosed_of_closure_subset fun y hy => ?_
  obtain ⟨_, x₀, _, rfl⟩ := closure_nonempty_iff.mp ⟨y, hy⟩
  -- Near `y`, the values of `f` on `A` come from a compact part of `A`.
  obtain ⟨R, -, hR⟩ := ((hasBasis_cobounded_compl_closedBall x₀).inf_principal A).mem_iff.mp
    (hp ((hasBasis_cobounded_compl_closedBall y).mem_of_mem (i := 1) trivial))
  set K := A ∩ closedBall x₀ R
  have hK : IsCompact (f '' K) :=
    ((isCompact_closedBall x₀ R).inter_left hA).image_of_continuousOn (hf.mono inter_subset_left)
  have hsub : ball y 1 ∩ f '' A ⊆ f '' K := by
    rintro _ ⟨hyb, x, hx, rfl⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    by_contra hxR
    exact hR ⟨hxR, hx⟩ (ball_subset_closedBall hyb)
  have hyK : y ∈ closure (f '' K) :=
    closure_mono hsub (isOpen_ball.inter_closure ⟨mem_ball_self one_pos, hy⟩)
  rw [hK.isClosed.closure_eq] at hyK
  exact image_mono inter_subset_left hyK

/-- **Continuity of the inverse of a map tending to infinity.**  If `f` is continuous on a closed
subset `A` of a proper space and tends to infinity at infinity along `A`, then any left inverse
`g` of `f` on `A` is continuous on `f '' A`.  For `f` injective on `A`, this applies to
`invFunOn f A` via `Set.InjOn.leftInvOn_invFunOn`. -/
theorem continuousOn_of_leftInvOn_of_tendsto_cobounded [MetricSpace β] {g : β → α}
    (hA : IsClosed A) (hf : ContinuousOn f A) (hg : LeftInvOn g f A)
    (hp : Tendsto f (cobounded α ⊓ 𝓟 A) (cobounded β)) :
    ContinuousOn g (f '' A) := by
  refine continuousOn_iff_isClosed.mpr fun t ht => ⟨f '' (A ∩ t), ?_, ?_⟩
  · exact isClosed_image_of_tendsto_cobounded (hA.inter ht) (hf.mono inter_subset_left)
      (hp.mono_left (inf_le_inf_left _ (principal_mono.mpr inter_subset_left)))
  · ext y
    constructor
    · rintro ⟨hyt, x, hx, rfl⟩
      rw [mem_preimage, hg hx] at hyt
      exact ⟨⟨x, ⟨hx, hyt⟩, rfl⟩, x, hx, rfl⟩
    · rintro ⟨⟨x, ⟨hx, hxt⟩, rfl⟩, -⟩
      exact ⟨by rwa [mem_preimage, hg hx], x, hx, rfl⟩

end TauCeti
