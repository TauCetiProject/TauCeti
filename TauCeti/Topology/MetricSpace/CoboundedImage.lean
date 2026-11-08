/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Images of closed sets under maps tending to infinity

Let `f` be continuous on a closed subset `A` of a topological space, with values in a metric space.
The image of each compact part of `A` is then bounded, so any choice of preimages of points
escaping to infinity eventually leaves every compact set.  If moreover `f` tends to infinity
along `A` outside compact sets, then `f '' A` is closed, and when `f` is injective on `A` its
inverse on `f '' A` is continuous: `f` restricted to `A` is a closed embedding.  On a proper
metric space, `Metric.cobounded_eq_cocompact` turns the cocompact filters here into cobounded
ones.

These facts let a map defined on a closed region, such as the closed upper half-plane, be
inverted continuously up to the boundary of its image.

## Main results

* `TauCeti.tendsto_invFunOn_cobounded_cocompact`: chosen preimages of points escaping to infinity
  eventually leave every compact set.
* `TauCeti.isClosed_image_of_tendsto_cobounded`: `f '' A` is closed when `f` tends to infinity
  along `A` outside compact sets.
* `TauCeti.continuousOn_of_leftInvOn_of_tendsto_cobounded`: any left inverse on `A` of such an
  `f`, for instance `invFunOn f A` when `f` is injective on `A`, is continuous on `f '' A`.
-/

public section

open Bornology Filter Function Metric Set Topology

namespace TauCeti

variable {α β : Type*} [TopologicalSpace α] {f : α → β} {A : Set α}

/-- If `f` is continuous on a closed subset `A` of a topological space, with values in a
pseudometric space, then any choice of preimages in `A` of points of `f '' A` escaping to infinity
eventually leaves every compact set. -/
theorem tendsto_invFunOn_cobounded_cocompact [Nonempty α] [PseudoMetricSpace β]
    (hA : IsClosed A) (hf : ContinuousOn f A) :
    Tendsto (invFunOn f A) (cobounded β ⊓ 𝓟 (f '' A)) (cocompact α) := by
  refine hasBasis_cocompact.tendsto_right_iff.mpr fun K hK => ?_
  -- The compact part `A ∩ K` has bounded image, and the chosen preimages of points outside that
  -- image lie outside `K`.
  have hKb := ((hK.inter_left hA).image_of_continuousOn (hf.mono inter_subset_left)).isBounded
  exact mem_inf_of_inter (isBounded_def.mp hKb) (mem_principal_self _)
    fun y ⟨hyK, hyA⟩ hy => hyK ⟨_, ⟨invFunOn_mem hyA, hy⟩, invFunOn_eq hyA⟩

/-- **Images of closed sets under maps tending to infinity are closed.**  If `f` is continuous on
a closed subset `A` of a topological space and tends to infinity along `A` outside compact sets,
then `f '' A` is closed. -/
theorem isClosed_image_of_tendsto_cobounded [MetricSpace β] (hA : IsClosed A)
    (hf : ContinuousOn f A) (hp : Tendsto f (cocompact α ⊓ 𝓟 A) (cobounded β)) :
    IsClosed (f '' A) := by
  refine isClosed_of_closure_subset fun y hy => ?_
  -- Near `y`, the values of `f` on `A` come from a compact part `A ∩ K` of `A`.
  obtain ⟨K, hK, hKA⟩ := (hasBasis_cocompact.inf_principal A).mem_iff.mp
    (hp (isBounded_def.mp (isBounded_ball (x := y) (r := 1))))
  have hsub : ball y 1 ∩ f '' A ⊆ f '' (A ∩ K) := by
    rintro _ ⟨hyb, x, hx, rfl⟩
    exact ⟨x, ⟨hx, by_contra fun hxK => hKA ⟨hxK, hx⟩ hyb⟩, rfl⟩
  have hc := (hK.inter_left hA).image_of_continuousOn (hf.mono inter_subset_left)
  exact image_mono inter_subset_left <| hc.isClosed.closure_subset <|
    closure_mono hsub (isOpen_ball.inter_closure ⟨mem_ball_self one_pos, hy⟩)

/-- **Continuity of the inverse of a map tending to infinity.**  If `f` is continuous on a closed
subset `A` of a topological space and tends to infinity along `A` outside compact sets, then any
left inverse `g` of `f` on `A` is continuous on `f '' A`.  For `f` injective on `A`, this applies
to `invFunOn f A` via `Set.InjOn.leftInvOn_invFunOn`. -/
theorem continuousOn_of_leftInvOn_of_tendsto_cobounded [MetricSpace β] {g : β → α}
    (hA : IsClosed A) (hf : ContinuousOn f A) (hg : LeftInvOn g f A)
    (hp : Tendsto f (cocompact α ⊓ 𝓟 A) (cobounded β)) :
    ContinuousOn g (f '' A) := by
  refine continuousOn_iff_isClosed.mpr fun t ht => ⟨f '' (t ∩ A), ?_, ?_⟩
  · exact isClosed_image_of_tendsto_cobounded (ht.inter hA) (hf.mono inter_subset_right)
      (hp.mono_left (inf_le_inf_left _ (principal_mono.mpr inter_subset_right)))
  · rw [← hg.image_inter', inter_eq_left.mpr (image_mono inter_subset_right)]

end TauCeti
