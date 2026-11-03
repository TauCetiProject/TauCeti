/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.Basic
public import TauCeti.Geometry.Manifold.ConnectedSum.Basic

import Mathlib.Topology.DiscreteSubset
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Topology.ConnectedComponents

/-!
# Compactness and connectedness of the connected sum

The connected sum `TauCeti.ConnectedSum e₁ e₂` of `M` and `N` removes the centres of the balls
`e₁ : E → M` and `e₂ : E → N` and glues `e₁ v` to `e₂ (inversion 0 1 v)` for `v ≠ 0`. This file
shows that it keeps the global properties of a closed connected manifold: the connected sum of two
compact spaces is compact, and that of two connected spaces is connected when `E` has dimension at
least two. Together with the Hausdorff property (`TauCeti.ConnectedSum.t2Space`) and the manifold
structure (`TauCeti.ConnectedSum.isManifold`), this places the connected sum of two closed
connected manifolds, such as two closed `3`-manifolds, among the closed connected manifolds again.

* **Compactness** (`TauCeti.ConnectedSum.compactSpace`). A punctured summand is not compact, but
  the connected sum is already covered by the two summands with the open unit balls removed,
  `M ∖ e₁ (ball 0 1)` and `N ∖ e₂ (ball 0 1)`, which are compact. A point `e₁ v` with
  `0 < ‖v‖ < 1` is glued to `e₂ (inversion 0 1 v)`, and `‖inversion 0 1 v‖ = ‖v‖⁻¹ > 1`, so it
  lies in the second piece.
* **Connectedness** (`TauCeti.ConnectedSum.connectedSpace`). Removing the centre of a ball modelled
  on a real vector space of dimension at least two does not disconnect a connected space
  (`TauCeti.ConnectedSum.isPreconnected_puncture`), since the ball punctured at its centre is
  connected. The two punctured summands are then connected open subspaces of the connected sum
  which meet along the glued punctured balls. In dimension one this fails: removing a point from
  the line disconnects it, and the connected sum of two lines along the identity is the disjoint
  union of two lines.

## Main results

* `TauCeti.ConnectedSum.isPreconnected_puncture`: a preconnected space with the centre of a ball of
  dimension at least two removed is preconnected.
* `TauCeti.ConnectedSum.compactSpace`: the connected sum of compact spaces is compact.
* `TauCeti.ConnectedSum.connectedSpace`: the connected sum of connected spaces along balls of
  dimension at least two is connected.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1.
-/

public section

open Set Function Metric Topology EuclideanGeometry

namespace TauCeti.ConnectedSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [T1Space M] {N : Type*} [TopologicalSpace N] [T1Space N]
  {e₁ : E → M} {e₂ : E → N}

omit [InnerProductSpace ℝ E] in
/-- **Removing the centre of a ball keeps a space preconnected**, when the ball `e : E → M` is an
open embedding of a real normed space of dimension at least two: near its centre, `M` is the
ball, and the ball punctured at its centre is connected. -/
theorem isPreconnected_puncture [NormedSpace ℝ E] [PreconnectedSpace M]
    (h : 1 < Module.rank ℝ E) {e : E → M}
    (he : IsOpenEmbedding e) : IsPreconnected (puncture e : Set M) := by
  -- The inverse of the ball is a partial homeomorphism of `M` onto `E` around the centre.
  set φ := (he.toOpenPartialHomeomorph e).symm
  have hφ : e 0 ∈ φ.source := by simp [φ]
  rw [coe_puncture]
  refine isPreconnected_compl_of_isDiscrete isClosed_singleton
    subsingleton_singleton.isDiscrete fun x hx U hU ↦ ?_
  rw [mem_singleton_iff] at hx
  subst hx
  exact exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source h φ hφ hU

omit [InnerProductSpace ℝ E] in
/-- A compact summand with the open unit ball of `e` removed is a compact subset of the punctured
summand. -/
private theorem isCompact_preimage_compl_image_ball [CompactSpace M] {e : E → M}
    (he : IsOpenEmbedding e) : IsCompact (((↑) : puncture e → M) ⁻¹' (e '' ball 0 1)ᶜ) := by
  rw [Subtype.isCompact_iff, image_preimage_eq_of_subset fun x hx ↦
    ⟨⟨x, mem_puncture.2 fun hx0 ↦ hx ⟨0, mem_ball_self one_pos, hx0.symm⟩⟩, rfl⟩]
  exact (he.isOpenMap _ isOpen_ball).isClosed_compl.isCompact

/-- **The connected sum of compact spaces is compact.** It is covered by the images of the two
summands with the open unit balls removed. -/
theorem compactSpace [CompactSpace M] [CompactSpace N] (h₁ : IsOpenEmbedding e₁)
    (h₂ : IsOpenEmbedding e₂) : CompactSpace (ConnectedSum e₁ e₂) := by
  -- A point of the open unit ball, other than its centre, is glued to a point outside the open
  -- unit ball of the other summand, as the inversion sends it outside the unit sphere.
  have hinv {v w : E} (hv : v ≠ 0) (hv1 : ‖v‖ < 1) (hw : ‖w‖ < 1) : inversion 0 1 v ≠ w := by
    rintro rfl
    have hd := dist_inversion_center (0 : E) v 1
    rw [dist_zero_right, dist_zero_right, one_pow] at hd
    rw [hd, one_div, inv_lt_one₀ (norm_pos_iff.2 hv)] at hw
    exact hv1.not_gt hw
  refine ⟨?_⟩
  have hcov : (univ : Set (ConnectedSum e₁ e₂)) =
      inl e₁ e₂ '' ((↑) ⁻¹' (e₁ '' ball 0 1)ᶜ) ∪ inr e₁ e₂ '' ((↑) ⁻¹' (e₂ '' ball 0 1)ᶜ) := by
    refine (eq_univ_of_forall fun p ↦ ?_).symm
    rcases range_inl_union_range_inr e₁ e₂ ▸ mem_univ p with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · by_cases hx : (x : M) ∈ e₁ '' ball 0 1
      · obtain ⟨v, hv, hxv⟩ := hx
        have hv0 : v ≠ 0 := by rintro rfl; exact mem_puncture.1 x.2 hxv.symm
        refine Or.inr ⟨⟨_, apply_inversion_mem_puncture h₂.injective hv0⟩, ?_, ?_⟩
        · rintro ⟨w, hw, hwv⟩
          exact hinv hv0 (mem_ball_zero_iff.1 hv) (mem_ball_zero_iff.1 hw) (h₂.injective hwv).symm
        · exact ((inl_eq_inr_iff h₁.injective h₂.injective).2 ⟨v, hv0, hxv, rfl⟩).symm
      · exact Or.inl ⟨x, hx, rfl⟩
    · by_cases hy : (y : N) ∈ e₂ '' ball 0 1
      · obtain ⟨w, hw, hyw⟩ := hy
        have hw0 : w ≠ 0 := by rintro rfl; exact mem_puncture.1 y.2 hyw.symm
        have hx := apply_inversion_mem_puncture h₁.injective hw0
        refine Or.inl ⟨⟨_, hx⟩, ?_, ?_⟩
        · rintro ⟨v, hv, hvw⟩
          exact hinv hw0 (mem_ball_zero_iff.1 hw) (mem_ball_zero_iff.1 hv) (h₁.injective hvw).symm
        · exact (inl_inversion_eq_inr hw0 hx (hyw ▸ y.2)).trans (congrArg _ (Subtype.ext hyw))
      · exact Or.inr ⟨y, hy, rfl⟩
  rw [hcov]
  exact ((isCompact_preimage_compl_image_ball h₁).image (continuous_inl e₁ e₂)).union
    ((isCompact_preimage_compl_image_ball h₂).image (continuous_inr e₁ e₂))

/-- **The connected sum of connected spaces is connected**, along balls modelled on a real inner
product space of dimension at least two. The two punctured summands are connected and meet along
the glued punctured balls. -/
theorem connectedSpace [ConnectedSpace M] [ConnectedSpace N] (h : 1 < Module.rank ℝ E)
    (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) : ConnectedSpace (ConnectedSum e₁ e₂) := by
  have : Nontrivial E := rank_pos_iff_nontrivial.1 (zero_lt_one.trans h)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hx : e₁ v ∈ puncture e₁ := mem_puncture.2 (h₁.injective.ne hv)
  have hy := apply_inversion_mem_puncture h₂.injective hv
  have := Subtype.preconnectedSpace (isPreconnected_puncture h h₁)
  have := Subtype.preconnectedSpace (isPreconnected_puncture h h₂)
  have hmem : inl e₁ e₂ ⟨_, hx⟩ ∈ range (inr e₁ e₂) := ⟨_, (inl_eq_inr v hv hx hy).symm⟩
  have : PreconnectedSpace (ConnectedSum e₁ e₂) := ⟨by
    rw [← range_inl_union_range_inr]
    exact (isPreconnected_range (continuous_inl e₁ e₂)).union _ (mem_range_self _) hmem
      (isPreconnected_range (continuous_inr e₁ e₂))⟩
  exact { toNonempty := ⟨inl e₁ e₂ ⟨_, hx⟩⟩ }

end TauCeti.ConnectedSum
