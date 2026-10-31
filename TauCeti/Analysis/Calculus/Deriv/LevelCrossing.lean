/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.LinearAlgebra.AffineSpace.Ordered
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Crossing a level with positive derivative

Let `g : ℝ → ℝ` be continuous on `[a, b]`, and suppose that at every point of `[a, b]` where `g`
takes the value `c` it is differentiable with positive derivative. Then `g` can cross the level
`c` only upwards: once `g ≥ c`, it stays strictly above `c` at every later time of `[a, b]`
(`TauCeti.lt_image_of_deriv_pos_boundary`), and once `g ≤ c`, it was strictly below `c` at every
earlier time (`TauCeti.image_lt_of_deriv_pos_boundary`).

No differentiability is assumed away from the level. The statements are the strict, one-level
counterpart of Mathlib's fencing inequalities such as `image_le_of_deriv_right_lt_deriv_boundary`,
which assume a derivative estimate at every point of `[a, b)`. They are what is needed to show
that the trajectories of a vector field which crosses a hypersurface transversally in one
direction cross it only in that direction.

## Main results

* `HasDerivAt.eventually_nhdsGT_lt_of_pos`, `HasDerivAt.eventually_nhdsLT_lt_of_pos`: near a point
  where its derivative is positive, a function is larger to the right and smaller to the left.
* `TauCeti.lt_image_of_deriv_pos_boundary`: if `c ≤ g a`, then `c < g t` for every `t ∈ (a, b]`.
* `TauCeti.image_lt_of_deriv_pos_boundary`: if `g b ≤ c`, then `g t < c` for every `t ∈ [a, b)`.
-/

public section

open Filter Set Topology

variable {g g' : ℝ → ℝ} {a b c : ℝ}

/-- A function with positive derivative at a point is larger at nearby points to the right. -/
theorem HasDerivAt.eventually_nhdsGT_lt_of_pos {t d : ℝ} (hg : HasDerivAt g d t) (hd : 0 < d) :
    ∀ᶠ s in 𝓝[>] t, g t < g s := by
  have h := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left (nhdsGT_le_nhdsNE t)
  filter_upwards [h.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with s hs hts
  exact (slope_pos_iff hts).1 hs

/-- A function with positive derivative at a point is smaller at nearby points to the left. -/
theorem HasDerivAt.eventually_nhdsLT_lt_of_pos {t d : ℝ} (hg : HasDerivAt g d t) (hd : 0 < d) :
    ∀ᶠ s in 𝓝[<] t, g s < g t := by
  have h := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left (nhdsLT_le_nhdsNE t)
  filter_upwards [h.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with s hs hst
  exact (slope_pos_iff_gt hst).1 hs

namespace TauCeti

/-- **A level crossed with positive derivative is crossed only upwards.** Let `g` be continuous
on `[a, b]`, with a positive derivative at every point of `[a, b]` where it takes the value `c`.
If `c ≤ g a`, then `c < g t` for every `t ∈ (a, b]`. -/
theorem lt_image_of_deriv_pos_boundary (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Icc a b, g t = c → HasDerivAt g (g' t) t ∧ 0 < g' t) (ha : c ≤ g a) :
    ∀ ⦃t⦄, t ∈ Ioc a b → c < g t := by
  -- First `c ≤ g` on `[a, b]`, by continuous induction.
  have hle : Icc a b ⊆ {t | c ≤ g t} := by
    refine IsClosed.Icc_subset_of_forall_exists_gt ?_ ha fun x ⟨hx, hxab⟩ y hy ↦ ?_
    · rw [inter_comm]
      exact hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hnhds : Icc a b ∈ 𝓝[>] x := Icc_mem_nhdsGT_of_mem hxab
    rcases (show c ≤ g x from hx).lt_or_eq with hlt | heq
    · -- Above the level, `g` stays above it for a while by continuity.
      have : ∀ᶠ s in 𝓝[>] x, c < g s := nhdsWithin_le_of_mem hnhds
        (hg x (Ico_subset_Icc_self hxab) (Ioi_mem_nhds hlt))
      exact (this.and (Ioc_mem_nhdsGT hy)).exists.imp fun s hs ↦ ⟨hs.1.le, hs.2⟩
    · -- On the level, `g` increases for a while since its derivative is positive.
      obtain ⟨hd, hpos⟩ := hg' x (Ico_subset_Icc_self hxab) heq.symm
      exact ((hd.eventually_nhdsGT_lt_of_pos hpos).and (Ioc_mem_nhdsGT hy)).exists.imp
        fun s hs ↦ ⟨(heq.trans_lt hs.1).le, hs.2⟩
  -- A later return to the level would be approached from below, contradicting `c ≤ g`.
  intro t ht
  refine (hle (Ioc_subset_Icc_self ht)).lt_of_ne fun heq ↦ ?_
  obtain ⟨hd, hpos⟩ := hg' t (Ioc_subset_Icc_self ht) heq.symm
  obtain ⟨s, hs, hsab⟩ := ((hd.eventually_nhdsLT_lt_of_pos hpos).and
    (Ioo_mem_nhdsLT ht.1)).exists
  exact (heq ▸ hs).not_ge (hle ⟨hsab.1.le, hsab.2.le.trans ht.2⟩)

/-- **A level crossed with positive derivative is crossed only upwards, looking backwards.** Let
`g` be continuous on `[a, b]`, with a positive derivative at every point of `[a, b]` where it takes
the value `c`. If `g b ≤ c`, then `g t < c` for every `t ∈ [a, b)`. -/
theorem image_lt_of_deriv_pos_boundary (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Icc a b, g t = c → HasDerivAt g (g' t) t ∧ 0 < g' t) (hb : g b ≤ c) :
    ∀ ⦃t⦄, t ∈ Ico a b → g t < c := fun _ ht ↦ not_le.1 fun hct ↦
  (lt_image_of_deriv_pos_boundary (hg.mono (Icc_subset_Icc_left ht.1))
    (fun s hs ↦ hg' s (Icc_subset_Icc_left ht.1 hs)) hct ⟨ht.2, le_rfl⟩).not_ge hb

end TauCeti
