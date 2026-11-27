/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

/-!
# Crossing a scalar level

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

A uniform derivative lower bound also gives a crossing inside a symmetric interval for
levels close to the central value. The absolute derivative version allows either direction.

## Main results

* `TauCeti.lt_image_of_deriv_pos_boundary`: if `c ≤ g a`, then `c < g t` for every `t ∈ (a, b]`.
* `TauCeti.image_lt_of_deriv_pos_boundary`: if `g b ≤ c`, then `g t < c` for every `t ∈ [a, b)`.
* `TauCeti.existsUnique_level_of_le_abs_deriv`: quantitative existence and uniqueness.

## References

* B. Kleiner and J. Lott, *Notes on Perelman's papers*, Theorem 46.1.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Filter Set Topology

variable {g g' : ℝ → ℝ} {a b c : ℝ}

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
      exact ((hd.hasDerivWithinAt.eventually_nhdsGT_lt_of_pos hpos).and
        (Ioc_mem_nhdsGT hy)).exists.imp fun s hs ↦ ⟨(heq.trans_lt hs.1).le, hs.2⟩
  -- A later return to the level would be approached from below, contradicting `c ≤ g`.
  intro t ht
  refine (hle (Ioc_subset_Icc_self ht)).lt_of_ne fun heq ↦ ?_
  obtain ⟨hd, hpos⟩ := hg' t (Ioc_subset_Icc_self ht) heq.symm
  obtain ⟨s, hs, hsab⟩ := ((hd.hasDerivWithinAt.eventually_nhdsLT_lt_of_pos hpos).and
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

/-- A uniform positive derivative bound forces exactly one crossing of every level whose
distance from the value at zero is less than the bound times the half-width. -/
theorem existsUnique_level_of_le_deriv {F : ℝ → ℝ} {W m c : ℝ}
    (hm : 0 < m) (hF : ContinuousOn F (Icc (-W) W))
    (hderiv : ∀ t ∈ Ioo (-W) W, m ≤ deriv F t)
    (hcenter : |F 0 - c| < m * W) :
    ∃! t : ℝ, t ∈ Ioo (-W) W ∧ F t = c := by
  have hW : 0 < W := pos_of_mul_pos_right ((abs_nonneg _).trans_lt hcenter) hm.le
  have hbound (t : ℝ) (ht : t ∈ interior (Icc (-W) W)) : m ≤ deriv F t :=
    hderiv t (by simpa only [interior_Icc] using ht)
  have hpos (t : ℝ) (ht : t ∈ interior (Icc (-W) W)) : 0 < deriv F t :=
    hm.trans_le (hbound t ht)
  have hd : DifferentiableOn ℝ F (interior (Icc (-W) W)) :=
    fun t ht ↦ (differentiableAt_of_deriv_ne_zero (hpos t ht).ne').differentiableWithinAt
  have hzero : (0 : ℝ) ∈ Icc (-W) W := ⟨by linarith, hW.le⟩
  have hle : -W ≤ W := by linarith
  have hl := (convex_Icc (-W) W).mul_sub_le_image_sub_of_le_deriv hF hd hbound
    (-W) ⟨le_rfl, hle⟩ 0 hzero hzero.1
  have hr := (convex_Icc (-W) W).mul_sub_le_image_sub_of_le_deriv hF hd hbound
    0 hzero W ⟨hle, le_rfl⟩ hzero.2
  have hvalues : F (-W) < c ∧ c < F W := by
    have hc := abs_lt.mp hcenter
    constructor <;> linarith [hc.1, hc.2]
  obtain ⟨t, ht, htc⟩ := intermediate_value_Ioo hle hF hvalues
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc (-W) W) hF hpos
  refine ⟨t, ⟨ht, htc⟩, fun s hs ↦ ?_⟩
  exact hmono.injOn ⟨hs.1.1.le, hs.1.2.le⟩ ⟨ht.1.le, ht.2.le⟩ (hs.2.trans htc.symm)

/-- A uniform absolute derivative bound gives a unique crossing. By Darboux's theorem, the
derivative has constant sign in the interior. -/
theorem existsUnique_level_of_le_abs_deriv {F : ℝ → ℝ} {W m c : ℝ}
    (hm : 0 < m) (hF : ContinuousOn F (Icc (-W) W))
    (hderiv : ∀ t ∈ Ioo (-W) W, m ≤ |deriv F t|)
    (hcenter : |F 0 - c| < m * W) :
    ∃! t : ℝ, t ∈ Ioo (-W) W ∧ F t = c := by
  have hne (t : ℝ) (ht : t ∈ Ioo (-W) W) : deriv F t ≠ 0 :=
    abs_pos.mp (hm.trans_le (hderiv t ht))
  have hd (t : ℝ) (ht : t ∈ Ioo (-W) W) :
      HasDerivWithinAt F (deriv F t) (Ioo (-W) W) t :=
    (differentiableAt_of_deriv_ne_zero (hne t ht)).hasDerivAt.hasDerivWithinAt
  rcases (hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Ioo (-W) W) hd hne).symm
    with hpos | hneg
  · exact existsUnique_level_of_le_deriv hm hF
      (fun t ht ↦ by simpa only [abs_of_pos (hpos t ht)] using hderiv t ht) hcenter
  · have hn (t : ℝ) (ht : t ∈ Ioo (-W) W) : m ≤ deriv (fun s ↦ -F s) t := by
      rw [deriv.fun_neg]
      simpa only [abs_of_neg (hneg t ht)] using hderiv t ht
    have hc : |(-F 0) - (-c)| < m * W := by
      simpa only [neg_sub_neg, abs_sub_comm] using hcenter
    obtain ⟨t, ht, hu⟩ := existsUnique_level_of_le_deriv hm hF.neg hn hc
    exact ⟨t, ⟨ht.1, neg_injective ht.2⟩,
      fun s hs ↦ hu s ⟨hs.1, congrArg Neg.neg hs.2⟩⟩


end TauCeti
