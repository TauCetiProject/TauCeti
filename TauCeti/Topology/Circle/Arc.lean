/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The closed and open arcs of the circle

Mathlib's `Circle.exp` parametrizes the circle by angles. This file reads a *closed arc*
`Circle.exp '' Set.Icc a b` off a subset of the circle and identifies its complement: a nonempty
closed preconnected proper subset of the circle is such an arc, and the complement of a closed arc
is the open arc `Circle.exp '' Set.Ioo b (a + 2 * π)` spanning the complementary angles.

Nothing here is specific to any curve theory; as with `TauCeti/Topology/Circle/Metric.lean`, these
are facts about the model circle, and the transport of them to a Jordan curve — where a compact
connected subset of the curve is thereby classified — is
`TauCeti/Topology/JordanCurve/Subcontinuum.lean`.

## The argument

The argument is the one for `ℝ`, run on a period of angles. Let `T ⊆ Circle` be closed,
preconnected and not the whole circle, and pick `z ∉ T`. Cutting the circle at `z` — that is,
reading it as `Circle.exp` on the period `[t, t + 2π]` for `Circle.exp t = z` — turns `T` into
`K = Circle.exp ⁻¹' T ∩ Icc t (t + 2 * π)`, a compact subset of `ℝ` avoiding *both* endpoints of
that period, so `K ⊆ Ioo t (t + 2 * π)` and `Circle.exp` is injective on `K`. A continuous injection
of a compact space into a Hausdorff one is a closed embedding (`Continuous.isClosedEmbedding`),
hence inducing, and an inducing map reflects preconnectedness
(`Topology.IsInducing.isPreconnected_image`), which carries preconnectedness of
`T = Circle.exp '' K` back to `K`; a compact connected subset of `ℝ` is then a closed interval
(`eq_Icc_of_connected_compact`).
Hence `T = Circle.exp '' Icc a b` with `b - a < 2 * π`, the degenerate case `a = b` being a point.

The complement is read off the same period, moved to `Ioc b (b + 2 * π)` so that the closed arc
becomes `Icc (a + 2 * π) (b + 2 * π)` and injectivity of `Circle.exp` applies to the difference.
Outside the range `a ≤ b`, `b - a < 2 * π` the formula still holds, both sides being trivial: an
empty closed arc against an open arc of more than a full turn, or a full circle against an empty
open arc.

## Main results

* `TauCeti.exists_eq_circleExp_image_Icc` — a nonempty closed preconnected proper subset of the
  circle is `Circle.exp '' Set.Icc a b` for a pair of angles less than a full turn apart.
* `TauCeti.compl_circleExp_image_Icc` — the complement of the closed arc
  `Circle.exp '' Set.Icc a b` is the open arc `Circle.exp '' Set.Ioo b (a + 2 * π)`, for any
  pair of angles.
-/

public section

namespace TauCeti

open Real Set

/-! Both statements below are about a *closed arc* `Circle.exp '' Set.Icc a b`. Nothing ties the
angles to a period, so a consumer may translate them by any multiple of `2 * π`. -/

/-- Translating the angles by a full turn does not change a closed arc. -/
private lemma circleExp_image_Icc_add_period (a b : ℝ) :
    Circle.exp '' Icc (a + 2 * π) (b + 2 * π) = Circle.exp '' Icc a b := by
  rw [← image_add_const_Icc, ← image_comp]
  exact image_congr fun x _ => Circle.exp_add_two_pi x

/-- **Preconnectedness pulls back along a continuous injection on a compact set.** If `f` is
continuous and injective on a compact `K` with values in a Hausdorff space, then `f '' K` is
preconnected exactly when `K` is. -/
private lemma isPreconnected_image_iff_of_injOn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y} {K : Set X} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hinj : InjOn f K) : IsPreconnected (f '' K) ↔ IsPreconnected K := by
  -- On the subtype the restriction is a closed embedding, so it reflects preconnectedness.
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [isPreconnected_iff_preconnectedSpace (s := K), preconnectedSpace_iff_univ,
    ← (hf.domRestrict.isClosedEmbedding hinj.injective).isInducing.isPreconnected_image, image_univ,
    range_domRestrict]

/-- **A nonempty closed preconnected proper subset of the circle is a closed arc.** The two angles
are less than a full turn apart, so `Circle.exp` is injective on the interval carrying them, and the
degenerate case `a = b` is a single point.

Closedness is what forces the arc to be closed: the set is compact, `Circle` being compact, and a
compact connected subset of the line is a closed interval. -/
theorem exists_eq_circleExp_image_Icc {T : Set Circle} (hT : IsClosed T) (hpre : IsPreconnected T)
    (hne : T.Nonempty) (hTuniv : T ≠ univ) :
    ∃ a b : ℝ, a ≤ b ∧ b - a < 2 * π ∧ T = Circle.exp '' Icc a b := by
  obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem T).mp hTuniv
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  set K : Set ℝ := Circle.exp ⁻¹' T ∩ Icc t (t + 2 * π)
  have hKcompact : IsCompact K := isCompact_Icc.inter_left (hT.preimage Circle.exp.continuous)
  have himg : Circle.exp '' K = T := by
    rw [image_preimage_inter, Circle.periodic_exp.image_Icc two_pi_pos,
      Circle.exp_surjective.range_eq, inter_univ]
  -- `K` avoids both endpoints of the period, since both are sent to the missing point `z`.
  have hKsub : K ⊆ Ioo t (t + 2 * π) := by
    rintro x ⟨hxT, hxI⟩
    refine ⟨hxI.1.lt_of_ne ?_, hxI.2.lt_of_ne ?_⟩ <;> rintro rfl
    · exact hz hxT
    · exact hz (by rwa [mem_preimage, Circle.exp_add_two_pi] at hxT)
  have hinj : InjOn Circle.exp K :=
    (Circle.exp_injOn_Ioc (by simp)).mono (hKsub.trans Ioo_subset_Ioc_self)
  have hKne : K.Nonempty := image_nonempty.mp (himg ▸ hne)
  have hKpre : IsPreconnected K := (isPreconnected_image_iff_of_injOn hKcompact
    Circle.exp.continuous.continuousOn hinj).mp (himg ▸ hpre)
  have hKeq : K = Icc (sInf K) (sSup K) := eq_Icc_of_connected_compact ⟨hKne, hKpre⟩ hKcompact
  have hle : sInf K ≤ sSup K := nonempty_Icc.mp (hKeq ▸ hKne)
  have hIsub : Icc (sInf K) (sSup K) ⊆ Ioo t (t + 2 * π) := hKeq ▸ hKsub
  refine ⟨sInf K, sSup K, hle, ?_, by rw [← hKeq, himg]⟩
  linarith [(hIsub (left_mem_Icc.mpr hle)).1, (hIsub (right_mem_Icc.mpr hle)).2]

/-- **The complement of a closed arc of the circle is the complementary open arc.** The two arcs
share their endpoints' angles: `Circle.exp '' Set.Icc a b` is complemented by
`Circle.exp '' Set.Ioo b (a + 2 * π)`. No constraint on the angles is needed: when `b < a` the
closed arc is empty and the open arc spans more than a full turn, and when `2 * π ≤ b - a` the
closed arc is the whole circle and the open arc is empty. Read left to right this removes a
complement, so it is the normal form a consumer should reach for. -/
@[simp]
theorem compl_circleExp_image_Icc (a b : ℝ) :
    (Circle.exp '' Icc a b)ᶜ = Circle.exp '' Ioo b (a + 2 * π) := by
  rcases lt_or_ge b a with hba | hab
  · -- The closed arc is empty; the open arc contains a full period `Ioc b (b + 2 * π)`.
    rw [Icc_eq_empty_of_lt hba, image_empty, compl_empty, eq_comm, ← univ_subset_iff,
      ← Circle.exp_surjective.range_eq, ← Circle.periodic_exp.image_Ioc two_pi_pos b]
    exact image_mono (Ioc_subset_Ioo_right (by linarith))
  rcases le_or_gt (2 * π) (b - a) with hge | hlt
  · -- The closed arc contains a full period `Icc a (a + 2 * π)`; the open arc is empty.
    rw [Ioo_eq_empty_of_le (by linarith), image_empty, compl_empty_iff, ← univ_subset_iff,
      ← Circle.exp_surjective.range_eq, ← Circle.periodic_exp.image_Icc two_pi_pos a]
    exact image_mono (Icc_subset_Icc_right (by linarith))
  -- Otherwise read both arcs off the period `Ioc b (b + 2 * π)`, on which `Circle.exp` is
  -- injective, with the closed arc translated to `Icc (a + 2 * π) (b + 2 * π)`.
  have hbsub : Icc (a + 2 * π) (b + 2 * π) ⊆ Ioc b (b + 2 * π) := fun x hx =>
    ⟨by linarith [hx.1], hx.2⟩
  have hdiff : Ioc b (b + 2 * π) \ Icc (a + 2 * π) (b + 2 * π) = Ioo b (a + 2 * π) := by
    ext x
    simp only [mem_sdiff, mem_Ioc, mem_Icc, mem_Ioo]
    grind
  rw [← circleExp_image_Icc_add_period a b, compl_eq_univ_sdiff,
    ← Circle.exp_surjective.range_eq, ← Circle.periodic_exp.image_Ioc two_pi_pos b,
    ← (Circle.exp_injOn_Ioc (by simp)).image_sdiff_subset hbsub, hdiff]

end TauCeti
