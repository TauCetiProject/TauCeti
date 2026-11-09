/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Topology.Connected.Basic

/-!
# The closed and open arcs of the circle

Mathlib's `Circle.exp` parametrizes the circle by angles. This file reads a *closed arc*
`Circle.exp '' Set.Icc a b` off a subset of the circle and identifies its complement: a nonempty
closed preconnected proper subset of the circle is such an arc, and the complement of a closed arc
is the open arc `Circle.exp '' Set.Ioo b (a + 2 * π)` spanning the complementary angles.

It also describes how two distinct points `x` and `y` cut the circle, using Mathlib's arcs
`Circle.path x y`: the complement of `{x, y}` has exactly the two open arcs as its connected
components, each with frontier `{x, y}` and with closure a closed arc, homeomorphic to the unit
interval with `x` and `y` at its endpoints. This is the one-dimensional case of the generalized
Schoenflies theorem.

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
on a compact set into a Hausdorff space reflects preconnectedness
(`IsCompact.isPreconnected_image_iff_of_injOn`), which carries preconnectedness of
`T = Circle.exp '' K` back to `K`; a compact connected subset of `ℝ` is then a closed interval
(`eq_Icc_of_connected_compact`).
Hence `T = Circle.exp '' Icc a b` with `b - a < 2 * π`, the degenerate case `a = b` being a point.

The complement is read off the same period, moved to `Ioc b (b + 2 * π)` so that the closed arc
becomes `Icc (a + 2 * π) (b + 2 * π)` and injectivity of `Circle.exp` applies to the difference.
Outside the range `a ≤ b`, `b - a < 2 * π` the formula still holds, both sides being trivial: an
empty closed arc against an open arc of more than a full turn, or a full circle against an empty
open arc.

## Main results

* `Circle.image_exp_Icc_add_two_pi` — translating both angles of a closed arc by a full turn does
  not change it.
* `TauCeti.exists_eq_circleExp_image_Icc` — a nonempty closed preconnected proper subset of the
  circle is `Circle.exp '' Set.Icc a b` for a pair of angles less than a full turn apart.
* `TauCeti.compl_circleExp_image_Icc` — the complement of the closed arc
  `Circle.exp '' Set.Icc a b` is the open arc `Circle.exp '' Set.Ioo b (a + 2 * π)`, for any
  pair of angles.
* `TauCeti.mem_circleExp_image_Icc_neg_iff` — the closed arc `Circle.exp '' Set.Icc (-a) a` is
  where the argument is at most `a` in absolute value.
* `TauCeti.exists_centeredArc_subset_of_mem_nhds` — every neighbourhood of `1` contains an arc
  about `1` of half-width at most `π`.
* `Circle.isOpen_path_image_Ioo`, `Circle.closure_path_image_Ioo` and
  `Circle.frontier_path_image_Ioo` — an open arc `Circle.path x y '' Set.Ioo 0 1` between two
  distinct points is open, with closure the closed arc and frontier its two endpoints.
* `Circle.connectedComponentIn_compl_pair` — the two open arcs between `x` and `y` are the
  connected components of `{x, y}ᶜ`.
* `Circle.frontier_connectedComponentIn_compl_pair` and
  `Circle.exists_homeomorph_closure_connectedComponentIn_compl_pair` — each component of `{x, y}ᶜ`
  has frontier `{x, y}`, and its closure is homeomorphic to the unit interval with `x` and `y` at
  the endpoints.
-/

public section

namespace TauCeti

open Real Set
open scoped Topology

/-! The statements below are about a *closed arc* `Circle.exp '' Set.Icc a b`. Nothing ties the
angles to a period, so a consumer may translate them by any multiple of `2 * π`. -/

/-- **Translating the angles by a full turn does not change a closed arc.** -/
theorem _root_.Circle.image_exp_Icc_add_two_pi (a b : ℝ) :
    Circle.exp '' Icc (a + 2 * π) (b + 2 * π) = Circle.exp '' Icc a b := by
  rw [← image_add_const_Icc, ← image_comp]
  exact image_congr fun x _ => Circle.exp_add_two_pi x

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
  have hKpre : IsPreconnected K := (hKcompact.isPreconnected_image_iff_of_injOn
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
  rw [← Circle.image_exp_Icc_add_two_pi a b, compl_eq_univ_sdiff,
    ← Circle.exp_surjective.range_eq, ← Circle.periodic_exp.image_Ioc two_pi_pos b,
    ← (Circle.exp_injOn_Ioc (by simp)).image_sdiff_subset hbsub, hdiff]

/-- A closed arc of the circle is closed. -/
theorem isClosed_circleExp_image_Icc (a b : ℝ) : IsClosed (Circle.exp '' Icc a b) :=
  (isCompact_Icc.image Circle.exp.continuous).isClosed

/-- **The closed arc symmetric about `1` is cut out by the argument.** A point lies on the closed
arc `Circle.exp '' Set.Icc (-a) a` exactly when its argument is at most `a` in absolute value. No
constraint on `a` is needed: for `π ≤ a` both sides hold everywhere, and for `a < 0` neither
does. -/
theorem mem_circleExp_image_Icc_neg_iff {a : ℝ} {z : Circle} :
    z ∈ Circle.exp '' Icc (-a) a ↔ |Complex.arg z| ≤ a := by
  refine ⟨?_, fun h => ⟨Complex.arg z, abs_le.1 h, Circle.exp_arg z⟩⟩
  rintro ⟨t, ht, rfl⟩
  rcases lt_or_ge a π with haπ | haπ
  · rw [Circle.arg_exp (by linarith [ht.1]) (by linarith [ht.2])]
    exact abs_le.2 ht
  · exact (Complex.abs_arg_le_pi _).trans haπ

/-- Every neighbourhood of `1` in the circle contains an arc `|arg z| < r` with `0 < r ≤ π`. -/
theorem exists_centeredArc_subset_of_mem_nhds {V : Set Circle} (hV : V ∈ 𝓝 1) :
    ∃ r, 0 < r ∧ r ≤ Real.pi ∧ Circle.centeredArc r ⊆ V := by
  have hV' : Circle.exp ⁻¹' V ∈ 𝓝 0 :=
    Circle.exp.continuous.continuousAt.preimage_mem_nhds (by rwa [Circle.exp_zero])
  obtain ⟨r', hr', hball⟩ := Metric.mem_nhds_iff.1 hV'
  have hmem {t : ℝ} (ht : |t| < min r' Real.pi) : t ∈ Metric.ball 0 r' := by
    simpa [Real.dist_eq] using ht.trans_le (min_le_left _ _)
  refine ⟨min r' Real.pi, lt_min hr' Real.pi_pos, min_le_right _ _, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hball (hmem ht)

end TauCeti

/-! ### The two arcs between two points

Two distinct points `x` and `y` cut the circle into the open arcs `Circle.path x y '' Ioo 0 1` and
`Circle.path y x '' Ioo 0 1`, running counterclockwise from `x` to `y` and from `y` to `x`. Each is
the complement of the opposite closed arc `range (Circle.path _ _)`
(`Circle.compl_range_path`), so it is open, and its closure is its own closed arc. Being
connected, the two open arcs are the connected components of `{x, y}ᶜ`, and each component has
the two points as its frontier and a closed interval as its closure. -/

namespace Circle

open Set

variable {x y z : Circle}

/-- An open arc between two distinct points of the circle is open: it is the complement of the
opposite closed arc. -/
theorem isOpen_path_image_Ioo (h : x ≠ y) : IsOpen (x.path y '' Ioo 0 1) := by
  rw [← compl_range_path h.symm]
  exact (isCompact_range (y.path x).continuous).isClosed.isOpen_compl

/-- The two open arcs between two distinct points cover the rest of the circle. -/
theorem path_image_Ioo_union_path_image_Ioo (h : x ≠ y) :
    x.path y '' Ioo 0 1 ∪ y.path x '' Ioo 0 1 = {x, y}ᶜ := by
  rw [← compl_range_path h.symm, ← compl_range_path h, ← compl_inter,
    range_path_inter_range_path h.symm, pair_comm]

/-- The two open arcs between two distinct points are disjoint. -/
theorem disjoint_path_image_Ioo (h : x ≠ y) :
    Disjoint (x.path y '' Ioo 0 1) (y.path x '' Ioo 0 1) := by
  rw [← compl_range_path h]
  exact disjoint_compl_right_iff_subset.mpr (image_subset_range _ _)

/-- The closure of an open arc is the closed arc. -/
theorem closure_path_image_Ioo (x y : Circle) :
    closure (x.path y '' Ioo 0 1) = range (x.path y) := by
  refine (closure_minimal (image_subset_range _ _)
    (isCompact_range (x.path y).continuous).isClosed).antisymm ?_
  have hcl : closure (Ioo (0 : unitInterval) 1) = univ := by
    rw [closure_Ioo zero_ne_one, unitInterval.univ_eq_Icc]
  rw [← image_univ, ← hcl]
  exact image_closure_subset_closure_image (x.path y).continuous

/-- The frontier of an open arc between two distinct points is the pair of its endpoints. -/
theorem frontier_path_image_Ioo (h : x ≠ y) :
    frontier (x.path y '' Ioo 0 1) = {x, y} := by
  rw [frontier, closure_path_image_Ioo, (isOpen_path_image_Ioo h).interior_eq,
    ← compl_range_path h.symm, sdiff_compl, range_path_inter_range_path h]

/-- **An open arc is a connected component of the complement of its endpoints.** -/
theorem connectedComponentIn_compl_pair (h : x ≠ y) (hz : z ∈ x.path y '' Ioo 0 1) :
    connectedComponentIn {x, y}ᶜ z = x.path y '' Ioo 0 1 := by
  have hU : IsPreconnected (x.path y '' Ioo 0 1) :=
    isPreconnected_Ioo.image _ (x.path y).continuous.continuousOn
  have hsub := path_image_Ioo_union_path_image_Ioo h
  refine subset_antisymm ?_ (hU.subset_connectedComponentIn hz (hsub ▸ subset_union_left))
  rcases isPreconnected_connectedComponentIn.subset_or_subset (isOpen_path_image_Ioo h)
    (isOpen_path_image_Ioo h.symm) (disjoint_path_image_Ioo h)
    ((connectedComponentIn_subset _ _).trans hsub.symm.subset) with hc | hc
  · exact hc
  · exact absurd (hc (mem_connectedComponentIn (hsub.subset (Or.inl hz))))
      (disjoint_left.mp (disjoint_path_image_Ioo h) hz)

/-- **Two points are the frontier of each component of their complement.** -/
theorem frontier_connectedComponentIn_compl_pair (h : x ≠ y) (hz : z ∉ ({x, y} : Set Circle)) :
    frontier (connectedComponentIn {x, y}ᶜ z) = {x, y} := by
  rcases (path_image_Ioo_union_path_image_Ioo h).symm.subset hz with hz | hz
  · rw [connectedComponentIn_compl_pair h hz, frontier_path_image_Ioo h]
  · rw [pair_comm, connectedComponentIn_compl_pair h.symm hz, frontier_path_image_Ioo h.symm]

/-- The closure of the component of the open arc from `x` to `y` is a closed interval with
endpoints `x` and `y`. -/
private theorem exists_homeomorph_closure_connectedComponentIn_compl_pair_of_mem (h : x ≠ y)
    (hz : z ∈ x.path y '' Ioo 0 1) :
    ∃ φ : closure (connectedComponentIn {x, y}ᶜ z) ≃ₜ unitInterval,
      ∀ w : closure (connectedComponentIn {x, y}ᶜ z),
        (w : Circle) ∈ ({x, y} : Set Circle) ↔ φ w = 0 ∨ φ w = 1 := by
  have hc : closure (connectedComponentIn {x, y}ᶜ z) = range (x.path y) := by
    rw [connectedComponentIn_compl_pair h hz, closure_path_image_Ioo]
  -- The arc is parametrized by `Circle.path x y`, a closed embedding of the unit interval.
  let ψ : unitInterval ≃ₜ range (x.path y) :=
    ((x.path y).continuous.isClosedEmbedding (path_injective_of_ne h)).isEmbedding.toHomeomorph
  refine ⟨(Homeomorph.setCongr hc).trans ψ.symm, fun w => ?_⟩
  have hw : x.path y ((Homeomorph.setCongr hc).trans ψ.symm w) = w :=
    congrArg Subtype.val (ψ.apply_symm_apply (Homeomorph.setCongr hc w))
  rw [← hw, mem_insert_iff, mem_singleton_iff, (path_injective_of_ne h).eq_iff' (x.path y).source,
    (path_injective_of_ne h).eq_iff' (x.path y).target]

/-- **The closure of each component of the complement of two points is an arc.** It is homeomorphic
to the unit interval by a homeomorphism carrying the two points onto the endpoints `0` and `1`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_pair (h : x ≠ y)
    (hz : z ∉ ({x, y} : Set Circle)) :
    ∃ φ : closure (connectedComponentIn {x, y}ᶜ z) ≃ₜ unitInterval,
      ∀ w : closure (connectedComponentIn {x, y}ᶜ z),
        (w : Circle) ∈ ({x, y} : Set Circle) ↔ φ w = 0 ∨ φ w = 1 := by
  rcases (path_image_Ioo_union_path_image_Ioo h).symm.subset hz with hz | hz
  · exact exists_homeomorph_closure_connectedComponentIn_compl_pair_of_mem h hz
  · rw [pair_comm]
    exact exists_homeomorph_closure_connectedComponentIn_compl_pair_of_mem h.symm hz

end Circle
