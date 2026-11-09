/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Interval

/-!
# Jordan curves traced by paths

A path whose two endpoints agree is a parametrised closed curve, but its range need not be a
Jordan curve: the path may pause, retrace an arc, or cross itself. This file supplies the exact
criterion needed to exclude those degeneracies. If a closed path has no repeated values except
for its two endpoint parameters, its range is a Jordan curve
(`TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints`).

The proof is the unit-interval case of `TauCeti.isJordanCurve_image_Icc`. The extension
`γ.extend : ℝ → X` of a path `γ : Path x x` is continuous, has equal values at `0` and `1`, and its
image of `[0, 1]` is the range of `γ`. The hypothesis on repetitions says precisely that it is
injective on `[0, 1)`, since representatives in `[0, 1)` cannot form the exceptional endpoint pair.

The condition is stated directly rather than bundled as a new notion of simple closed path. This
is the only operation needed here, and keeping it as a theorem hypothesis avoids introducing a
second simplicity vocabulary alongside Mathlib's path API.

## Gluing two arcs

The criterion has one immediate use that is worth naming on its own: two *arcs* — ranges of
injective paths — that share their two endpoints and meet nowhere else glue to a Jordan curve
(`TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair`). The closed path traversed is
`γ.trans δ.symm`, whose range is `range γ ∪ range δ`; the meeting hypothesis is what turns a
coincidence between a value of `γ` and a value of `δ` into a coincidence of endpoints, and
injectivity of each of the two paths handles the coincidences internal to one of them. The
endpoints are not asked to be distinct: injectivity of `δ` already forces that, since a path with
equal endpoints repeats the value at the two distinct parameters `0` and `1`.

## Main results

* `TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints` — the range of a closed path whose only
  possible repetition is its pair of endpoints is a Jordan curve.
* `TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair` — two arcs with the same two
  endpoints, meeting exactly there, glue to a Jordan curve.

## Use in the Carathéodory boundary correspondence

This is the topological gluing step of the Carathéodory boundary correspondence. A finite-length
image crosscut is packaged as a path with exactly this simplicity property in
`TauCeti/Analysis/Complex/Conformal/Crosscut/Path.lean`; when its two boundary ends coincide, the
first result below identifies the closure of that crosscut as a Jordan curve, and when they are
distinct the second closes that crosscut up with an arc of the boundary of the image domain. The
coincident-end specialization is in `TauCeti/Analysis/Complex/Conformal/Crosscut/Jordan.lean` and
the distinct-end one in `TauCeti/Analysis/Complex/Conformal/Crosscut/Arc.lean`.
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X] [T2Space X] {x : X}

/-- **The range of a simple closed path is a Jordan curve.** Let `γ : Path x x` be a closed path.
If equality `γ s = γ t` forces either `s = t` or the unordered pair of parameters to be `{0, 1}`,
then `range γ` is homeomorphic to the circle.

The disjunction records both orientations of the exceptional endpoint pair explicitly. No local
injectivity or embedding hypothesis is needed, and no separation assumption on the ambient space
beyond the Hausdorffness that `TauCeti.isJordanCurve_image_Icc` asks for. -/
theorem isJordanCurve_range_of_eq_or_eq_endpoints (γ : Path x x)
    (hγ : ∀ ⦃s t : unitInterval⦄, γ s = γ t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    IsJordanCurve (range γ) := by
  -- Representatives in `[0, 1)` cannot form the exceptional endpoint pair.
  have hinj : InjOn γ.extend (Ico 0 1) := by
    intro s hs t ht hst
    rw [γ.extend_extends' ⟨s, hs.1, hs.2.le⟩, γ.extend_extends' ⟨t, ht.1, ht.2.le⟩] at hst
    rcases hγ hst with hst | hends | hends
    · exact congrArg Subtype.val hst
    · exact absurd (congrArg Subtype.val hends.2) ht.2.ne
    · exact absurd (congrArg Subtype.val hends.1) hs.2.ne
  rw [← γ.image_extend_of_subset subset_rfl]
  exact isJordanCurve_image_Icc zero_lt_one γ.continuous_extend.continuousOn (by simp) hinj

/-! ### Gluing two arcs along their endpoints -/

omit [T2Space X] in
/-- **A value shared by two arcs with the same endpoints is attained at a shared parameter.** If
the ranges of `γ δ : Path x y` meet exactly in `{x, y}`, then `γ a = δ b` forces both parameters to
be `0` or both to be `1`.

The shared value lies in `range γ ∩ range δ = {x, y}`, and injectivity of each path identifies the
parameter at which it takes the endpoint value. -/
private theorem eq_zero_and_eq_zero_or_eq_one_and_eq_one_of_apply_eq {y : X} {γ δ : Path x y}
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hmeet : range γ ∩ range δ = {x, y}) {a b : unitInterval} (hab : γ a = δ b) :
    (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  have hmem : γ a ∈ ({x, y} : Set X) :=
    hmeet ▸ ⟨mem_range_self a, hab ▸ mem_range_self b⟩
  rcases hmem with h | h
  · exact Or.inl ⟨hγ (h.trans γ.source.symm), hδ (hab.symm.trans (h.trans δ.source.symm))⟩
  · exact Or.inr ⟨hγ (h.trans γ.target.symm), hδ (hab.symm.trans (h.trans δ.target.symm))⟩

/-- **Two arcs meeting exactly at their common endpoints glue to a Jordan curve.** Let
`γ δ : Path x y` be injective and let their ranges meet in exactly the two endpoints,
`range γ ∩ range δ = {x, y}`. Then `range γ ∪ range δ` is a Jordan curve.

The curve traversed is `γ.trans δ.symm`, a closed path at `x` whose range is `range γ ∪ range δ`
by `Path.trans_range` and `Path.symm_range`. Its only repetitions are the ones
`TauCeti.isJordanCurve_range_of_eq_or_eq_endpoints` allows: a coincidence between two parameters on
the same half is excluded by injectivity of that half, and one between the two halves lands in
`{x, y}`, so it is either the pair `{0, 1}` of endpoint parameters or the single parameter `1 / 2`
at which the two halves are joined.

Distinctness of `x` and `y` is a consequence rather than a hypothesis: `δ 0 = δ 1` would contradict
injectivity of `δ`. -/
theorem isJordanCurve_range_union_range_of_inter_eq_pair {y : X} {γ δ : Path x y}
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hmeet : range γ ∩ range δ = {x, y}) :
    IsJordanCurve (range γ ∪ range δ) := by
  have hrange : range (γ.trans δ.symm) = range γ ∪ range δ := by
    rw [Path.trans_range, Path.symm_range]
  rw [← hrange]
  refine isJordanCurve_range_of_eq_or_eq_endpoints _ fun s t hst => ?_
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · -- Both parameters on the first half: injectivity of `γ`.
    have h : (2 : ℝ) * s = 2 * t := congrArg Subtype.val (hγ hst)
    exact Or.inl (Subtype.ext (show (s : ℝ) = (t : ℝ) by linarith))
  · -- The first parameter on `γ`, the second on `δ` read backwards.
    simp only [Path.symm_apply, Function.comp_apply] at hst
    rcases eq_zero_and_eq_zero_or_eq_one_and_eq_one_of_apply_eq hγ hδ hmeet hst with ⟨ha, hb⟩ | h
    · have h1 : (2 : ℝ) * s = 0 := congrArg Subtype.val ha
      have h2 : 1 - (2 * (t : ℝ) - 1) = 0 := congrArg Subtype.val hb
      exact Or.inr (Or.inl ⟨Subtype.ext (show (s : ℝ) = 0 by linarith),
        Subtype.ext (show (t : ℝ) = 1 by linarith)⟩)
    · have _ : (2 : ℝ) * s = 1 := congrArg Subtype.val h.1
      have h2 : 1 - (2 * (t : ℝ) - 1) = 1 := congrArg Subtype.val h.2
      exact Or.inl (Subtype.ext (show (s : ℝ) = (t : ℝ) by linarith))
  · -- The mirror image of the previous case.
    simp only [Path.symm_apply, Function.comp_apply] at hst
    rcases eq_zero_and_eq_zero_or_eq_one_and_eq_one_of_apply_eq hγ hδ hmeet hst.symm with
      ⟨ha, hb⟩ | h
    · have h1 : (2 : ℝ) * t = 0 := congrArg Subtype.val ha
      have h2 : 1 - (2 * (s : ℝ) - 1) = 0 := congrArg Subtype.val hb
      exact Or.inr (Or.inr ⟨Subtype.ext (show (s : ℝ) = 1 by linarith),
        Subtype.ext (show (t : ℝ) = 0 by linarith)⟩)
    · have _ : (2 : ℝ) * t = 1 := congrArg Subtype.val h.1
      have h2 : 1 - (2 * (s : ℝ) - 1) = 1 := congrArg Subtype.val h.2
      exact Or.inl (Subtype.ext (show (s : ℝ) = (t : ℝ) by linarith))
  · -- Both parameters on the second half: injectivity of `δ` read backwards.
    simp only [Path.symm_apply, Function.comp_apply] at hst
    have h : 1 - (2 * (s : ℝ) - 1) = 1 - (2 * (t : ℝ) - 1) := congrArg Subtype.val (hδ hst)
    exact Or.inl (Subtype.ext (show (s : ℝ) = (t : ℝ) by linarith))

end TauCeti
