/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Glue
public import TauCeti.Combinatorics.PlanarMatching.TLDiagram
import all TauCeti.Combinatorics.PlanarMatching.Glue

/-!
# Composing Temperley–Lieb diagrams

Two Temperley–Lieb diagrams `f : n → m` and `g : m → p` are composed by stacking `g` on top of
`f`, gluing the top boundary of `f` to the bottom boundary of `g`. This file builds the composite
`TauCeti.TLDiagram.comp f g : TLDiagram n p` out of the operations on planar matchings of
`TauCeti.Combinatorics.PlanarMatching.Glue`.

In the counterclockwise numbering, the boundary of `f` reads its bottom points from left to right,
then its top points from right to left, and likewise for `g`. So in the juxtaposition
`TauCeti.PlanarMatching.append f.matching g.matching` the top points of `f` and the bottom points
of `g` meet in the middle, nested around the junction: the leftmost top point of `f` and the
leftmost bottom point of `g` are consecutive, the next two enclose them, and so on. Gluing the
middle boundary is contracting the junction pair `m` times (`TauCeti.PlanarMatching.glueMiddle`),
counting the circles closed on the way (`TauCeti.PlanarMatching.glueMiddleCircles`). The composite
keeps the circles of both diagrams and adds these new ones. With this convention `cup ≫ cap` is a
single circle and `cap ≫ cup` is the generator `e₁ : 2 → 2`, and the identity diagrams are units.

## Main definitions

* `TauCeti.TLDiagram.comp f g`: the composite of `f : n → m` and `g : m → p`, with `g` stacked on
  top of `f`.

## Main results

* `TauCeti.TLDiagram.comp_id`, `TauCeti.TLDiagram.id_comp`: the identity diagrams are units for
  composition.
* `TauCeti.TLDiagram.cup_comp_cap`, `TauCeti.TLDiagram.cap_comp_cup_matching_val`: a cup followed
  by a cap is one circle, and a cap followed by a cup has the matching of `e₁`.

## Implementation notes

The explicit composites are computed through the partner numbers of the boundary points, using
the private index arithmetic of `TauCeti.Combinatorics.PlanarMatching.Glue`, which this file
imports with `import all`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
-/

public section

open Equiv

namespace TauCeti

namespace TLDiagram

variable {n m p : ℕ}

/-- **Composition of Temperley–Lieb diagrams**: `f.comp g`, the composite `f ≫ g` in the
convention where `g` is drawn above `f`, stacks `g : m → p` on top of `f : n → m` and glues the top
boundary of `f` to the bottom boundary of `g`. Its matching is obtained from the juxtaposition of
the two matchings by contracting the `m` pairs of glued points, and its circles are those of `f`,
those of `g`, and those closed up in the middle. -/
def comp (f : TLDiagram n m) (g : TLDiagram m p) : TLDiagram n p where
  matching := PlanarMatching.glueMiddle m (f.matching.append g.matching)
  circles := f.circles + g.circles +
    PlanarMatching.glueMiddleCircles m (f.matching.append g.matching)

/-- The matching of a composite: the juxtaposed matchings, glued across the middle. -/
@[simp]
theorem matching_comp (f : TLDiagram n m) (g : TLDiagram m p) :
    (f.comp g).matching = PlanarMatching.glueMiddle m (f.matching.append g.matching) := (rfl)

/-- The circles of a composite: those of both factors, and those closed up in the middle. -/
@[simp]
theorem circles_comp (f : TLDiagram n m) (g : TLDiagram m p) :
    (f.comp g).circles = f.circles + g.circles +
      PlanarMatching.glueMiddleCircles m (f.matching.append g.matching) := (rfl)

/-- The identity diagram is a right unit for composition. -/
@[simp]
theorem comp_id (f : TLDiagram n m) : f.comp (id m) = f := by
  ext : 1
  · rw [matching_comp, matching_id, PlanarMatching.glueMiddle_append_nested]
  · rw [circles_comp, matching_id, PlanarMatching.glueMiddleCircles_append_nested, circles_id,
      add_zero, add_zero]

/-- The identity diagram is a left unit for composition. -/
@[simp]
theorem id_comp (f : TLDiagram n m) : (id n).comp f = f := by
  ext : 1
  · rw [matching_comp, matching_id, PlanarMatching.glueMiddle_nested_append]
  · rw [circles_comp, matching_id, PlanarMatching.glueMiddleCircles_nested_append, circles_id,
      zero_add, add_zero]

private theorem val_mk_eq_mk_iff {K : ℕ} (x : PlanarMatching K) {q r : ℕ} (hq : q < K)
    (hr : r < K) : x.1.val ⟨q, hq⟩ = ⟨r, hr⟩ ↔ PlanarMatching.pv x q = r := by
  rw [PlanarMatching.pv_of_lt x hq, Fin.ext_iff]

private theorem pv_cup_matching {q : ℕ} (hq : q < 2) :
    PlanarMatching.pv cup.matching q = 1 - q := by
  rw [PlanarMatching.pv_of_lt _ hq, cup_matching_val]
  rcases q with _ | _ | q
  · rfl
  · rfl
  · omega

private theorem pv_cap_matching {q : ℕ} (hq : q < 2) :
    PlanarMatching.pv cap.matching q = 1 - q := by
  rw [PlanarMatching.pv_of_lt _ hq, cap_matching_val]
  rcases q with _ | _ | q
  · rfl
  · rfl
  · omega

/-- **A cup followed by a cap is a closed circle**: the composite `cup ≫ cap : 0 → 0` is the empty
diagram with one circle. -/
theorem cup_comp_cap : cup.comp cap = ⟨(id 0).matching, 1⟩ := by
  ext : 1
  · exact PlanarMatching.ext fun a => a.elim0
  rw [circles_comp, circles_cup, circles_cap, PlanarMatching.glueMiddleCircles_succ,
    PlanarMatching.glueMiddleCircles_succ, PlanarMatching.glueMiddleCircles_zero]
  simp only [val_mk_eq_mk_iff, PlanarMatching.pv_cast]
  simp [PlanarMatching.pv_contract, PlanarMatching.skipN, PlanarMatching.joinN,
    PlanarMatching.unskipN, PlanarMatching.pv_append_left, PlanarMatching.pv_append_right,
    pv_cup_matching, pv_cap_matching]

/-- **A cap followed by a cup** has the matching of the diagram `e₁ : 2 → 2`, joining the two
bottom points and the two top points. -/
theorem cap_comp_cup_matching_val : (cap.comp cup).matching.1.val = swap 0 1 * swap 2 3 := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [← PlanarMatching.pv_coe, matching_comp, PlanarMatching.glueMiddle_zero,
    PlanarMatching.pv_cast]
  fin_cases i <;>
    simp [PlanarMatching.pv_append_left, PlanarMatching.pv_append_right, pv_cup_matching,
      pv_cap_matching, swap_apply_of_ne_of_ne]

end TLDiagram

/-- Composing `e₁ = cap ≫ cup` with itself gives `e₁` again, with one circle closed in the
middle. -/
example : (TLDiagram.cap.comp TLDiagram.cup).comp (TLDiagram.cap.comp TLDiagram.cup) =
    ⟨(TLDiagram.cap.comp TLDiagram.cup).matching, 1⟩ := by
  ext : 1
  · refine PlanarMatching.ext fun i => Fin.ext ?_
    rw [← PlanarMatching.pv_coe, ← PlanarMatching.pv_coe, TLDiagram.matching_comp,
      PlanarMatching.glueMiddle_succ, PlanarMatching.glueMiddle_succ,
      PlanarMatching.glueMiddle_zero]
    fin_cases i <;>
      simp [PlanarMatching.pv_contract, PlanarMatching.skipN, PlanarMatching.joinN,
        PlanarMatching.unskipN, PlanarMatching.pv_append_left, PlanarMatching.pv_append_right,
        TLDiagram.pv_cup_matching, TLDiagram.pv_cap_matching]
  · rw [TLDiagram.circles_comp, TLDiagram.circles_comp, TLDiagram.circles_cap,
      TLDiagram.circles_cup, PlanarMatching.glueMiddleCircles_zero,
      PlanarMatching.glueMiddleCircles_succ, PlanarMatching.glueMiddleCircles_succ,
      PlanarMatching.glueMiddleCircles_zero]
    simp only [TLDiagram.val_mk_eq_mk_iff, PlanarMatching.pv_cast]
    simp [PlanarMatching.pv_contract, PlanarMatching.skipN, PlanarMatching.joinN,
      PlanarMatching.unskipN, PlanarMatching.pv_append_left, PlanarMatching.pv_append_right,
      TLDiagram.pv_cup_matching, TLDiagram.pv_cap_matching]

end TauCeti
