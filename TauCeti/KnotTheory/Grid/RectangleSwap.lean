/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.KnotTheory.Grid.Rectangle

/-!
# A grid rectangle move is a column transposition

An oriented rectangle `R : GridRectangleBetween x y` records the two side columns at which the
target state `y` differs from the source state `x`: at the initial side column `y` reads the
row `x` uses at the terminal side, and vice versa, while the two states agree away from the two
side columns. That is exactly the effect of swapping the two side columns of `x`, so the target
state is the column transposition `x.swapColumns R.left R.right`.

This file makes that identification precise and draws the point-set consequences: the two
states share all but two of their occupied squares, and each occupied square they do not share
is one of the four corners of the rectangle. The shared squares are exactly the intersection of
the two point sets, which has `n - 2` elements. These are the bookkeeping facts a Maslov or
Alexander grading-change computation across a rectangle rests on, and they let later
`∂² = 0`-style arguments reason about `x` and `y` through a single transposition.

## Main results

* `TauCeti.GridRectangleBetween.target_eq_swapColumns`: the target state of a rectangle is the
  source state with the two side columns swapped.
* `TauCeti.GridRectangleBetween.source_eq_swapColumns`: the symmetric statement recovering the
  source from the target.
* `TauCeti.GridState.mem_pointSet_inter_swapColumns_iff`: a square is shared by a state and
  a column swap exactly when it belongs to the source and avoids the two swapped columns.
* `TauCeti.GridRectangleBetween.mem_pointSet_inter_iff`: the rectangle specialization of the
  preceding column-swap statement.
* `TauCeti.GridRectangleBetween.source_pointSet_eq`,
  `TauCeti.GridRectangleBetween.target_pointSet_eq`: each state's point set is the shared part
  together with its own two corners.
* `TauCeti.GridRectangleBetween.card_pointSet_inter`: the two states share exactly `n - 2`
  squares.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.2, "grading-change formulas across a rectangle", and Lane G.3, "The complexes and
`∂² = 0`". The column-transposition picture of a rectangle move follows Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 4.
-/

namespace TauCeti

namespace GridState

variable {n : ℕ} (x : GridState n) {a b : Fin n}

/-- A square is shared by a grid state and the state with columns `a` and `b` swapped exactly
when it is a source-state square away from the two swapped columns. -/
@[simp]
theorem mem_pointSet_inter_swapColumns_iff (h : a ≠ b) (p : Fin n × Fin n) :
    p ∈ x.pointSet ∩ (x.swapColumns a b).pointSet ↔
      p ∈ x.pointSet ∧ p.1 ≠ a ∧ p.1 ≠ b := by
  rw [Finset.mem_inter, mem_pointSet_swapColumns]
  constructor
  · rintro ⟨hx, hswap⟩
    refine ⟨hx, ?_, ?_⟩
    · rintro hpa
      have hxa : x a = p.2 := by
        simpa [hpa] using (mem_pointSet x p).mp hx
      have hxb : x b = p.2 := by
        simpa [hpa] using (mem_pointSet x (Equiv.swap a b p.1, p.2)).mp hswap
      exact h (x.toPerm.injective (hxa.trans hxb.symm))
    · rintro hpb
      have hxb : x b = p.2 := by
        simpa [hpb] using (mem_pointSet x p).mp hx
      have hxa : x a = p.2 := by
        simpa [hpb] using (mem_pointSet x (Equiv.swap a b p.1, p.2)).mp hswap
      exact h (x.toPerm.injective (hxa.trans hxb.symm))
  · rintro ⟨hx, ha, hb⟩
    refine ⟨hx, ?_⟩
    simpa [Equiv.swap_apply_of_ne_of_ne ha hb] using hx

/-- The point set of a grid state is the shared part with a column swap, together with the two
source-state squares in the swapped columns. -/
theorem pointSet_eq_insert_insert_inter_swapColumns (h : a ≠ b) :
    x.pointSet =
      insert (a, x a) (insert (b, x b) (x.pointSet ∩ (x.swapColumns a b).pointSet)) := by
  ext p
  simp only [Finset.mem_insert]
  constructor
  · intro hx
    rcases eq_or_ne p.1 a with ha | ha
    · refine Or.inl ?_
      have : p.2 = x a := by
        simpa [ha] using ((mem_pointSet x p).mp hx).symm
      exact Prod.ext ha this
    · rcases eq_or_ne p.1 b with hb | hb
      · refine Or.inr (Or.inl ?_)
        have : p.2 = x b := by
          simpa [hb] using ((mem_pointSet x p).mp hx).symm
        exact Prod.ext hb this
      · exact Or.inr (Or.inr ((mem_pointSet_inter_swapColumns_iff x h p).mpr ⟨hx, ha, hb⟩))
  · rintro (rfl | rfl | hp)
    · simp
    · simp
    · exact Finset.mem_of_mem_inter_left hp

/-- The point set after swapping columns `a` and `b` is the shared part with the source state,
together with the two target-state squares in the swapped columns. -/
theorem swapColumns_pointSet_eq_insert_insert_inter (h : a ≠ b) :
    (x.swapColumns a b).pointSet =
      insert (a, x b) (insert (b, x a) (x.pointSet ∩ (x.swapColumns a b).pointSet)) := by
  ext p
  simp only [Finset.mem_insert]
  constructor
  · intro hp
    rcases eq_or_ne p.1 a with ha | ha
    · refine Or.inl ?_
      have : p.2 = x b := by
        simpa [ha] using ((mem_pointSet (x.swapColumns a b) p).mp hp).symm
      exact Prod.ext ha this
    · rcases eq_or_ne p.1 b with hb | hb
      · refine Or.inr (Or.inl ?_)
        have : p.2 = x a := by
          simpa [hb] using ((mem_pointSet (x.swapColumns a b) p).mp hp).symm
        exact Prod.ext hb this
      · refine Or.inr (Or.inr ?_)
        have hx : p ∈ x.pointSet := by
          rw [mem_pointSet] at hp ⊢
          rw [swapColumns_apply, Equiv.swap_apply_of_ne_of_ne ha hb] at hp
          exact hp
        exact (mem_pointSet_inter_swapColumns_iff x h p).mpr ⟨hx, ha, hb⟩
  · rintro (rfl | rfl | hp)
    · simp
    · simp
    · exact Finset.mem_of_mem_inter_right hp

/-- The source-state square in column `a` is not shared with the state whose columns `a` and
`b` have been swapped. -/
theorem left_notMem_pointSet_inter_swapColumns (h : a ≠ b) :
    (a, x a) ∉ x.pointSet ∩ (x.swapColumns a b).pointSet := by
  rw [mem_pointSet_inter_swapColumns_iff x h]
  rintro ⟨_, ha, _⟩
  exact ha rfl

/-- The source-state square in column `b` is not shared with the state whose columns `a` and
`b` have been swapped. -/
theorem right_notMem_pointSet_inter_swapColumns (h : a ≠ b) :
    (b, x b) ∉ x.pointSet ∩ (x.swapColumns a b).pointSet := by
  rw [mem_pointSet_inter_swapColumns_iff x h]
  rintro ⟨_, _, hb⟩
  exact hb rfl

/-- The target-state square in column `a` after swapping columns `a` and `b` is not shared
with the source state. -/
theorem swapColumns_left_notMem_pointSet_inter (h : a ≠ b) :
    (a, x b) ∉ x.pointSet ∩ (x.swapColumns a b).pointSet := by
  rw [mem_pointSet_inter_swapColumns_iff x h]
  rintro ⟨_, ha, _⟩
  exact ha rfl

/-- The target-state square in column `b` after swapping columns `a` and `b` is not shared
with the source state. -/
theorem swapColumns_right_notMem_pointSet_inter (h : a ≠ b) :
    (b, x a) ∉ x.pointSet ∩ (x.swapColumns a b).pointSet := by
  rw [mem_pointSet_inter_swapColumns_iff x h]
  rintro ⟨_, _, hb⟩
  exact hb rfl

/-- The two source-state squares in the swapped columns are distinct. -/
theorem left_ne_right_pointSet_swapColumns (h : a ≠ b) :
    ((a, x a) : Fin n × Fin n) ≠ (b, x b) := by
  rw [Ne, Prod.mk.injEq, not_and]
  intro hab
  exact absurd hab h

/-- The two target-state squares in the swapped columns are distinct. -/
theorem swapColumns_left_ne_right_pointSet (h : a ≠ b) :
    ((a, x b) : Fin n × Fin n) ≠ (b, x a) := by
  rw [Ne, Prod.mk.injEq, not_and]
  intro hab
  exact absurd hab h

/-- A grid state and a swap of two distinct columns share exactly `n - 2` squares. -/
theorem card_pointSet_inter_swapColumns (h : a ≠ b) :
    (x.pointSet ∩ (x.swapColumns a b).pointSet).card = n - 2 := by
  have hne : (b, x b) ∉ x.pointSet ∩ (x.swapColumns a b).pointSet :=
    right_notMem_pointSet_inter_swapColumns x h
  have hne' :
      (a, x a) ∉ insert (b, x b) (x.pointSet ∩ (x.swapColumns a b).pointSet) := by
    rw [Finset.mem_insert]
    rintro (hab | ha)
    · exact left_ne_right_pointSet_swapColumns x h hab
    · exact left_notMem_pointSet_inter_swapColumns x h ha
  have hcard := congrArg Finset.card (pointSet_eq_insert_insert_inter_swapColumns x h)
  rw [card_pointSet, Finset.card_insert_of_notMem hne',
    Finset.card_insert_of_notMem hne] at hcard
  omega

end GridState

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n} (R : GridRectangleBetween x y)

/-- Pointwise form of the column-transposition identity: at each column the target state reads
the row the source state reads at the swapped column. -/
theorem target_apply (c : Fin n) : y c = x (Equiv.swap R.left R.right c) := by
  rcases eq_or_ne c R.left with h | hl
  · subst h
    rw [Equiv.swap_apply_left]
    exact R.map_left
  · rcases eq_or_ne c R.right with h | hr
    · subst h
      rw [Equiv.swap_apply_right]
      exact R.map_right
    · rw [Equiv.swap_apply_of_ne_of_ne hl hr]
      exact R.map_of_ne c hl hr

/-- The target state of an oriented rectangle is the source state with its two side columns
swapped. The rectangle's defining equations -- the two side columns exchange their rows and the
other columns are unchanged -- are precisely the action of the column transposition. -/
theorem target_eq_swapColumns : y = x.swapColumns R.left R.right := by
  refine GridState.ext fun c => ?_
  rw [GridState.swapColumns_apply]
  exact target_apply R c

/-- The source state of an oriented rectangle is the target state with its two side columns
swapped: swapping the same pair of columns twice is the identity. -/
theorem source_eq_swapColumns : x = y.swapColumns R.left R.right := by
  refine GridState.ext fun c => ?_
  rw [GridState.swapColumns_apply]
  have h := target_apply R (Equiv.swap R.left R.right c)
  rw [Equiv.swap_apply_self] at h
  exact h.symm

/-- The underlying permutation of the target state is the source permutation precomposed with
the transposition of the two side columns. -/
theorem target_toPerm_eq :
    y.toPerm = (Equiv.swap R.left R.right).trans x.toPerm := by
  refine Equiv.ext fun c => ?_
  rw [Equiv.trans_apply]
  exact target_apply R c

/-- A square lies in the target state exactly when its column-transposed square lies in the
source state. -/
theorem mem_target_pointSet_iff (p : Fin n × Fin n) :
    p ∈ y.pointSet ↔ (Equiv.swap R.left R.right p.1, p.2) ∈ x.pointSet := by
  rw [GridState.mem_pointSet, GridState.mk_mem_pointSet, target_apply R p.1]

/-- The two side columns carry the four corners of a rectangle, so a square that the two states
share must avoid both side columns. Conversely, away from the side columns the two states agree,
so every source square off the side columns is shared. -/
theorem mem_pointSet_inter_iff (p : Fin n × Fin n) :
    p ∈ x.pointSet ∩ y.pointSet ↔
      p ∈ x.pointSet ∧ p.1 ≠ R.left ∧ p.1 ≠ R.right := by
  simpa [target_eq_swapColumns R] using
    GridState.mem_pointSet_inter_swapColumns_iff x R.left_ne_right p

/-- The lower-left corner is not shared with the target state: it sits on a side column. -/
theorem left_bottom_notMem_inter :
    (R.left, R.bottom) ∉ x.pointSet ∩ y.pointSet := by
  rw [mem_pointSet_inter_iff R]
  rintro ⟨_, hleft, _⟩
  exact hleft rfl

/-- The upper-right corner is not shared with the target state: it sits on a side column. -/
theorem right_top_notMem_inter :
    (R.right, R.top) ∉ x.pointSet ∩ y.pointSet := by
  rw [mem_pointSet_inter_iff R]
  rintro ⟨_, _, hright⟩
  exact hright rfl

/-- The two corners of the source state are distinct. -/
theorem left_bottom_ne_right_top :
    ((R.left, R.bottom) : Fin n × Fin n) ≠ (R.right, R.top) := by
  rw [Ne, Prod.mk.injEq, not_and]
  intro h
  exact absurd h R.left_ne_right

/-- The upper-left target corner is not shared with the source state: it sits on a side column. -/
theorem left_top_notMem_inter :
    (R.left, R.top) ∉ x.pointSet ∩ y.pointSet := by
  rw [mem_pointSet_inter_iff R]
  rintro ⟨_, hleft, _⟩
  exact hleft rfl

/-- The lower-right target corner is not shared with the source state: it sits on a side column. -/
theorem right_bottom_notMem_inter :
    (R.right, R.bottom) ∉ x.pointSet ∩ y.pointSet := by
  rw [mem_pointSet_inter_iff R]
  rintro ⟨_, _, hright⟩
  exact hright rfl

/-- The two corners of the target state are distinct. -/
theorem left_top_ne_right_bottom :
    ((R.left, R.top) : Fin n × Fin n) ≠ (R.right, R.bottom) := by
  rw [Ne, Prod.mk.injEq, not_and]
  intro h
  exact absurd h R.left_ne_right

/-- The source state's point set is its shared intersection with the target point set together
with the two source corners `(R.left, R.bottom)` and `(R.right, R.top)`. -/
theorem source_pointSet_eq :
    x.pointSet =
      insert (R.left, R.bottom) (insert (R.right, R.top) (x.pointSet ∩ y.pointSet)) := by
  simpa [target_eq_swapColumns R, bottom, top] using
    GridState.pointSet_eq_insert_insert_inter_swapColumns x R.left_ne_right

/-- The target state's point set is the shared part together with its own two corners. -/
theorem target_pointSet_eq :
    y.pointSet =
      insert (R.left, R.top) (insert (R.right, R.bottom) (x.pointSet ∩ y.pointSet)) := by
  simpa [target_eq_swapColumns R, bottom, top] using
    GridState.swapColumns_pointSet_eq_insert_insert_inter x R.left_ne_right

include R in
/-- The source and target states share exactly `n - 2` squares: all of the source's `n` squares
except its two corners. -/
theorem card_pointSet_inter : (x.pointSet ∩ y.pointSet).card = n - 2 := by
  simpa [target_eq_swapColumns R] using
    GridState.card_pointSet_inter_swapColumns x R.left_ne_right

end GridRectangleBetween

end TauCeti
