/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import TauCeti.KnotTheory.Grid.Differential.Square.Zero
public import TauCeti.KnotTheory.Grid.Homology.Basic
public import TauCeti.KnotTheory.Grid.Rectangle.Count
public import TauCeti.KnotTheory.Grid.Rectangle.Swap
public import TauCeti.KnotTheory.Grid.Unknot.Rectangle

/-!
# The fully blocked homology of the three-by-three unknot grid

In the standard unknot grid diagram the `O` markings sit on the diagonal and the `X` markings
one row above it, so the markings a rectangle covers can be read off from its columns alone. A
rectangle whose column arc is the half-open arc `[l, r)` covers the `O` markings of the rows in
`[l, r)` and the `X` markings of the rows in `[l + 1, r]`, so it avoids the markings exactly when
its row arc misses the arc `[l, r]`, which is one row longer than its column arc
(`GridRectangleBetween.avoidsMarkings_unknot_iff` states this column by column).

In grid number three this leaves no freedom at all. Both arcs must be single, the row arc must
be the one row the column arc does not forbid, and the source state is pinned down to the
*subdiagonal* state `GridState.subdiagonal 3`, whose point in each column lies one row below the
diagonal. Conversely every rectangle leaving that state through a pair of cyclically consecutive
columns is fully blocked
(`GridRectangleBetween.avoidsMarkings_unknot_one_iff`). So the fully blocked differential of the
`3 × 3` unknot grid kills all five other grid states and sends the subdiagonal state to the sum
of its three cyclically consecutive column transpositions.

This is the first grid diagram on which the fully blocked differential is nonzero: on grids of
size at most two every square is marked and no rectangle survives. The resulting homology has
`ZMod 2`-dimension `4`, against dimension `2` on the `2 × 2` unknot grid
(`GridDiagram.finrank_fullyBlockedHomology_of_two`). Those are the ranks `2 ^ (N - 1)` of the
`(N - 1)`-fold tensor power of `W = 𝔽 ⊕ 𝔽`, the stabilization factor predicted for an `N`-grid
unknot, so the dependence of the fully blocked theory on the grid number is real. The bigrading
of the homology is not computed here.

## Main results

* `TauCeti.GridDiagram.mem_fullyBlockedRectangles_unknot_one_iff`: in grid number three a
  rectangle is fully blocked exactly when it leaves the subdiagonal state through two cyclically
  consecutive columns.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount_unknot_one_eq_one_iff`: the matrix entries of
  the fully blocked differential of the `3 × 3` unknot grid.
* `TauCeti.GridDiagram.fullyBlockedDifferentialOnGenerator_unknot_one_subdiagonal`: the value of
  the differential on its unique nonzero generator.
* `TauCeti.GridDiagram.fullyBlockedDifferential_unknot_one_ne_zero`: that differential is
  nonzero.
* `TauCeti.GridDiagram.finrank_fullyBlockedHomology_unknot_one`: the fully blocked homology of
  the `3 × 3` unknot grid has dimension four.

## References

The diagram and the fully blocked theory follow Ozsváth--Stipsicz--Szabó, *Grid Homology for
Knots and Links*, Chapters 3 and 4; the rank `2 ^ (N - 1)` expected of the fully blocked
homology of an `N`-grid unknot is the stabilization statement of Chapter 4.6 there.
-/

public section

namespace TauCeti

namespace GridDiagram

/-- A rectangle of the `3 × 3` unknot grid is fully blocked exactly when it leaves the
subdiagonal state and its two side columns are cyclically consecutive: emptiness is then
automatic, there being no column strictly between them. -/
theorem mem_fullyBlockedRectangles_unknot_one_iff {x y : GridState 3}
    (R : GridRectangleBetween x y) :
    R ∈ (unknot 1).fullyBlockedRectangles x y ↔
      x = GridState.subdiagonal 3 ∧ R.right = R.left + 1 := by
  rw [mem_fullyBlockedRectangles, R.avoidsMarkings_unknot_one_iff]
  exact ⟨And.right, fun h =>
    ⟨R.isEmpty_of_right_eq_finRotate (by rw [h.2, finRotate_apply]), h⟩⟩

/-- Each of the three cyclically consecutive column transpositions of the subdiagonal state is
joined to it by exactly one fully blocked rectangle of the `3 × 3` unknot grid. -/
theorem fullyBlockedRectangleCount_unknot_one_subdiagonal (l : Fin 3) :
    (unknot 1).fullyBlockedRectangleCount (GridState.subdiagonal 3)
        ((GridState.subdiagonal 3).swapColumns l (l + 1)) = 1 := by
  have hne : ∀ l : Fin 3, l ≠ l + 1 ∧ l ≠ l + 1 + 1 := by decide
  set x := GridState.subdiagonal 3 with hx
  set R := GridRectangleBetween.ofSwapColumns x (x.swapColumns l (l + 1)) l (l + 1)
    (hne l).1 rfl with hRdef
  have hleft : R.left = l := by rw [hRdef]; simp
  have hright : R.right = l + 1 := by rw [hRdef]; simp
  have hmem : R ∈ (unknot 1).fullyBlockedRectangles x (x.swapColumns l (l + 1)) :=
    (mem_fullyBlockedRectangles_unknot_one_iff R).mpr ⟨hx, by rw [hleft, hright]⟩
  have hsingle : (unknot 1).fullyBlockedRectangles x (x.swapColumns l (l + 1)) = {R} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun S hS => by
      have hSr := ((mem_fullyBlockedRectangles_unknot_one_iff S).mp hS).2
      rcases R.eq_or_eq_swapSides S with h | h
      · exact h
      · rw [h, GridRectangleBetween.swapSides_left, GridRectangleBetween.swapSides_right,
          hleft, hright] at hSr
        exact absurd hSr (hne l).2
    ⟩
  rw [fullyBlockedRectangleCount_def, hsingle, Finset.card_singleton, Nat.cast_one]

/-- The `3 × 3` unknot grid has no fully blocked rectangle except from the subdiagonal state to
one of its cyclically consecutive column transpositions. -/
theorem fullyBlockedRectangles_unknot_one_eq_empty {x y : GridState 3}
    (h : ¬ (x = GridState.subdiagonal 3 ∧ ∃ l : Fin 3, y = x.swapColumns l (l + 1))) :
    (unknot 1).fullyBlockedRectangles x y = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun R hR => h ?_
  obtain ⟨hx, hr⟩ := (mem_fullyBlockedRectangles_unknot_one_iff R).mp hR
  exact ⟨hx, R.left, hr ▸ R.target_eq_swapColumns⟩

/-- The matrix entries of the fully blocked differential of the `3 × 3` unknot grid: the entry
from `x` to `y` is one exactly when `x` is the subdiagonal state and `y` is obtained from it by
exchanging two cyclically consecutive columns. -/
theorem fullyBlockedRectangleCount_unknot_one_eq_one_iff (x y : GridState 3) :
    (unknot 1).fullyBlockedRectangleCount x y = 1 ↔
      x = GridState.subdiagonal 3 ∧ ∃ l : Fin 3, y = x.swapColumns l (l + 1) := by
  refine ⟨fun h1 => by_contra fun h => ?_, ?_⟩
  · rw [fullyBlockedRectangleCount_def, fullyBlockedRectangles_unknot_one_eq_empty h] at h1
    simp at h1
  · rintro ⟨rfl, l, rfl⟩
    exact fullyBlockedRectangleCount_unknot_one_subdiagonal l

/-- The fully blocked differential of the `3 × 3` unknot grid kills every grid state other than
the subdiagonal one. -/
theorem fullyBlockedDifferentialOnGenerator_unknot_one_eq_zero {x : GridState 3}
    (hx : x ≠ GridState.subdiagonal 3) :
    (unknot 1).fullyBlockedDifferentialOnGenerator x = 0 := by
  ext y
  rw [fullyBlockedDifferentialOnGenerator_apply, Finsupp.coe_zero, Pi.zero_apply,
    fullyBlockedRectangleCount_def, fullyBlockedRectangles_unknot_one_eq_empty
      fun h => hx h.1]
  simp

/-- The fully blocked differential of the subdiagonal state of the `3 × 3` unknot grid is the
sum of its three cyclically consecutive column transpositions. -/
theorem fullyBlockedDifferentialOnGenerator_unknot_one_subdiagonal :
    (unknot 1).fullyBlockedDifferentialOnGenerator (GridState.subdiagonal 3) =
      ∑ l : Fin 3, Finsupp.single ((GridState.subdiagonal 3).swapColumns l (l + 1)) 1 := by
  classical
  ext y
  apply (by decide : ∀ a b : ZMod 2, (a = 1 ↔ b = 1) → a = b)
  have hinj : Function.Injective
      (fun l : Fin 3 => (GridState.subdiagonal 3).swapColumns l (l + 1)) := by
    intro l m h
    revert l m
    decide
  have hsum :
      ((∑ l : Fin 3, Finsupp.single ((GridState.subdiagonal 3).swapColumns l (l + 1)) 1) y =
        (1 : ZMod 2) ↔
          ∃ l : Fin 3, y = (GridState.subdiagonal 3).swapColumns l (l + 1)) := by
    by_cases hy : ∃ l : Fin 3, y = (GridState.subdiagonal 3).swapColumns l (l + 1)
    · obtain ⟨l, rfl⟩ := hy
      simp [Finset.sum_apply, Finsupp.single_apply, hinj.eq_iff]
    · have hne : ∀ l : Fin 3, (GridState.subdiagonal 3).swapColumns l (l + 1) ≠ y :=
        fun l h => hy ⟨l, h.symm⟩
      simp [Finset.sum_apply, hne, hy]
  rw [fullyBlockedDifferentialOnGenerator_apply,
    fullyBlockedRectangleCount_unknot_one_eq_one_iff]
  simpa using hsum.symm

/-- The subdiagonal state of the `3 × 3` unknot grid is not a cycle. -/
theorem fullyBlockedDifferentialOnGenerator_unknot_one_subdiagonal_ne_zero :
    (unknot 1).fullyBlockedDifferentialOnGenerator (GridState.subdiagonal 3) ≠ 0 := by
  intro h
  have hy : (unknot 1).fullyBlockedDifferentialOnGenerator (GridState.subdiagonal 3)
      ((GridState.subdiagonal 3).swapColumns 0 1) = 1 := by
    rw [fullyBlockedDifferentialOnGenerator_apply]
    simpa using fullyBlockedRectangleCount_unknot_one_subdiagonal (0 : Fin 3)
  rw [h] at hy
  simp at hy

/-- The fully blocked differential of the `3 × 3` unknot grid is nonzero: the first grid diagram
on which the fully blocked theory sees a rectangle at all. -/
theorem fullyBlockedDifferential_unknot_one_ne_zero :
    (unknot 1).fullyBlockedDifferential ≠ 0 := by
  intro h
  refine fullyBlockedDifferentialOnGenerator_unknot_one_subdiagonal_ne_zero ?_
  rw [← fullyBlockedDifferential_single, h, LinearMap.zero_apply]

/-- The boundaries of the `3 × 3` unknot grid are the multiples of the differential of the
subdiagonal state, the only grid state with a nonzero differential. -/
theorem range_fullyBlockedDifferential_unknot_one :
    LinearMap.range (unknot 1).fullyBlockedDifferential =
      Submodule.span (ZMod 2)
        {(unknot 1).fullyBlockedDifferentialOnGenerator (GridState.subdiagonal 3)} := by
  refine le_antisymm ?_ ?_
  · rw [LinearMap.range_eq_map, ← Finsupp.basisSingleOne.span_eq, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    by_cases hx : x = GridState.subdiagonal 3
    · subst hx
      exact Submodule.subset_span (by simp [Finsupp.coe_basisSingleOne])
    · simp only [Finsupp.coe_basisSingleOne, fullyBlockedDifferential_single,
        fullyBlockedDifferentialOnGenerator_unknot_one_eq_zero hx, SetLike.mem_coe]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨Finsupp.single (GridState.subdiagonal 3) 1, by simp⟩

/-- The coefficient ring `ZMod 2` is a field, which the dimension count below needs. -/
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The fully blocked grid homology of the `3 × 3` unknot grid is four-dimensional: the six grid
states carry a rank-one differential, so five cycles modulo one boundary. This is the rank of
`W ^ ⊗ 2` with `W = 𝔽 ⊕ 𝔽`, the stabilization factor predicted for a grid number three
unknot. -/
theorem finrank_fullyBlockedHomology_unknot_one :
    Module.finrank (ZMod 2) (unknot 1).fullyBlockedHomology = 4 := by
  have hB : Module.finrank (ZMod 2) (LinearMap.range (unknot 1).fullyBlockedDifferential) = 1 := by
    rw [range_fullyBlockedDifferential_unknot_one,
      finrank_span_singleton fullyBlockedDifferentialOnGenerator_unknot_one_subdiagonal_ne_zero]
  have hdim := (unknot 1).finrank_fullyBlockedHomology_add_two_mul_finrank_range
    (unknot 1).fullyBlockedDifferential_comp_self_eq_zero
  rw [hB] at hdim
  norm_num [Nat.factorial] at hdim
  omega

end GridDiagram

end TauCeti
