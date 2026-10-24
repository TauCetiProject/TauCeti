/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Components
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Basic
public import TauCeti.KnotTheory.Grid.Grading.MarkingCount
public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain
public import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Grading changes across grid commutation pentagons

Let `C` be a column turn (`GridDiagram.ColumnTurn`) of a grid diagram `G`, exchanging the column
`a = C.column` with the next column `b = finRotate n a` and turning in the square row
`s = C.turnRow`, and let `G'` be the diagram `G.swapColumns a b`. The pentagon map
`Φ : GC⁻(G) → GC⁻(G')` (`GridDiagram.pentagonMap`) sends a state `x` to the sum, over the empty
pentagons `P` from `x` carrying no `X`-marking and turning on their terminal side, of
`V^{𝕆 ∩ P} · y` with `y` the target of `P`. This file proves the state-grading formulas for
pentagons turning on either side. `Grading/Map.lean` uses them to prove that both parts and the
full commutation map `GridDiagram.commutationMap` are homogeneous for the (`O`-Maslov, Alexander)
bigrading of `Grading/Unblocked/Chain.lean`, of the bidegree `GridDiagram.commutationBidegree C`
defined here.

The grid states of `G` and `G'` are the same permutations, and the comparison rests on two
grading formulas.

* **Changing the diagram.** Exchanging the two markings of the adjacent columns `a` and `b`
  changes the `O`-Maslov grading of a fixed state `x` by `±1`
  (`GridDiagram.maslovOℤ_swapColumns_finRotate`). It rises by one exactly when the point of `x`
  on the grid line between the two columns lies on one of the lines `G.O a + 1, …, G.O b`, which
  the two `O`-markings pass when they trade columns.
* **Following a pentagon.** For every empty pentagon `P` from `x` to `y`,
  `M_O'(y) = M_O(x) + 2 #(𝕆 ∩ P)` (`GridDiagram.maslovOℤ_swapColumns_of_isEmpty`), and likewise
  `M_X'(y) = M_X(x) + 2 #(𝕏 ∩ P)` (`GridDiagram.maslovXℤ_swapColumns_of_isEmpty`), counting the
  markings of `G` that `P` carries and writing `M_O'`, `M_X'` for the gradings of `G'`, up to a
  correction `-2` when `s` lies strictly between the two `O`-markings, respectively `X`-markings,
  of the columns `b` and `a`, going up.

The correction is the bookkeeping of the cut at the turn row: the pentagon carries a marking of
column `a` exactly when it lies above `s` and one of column `b` exactly when it lies below `s`.
For a column commutation, whose markings lie in the bigons below and above the turn, the
corrections vanish (`GridDiagram.ColumnCommutationData.commutationBidegree_eq_zero`). When the
two marking segments interleave they need not, which is the source of the nonzero bidegrees of
the crossing change maps in `TauCeti.KnotTheory.Grid.CrossingChange.Grading`.

A counted pentagon carries no `X`-marking, so it changes `M_X` only by the correction and raises
the Alexander grading by the number of `O`-markings it carries plus the Alexander component of
`GridDiagram.commutationBidegree C` (`GridDiagram.alexanderTwoℤ_swapColumns_of_mem_pentagons` and
`OddComponentGridDiagram.alexanderℤ_swapColumns_of_mem_pentagons`). Since every variable has
bidegree `(-2, -1)`, each term `V^{𝕆 ∩ P} · y` of `Φ(x)` has the bidegree of `x` plus
`GridDiagram.commutationBidegree C`.

## Main definitions

* `TauCeti.GridDiagram.commutationBidegree`: the bidegree of the pentagon maps of a column turn.
* `TauCeti.OddComponentGridDiagram.swapColumns`: the diagram with the two columns of a column
  turn exchanged, again with an odd number of components.

## Main results

* `TauCeti.GridDiagram.maslovOℤ_swapColumns_finRotate`: the `O`-Maslov grading of a state under
  an exchange of two adjacent columns of the diagram.
* `TauCeti.GridDiagram.ColumnCommutationData.commutationBidegree_eq_zero`: the turn of a column
  commutation has bidegree zero.
* `TauCeti.GridDiagram.maslovOℤ_swapColumns_of_isEmpty`,
  `TauCeti.GridDiagram.maslovXℤ_swapColumns_of_isEmpty`: the two Maslov gradings across an empty
  pentagon.
* `TauCeti.GridDiagram.maslovOℤ_swapColumns_initialPentagon_of_isEmpty`,
  `TauCeti.GridDiagram.maslovXℤ_swapColumns_initialPentagon_of_isEmpty`: the Maslov grading changes
  across an empty initial-side pentagon.
* `TauCeti.OddComponentGridDiagram.alexanderℤ_swapColumns_of_mem_initialPentagons`: the
  Alexander grading change across a counted initial-side pentagon.
* `TauCeti.OddComponentGridDiagram.alexanderℤ_swapColumns_of_mem_pentagons`: the Alexander
  grading across a counted pentagon.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical
  Surveys and Monographs 208, 2015, Section 5.1, where the pentagon map of a commutation is shown
  to preserve the Maslov and Alexander gradings, and Section 6.1 for the crossing change maps.
* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 3.1 (arXiv:math/0610559).
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ}

/-! ### Cyclic bookkeeping at the turn of a pentagon -/

/-- The grid line `s` lies in the band of lines `α + 1, …, β` unless it is the line `α` or lies
strictly between `β` and `α` going up: the band is the complement of the lines `β + 1, …, α`. -/
private theorem ite_mem_cIco_finRotate_eq {s α β : Fin n} (hαβ : α ≠ β) :
    (if s ∈ Grid.cIco (finRotate n α) (finRotate n β) then 1 else 0 : ℤ) =
      1 - (if α = s then 1 else 0) - if s ∈ Grid.cIoo β α then 1 else 0 := by
  have hband := Grid.mem_cIco_finRotate_iff_mem_insert_cIoo (x := s) hαβ
  have hαα : α ∉ Grid.cIoo β α := Grid.right_notMem_cIoo β α
  have hα : α ∉ insert β (Grid.cIoo α β) := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hαβ, Grid.left_notMem_cIoo α β⟩
  by_cases hsα : α = s
  · subst hsα
    simp only [mt hband.mp hα, hαα, ite_true, ite_false]
    ring
  by_cases hs : s ∈ Grid.cIoo β α
  · have hs' : s ∉ insert β (Grid.cIoo α β) := by
      rw [Finset.mem_insert]
      rintro (rfl | h)
      · exact Grid.left_notMem_cIoo _ _ hs
      · exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap α β) h hs
    simp only [mt hband.mp hs', hsα, hs, ite_true, ite_false]
    ring
  · have hs' : s ∈ insert β (Grid.cIoo α β) := by
      rcases (Grid.not_mem_cIoo_iff hαβ.symm).mp hs with h | h | h
      · exact h ▸ Finset.mem_insert_self _ _
      · exact absurd h.symm hsα
      · exact Finset.mem_insert_of_mem h
    simp only [hband.mpr hs', hsα, hs, ite_true, ite_false]
    ring

/-- The cyclic bookkeeping of a pentagon at the replaced grid line. The pentagon's terminal side
runs from row `B` up to row `T`, through the turn row `s`, and `α ≠ β` are the square rows of two
markings next to the line. The total vanishes unless `s` lies strictly between `β` and `α` going
up, which never happens when `α` and `β` lie in the two bigons below and above the turn of a
column commutation. -/
private theorem pentagon_ite_identity {B T s α β : Fin n} (hs : s ∈ Grid.cIco B T)
    (hαβ : α ≠ β) :
    (if T ∈ Grid.cIco (finRotate n α) (finRotate n β) then 1 else -1 : ℤ) - 1 +
      2 * ((if β ∈ Grid.cIco B T then 1 else 0) - (if α ∈ Grid.cIoo s T then 1 else 0) -
        (if β ∈ Grid.cIco B s then 1 else 0)) =
      -2 * if s ∈ Grid.cIoo β α then 1 else 0 := by
  have hsT : s ≠ T := fun h => Grid.right_notMem_cIco B T (h ▸ hs)
  have hcross := Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco_finRotate hsT hαβ
  have hline := ite_mem_cIco_finRotate_eq (s := s) hαβ
  have hα₁ := congrArg (Nat.cast : ℕ → ℤ) (Grid.ite_mem_cIco_eq_add_add (Grid.left_mem_cIco hsT) α)
  have hβ₁ := congrArg (Nat.cast : ℕ → ℤ) (Grid.ite_mem_cIco_eq_add_add (Grid.left_mem_cIco hsT) β)
  have hβ₂ := congrArg (Nat.cast : ℕ → ℤ) (Grid.ite_mem_cIco_eq_add_add hs β)
  simp only [Grid.cIco_self, Finset.notMem_empty, ite_false, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, zero_add] at hα₁ hβ₁ hβ₂
  have hT : (if T ∈ Grid.cIco (finRotate n α) (finRotate n β) then 1 else -1 : ℤ) =
      2 * (if T ∈ Grid.cIco (finRotate n α) (finRotate n β) then 1 else 0) - 1 := by
    split_ifs <;> norm_num
  rw [hT]
  linarith

/-- If the square rows `α ≠ β` lie in the two bigons below and above the turn row `s`, going up
from `s` first `β` is reached, at the latest at the other turn row `t`, and then `α`, at the
latest back at `s`. So `s` does not lie strictly between `β` and `α`. -/
private theorem notMem_cIoo_of_mem_insert_cIco {s t α β : Fin n}
    (hα : α ∈ insert s (Grid.cIco t s)) (hβ : β ∈ insert t (Grid.cIco s t)) :
    s ∉ Grid.cIoo β α := by
  simp only [Finset.mem_insert, Grid.mem_cIco, Grid.mem_cIoo, ne_eq, ← Fin.val_inj] at hα hβ ⊢
  split_ifs at hα hβ ⊢ <;> omega

/-! ### The `O`-Maslov grading under an adjacent column swap -/

/-- The number of `O`-markings in a set of squares, as a sum over the columns. -/
private theorem card_OSet_inter_eq_sum (G : GridDiagram n) (S : Finset (Fin n × Fin n)) :
    ((G.OSet ∩ S).card : ℤ) = ∑ c, if (c, G.O c) ∈ S then 1 else 0 := by
  classical
  have hcols : G.OColumnsOfSquares S = Finset.univ.filter fun c => (c, G.O c) ∈ S := by
    ext c
    simp
  rw [← G.card_OColumnsOfSquares, hcols, Finset.card_filter]
  push_cast
  rfl

/-- Swapping two columns of the diagram changes the difference of the `O`-Maslov gradings at the
two ends of a rectangle by twice the change in the number of covered `O`-markings. The rectangle
need not be empty: the count of covered source-state squares is the same in both diagrams. -/
private theorem maslovOℤ_swapColumns_sub_sub (G : GridDiagram n) (a b : Fin n) {x y : GridState n}
    (R : GridRectangleBetween x y) :
    ((G.swapColumns a b).maslovOℤ x - G.maslovOℤ x) -
        ((G.swapColumns a b).maslovOℤ y - G.maslovOℤ y) =
      2 * (((G.OSet ∩ R.toGridRectangle.coveredSquares).card : ℤ) -
        ((G.swapColumns a b).OSet ∩ R.toGridRectangle.coveredSquares).card) := by
  have h := G.maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card R
  have h' := (G.swapColumns a b).maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card R
  rw [maslovO_eq_intCast, maslovO_eq_intCast] at h h'
  have hq : ((((G.swapColumns a b).maslovOℤ x - G.maslovOℤ x) -
        ((G.swapColumns a b).maslovOℤ y - G.maslovOℤ y) : ℤ) : ℚ) =
      ((2 * (((G.OSet ∩ R.toGridRectangle.coveredSquares).card : ℤ) -
        ((G.swapColumns a b).OSet ∩ R.toGridRectangle.coveredSquares).card) : ℤ) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast hq

/-- Across the rectangle from `x` to `x.swapColumns i j`, the change in the number of covered
`O`-markings caused by swapping two columns `a` and `b` of the diagram only sees those two
columns. -/
private theorem card_OSet_inter_sub_card_swapColumns_OSet_inter (G : GridDiagram n) {a b : Fin n}
    (hab : a ≠ b) (S : Finset (Fin n × Fin n)) :
    ((G.OSet ∩ S).card : ℤ) - ((G.swapColumns a b).OSet ∩ S).card =
      ((if (a, G.O a) ∈ S then 1 else 0) - if (a, G.O b) ∈ S then 1 else 0) +
        ((if (b, G.O b) ∈ S then 1 else 0) - if (b, G.O a) ∈ S then 1 else 0) := by
  rw [card_OSet_inter_eq_sum, card_OSet_inter_eq_sum, ← Finset.sum_sub_distrib,
    Fintype.sum_eq_add a b hab]
  · simp [GridState.swapColumns_apply]
  · rintro c ⟨hca, hcb⟩
    simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hca hcb]

/-- Exchanging the cyclically adjacent columns `a` and `b = finRotate n a` of the diagram changes
the `O`-Maslov grading of a state `u` and of its column swap `u.swapColumns i j` by amounts that
differ by twice the change in whether the point on the grid line `b` lies on one of the lines
`G.O a + 1, …, G.O b`. -/
private theorem maslovOℤ_swapColumns_sub_sub_swapColumns (G : GridDiagram n) {a : Fin n}
    (ha : a ≠ finRotate n a) (u : GridState n) {i j : Fin n} (hij : i ≠ j) :
    ((G.swapColumns a (finRotate n a)).maslovOℤ u - G.maslovOℤ u) -
        ((G.swapColumns a (finRotate n a)).maslovOℤ (u.swapColumns i j) -
          G.maslovOℤ (u.swapColumns i j)) =
      2 * ((if u (finRotate n a) ∈
            Grid.cIco (finRotate n (G.O a)) (finRotate n (G.O (finRotate n a))) then 1 else 0) -
        if u.swapColumns i j (finRotate n a) ∈
            Grid.cIco (finRotate n (G.O a)) (finRotate n (G.O (finRotate n a))) then 1 else 0) := by
  set b := finRotate n a with hb
  have hOab : G.O a ≠ G.O b := G.O.toPerm.injective.ne ha
  let R := GridRectangleBetween.ofSwapColumns u (u.swapColumns i j) i j hij rfl
  have hR : ∀ p : Fin n × Fin n, p ∈ R.toGridRectangle.coveredSquares ↔
      p.1 ∈ Grid.cIco i j ∧ p.2 ∈ Grid.cIco (u i) (u j) := by
    intro p
    simp [R, GridRectangle.mem_coveredSquares]
  rw [G.maslovOℤ_swapColumns_sub_sub a b R, G.card_OSet_inter_sub_card_swapColumns_OSet_inter ha]
  simp only [hR, GridState.swapColumns_apply]
  have hcross :=
    Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco_finRotate (u.toPerm.injective.ne hij) hOab
  -- Only a rectangle with a side on the grid line `b` moves the point on that line; it covers
  -- exactly one of the columns `a` and `b`.
  by_cases hbj : b = j
  · subst hbj
    have hai : a ∈ Grid.cIco i b := Grid.self_mem_cIco_finRotate hij
    have hbi : b ∉ Grid.cIco i b := Grid.right_notMem_cIco i b
    rw [Equiv.swap_apply_right]
    simp only [hai, hbi, true_and, false_and, ite_false] at hcross ⊢
    linarith
  by_cases hbi : b = i
  · subst hbi
    have haj : a ∉ Grid.cIco b j := by simp [hb, finRotate_apply]
    have hbj' : b ∈ Grid.cIco b j := Grid.left_mem_cIco hij
    rw [Equiv.swap_apply_left]
    simp only [haj, hbj', true_and, false_and, ite_false] at hcross ⊢
    linarith
  · rw [Equiv.swap_apply_of_ne_of_ne hbi hbj]
    have hiff : a ∈ Grid.cIco i j ↔ b ∈ Grid.cIco i j :=
      (Grid.mem_cIco_finRotate_iff_of_ne (Ne.symm hbi) (Ne.symm hbj)).symm
    by_cases hai : a ∈ Grid.cIco i j
    · simp [hai, hiff.mp hai]
    · simp [hai, mt hiff.mpr hai]

/-- Exchanging the cyclically adjacent columns `a` and `b = finRotate n a` raises the `O`-Maslov
grading of the `O`-marking state by one: in the commuted diagram, the `O`-marking state is the
target of the thin rectangle in column `a` that starts from the original `O`-marking state. -/
private theorem maslovOℤ_swapColumns_O (G : GridDiagram n) {a : Fin n} (ha : a ≠ finRotate n a) :
    (G.swapColumns a (finRotate n a)).maslovOℤ G.O = G.maslovOℤ G.O + 1 := by
  set b := finRotate n a with hb
  have hOab : G.O a ≠ G.O b := G.O.toPerm.injective.ne ha
  let R := GridRectangleBetween.ofSwapColumns G.O (G.O.swapColumns a b) a b ha rfl
  have h := (G.swapColumns a b).maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card R
  have hO' := (G.swapColumns a b).maslovOℤ_O
  rw [swapColumns_O] at hO'
  rw [maslovO_eq_intCast, maslovO_eq_intCast, hO', ← OSet_def] at h
  have h' : (G.swapColumns a b).maslovOℤ G.O - (1 - n) =
      2 * ((G.OSet ∩ R.toGridRectangle.coveredSquares).card : ℤ) - 1 -
        2 * ((G.swapColumns a b).OSet ∩ R.toGridRectangle.coveredSquares).card := by
    exact_mod_cast h
  rw [card_OSet_inter_eq_sum, card_OSet_inter_eq_sum] at h'
  have hR : ∀ p : Fin n × Fin n, p ∈ R.toGridRectangle.coveredSquares ↔
      p.1 = a ∧ p.2 ∈ Grid.cIco (G.O a) (G.O b) := by
    intro p
    simp [R, GridRectangle.mem_coveredSquares, Grid.cIco_eq_singleton_iff.mpr ⟨rfl, hb, ha⟩]
  simp only [hR, swapColumns_O, GridState.swapColumns_apply] at h'
  rw [Fintype.sum_eq_single a (by intro c hc; simp [hc]),
    Fintype.sum_eq_single a (by intro c hc; simp [hc])] at h'
  simp only [Equiv.swap_apply_left, Grid.left_mem_cIco hOab, Grid.right_notMem_cIco,
    and_self, and_false, ite_true, ite_false] at h'
  rw [G.maslovOℤ_O]
  linarith

/-- **The `O`-Maslov grading under an adjacent column swap.** Exchanging two cyclically adjacent
columns `a` and `b = finRotate n a` of a grid diagram changes the `O`-Maslov grading of a grid
state `x` by `±1`: it rises by one exactly when the point of `x` on the grid line between the two
columns, in row `x b`, lies strictly above the `O`-marking of column `a` and weakly below that of
column `b`, cyclically. Those are the lines `G.O a + 1, …, G.O b`, which the two markings pass
when they trade columns. -/
theorem maslovOℤ_swapColumns_finRotate (G : GridDiagram n) {a : Fin n} (ha : a ≠ finRotate n a)
    (x : GridState n) :
    (G.swapColumns a (finRotate n a)).maslovOℤ x = G.maslovOℤ x +
      if x (finRotate n a) ∈ Grid.cIco (finRotate n (G.O a)) (finRotate n (G.O (finRotate n a)))
      then 1 else -1 := by
  have hOab : G.O a ≠ G.O (finRotate n a) := G.O.toPerm.injective.ne ha
  have hsign : ∀ p : Prop, [Decidable p] →
      (if p then 1 else -1 : ℤ) = 2 * (if p then 1 else 0) - 1 := by
    intro p _
    split_ifs <;> norm_num
  -- The claim holds at the `O`-marking state, where it reads `M_O' = M_O + 1` because `M_O` rises
  -- by one across a thin rectangle of the commuted diagram. Every state is reached from there by
  -- column swaps, and the rectangle formula `M_O(x) - M_O(z) = 2 #(x ∩ r) - 1 - 2 #(𝕆 ∩ r)` of
  -- `Grading/MarkingCount.lean`, read in both diagrams, shows that both sides change by the same
  -- amount across each swap.
  have key : ∀ σ : Equiv.Perm (Fin n),
      (G.swapColumns a (finRotate n a)).maslovOℤ ⟨G.O.toPerm * σ⟩ =
        G.maslovOℤ ⟨G.O.toPerm * σ⟩ +
          if (⟨G.O.toPerm * σ⟩ : GridState n) (finRotate n a) ∈
            Grid.cIco (finRotate n (G.O a)) (finRotate n (G.O (finRotate n a))) then 1 else -1 := by
    intro σ
    induction σ using Equiv.Perm.swap_induction_on' with
    | one =>
      have hmem : G.O (finRotate n a) ∈
          Grid.cIco (finRotate n (G.O a)) (finRotate n (G.O (finRotate n a))) :=
        Grid.self_mem_cIco_finRotate ((finRotate n).injective.ne hOab)
      have hO : (⟨G.O.toPerm * 1⟩ : GridState n) = G.O := by rw [mul_one]
      rw [hO, G.maslovOℤ_swapColumns_O ha]
      simp only [hmem, ite_true]
    | mul_swap σ i j hij ih =>
      have hu : (⟨G.O.toPerm * (σ * Equiv.swap i j)⟩ : GridState n) =
          (⟨G.O.toPerm * σ⟩ : GridState n).swapColumns i j :=
        GridState.ext fun c => by simp [GridState.swapColumns_apply]
      have := G.maslovOℤ_swapColumns_sub_sub_swapColumns ha ⟨G.O.toPerm * σ⟩ hij
      rw [hu, hsign]
      rw [hsign] at ih
      linarith
  have hx := key (G.O.toPerm⁻¹ * x.toPerm)
  rwa [mul_inv_cancel_left] at hx

/-! ### The bidegree of a column turn -/

variable (G : GridDiagram n)

/-- The bidegree of the pentagon maps of the column turn `C` of `G`, for the (`O`-Maslov,
Alexander) bigrading. Write `a = C.column`, `b = finRotate n a` and `s = C.turnRow`. The
`O`-markings of the two columns contribute `(-2, -1)` when `s` lies strictly between `G.O b` and
`G.O a` going up, that is, outside the closed arc from `G.O a` up to `G.O b`. The `X`-markings
contribute `(0, 1)` when `s` lies strictly between `G.X b` and `G.X a`. For the turn of a column
commutation both contributions vanish
(`GridDiagram.ColumnCommutationData.commutationBidegree_eq_zero`); when the two marking segments
interleave they need not. -/
noncomputable def commutationBidegree (C : ColumnTurn n) : ℤ × ℤ :=
  (if C.turnRow ∈ Grid.cIoo (G.O (finRotate n C.column)) (G.O C.column) then (-2, -1) else 0) +
    if C.turnRow ∈ Grid.cIoo (G.X (finRotate n C.column)) (G.X C.column) then (0, 1) else 0

/-- The `O`-Maslov component of the bidegree of a column turn. -/
@[simp]
theorem commutationBidegree_fst (C : ColumnTurn n) :
    (G.commutationBidegree C).1 =
      if C.turnRow ∈ Grid.cIoo (G.O (finRotate n C.column)) (G.O C.column) then -2 else 0 := by
  rw [commutationBidegree]
  split_ifs <;> simp

/-- The Alexander component of the bidegree of a column turn. -/
@[simp]
theorem commutationBidegree_snd (C : ColumnTurn n) :
    (G.commutationBidegree C).2 =
      (if C.turnRow ∈ Grid.cIoo (G.X (finRotate n C.column)) (G.X C.column) then 1 else 0) -
        if C.turnRow ∈ Grid.cIoo (G.O (finRotate n C.column)) (G.O C.column) then 1 else 0 := by
  rw [commutationBidegree]
  split_ifs <;> simp

/-- The turn of a column commutation has bidegree zero: the markings of its first column lie in
the bigon below the turn and those of the next column in the bigon above it. -/
@[simp]
theorem ColumnCommutationData.commutationBidegree_eq_zero (C : ColumnCommutationData G) :
    G.commutationBidegree C = 0 := by
  have hO := notMem_cIoo_of_mem_insert_cIco C.O_column_below C.O_next_above
  have hX := notMem_cIoo_of_mem_insert_cIco C.X_column_below C.X_next_above
  simp only [commutationBidegree, hO, hX, ite_false, add_zero]

/-! ### The gradings across a pentagon -/

/-- The `O`-Maslov grading across an empty pentagon turning in the square row `s`, for arbitrary
positions of the `O`-markings of the two exchanged columns. -/
private theorem maslovOℤ_swapColumns_of_isEmpty_aux {a s : Fin n} {x y : GridState n}
    (P : GridPentagonBetween a s x y) (hP : P.IsEmpty) :
    (G.swapColumns a (finRotate n a)).maslovOℤ y =
      G.maslovOℤ x + 2 * ((G.OSet ∩ P.coveredSquares).card : ℤ) -
        2 * if s ∈ Grid.cIoo (G.O (finRotate n a)) (G.O a) then 1 else 0 := by
  set b := finRotate n a with hb
  have hn : 1 < n := by
    by_contra hn
    exact P.left_ne (Fin.ext (by have := P.left.isLt; have := (finRotate n a).isLt; omega))
  have hab : a ≠ b := (Grid.finRotate_ne_self hn a).symm
  have hOab : G.O a ≠ G.O b := G.O.toPerm.injective.ne hab
  -- The underlying empty rectangle of `P` is a rectangle of the commuted diagram from `x` to `y`,
  -- so `M_O'(x) - M_O'(y) = 1 - 2 #(𝕆' ∩ r)`.
  have hR := (G.swapColumns a b).maslovO_sub_maslovO_eq_one_sub_two_mul_card
    P.toGridRectangleBetween hP
  rw [maslovO_eq_intCast, maslovO_eq_intCast] at hR
  have hR' : (G.swapColumns a b).maslovOℤ x - (G.swapColumns a b).maslovOℤ y =
      1 - 2 * (((G.swapColumns a b).OSet ∩ P.toGridRectangle.coveredSquares).card : ℤ) := by
    exact_mod_cast hR
  -- The commuted diagram and the pentagon see the same `O`-markings away from columns `a`, `b`.
  have hcount : (((G.swapColumns a b).OSet ∩ P.toGridRectangle.coveredSquares).card : ℤ) -
      (G.OSet ∩ P.coveredSquares).card =
        (if G.O b ∈ Grid.cIco (x P.left) (x b) then 1 else 0) -
          (if G.O a ∈ Grid.cIoo s (x b) then 1 else 0) -
          (if G.O b ∈ Grid.cIco (x P.left) s then 1 else 0) := by
    rw [card_OSet_inter_eq_sum, card_OSet_inter_eq_sum, ← Finset.sum_sub_distrib,
      Fintype.sum_eq_add a b hab]
    · have hla : a ∈ Grid.cIco P.left b := Grid.self_mem_cIco_finRotate P.left_ne
      have hlb : b ∉ Grid.cIco P.left b := Grid.right_notMem_cIco _ _
      simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, P.mem_coveredSquares,
        P.right_eq, swapColumns_O, GridState.swapColumns_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_right, hla, hlb, ← hb, GridRectangleBetween.bottom_def,
        GridRectangleBetween.top_def]
      simp [hab, hab.symm]
      ring
    · rintro c ⟨hca, hcb⟩
      have hcb' : c ≠ finRotate n a := hcb
      simp [P.mem_coveredSquares_iff_of_ne (p := (c, G.O c)) hca hcb',
        GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hca hcb]
  -- The pentagon covers the same squares as the rectangle away from the columns `a` and `b`; the
  -- position of the `O`-markings of those two columns relative to the turn row accounts for the
  -- rest, together with the change of diagram at the state `x`.
  have hD := G.maslovOℤ_swapColumns_finRotate hab x
  have hid := pentagon_ite_identity (B := x P.left) (T := x b) P.turn_mem_cIco hOab
  linarith

variable (C : ColumnTurn n) {x y : GridState n}

/-- **The `O`-Maslov grading across a pentagon.** If `P` is an empty pentagon of the column turn
`C` from a state `x` of `G` to a state `y` of the diagram with the two columns of `C` exchanged,
then `M_O(y) = M_O(x) + 2 #(𝕆 ∩ P) + δ`, counting the `O`-markings of `G` that `P` carries, where
`δ` is the Maslov component of `G.commutationBidegree C`. With every variable of weight `-2`, the
term `V^{𝕆 ∩ P} · y` of the pentagon map has the `O`-Maslov grading of `x` shifted by `δ`, which
vanishes for a column commutation. -/
theorem maslovOℤ_swapColumns_of_isEmpty {P : GridPentagonBetween C.column C.turnRow x y}
    (hP : P.IsEmpty) :
    (G.swapColumns C.column (finRotate n C.column)).maslovOℤ y =
      G.maslovOℤ x + 2 * ((G.pentagonOColumns C P).card : ℤ) + (G.commutationBidegree C).1 := by
  rw [card_pentagonOColumns, G.maslovOℤ_swapColumns_of_isEmpty_aux P hP, commutationBidegree_fst]
  split_ifs <;> ring

/-- **The `X`-Maslov grading across a pentagon.** If `P` is an empty pentagon of the column turn
`C` from `x` to `y`, then `M_X(y) = M_X(x) + 2 #(𝕏 ∩ P)`, corrected by `-2` when the turn row lies
strictly between the `X`-markings of the second and the first column of `C`, going up. -/
theorem maslovXℤ_swapColumns_of_isEmpty {P : GridPentagonBetween C.column C.turnRow x y}
    (hP : P.IsEmpty) :
    (G.swapColumns C.column (finRotate n C.column)).maslovXℤ y =
      G.maslovXℤ x + 2 * ((G.XSet ∩ P.coveredSquares).card : ℤ) -
        2 * if C.turnRow ∈ Grid.cIoo (G.X (finRotate n C.column)) (G.X C.column) then 1 else 0 := by
  have h := G.swapMarkings.maslovOℤ_swapColumns_of_isEmpty_aux P hP
  rwa [← swapColumns_swapMarkings, maslovOℤ_swapMarkings, maslovOℤ_swapMarkings,
    swapMarkings_OSet, swapMarkings_O] at h

/-- A pentagon counted by the pentagon map carries no `X`-marking, so it changes the `X`-Maslov
grading only by the correction of `maslovXℤ_swapColumns_of_isEmpty`; in particular it preserves
the `X`-Maslov grading for a column commutation. -/
theorem maslovXℤ_swapColumns_of_mem_pentagons {P : GridPentagonBetween C.column C.turnRow x y}
    (hP : P ∈ G.pentagons C x y) :
    (G.swapColumns C.column (finRotate n C.column)).maslovXℤ y =
      G.maslovXℤ x -
        2 * if C.turnRow ∈ Grid.cIoo (G.X (finRotate n C.column)) (G.X C.column) then 1 else 0 := by
  rw [mem_pentagons] at hP
  rw [G.maslovXℤ_swapColumns_of_isEmpty C hP.1,
    Finset.disjoint_iff_inter_eq_empty.mp hP.2.symm]
  simp

/-- **The Alexander grading across a counted pentagon**, in its doubled integer form: a pentagon
counted by the pentagon map from `x` to `y` raises it by twice the number of `O`-markings it
carries, shifted by twice the Alexander component of `G.commutationBidegree C`. -/
theorem alexanderTwoℤ_swapColumns_of_mem_pentagons
    {P : GridPentagonBetween C.column C.turnRow x y} (hP : P ∈ G.pentagons C x y) :
    (G.swapColumns C.column (finRotate n C.column)).alexanderTwoℤ y =
      G.alexanderTwoℤ x + 2 * ((G.pentagonOColumns C P).card : ℤ) +
        2 * (G.commutationBidegree C).2 := by
  have hO := G.maslovOℤ_swapColumns_of_isEmpty C ((G.mem_pentagons P).mp hP).1
  have hX := G.maslovXℤ_swapColumns_of_mem_pentagons C hP
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, hO, hX, commutationBidegree_fst,
    commutationBidegree_snd]
  split_ifs <;> ring

/-- The `O`-Maslov grading across an empty initial-side pentagon turning in the square row `s`,
for arbitrary positions of the `O`-markings of the two exchanged columns. -/
private theorem maslovOℤ_swapColumns_initialPentagon_of_isEmpty_aux {a s : Fin n}
    {x y : GridState n} (P : GridInitialPentagonBetween a s x y) (hP : P.IsEmpty)
    (hab : a ≠ finRotate n a) :
    (G.swapColumns a (finRotate n a)).maslovOℤ y =
      G.maslovOℤ x + 2 * ((G.OSet ∩ P.coveredSquares).card : ℤ) -
        2 * if s ∈ Grid.cIoo (G.O (finRotate n a)) (G.O a) then 1 else 0 := by
  set b := finRotate n a with hb
  -- Unlike a terminal-side pentagon, use the rectangle in the original diagram and change
  -- diagrams at the target. Its point on the replaced line lies on the rectangle's top side.
  have hR := G.maslovO_sub_maslovO_eq_one_sub_two_mul_card P.toGridRectangleBetween hP
  rw [maslovO_eq_intCast, maslovO_eq_intCast] at hR
  have hR' : G.maslovOℤ x - G.maslovOℤ y =
      1 - 2 * ((G.OSet ∩ P.toGridRectangle.coveredSquares).card : ℤ) := by
    exact_mod_cast hR
  have hcount : ((G.OSet ∩ P.toGridRectangle.coveredSquares).card : ℤ) -
      (G.OSet ∩ P.coveredSquares).card =
        (if G.O b ∈ Grid.cIco (x b) (x P.right) then 1 else 0) -
          (if G.O a ∈ Grid.cIoo s (x P.right) then 1 else 0) -
          (if G.O b ∈ Grid.cIco (x b) s then 1 else 0) := by
    rw [card_OSet_inter_eq_sum, card_OSet_inter_eq_sum, ← Finset.sum_sub_distrib,
      Fintype.sum_eq_add a b hab]
    · have ha : a ∉ Grid.cIco b P.right := by simp [hb, finRotate_apply]
      have hb' : b ∈ Grid.cIco b P.right := Grid.left_mem_cIco P.right_ne.symm
      simp only [GridRectangleBetween.mem_toGridRectangle_coveredSquares, P.mem_coveredSquares,
        P.left_eq, ha, hb', ← hb, GridRectangleBetween.bottom_def,
        GridRectangleBetween.top_def]
      simp only [Grid.mem_cIco, ne_eq, EmbeddingLike.apply_eq_iff_eq, Fin.val_fin_lt,
        Fin.val_fin_le, false_and, ↓reduceIte, hab, not_false_eq_true, and_false, Grid.mem_cIoo,
        true_and, or_false, false_or, zero_sub, not_true_eq_false, hab.symm]
      ring
    · rintro c ⟨hca, hcb⟩
      simp [P.mem_coveredSquares_iff_of_ne (p := (c, G.O c)) hca hcb]
  have hD := G.maslovOℤ_swapColumns_finRotate hab y
  have hyb : y b = x P.right := by simpa only [P.left_eq] using P.map_left
  rw [hyb] at hD
  have hid := pentagon_ite_identity P.turn_mem_cIco (G.O.toPerm.injective.ne hab)
  linarith

/-- An empty pentagon turning on its initial side raises the target `O`-Maslov grading by twice
its number of covered `O`-markings, shifted by the Maslov component of `G.commutationBidegree C`. -/
theorem maslovOℤ_swapColumns_initialPentagon_of_isEmpty
    {P : GridInitialPentagonBetween C.column C.turnRow x y} (hP : P.IsEmpty) :
    (G.swapColumns C.column (finRotate n C.column)).maslovOℤ y =
      G.maslovOℤ x + 2 * ((G.OColumnsOfSquares P.coveredSquares).card : ℤ) +
        (G.commutationBidegree C).1 := by
  rw [G.card_OColumnsOfSquares,
    G.maslovOℤ_swapColumns_initialPentagon_of_isEmpty_aux P hP C.column_ne_next,
    commutationBidegree_fst]
  split_ifs <;> ring

/-- An empty pentagon turning on its initial side raises the target `X`-Maslov grading by twice
its number of covered `X`-markings, corrected by `-2` when the turn row lies strictly between the
`X`-markings of the second and the first column of `C`, going up. -/
theorem maslovXℤ_swapColumns_initialPentagon_of_isEmpty
    {P : GridInitialPentagonBetween C.column C.turnRow x y} (hP : P.IsEmpty) :
    (G.swapColumns C.column (finRotate n C.column)).maslovXℤ y =
      G.maslovXℤ x + 2 * ((G.XSet ∩ P.coveredSquares).card : ℤ) -
        2 * if C.turnRow ∈ Grid.cIoo (G.X (finRotate n C.column)) (G.X C.column) then 1 else 0 := by
  have h := G.swapMarkings.maslovOℤ_swapColumns_initialPentagon_of_isEmpty_aux P hP
    C.column_ne_next
  rwa [← swapColumns_swapMarkings, maslovOℤ_swapMarkings, maslovOℤ_swapMarkings,
    swapMarkings_OSet, swapMarkings_O] at h

/-- A counted initial-side pentagon avoids every `X`-marking, so it changes the `X`-Maslov
grading only by the correction of `maslovXℤ_swapColumns_initialPentagon_of_isEmpty`. -/
theorem maslovXℤ_swapColumns_of_mem_initialPentagons
    {P : GridInitialPentagonBetween C.column C.turnRow x y}
    (hP : P ∈ G.initialPentagons C x y) :
    (G.swapColumns C.column (finRotate n C.column)).maslovXℤ y =
      G.maslovXℤ x -
        2 * if C.turnRow ∈ Grid.cIoo (G.X (finRotate n C.column)) (G.X C.column) then 1 else 0 := by
  rw [mem_initialPentagons] at hP
  rw [G.maslovXℤ_swapColumns_initialPentagon_of_isEmpty C hP.1,
    Finset.disjoint_iff_inter_eq_empty.mp hP.2.symm]
  simp

/-- A counted initial-side pentagon raises the doubled Alexander grading by twice its number
of covered `O`-markings, shifted by twice the Alexander component of `G.commutationBidegree C`. -/
theorem alexanderTwoℤ_swapColumns_of_mem_initialPentagons
    {P : GridInitialPentagonBetween C.column C.turnRow x y}
    (hP : P ∈ G.initialPentagons C x y) :
    (G.swapColumns C.column (finRotate n C.column)).alexanderTwoℤ y =
      G.alexanderTwoℤ x + 2 * ((G.OColumnsOfSquares P.coveredSquares).card : ℤ) +
        2 * (G.commutationBidegree C).2 := by
  have hO := G.maslovOℤ_swapColumns_initialPentagon_of_isEmpty C
    ((G.mem_initialPentagons P).mp hP).1
  have hX := G.maslovXℤ_swapColumns_of_mem_initialPentagons C hP
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, hO, hX, commutationBidegree_fst,
    commutationBidegree_snd]
  split_ifs <;> ring

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (C : GridDiagram.ColumnTurn n)
  {x y : GridState n}

/-- The diagram obtained from a grid diagram with an odd number of components by exchanging the
two columns of a column turn: relabeling columns does not change the number of components. -/
abbrev swapColumns : OddComponentGridDiagram n :=
  ⟨G.1.swapColumns C.column (finRotate n C.column), by
    rw [GridDiagram.swapColumns, GridDiagram.componentCount_relabelColumns]
    exact G.2⟩

/-- The underlying grid diagram of `G.swapColumns C` exchanges the two columns of `C`. -/
theorem val_swapColumns : (G.swapColumns C).1 = G.1.swapColumns C.column (finRotate n C.column) :=
  (rfl)

/-- **The Alexander grading across a counted pentagon**: a pentagon counted by the pentagon map
from `x` to `y` raises the Alexander grading by the number of `O`-markings it carries, shifted by
the Alexander component of `G.commutationBidegree C`. -/
theorem alexanderℤ_swapColumns_of_mem_pentagons
    {P : GridPentagonBetween C.column C.turnRow x y} (hP : P ∈ G.1.pentagons C x y) :
    (G.swapColumns C).alexanderℤ y =
      G.alexanderℤ x + (G.1.pentagonOColumns C P).card + (G.1.commutationBidegree C).2 := by
  have h := G.1.alexanderTwoℤ_swapColumns_of_mem_pentagons C hP
  rw [← val_swapColumns, ← two_mul_alexanderℤ, ← two_mul_alexanderℤ] at h
  omega

/-- A counted initial-side pentagon raises the integer Alexander grading by its number of
covered `O`-markings, shifted by the Alexander component of `G.commutationBidegree C`. -/
theorem alexanderℤ_swapColumns_of_mem_initialPentagons
    {P : GridInitialPentagonBetween C.column C.turnRow x y}
    (hP : P ∈ G.1.initialPentagons C x y) :
    (G.swapColumns C).alexanderℤ y =
      G.alexanderℤ x + (G.1.OColumnsOfSquares P.coveredSquares).card +
        (G.1.commutationBidegree C).2 := by
  have h := G.1.alexanderTwoℤ_swapColumns_of_mem_initialPentagons C hP
  rw [← val_swapColumns, ← two_mul_alexanderℤ, ← two_mul_alexanderℤ] at h
  omega

end OddComponentGridDiagram

end TauCeti
