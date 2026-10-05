/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Components
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon
public import TauCeti.KnotTheory.Grid.Grading.MarkingCount
public import TauCeti.KnotTheory.Grid.Grading.UnblockedChain
public import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Grading changes across grid commutation pentagons

Let `C` be a validated column commutation of a grid diagram `G`, exchanging the column
`a = C.column` with the next column `b = finRotate n a`, and let `G'` be the commuted diagram
`G.swapColumns a b`. The pentagon map `Φ : GC⁻(G) → GC⁻(G')` (`GridDiagram.pentagonMap`) sends a
state `x` to the sum, over the empty pentagons `P` from `x` carrying no `X`-marking and turning on
their terminal side, of `V^{𝕆 ∩ P} · y` with `y` the target of `P`. This file proves the
state-grading formulas for pentagons turning on either side. `Grading/Map.lean` uses them to prove
that both parts and the full commutation map `GridDiagram.commutationMap` have bidegree `(0, 0)`
for the (`O`-Maslov, Alexander) bigrading of `Grading/UnblockedChain.lean`.

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
  markings of `G` that `P` carries and writing `M_O'`, `M_X'` for the gradings of `G'`.

A counted pentagon carries no `X`-marking, so it preserves `M_X` and raises the Alexander grading
by the number of `O`-markings it carries (`GridDiagram.alexanderTwoℤ_swapColumns_of_mem_pentagons`
and `OddComponentGridDiagram.alexanderℤ_swapColumns_of_mem_pentagons`). Since every variable has
bidegree `(-2, -1)`, each term `V^{𝕆 ∩ P} · y` of `Φ(x)` has the bidegree of `x`.

## Main definitions

* `TauCeti.OddComponentGridDiagram.swapColumns`: the commuted diagram of a validated column
  commutation, again with an odd number of components.

## Main results

* `TauCeti.GridDiagram.maslovOℤ_swapColumns_finRotate`: the `O`-Maslov grading of a state under
  an exchange of two adjacent columns of the diagram.
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
  to preserve the Maslov and Alexander gradings.
* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 3.1 (arXiv:math/0610559).
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ}

/-! ### Cyclic bookkeeping at the turn of a pentagon -/

/-- Let the square rows `α` and `β` lie in the two bigons below and above the turn row `s`: going
up from `s`, first `β` is reached, at the latest at the other turn row `t`, and then `α`, at the
latest back at `s`. Then the grid line `s` lies in the band of lines `α + 1, …, β` unless
`α = s`. -/
private theorem mem_cIco_finRotate_iff_ne {s t α β : Fin n}
    (hα : α ∈ insert s (Grid.cIco t s)) (hβ : β ∈ insert t (Grid.cIco s t)) (hαβ : α ≠ β) :
    s ∈ Grid.cIco (finRotate n α) (finRotate n β) ↔ α ≠ s := by
  have hI : β ∈ Grid.cIco (finRotate n α) (finRotate n β) :=
    Grid.self_mem_cIco_finRotate ((finRotate n).injective.ne hαβ)
  rcases eq_or_ne s β with rfl | hsβ
  · exact iff_of_true hI hαβ
  -- Going up from `s`, the line `s` lies in the band unless `α` is passed before `β`, which the
  -- position of the two bigons allows only for `α = s`.
  have hpass : α ∈ Grid.cIco s β ↔ α = s := by
    refine ⟨fun h => ?_, fun h => by rw [h]; exact Grid.left_mem_cIco hsβ⟩
    simp only [Finset.mem_insert, Grid.mem_cIco, ne_eq, ← Fin.val_inj] at hα hβ h hαβ hsβ ⊢
    split_ifs at hα hβ h <;> omega
  have hcross := Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco_finRotate hsβ hαβ
  have hβs : β ∉ Grid.cIco s β := Grid.right_notMem_cIco s β
  by_cases hs : s ∈ Grid.cIco (finRotate n α) (finRotate n β)
  · have hαs : α ∉ Grid.cIco s β := by
      intro hαs
      simp only [hI, hs, hαs, hβs, ite_true, ite_false] at hcross
      omega
    exact iff_of_true hs fun h => hαs (hpass.mpr h)
  · have hαs : α ∈ Grid.cIco s β := by
      by_contra hαs
      simp only [hI, hs, hαs, hβs, ite_true, ite_false] at hcross
      omega
    exact iff_of_false hs fun h => h (hpass.mp hαs)

/-- The cyclic bookkeeping of a pentagon at the replaced grid line. The pentagon's terminal side
runs from row `B` up to row `T`, through the turn row `s`, and the square rows `α` and `β` of two
markings next to the line lie in the bigons below and above the turn, as in
`mem_cIco_finRotate_iff_ne`. -/
private theorem pentagon_ite_identity {B T s t α β : Fin n} (hs : s ∈ Grid.cIco B T)
    (hα : α ∈ insert s (Grid.cIco t s)) (hβ : β ∈ insert t (Grid.cIco s t)) (hαβ : α ≠ β) :
    (if T ∈ Grid.cIco (finRotate n α) (finRotate n β) then 1 else -1 : ℤ) - 1 +
      2 * ((if β ∈ Grid.cIco B T then 1 else 0) - (if α ∈ Grid.cIoo s T then 1 else 0) -
        (if β ∈ Grid.cIco B s then 1 else 0)) = 0 := by
  have hsT : s ≠ T := fun h => Grid.right_notMem_cIco B T (h ▸ hs)
  have hcross := Grid.ite_mem_cIco_finRotate_sub_ite_mem_cIco_finRotate hsT hαβ
  have hline : (if s ∈ Grid.cIco (finRotate n α) (finRotate n β) then 1 else 0 : ℤ) =
      1 - if α = s then 1 else 0 := by
    have key := mem_cIco_finRotate_iff_ne hα hβ hαβ
    by_cases h : α = s
    · have hs' : s ∉ Grid.cIco (finRotate n α) (finRotate n β) := fun hm => key.mp hm h
      simp only [hs', ite_false]
      simp [h]
    · simp only [key.mpr h, h, ite_true, ite_false, sub_zero]
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

/-! ### The gradings across a pentagon -/

/-- The `O`-Maslov grading across an empty pentagon, for a diagram whose `O`-markings in the two
commuted columns lie in the two bigons on either side of the turn. -/
private theorem maslovOℤ_swapColumns_of_isEmpty_of_mem (G : GridDiagram n) {a s t : Fin n}
    {x y : GridState n} (P : GridPentagonBetween a s x y) (hP : P.IsEmpty)
    (hOa : G.O a ∈ insert s (Grid.cIco t s))
    (hOb : G.O (finRotate n a) ∈ insert t (Grid.cIco s t)) :
    (G.swapColumns a (finRotate n a)).maslovOℤ y =
      G.maslovOℤ x + 2 * ((G.OSet ∩ P.coveredSquares).card : ℤ) := by
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
  -- position of the `O`-markings of those two columns in the bigons on either side of the turn
  -- row accounts for the rest, together with the change of diagram at the state `x`.
  have hD := G.maslovOℤ_swapColumns_finRotate hab x
  have hid := pentagon_ite_identity (B := x P.left) (T := x b) P.turn_mem_cIco hOa hOb hOab
  linarith

variable (G : GridDiagram n) (C : ColumnCommutationData G) {x y : GridState n}

/-- **The `O`-Maslov grading across a pentagon.** If `P` is an empty pentagon of the column
commutation `C` from a state `x` of `G` to a state `y` of the commuted diagram, then
`M_O(y) = M_O(x) + 2 #(𝕆 ∩ P)`, counting the `O`-markings of `G` that `P` carries. With every
variable of weight `-2`, the term `V^{𝕆 ∩ P} · y` of the pentagon map has the `O`-Maslov grading
of `x`. -/
theorem maslovOℤ_swapColumns_of_isEmpty {P : GridPentagonBetween C.column C.turnRow x y}
    (hP : P.IsEmpty) :
    (G.swapColumns C.column (finRotate n C.column)).maslovOℤ y =
      G.maslovOℤ x + 2 * ((G.pentagonOColumns C P).card : ℤ) := by
  rw [card_pentagonOColumns]
  exact G.maslovOℤ_swapColumns_of_isEmpty_of_mem P hP C.O_column_below C.O_next_above

/-- **The `X`-Maslov grading across a pentagon.** If `P` is an empty pentagon of the column
commutation `C` from `x` to `y`, then `M_X(y) = M_X(x) + 2 #(𝕏 ∩ P)`. -/
theorem maslovXℤ_swapColumns_of_isEmpty {P : GridPentagonBetween C.column C.turnRow x y}
    (hP : P.IsEmpty) :
    (G.swapColumns C.column (finRotate n C.column)).maslovXℤ y =
      G.maslovXℤ x + 2 * ((G.XSet ∩ P.coveredSquares).card : ℤ) := by
  have h := G.swapMarkings.maslovOℤ_swapColumns_of_isEmpty_of_mem P hP C.X_column_below
    C.X_next_above
  rwa [← swapColumns_swapMarkings, maslovOℤ_swapMarkings, maslovOℤ_swapMarkings,
    swapMarkings_OSet] at h

/-- A pentagon counted by the pentagon map preserves the `X`-Maslov grading: it carries no
`X`-marking. -/
theorem maslovXℤ_swapColumns_of_mem_pentagons {P : GridPentagonBetween C.column C.turnRow x y}
    (hP : P ∈ G.pentagons C x y) :
    (G.swapColumns C.column (finRotate n C.column)).maslovXℤ y = G.maslovXℤ x := by
  rw [mem_pentagons] at hP
  rw [G.maslovXℤ_swapColumns_of_isEmpty C hP.1,
    Finset.disjoint_iff_inter_eq_empty.mp hP.2.symm]
  simp

/-- **The Alexander grading across a counted pentagon**, in its doubled integer form: a pentagon
counted by the pentagon map from `x` to `y` raises it by twice the number of `O`-markings it
carries, `2 A(y) = 2 A(x) + 2 #(𝕆 ∩ P)`. -/
theorem alexanderTwoℤ_swapColumns_of_mem_pentagons
    {P : GridPentagonBetween C.column C.turnRow x y} (hP : P ∈ G.pentagons C x y) :
    (G.swapColumns C.column (finRotate n C.column)).alexanderTwoℤ y =
      G.alexanderTwoℤ x + 2 * ((G.pentagonOColumns C P).card : ℤ) := by
  have hO := G.maslovOℤ_swapColumns_of_isEmpty C ((G.mem_pentagons P).mp hP).1
  have hX := G.maslovXℤ_swapColumns_of_mem_pentagons C hP
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, hO, hX]
  ring

/-- The `O`-Maslov grading across an empty initial-side pentagon, when the markings lie in
its two commutation bigons. -/
private theorem maslovOℤ_swapColumns_initialPentagon_of_isEmpty_of_mem (G : GridDiagram n)
    {a s t : Fin n} {x y : GridState n} (P : GridInitialPentagonBetween a s x y)
    (hP : P.IsEmpty) (hab : a ≠ finRotate n a)
    (hOa : G.O a ∈ insert s (Grid.cIco t s))
    (hOb : G.O (finRotate n a) ∈ insert t (Grid.cIco s t)) :
    (G.swapColumns a (finRotate n a)).maslovOℤ y =
      G.maslovOℤ x + 2 * ((G.OSet ∩ P.coveredSquares).card : ℤ) := by
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
  have hid := pentagon_ite_identity P.turn_mem_cIco hOa hOb
    (G.O.toPerm.injective.ne hab)
  linarith

/-- An empty pentagon turning on its initial side raises the target `O`-Maslov grading by twice
its number of covered `O`-markings. -/
theorem maslovOℤ_swapColumns_initialPentagon_of_isEmpty
    {P : GridInitialPentagonBetween C.column C.turnRow x y} (hP : P.IsEmpty) :
    (G.swapColumns C.column (finRotate n C.column)).maslovOℤ y =
      G.maslovOℤ x + 2 * ((G.OColumnsOfSquares P.coveredSquares).card : ℤ) := by
  rw [G.card_OColumnsOfSquares]
  exact G.maslovOℤ_swapColumns_initialPentagon_of_isEmpty_of_mem P hP C.column_ne_next
    C.O_column_below C.O_next_above

/-- An empty pentagon turning on its initial side raises the target `X`-Maslov grading by twice
its number of covered `X`-markings. -/
theorem maslovXℤ_swapColumns_initialPentagon_of_isEmpty
    {P : GridInitialPentagonBetween C.column C.turnRow x y} (hP : P.IsEmpty) :
    (G.swapColumns C.column (finRotate n C.column)).maslovXℤ y =
      G.maslovXℤ x + 2 * ((G.XSet ∩ P.coveredSquares).card : ℤ) := by
  have h := G.swapMarkings.maslovOℤ_swapColumns_initialPentagon_of_isEmpty_of_mem P hP
    C.column_ne_next C.X_column_below C.X_next_above
  rwa [← swapColumns_swapMarkings, maslovOℤ_swapMarkings, maslovOℤ_swapMarkings,
    swapMarkings_OSet] at h

/-- A counted initial-side pentagon preserves the `X`-Maslov grading, since it avoids every
`X`-marking. -/
theorem maslovXℤ_swapColumns_of_mem_initialPentagons
    {P : GridInitialPentagonBetween C.column C.turnRow x y}
    (hP : P ∈ G.initialPentagons C x y) :
    (G.swapColumns C.column (finRotate n C.column)).maslovXℤ y = G.maslovXℤ x := by
  rw [mem_initialPentagons] at hP
  rw [G.maslovXℤ_swapColumns_initialPentagon_of_isEmpty C hP.1,
    Finset.disjoint_iff_inter_eq_empty.mp hP.2.symm]
  simp

/-- A counted initial-side pentagon raises the doubled Alexander grading by twice its number
of covered `O`-markings. -/
theorem alexanderTwoℤ_swapColumns_of_mem_initialPentagons
    {P : GridInitialPentagonBetween C.column C.turnRow x y}
    (hP : P ∈ G.initialPentagons C x y) :
    (G.swapColumns C.column (finRotate n C.column)).alexanderTwoℤ y =
      G.alexanderTwoℤ x + 2 * ((G.OColumnsOfSquares P.coveredSquares).card : ℤ) := by
  have hO := G.maslovOℤ_swapColumns_initialPentagon_of_isEmpty C
    ((G.mem_initialPentagons P).mp hP).1
  have hX := G.maslovXℤ_swapColumns_of_mem_initialPentagons C hP
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, hO, hX]
  ring

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (C : GridDiagram.ColumnCommutationData G.1)
  {x y : GridState n}

/-- The diagram obtained from a grid diagram with an odd number of components by a validated
column commutation: a commutation does not change the number of components. -/
def swapColumns : OddComponentGridDiagram n :=
  ⟨G.1.swapColumns C.column (finRotate n C.column), by
    rw [C.isColumnCommutation.componentCount_eq]
    exact G.2⟩

/-- The underlying grid diagram of `G.swapColumns C` exchanges the two columns of `C`. -/
@[simp]
theorem val_swapColumns : (G.swapColumns C).1 = G.1.swapColumns C.column (finRotate n C.column) :=
  (rfl)

/-- **The Alexander grading across a counted pentagon**: a pentagon counted by the pentagon map
from `x` to `y` raises the Alexander grading by the number of `O`-markings it carries,
`A(y) = A(x) + #(𝕆 ∩ P)`. -/
theorem alexanderℤ_swapColumns_of_mem_pentagons
    {P : GridPentagonBetween C.column C.turnRow x y} (hP : P ∈ G.1.pentagons C x y) :
    (G.swapColumns C).alexanderℤ y = G.alexanderℤ x + (G.1.pentagonOColumns C P).card := by
  have h := G.1.alexanderTwoℤ_swapColumns_of_mem_pentagons C hP
  rw [← val_swapColumns, ← two_mul_alexanderℤ, ← two_mul_alexanderℤ] at h
  omega

/-- A counted initial-side pentagon raises the integer Alexander grading by its number of
covered `O`-markings. -/
theorem alexanderℤ_swapColumns_of_mem_initialPentagons
    {P : GridInitialPentagonBetween C.column C.turnRow x y}
    (hP : P ∈ G.1.initialPentagons C x y) :
    (G.swapColumns C).alexanderℤ y =
      G.alexanderℤ x + (G.1.OColumnsOfSquares P.coveredSquares).card := by
  have h := G.1.alexanderTwoℤ_swapColumns_of_mem_initialPentagons C hP
  rw [← val_swapColumns, ← two_mul_alexanderℤ, ← two_mul_alexanderℤ] at h
  omega

end OddComponentGridDiagram

end TauCeti
