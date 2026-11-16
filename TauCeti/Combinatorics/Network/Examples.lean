/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import TauCeti.Combinatorics.Network.Acyclic
import TauCeti.Combinatorics.Network.Coefficients
import TauCeti.Combinatorics.Network.CycleAdjustment
public import TauCeti.Combinatorics.Network.ShortestAugmentation

/-!
# Examples of bounded assignments and flows

Take two vertices `false` and `true`, with one arrow for each ordered pair, including the two
loops, lower bound `-2` and upper bound `1` on every arrow. The integral assignment with value
`-1` on the arrow from `false` to `true` and zero elsewhere is a bounded `false`–`true` assignment
of negative value `-1`; conservation is vacuous because both vertices are terminals. Casting its
coefficients from `ℤ` to `ℝ` gives a real bounded assignment for the cast bounds, of value `-1`.

Take four vertices `s = 0`, `a = 1`, `b = 2` and `t = 3`, with one arrow for each ordered pair. The
unit flows along `s → a → b → t` and `s → b → a → t` add up to an `s`–`t` flow of value `2` that
these two paths decompose without any cycle, although its arrows of positive value contain the
cycle `a → b → a`. The unit flows along `s → a → t` and `s → b → t` add up to an acyclic flow of
the same value below it.

Take two vertices `false` and `true` again, now with two parallel arrows `false` and `true` for
each ordered pair, bounds `0` and `1`, and the unit assignments `f` and `g` on the two parallel
arrows from `false` to `true`. They have the same excess, and the residual cycle adjustments of
their residual difference lead from `f` to `g` through feasible assignments of that excess. The
residual difference from `f` to zero is a residual assignment of nonzero excess, computed directly
at both vertices, which cancels the excess of `f`.

Finally, on the four-vertex network with outer capacities `(1, 0)` and cross capacity `(0, 1)` in
the lexicographically ordered group `ℤ ×ₗ ℤ`, alternating between the two three-arrow residual
paths gives an infinite sequence of full-bottleneck augmentations. After every two steps the four
outer arrows carry `(0, m)` and the cross arrow carries zero, so the value is `(0, 2m)`. The two
shortest paths instead augment by `(1, 0)` and reach the maximum value `(2, 0)` in two steps. This
shows why arbitrary augmenting paths need not terminate over general ordered coefficient groups.
-/

public section

namespace TauCeti

namespace LexicographicAugmentationExample

/-- The lexicographically ordered coefficient group used by the nonterminating augmentation
example. -/
abbrev LexIntPair := ℤ ×ₗ ℤ

/-- A pair of integers, regarded as an element of the lexicographic coefficient group. -/
def lexPair (a b : ℤ) : LexIntPair :=
  toLex (a, b)

/-- The capacities of the nonterminating augmentation example. The four outer arrows have
capacity `(1, 0)`, the arrow `1 → 2` has capacity `(0, 1)`, and all other arrows have capacity
zero. -/
def capacity : Assignment (fun _ _ : Fin 4 ↦ Unit) LexIntPair :=
  fun x y _ ↦
    if (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3) ∨ (x = 2 ∧ y = 3) then
      lexPair 1 0
    else if x = 1 ∧ y = 2 then lexPair 0 1 else 0

/-- Evaluation of the capacity assignment on an arrow. -/
@[simp]
theorem capacity_apply (x y : Fin 4) (e : Unit) :
    capacity (x := x) (y := y) e =
      if (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3) ∨ (x = 2 ∧ y = 3) then
        lexPair 1 0
      else if x = 1 ∧ y = 2 then lexPair 0 1 else 0 := by
  rw [capacity]

/-- After `2m` alternating augmentations, every outer arrow carries `(0, m)` and the cross arrow
carries zero. -/
def evenAssignment (m : ℕ) :
    Assignment (fun _ _ : Fin 4 ↦ Unit) LexIntPair :=
  fun x y _ ↦
    if (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3) ∨ (x = 2 ∧ y = 3) then
      lexPair 0 m
    else 0

/-- Evaluation of the even-indexed assignment on an arrow. -/
@[simp]
theorem evenAssignment_apply (m : ℕ) (x y : Fin 4) (e : Unit) :
    evenAssignment m (x := x) (y := y) e =
      if (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3) ∨ (x = 2 ∧ y = 3) then
        lexPair 0 m
      else 0 := by
  rw [evenAssignment]

/-- After `2m + 1` alternating augmentations, the first path's outer arrows carry `(0, m + 1)`,
the other two outer arrows carry `(0, m)`, and the cross arrow carries `(0, 1)`. -/
def oddAssignment (m : ℕ) :
    Assignment (fun _ _ : Fin 4 ↦ Unit) LexIntPair :=
  fun x y _ ↦
    if (x = 0 ∧ y = 1) ∨ (x = 2 ∧ y = 3) then lexPair 0 (m + 1)
    else if (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3) then lexPair 0 m
    else if x = 1 ∧ y = 2 then lexPair 0 1 else 0

/-- Evaluation of the odd-indexed assignment on an arrow. -/
@[simp]
theorem oddAssignment_apply (m : ℕ) (x y : Fin 4) (e : Unit) :
    oddAssignment m (x := x) (y := y) e =
      if (x = 0 ∧ y = 1) ∨ (x = 2 ∧ y = 3) then lexPair 0 (m + 1)
      else if (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3) then lexPair 0 m
      else if x = 1 ∧ y = 2 then lexPair 0 1 else 0 := by
  rw [oddAssignment]

private theorem lexPair_nonneg_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ lexPair a b := by
  rw [← toLex_zero, lexPair, Prod.Lex.toLex_le_toLex']
  exact ⟨ha, fun _ ↦ hb⟩

/-- Addition of lexicographically ordered pairs is coordinatewise. -/
@[simp]
theorem lexPair_add (a b c d : ℤ) :
    lexPair a b + lexPair c d = lexPair (a + c) (b + d) := by
  unfold lexPair; rfl

/-- Subtraction of lexicographically ordered pairs is coordinatewise. -/
@[simp]
theorem lexPair_sub (a b c d : ℤ) :
    lexPair a b - lexPair c d = lexPair (a - c) (b - d) := by
  unfold lexPair; rfl

/-- The pair `(0, 0)` is zero in the lexicographic coefficient group. -/
@[simp]
theorem lexPair_zero : lexPair 0 0 = 0 := by
  unfold lexPair; rfl

@[simp]
private theorem lexPair_natCast_nonneg (m : ℕ) : 0 ≤ lexPair 0 m :=
  lexPair_nonneg_of_nonneg (by simp) (by simp)

@[simp]
private theorem lexPair_natSucc_nonneg (m : ℕ) : 0 ≤ lexPair 0 (m + 1) :=
  lexPair_nonneg_of_nonneg (by simp) (by omega)

@[simp]
private theorem lexPair_one_nonneg : 0 ≤ lexPair 0 1 :=
  lexPair_nonneg_of_nonneg (by simp) (by simp)

@[simp]
private theorem lexPair_zero_le_one (a b : ℤ) : lexPair 0 a ≤ lexPair 1 b := by
  rw [lexPair, lexPair, Prod.Lex.toLex_le_toLex]
  exact Or.inl (by omega)

@[simp]
private theorem lexPair_zero_one_pos : 0 < lexPair 0 1 := by
  rw [← toLex_zero, lexPair]
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, Int.zero_lt_one⟩)

@[simp]
private theorem lexPair_one_zero_nonneg : 0 ≤ lexPair 1 0 :=
  lexPair_nonneg_of_nonneg (by omega) (by omega)

@[simp]
private theorem lexPair_one_zero_pos : 0 < lexPair 1 0 := by
  rw [← toLex_zero, lexPair]
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl Int.zero_lt_one)

private theorem evenAssignment_nonneg (m : ℕ) : 0 ≤ evenAssignment m := by
  intro x y e
  fin_cases x <;> fin_cases y <;>
    simp [evenAssignment]

private theorem evenAssignment_le_capacity (m : ℕ) : evenAssignment m ≤ capacity := by
  intro x y e
  fin_cases x <;> fin_cases y <;> simp [evenAssignment, capacity, lexPair_zero_le_one]

private theorem oddAssignment_nonneg (m : ℕ) : 0 ≤ oddAssignment m := by
  intro x y e
  fin_cases x <;> fin_cases y <;>
    simp [oddAssignment]

private theorem oddAssignment_le_capacity (m : ℕ) : oddAssignment m ≤ capacity := by
  intro x y e
  fin_cases x <;> fin_cases y <;> simp [oddAssignment, capacity, lexPair_zero_le_one]

/-- All capacities in the example are nonnegative. -/
theorem capacity_nonneg : 0 ≤ capacity := by
  intro x y e
  fin_cases x <;> fin_cases y <;>
    simp [capacity, lexPair_nonneg_of_nonneg]

/-- The feasible flow after an even number `2m` of alternating augmentations. -/
def evenFlow (m : ℕ) : Flow capacity (0 : Fin 4) 3 where
  toFun := evenAssignment m
  mem_Icc := ⟨evenAssignment_nonneg m, evenAssignment_le_capacity m⟩
  conserve v hv0 hv3 := by
    fin_cases v <;>
      simp_all [evenAssignment, excessAt_def]
  excessAt_sink_nonneg :=
    excessAt_nonneg_of_nonneg_of_forall_out_eq_zero (evenAssignment_nonneg m) (by
      intro w e
      fin_cases w <;> simp [evenAssignment])

/-- The assignment underlying the even-indexed flow. -/
@[simp]
theorem evenFlow_toFun (m : ℕ) : (evenFlow m).toFun = evenAssignment m := by
  rw [evenFlow]

/-- The feasible flow after an odd number `2m + 1` of alternating augmentations. -/
def oddFlow (m : ℕ) : Flow capacity (0 : Fin 4) 3 where
  toFun := oddAssignment m
  mem_Icc := ⟨oddAssignment_nonneg m, oddAssignment_le_capacity m⟩
  conserve v hv0 hv3 := by
    fin_cases v <;>
      simp_all [oddAssignment, excessAt_def, Fin.sum_univ_four, one_nsmul, add_comm]
  excessAt_sink_nonneg :=
    excessAt_nonneg_of_nonneg_of_forall_out_eq_zero (oddAssignment_nonneg m) (by
      intro w e
      fin_cases w <;> simp [oddAssignment])

/-- The assignment underlying the odd-indexed flow. -/
@[simp]
theorem oddFlow_toFun (m : ℕ) : (oddFlow m).toFun = oddAssignment m := by
  rw [oddFlow]

/-- The residual path `0 → 1 → 2 → 3`, using the forward copy of the cross arrow. -/
def forwardPath :
    ArrowWalk (ResidualHom (fun _ _ : Fin 4 ↦ Unit)) 0 3 :=
  (((ArrowWalk.nil (Q := ResidualHom (fun _ _ : Fin 4 ↦ Unit)) 0).cons
    (x := 1) (Sum.inl ())).cons (x := 2) (Sum.inl ())).cons
    (x := 3) (Sum.inl ())

/-- The residual path `0 → 2 → 1 → 3`, using the reverse copy of the cross arrow. -/
def reversePath :
    ArrowWalk (ResidualHom (fun _ _ : Fin 4 ↦ Unit)) 0 3 :=
  (((ArrowWalk.nil (Q := ResidualHom (fun _ _ : Fin 4 ↦ Unit)) 0).cons
    (x := 2) (Sum.inl ())).cons (x := 1) (Sum.inr ())).cons
    (x := 3) (Sum.inl ())

/-- The residual arrows traversed by `forwardPath`. -/
@[simp]
theorem forwardPath_arrows :
    forwardPath.arrows =
      [⟨0, 1, Sum.inl ()⟩, ⟨1, 2, Sum.inl ()⟩, ⟨2, 3, Sum.inl ()⟩] := by
  simp [forwardPath, ArrowWalk.arrows_cons]

/-- The path `forwardPath` has three arrows. -/
@[simp]
theorem forwardPath_length : forwardPath.length = 3 := by
  simp [forwardPath, ArrowWalk.length]

/-- The residual arrows traversed by `reversePath`. -/
@[simp]
theorem reversePath_arrows :
    reversePath.arrows =
      [⟨0, 2, Sum.inl ()⟩, ⟨2, 1, Sum.inr ()⟩, ⟨1, 3, Sum.inl ()⟩] := by
  simp [reversePath, ArrowWalk.arrows_cons]

/-- The path `reversePath` has three arrows. -/
@[simp]
theorem reversePath_length : reversePath.length = 3 := by
  simp [reversePath, ArrowWalk.length]

/-- The residual path `0 → 1 → 2 → 3` uses no residual arrow twice. -/
theorem forwardPath_nodup : forwardPath.arrows.Nodup := by
  simp [forwardPath, ArrowWalk.arrows_cons]

/-- The residual path `0 → 1 → 2 → 3` is nonempty. -/
theorem forwardPath_nonempty : forwardPath.arrows ≠ [] := by
  simp [forwardPath, ArrowWalk.arrows_cons]

/-- The residual path `0 → 2 → 1 → 3` uses no residual arrow twice. -/
theorem reversePath_nodup : reversePath.arrows.Nodup := by
  simp [reversePath, ArrowWalk.arrows_cons]

/-- The residual path `0 → 2 → 1 → 3` is nonempty. -/
theorem reversePath_nonempty : reversePath.arrows ≠ [] := by
  simp [reversePath, ArrowWalk.arrows_cons]

/-- Every arrow of `0 → 1 → 2 → 3` has positive residual capacity in the even state. -/
theorem forwardPath_positive (m : ℕ) :
    ∀ a ∈ forwardPath.arrows,
      0 < residualCapacity 0 capacity (evenFlow m).toFun a.2.2 := by
  intro a ha
  simp only [forwardPath, ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append,
    List.mem_append, List.mem_singleton] at ha
  rcases ha with (rfl | rfl) | rfl
  · simp [capacity, evenFlow, evenAssignment, lexPair, Prod.Lex.toLex_lt_toLex]
  · simp [capacity, evenFlow, evenAssignment]
  · simp [capacity, evenFlow, evenAssignment, lexPair, Prod.Lex.toLex_lt_toLex]

/-- Every arrow of `0 → 2 → 1 → 3` has positive residual capacity in the odd state. -/
theorem reversePath_positive (m : ℕ) :
    ∀ a ∈ reversePath.arrows,
      0 < residualCapacity 0 capacity (oddFlow m).toFun a.2.2 := by
  intro a ha
  simp only [reversePath, ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append,
    List.mem_append, List.mem_singleton] at ha
  rcases ha with (rfl | rfl) | rfl
  · simp [capacity, oddFlow, oddAssignment, lexPair, Prod.Lex.toLex_lt_toLex]
  · simp [oddFlow, oddAssignment]
  · simp [capacity, oddFlow, oddAssignment, lexPair, Prod.Lex.toLex_lt_toLex]

/-- In the even state, the path `0 → 1 → 2 → 3` has bottleneck `(0, 1)`. -/
theorem forwardPath_bottleneck (m : ℕ) :
    forwardPath.bottleneck (residualCapacity 0 capacity (evenFlow m).toFun)
      forwardPath_nonempty = lexPair 0 1 := by
  apply le_antisymm
  · have hmem :
        (⟨1, 2, Sum.inl ()⟩ : Σ x y, ResidualHom (fun _ _ : Fin 4 ↦ Unit) x y) ∈
          forwardPath.arrows := by
      simp [forwardPath, ArrowWalk.arrows_cons]
    simpa [capacity, evenFlow, evenAssignment] using
      (ArrowWalk.bottleneck_le (c := residualCapacity 0 capacity (evenFlow m).toFun)
        (hne := forwardPath_nonempty) hmem)
  · rw [ArrowWalk.le_bottleneck_iff]
    intro a ha
    simp only [forwardPath, ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append,
      List.mem_append, List.mem_singleton] at ha
    rcases ha with (rfl | rfl) | rfl
    all_goals simp [capacity, evenFlow, evenAssignment]

/-- In the odd state, the path `0 → 2 → 1 → 3` has bottleneck `(0, 1)`. -/
theorem reversePath_bottleneck (m : ℕ) :
    reversePath.bottleneck (residualCapacity 0 capacity (oddFlow m).toFun)
      reversePath_nonempty = lexPair 0 1 := by
  apply le_antisymm
  · have hmem :
        (⟨2, 1, Sum.inr ()⟩ : Σ x y, ResidualHom (fun _ _ : Fin 4 ↦ Unit) x y) ∈
          reversePath.arrows := by
      simp [reversePath, ArrowWalk.arrows_cons]
    simpa [oddFlow, oddAssignment] using
      (ArrowWalk.bottleneck_le (c := residualCapacity 0 capacity (oddFlow m).toFun)
        (hne := reversePath_nonempty) hmem)
  · rw [ArrowWalk.le_bottleneck_iff]
    intro a ha
    simp only [reversePath, ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append,
      List.mem_append, List.mem_singleton] at ha
    rcases ha with (rfl | rfl) | rfl
    all_goals simp [capacity, oddFlow, oddAssignment]

/-- Augmenting the even state along `0 → 1 → 2 → 3` gives the following odd state. -/
theorem evenFlow_augmentsTo_oddFlow (m : ℕ) :
    (evenFlow m).AugmentsTo (oddFlow m) := by
  rw [Flow.augmentsTo_iff]
  refine ⟨forwardPath, forwardPath_nodup, forwardPath_nonempty, forwardPath_positive m, ?_⟩
  apply Flow.ext
  rw [Flow.augmentBottleneck_toFun, forwardPath_bottleneck]
  funext x y e
  fin_cases x <;> fin_cases y <;>
    simp [forwardPath, oddFlow, oddAssignment, evenFlow, evenAssignment, Assignment.single_apply]

/-- Augmenting the odd state along `0 → 2 → 1 → 3` gives the next even state. -/
theorem oddFlow_augmentsTo_evenFlow (m : ℕ) :
    (oddFlow m).AugmentsTo (evenFlow (m + 1)) := by
  rw [Flow.augmentsTo_iff]
  refine ⟨reversePath, reversePath_nodup, reversePath_nonempty, reversePath_positive m, ?_⟩
  apply Flow.ext
  rw [Flow.augmentBottleneck_toFun, reversePath_bottleneck]
  funext x y e
  fin_cases x <;> fin_cases y <;>
    simp [reversePath, oddFlow, oddAssignment, evenFlow, evenAssignment, Assignment.single_apply]

/-- The even state has value `(0, 2m)`. -/
@[simp]
theorem evenFlow_val (m : ℕ) : (evenFlow m).val = lexPair 0 (2 * m) := by
  simp [BoundedFlow.val_def, excessAt_def, evenFlow, evenAssignment, Fin.sum_univ_four,
    one_nsmul]
  congr 1
  omega

/-- The odd state has value `(0, 2m + 1)`. -/
@[simp]
theorem oddFlow_val (m : ℕ) : (oddFlow m).val = lexPair 0 (2 * m + 1) := by
  simp [BoundedFlow.val_def, excessAt_def, oddFlow, oddAssignment, Fin.sum_univ_four,
    one_nsmul]
  congr 1
  omega

/-- The flow after `n` steps of the alternating augmentation sequence. -/
def alternatingFlow (n : ℕ) : Flow capacity 0 3 :=
  if Even n then evenFlow (n / 2) else oddFlow (n / 2)

/-- The even-indexed terms of `alternatingFlow`. -/
@[simp]
theorem alternatingFlow_even (m : ℕ) : alternatingFlow (2 * m) = evenFlow m := by
  simp [alternatingFlow]

/-- The odd-indexed terms of `alternatingFlow`. -/
@[simp]
theorem alternatingFlow_odd (m : ℕ) : alternatingFlow (2 * m + 1) = oddFlow m := by
  simp [alternatingFlow]
  congr 1
  omega

/-- Every consecutive pair in `alternatingFlow` is related by a full-bottleneck augmentation. -/
theorem alternatingFlow_augmentsTo_succ (n : ℕ) :
    (alternatingFlow n).AugmentsTo (alternatingFlow (n + 1)) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [alternatingFlow_even, alternatingFlow_odd]
    exact evenFlow_augmentsTo_oddFlow m
  · rw [alternatingFlow_odd, show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
      alternatingFlow_even]
    exact oddFlow_augmentsTo_evenFlow m

/-- The alternating sequence starts at zero, augments at every step, and has value `(0, 2m)`
after `2m` steps. In particular, full-bottleneck augmentation need not terminate. -/
theorem exists_infinite_augmentation_sequence :
    ∃ f : ℕ → Flow capacity 0 3,
      f 0 = Flow.zero capacity_nonneg ∧
      (∀ n, (f n).AugmentsTo (f (n + 1))) ∧
      ∀ m, (f (2 * m)).toFun = evenAssignment m ∧
        (f (2 * m)).val = lexPair 0 (2 * m) := by
  refine ⟨alternatingFlow, ?_, alternatingFlow_augmentsTo_succ, fun m ↦ ?_⟩
  · apply Flow.ext
    funext x y e
    fin_cases x <;> fin_cases y <;> simp [alternatingFlow, evenFlow, evenAssignment]
  · rw [alternatingFlow_even]
    exact ⟨rfl, evenFlow_val m⟩

/-- The assignment after augmenting along the shortest path `0 → 1 → 3`. -/
def firstShortestAssignment : Assignment (fun _ _ : Fin 4 ↦ Unit) LexIntPair :=
  fun x y _ ↦ if (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 3) then lexPair 1 0 else 0

/-- Evaluation of the first shortest-path assignment on an arrow. -/
@[simp]
theorem firstShortestAssignment_apply (x y : Fin 4) (e : Unit) :
    firstShortestAssignment (x := x) (y := y) e =
      if (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 3) then lexPair 1 0 else 0 := by
  rw [firstShortestAssignment]

/-- The assignment saturating all four outer arrows, obtained after the two shortest-path
augmentations. -/
def maximumAssignment : Assignment (fun _ _ : Fin 4 ↦ Unit) LexIntPair :=
  fun x y _ ↦
    if (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3) ∨ (x = 2 ∧ y = 3) then
      lexPair 1 0
    else 0

/-- Evaluation of the maximum assignment on an arrow. -/
@[simp]
theorem maximumAssignment_apply (x y : Fin 4) (e : Unit) :
    maximumAssignment (x := x) (y := y) e =
      if (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3) ∨ (x = 2 ∧ y = 3) then
        lexPair 1 0
      else 0 := by
  rw [maximumAssignment]

private theorem firstShortestAssignment_nonneg : 0 ≤ firstShortestAssignment := by
  intro x y e
  fin_cases x <;> fin_cases y <;> simp [firstShortestAssignment, lexPair_nonneg_of_nonneg]

private theorem firstShortestAssignment_le : firstShortestAssignment ≤ capacity := by
  intro x y e
  fin_cases x <;> fin_cases y <;> simp [firstShortestAssignment, capacity]

private theorem maximumAssignment_nonneg : 0 ≤ maximumAssignment := by
  intro x y e
  fin_cases x <;> fin_cases y <;> simp [maximumAssignment, lexPair_nonneg_of_nonneg]

private theorem maximumAssignment_le : maximumAssignment ≤ capacity := by
  intro x y e
  fin_cases x <;> fin_cases y <;> simp [maximumAssignment, capacity]

/-- The flow after the first shortest-path augmentation. -/
def firstShortestFlow : Flow capacity 0 3 where
  toFun := firstShortestAssignment
  mem_Icc := ⟨firstShortestAssignment_nonneg, firstShortestAssignment_le⟩
  conserve v hv0 hv3 := by
    fin_cases v <;> simp_all [firstShortestAssignment, excessAt_def]
  excessAt_sink_nonneg :=
    excessAt_nonneg_of_nonneg_of_forall_out_eq_zero firstShortestAssignment_nonneg (by
      intro w e
      fin_cases w <;> simp [firstShortestAssignment])

/-- The assignment underlying the flow after the first shortest-path augmentation. -/
@[simp]
theorem firstShortestFlow_toFun : firstShortestFlow.toFun = firstShortestAssignment := by
  rw [firstShortestFlow]

/-- The maximum flow obtained after the two shortest-path augmentations. -/
def maximumFlow : Flow capacity 0 3 where
  toFun := maximumAssignment
  mem_Icc := ⟨maximumAssignment_nonneg, maximumAssignment_le⟩
  conserve v hv0 hv3 := by
    fin_cases v <;> simp_all [maximumAssignment, excessAt_def]
  excessAt_sink_nonneg :=
    excessAt_nonneg_of_nonneg_of_forall_out_eq_zero maximumAssignment_nonneg (by
      intro w e
      fin_cases w <;> simp [maximumAssignment])

/-- The assignment underlying the maximum flow. -/
@[simp]
theorem maximumFlow_toFun : maximumFlow.toFun = maximumAssignment := by
  rw [maximumFlow]

/-- The residual path `0 → 1 → 3`, the first shortest augmenting path from zero. -/
def firstShortestPath :
    ArrowWalk (ResidualHom (fun _ _ : Fin 4 ↦ Unit)) 0 3 :=
  ((ArrowWalk.nil (Q := ResidualHom (fun _ _ : Fin 4 ↦ Unit)) 0).cons
    (x := 1) (Sum.inl ())).cons (x := 3) (Sum.inl ())

/-- The residual path `0 → 2 → 3`, the second shortest augmenting path. -/
def secondShortestPath :
    ArrowWalk (ResidualHom (fun _ _ : Fin 4 ↦ Unit)) 0 3 :=
  ((ArrowWalk.nil (Q := ResidualHom (fun _ _ : Fin 4 ↦ Unit)) 0).cons
    (x := 2) (Sum.inl ())).cons (x := 3) (Sum.inl ())

/-- The residual arrows traversed by `firstShortestPath`. -/
@[simp]
theorem firstShortestPath_arrows :
    firstShortestPath.arrows = [⟨0, 1, Sum.inl ()⟩, ⟨1, 3, Sum.inl ()⟩] := by
  simp [firstShortestPath, ArrowWalk.arrows_cons]

/-- The path `firstShortestPath` has two arrows. -/
@[simp]
theorem firstShortestPath_length : firstShortestPath.length = 2 := by
  simp [firstShortestPath, ArrowWalk.length]

/-- The residual arrows traversed by `secondShortestPath`. -/
@[simp]
theorem secondShortestPath_arrows :
    secondShortestPath.arrows = [⟨0, 2, Sum.inl ()⟩, ⟨2, 3, Sum.inl ()⟩] := by
  simp [secondShortestPath, ArrowWalk.arrows_cons]

/-- The path `secondShortestPath` has two arrows. -/
@[simp]
theorem secondShortestPath_length : secondShortestPath.length = 2 := by
  simp [secondShortestPath, ArrowWalk.length]

/-- The residual path `0 → 1 → 3` is nonempty. -/
theorem firstShortestPath_nonempty : firstShortestPath.arrows ≠ [] := by
  simp [firstShortestPath, ArrowWalk.arrows_cons]

/-- The residual path `0 → 2 → 3` is nonempty. -/
theorem secondShortestPath_nonempty : secondShortestPath.arrows ≠ [] := by
  simp [secondShortestPath, ArrowWalk.arrows_cons]

/-- Every arrow of `0 → 1 → 3` has positive residual capacity for the zero flow. -/
theorem firstShortestPath_positive :
    ∀ a ∈ firstShortestPath.arrows,
      0 < residualCapacity 0 capacity
        (Flow.zero capacity_nonneg : Flow capacity (0 : Fin 4) 3).toFun a.2.2 := by
  intro a ha
  simp only [firstShortestPath, ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append,
    List.mem_append, List.mem_singleton] at ha
  rcases ha with rfl | rfl
  all_goals simp [capacity]

/-- Every arrow of `0 → 2 → 3` has positive residual capacity after the first augmentation. -/
theorem secondShortestPath_positive :
    ∀ a ∈ secondShortestPath.arrows,
      0 < residualCapacity 0 capacity firstShortestFlow.toFun a.2.2 := by
  intro a ha
  simp only [secondShortestPath, ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append,
    List.mem_append, List.mem_singleton] at ha
  rcases ha with rfl | rfl
  all_goals simp [capacity, firstShortestFlow, firstShortestAssignment]

/-- The path `0 → 1 → 3` is a shortest positive residual path for the zero flow. -/
theorem firstShortestPath_distance :
    (firstShortestPath.length : ℕ∞) =
      positiveEDist (residualCapacity 0 capacity
        (Flow.zero capacity_nonneg : Flow capacity (0 : Fin 4) 3).toFun) 0 3 := by
  apply le_antisymm
  · let d : Fin 4 → ℕ∞ := ![0, 1, 1, 2]
    have hd : d 3 ≤
        positiveEDist (residualCapacity 0 capacity
          (Flow.zero capacity_nonneg : Flow capacity (0 : Fin 4) 3).toFun) 0 3 := by
      apply le_positiveEDist (φ := d) (by simp [d])
      intro u v e he
      rcases e with e | e <;> fin_cases u <;> fin_cases v <;>
        simp [d, capacity] at he ⊢ <;> norm_num
    simpa [firstShortestPath, ArrowWalk.length, d] using hd
  · simpa [firstShortestPath, ArrowWalk.length] using
      positiveEDist_le_length firstShortestPath firstShortestPath_positive

/-- The path `0 → 2 → 3` is a shortest positive residual path after the first augmentation. -/
theorem secondShortestPath_distance :
    (secondShortestPath.length : ℕ∞) =
      positiveEDist (residualCapacity 0 capacity firstShortestFlow.toFun) 0 3 := by
  apply le_antisymm
  · let d : Fin 4 → ℕ∞ := ![0, 1, 1, 2]
    have hd : d 3 ≤ positiveEDist (residualCapacity 0 capacity firstShortestFlow.toFun) 0 3 := by
      apply le_positiveEDist (φ := d) (by simp [d])
      intro u v e he
      rcases e with e | e <;> fin_cases u <;> fin_cases v <;>
        simp [d, capacity, firstShortestFlow, firstShortestAssignment] at he ⊢
      norm_num
    simpa [secondShortestPath, ArrowWalk.length, d] using hd
  · simpa [secondShortestPath, ArrowWalk.length] using
      positiveEDist_le_length secondShortestPath secondShortestPath_positive

/-- For the zero flow, the path `0 → 1 → 3` has bottleneck `(1, 0)`. -/
theorem firstShortestPath_bottleneck :
    firstShortestPath.bottleneck (residualCapacity 0 capacity
      (Flow.zero capacity_nonneg : Flow capacity (0 : Fin 4) 3).toFun)
      firstShortestPath_nonempty = lexPair 1 0 := by
  apply le_antisymm
  · have hmem :
        (⟨0, 1, Sum.inl ()⟩ : Σ x y, ResidualHom (fun _ _ : Fin 4 ↦ Unit) x y) ∈
          firstShortestPath.arrows := by
      simp [firstShortestPath, ArrowWalk.arrows_cons]
    simpa [capacity] using
      (ArrowWalk.bottleneck_le (c := residualCapacity 0 capacity
        (Flow.zero capacity_nonneg : Flow capacity (0 : Fin 4) 3).toFun)
        (hne := firstShortestPath_nonempty) hmem)
  · rw [ArrowWalk.le_bottleneck_iff]
    intro a ha
    simp only [firstShortestPath, ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append,
      List.mem_append, List.mem_singleton] at ha
    rcases ha with rfl | rfl
    all_goals simp [capacity]

/-- After the first augmentation, the path `0 → 2 → 3` has bottleneck `(1, 0)`. -/
theorem secondShortestPath_bottleneck :
    secondShortestPath.bottleneck (residualCapacity 0 capacity firstShortestFlow.toFun)
      secondShortestPath_nonempty = lexPair 1 0 := by
  apply le_antisymm
  · have hmem :
        (⟨0, 2, Sum.inl ()⟩ : Σ x y, ResidualHom (fun _ _ : Fin 4 ↦ Unit) x y) ∈
          secondShortestPath.arrows := by
      simp [secondShortestPath, ArrowWalk.arrows_cons]
    simpa [capacity, firstShortestFlow, firstShortestAssignment] using
      (ArrowWalk.bottleneck_le
        (c := residualCapacity 0 capacity firstShortestFlow.toFun)
        (hne := secondShortestPath_nonempty) hmem)
  · rw [ArrowWalk.le_bottleneck_iff]
    intro a ha
    simp only [secondShortestPath, ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append,
      List.mem_append, List.mem_singleton] at ha
    rcases ha with rfl | rfl
    all_goals simp [capacity, firstShortestFlow, firstShortestAssignment]

/-- The first direct path is a shortest-path augmentation step from the zero flow. -/
theorem zero_shortestAugmentationStep_firstShortestFlow :
    BoundedFlow.ShortestAugmentationStep
      (Flow.zero capacity_nonneg : Flow capacity (0 : Fin 4) 3).toBoundedFlow
      firstShortestFlow.toBoundedFlow := by
  rw [BoundedFlow.shortestAugmentationStep_def]
  refine ⟨firstShortestPath, firstShortestPath_nonempty, firstShortestPath_positive,
    firstShortestPath_distance, ?_⟩
  rw [firstShortestPath_bottleneck]
  funext x y e
  fin_cases x <;> fin_cases y <;>
    simp [firstShortestPath, firstShortestFlow, firstShortestAssignment, Assignment.single_apply]

/-- The second direct path is a shortest-path augmentation step to the maximum flow. -/
theorem firstShortestFlow_shortestAugmentationStep_maximumFlow :
    firstShortestFlow.toBoundedFlow.ShortestAugmentationStep maximumFlow.toBoundedFlow := by
  rw [BoundedFlow.shortestAugmentationStep_def]
  refine ⟨secondShortestPath, secondShortestPath_nonempty, secondShortestPath_positive,
    secondShortestPath_distance, ?_⟩
  rw [secondShortestPath_bottleneck]
  funext x y e
  fin_cases x <;> fin_cases y <;>
    simp [secondShortestPath, firstShortestFlow, firstShortestAssignment, maximumFlow,
      maximumAssignment, Assignment.single_apply]

/-- The flow obtained by the two shortest paths has value `(2, 0)`. -/
@[simp]
theorem maximumFlow_val : maximumFlow.val = lexPair 2 0 := by
  simp [BoundedFlow.val_def, excessAt_def, maximumFlow, maximumAssignment,
    Fin.sum_univ_four, one_nsmul]

/-- The flow obtained by the two shortest paths is maximum. -/
theorem maximumFlow_isMaximum : maximumFlow.IsMaximum := by
  rw [Flow.isMaximum_iff]
  intro f
  calc
    f.val ≤ arrowSum capacity {0} {0}ᶜ := f.val_le_arrowSum (by simp) (by simp)
    _ = lexPair 2 0 := by
      rw [show ({0} : Finset (Fin 4))ᶜ = {1, 2, 3} by decide]
      simp [arrowSum_def, capacity, one_nsmul]
    _ = maximumFlow.val := maximumFlow_val.symm

end LexicographicAugmentationExample

-- An integral bounded assignment with negative bounds and negative value, carried to `ℝ`.
example :
    let lo : Assignment (fun _ _ : Bool ↦ Unit) ℤ := fun _ _ _ ↦ -2
    let hi : Assignment (fun _ _ : Bool ↦ Unit) ℤ := fun _ _ _ ↦ 1
    let φ : ℤ →+o ℝ :=
      { toFun := Int.cast
        map_zero' := Int.cast_zero
        map_add' := Int.cast_add
        monotone' := Int.cast_mono }
    ∃ f : BoundedFlow lo hi false true, f.val = -1 ∧ (f.map φ).val = -1 ∧
      (f.map φ).toFun (x := false) (y := true) () = -1 := by
  intro lo hi φ
  refine ⟨⟨fun a b _ ↦ if a = false ∧ b = true then -1 else 0, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro a b _
    simp only [lo]
    split_ifs <;> norm_num
  · intro a b _
    simp only [hi]
    split_ifs <;> norm_num
  · intro v hvs hvt
    cases v <;> simp_all
  · simp [BoundedFlow.val_def, excessAt_def]
  · simp [BoundedFlow.val_def, excessAt_def, φ]
  · simp [φ]

-- A flow with a cycle-free decomposition whose support contains a cycle, and an acyclic flow of
-- the same value below it.
example :
    let p₁ : ArrowWalk (fun _ _ : Fin 4 ↦ Unit) 0 3 :=
      (((ArrowWalk.nil 0).cons (x := 1) ()).cons (x := 2) ()).cons (x := 3) ()
    let p₂ : ArrowWalk (fun _ _ : Fin 4 ↦ Unit) 0 3 :=
      (((ArrowWalk.nil 0).cons (x := 2) ()).cons (x := 1) ()).cons (x := 3) ()
    let q₁ : ArrowWalk (fun _ _ : Fin 4 ↦ Unit) 0 3 :=
      ((ArrowWalk.nil 0).cons (x := 1) ()).cons (x := 3) ()
    let q₂ : ArrowWalk (fun _ _ : Fin 4 ↦ Unit) 0 3 :=
      ((ArrowWalk.nil 0).cons (x := 2) ()).cons (x := 3) ()
    let f : Assignment (fun _ _ : Fin 4 ↦ Unit) ℤ := walkAssignment p₁ 1 + walkAssignment p₂ 1
    let g : Assignment (fun _ _ : Fin 4 ↦ Unit) ℤ := walkAssignment q₁ 1 + walkAssignment q₂ 1
    ∃ (F G : Flow f 0 3) (D : PathCycleDecomposition f), F.toFun = f ∧ G.toFun = g ∧
      F.val = 2 ∧ G.val = 2 ∧ D.cycles = [] ∧ ¬f.IsAcyclic ∧ g.IsAcyclic := by
  intro p₁ p₂ q₁ q₂ f g
  have hf₀ : 0 ≤ f := add_nonneg (walkAssignment_nonneg _ zero_le_one)
    (walkAssignment_nonneg _ zero_le_one)
  have hgf : g ≤ f := by
    intro x y e
    fin_cases x <;> fin_cases y <;>
      simp [f, g, p₁, p₂, q₁, q₂, Assignment.single_apply]
  let F : Flow f 0 3 :=
    { toFun := f
      mem_Icc := ⟨hf₀, le_rfl⟩
      conserve v hv₀ hv₃ := by simp [f, excessAt_add, hv₀, hv₃]
      excessAt_sink_nonneg := by simp [f, excessAt_add] }
  let G : Flow f 0 3 :=
    { toFun := g
      mem_Icc := ⟨add_nonneg (walkAssignment_nonneg _ zero_le_one)
        (walkAssignment_nonneg _ zero_le_one), hgf⟩
      conserve v hv₀ hv₃ := by simp [g, excessAt_add, hv₀, hv₃]
      excessAt_sink_nonneg := by simp [g, excessAt_add] }
  let D : PathCycleDecomposition f :=
    { paths := [⟨0, 3, p₁, 1⟩, ⟨0, 3, p₂, 1⟩]
      cycles := []
      isPath_walk := by simp [ArrowWalk.isPath_def, p₁, p₂, Quiver.Path.vertices_cons]
      isCycle_walk := by simp
      weight_pos_of_mem_paths := by simp
      weight_pos_of_mem_cycles := by simp
      excessAt_source_neg := by simp [f, excessAt_add]
      excessAt_target_pos := by simp [f, excessAt_add]
      sum_paths_add_sum_cycles := by simp [f, WeightedWalk.assignment_def] }
  refine ⟨F, G, D, rfl, rfl, ?_, ?_, rfl, ?_, ?_⟩
  · simp [F, BoundedFlow.val_def, f, excessAt_add]
  · simp [G, BoundedFlow.val_def, g, excessAt_add]
  · -- The arrows `a → b` and `b → a` both carry one unit.
    rw [Assignment.isAcyclic_iff_forall_not_transGen]
    push Not
    refine ⟨1, .tail (.single ⟨(), ?_⟩) (c := 1) (b := 2) ⟨(), ?_⟩⟩ <;>
      simp [f, p₁, p₂, Assignment.single_apply]
  · -- Every arrow of positive value strictly raises the rank `![0, 1, 1, 2]`.
    let r : Fin 4 → ℕ := ![0, 1, 1, 2]
    have step (x y : Fin 4) (h : ∃ e, 0 < g (x := x) (y := y) e) : r x < r y := by
      fin_cases x <;> fin_cases y <;> simp_all [r, g, q₁, q₂, Assignment.single_apply]
    rw [Assignment.isAcyclic_iff_forall_not_transGen]
    intro v h
    suffices ∀ {x y}, Relation.TransGen (fun v w ↦ ∃ e, 0 < g (x := v) (y := w) e) x y →
        r x < r y from lt_irrefl _ (this h)
    intro x y hxy
    induction hxy with
    | single h => exact step _ _ h
    | tail _ h ih => exact ih.trans (step _ _ h)

-- Two feasible assignments of the same excess, connected by residual cycle adjustments.
example :
    let lo : Assignment (fun _ _ : Bool ↦ Bool) ℤ := 0
    let hi : Assignment (fun _ _ : Bool ↦ Bool) ℤ := fun _ _ _ ↦ 1
    let f : Assignment (fun _ _ : Bool ↦ Bool) ℤ :=
      Assignment.single (x := false) (y := true) false 1
    let g : Assignment (fun _ _ : Bool ↦ Bool) ℤ :=
      Assignment.single (x := false) (y := true) true 1
    f ≠ g ∧ ∃ D : PathCycleDecomposition (residualDifference f g), D.cycles ≠ [] ∧
      (∀ k, D.cycleUpdate f k ∈ Set.Icc lo hi ∧
        ∀ v, excessAt (D.cycleUpdate f k) v = excessAt f v) ∧
      D.cycleUpdate f D.cycles.length = g := by
  intro lo hi f g
  have hfg : ∀ v, excessAt f v = excessAt g v := by simp [f, g]
  have hf : f ∈ Set.Icc lo hi := by
    constructor <;> intro v w e <;> simp only [f, lo, hi, Assignment.single_apply] <;>
      split_ifs <;> simp
  have hg : g ∈ Set.Icc lo hi := by
    constructor <;> intro v w e <;> simp only [g, lo, hi, Assignment.single_apply] <;>
      split_ifs <;> simp
  have hne : f ≠ g := fun h ↦ by
    have := congrArg (fun h : Assignment (fun _ _ : Bool ↦ Bool) ℤ ↦
      h (x := false) (y := true) false) h
    simp [f, g, Assignment.single_apply] at this
  obtain ⟨D⟩ := nonempty_pathCycleDecomposition (residualDifference_nonneg f g)
  have hend := D.cycleUpdate_length_residualDifference hfg
  refine ⟨hne, D, fun h ↦ hne ?_, fun k ↦
    ⟨D.cycleUpdate_mem_Icc (residualDifference_mem_Icc hf hg).2 k, D.excessAt_cycleUpdate f k⟩,
    hend⟩
  -- Without cycles the adjustment would end where it starts.
  rwa [h, List.length_nil, PathCycleDecomposition.cycleUpdate_zero] at hend

-- A residual assignment of nonzero excess: the excess `-1` at `true` and `1` at `false` of the
-- residual difference from `f` to zero cancels the excess of `f`, and the update returns zero.
example :
    let f : Assignment (fun _ _ : Bool ↦ Bool) ℤ :=
      Assignment.single (x := false) (y := true) false 1
    let r := residualDifference f 0
    excessAt f true = 1 ∧ excessAt f false = -1 ∧ excessAt r true = -1 ∧ excessAt r false = 1 ∧
      residualUpdate f r = 0 := by
  intro f r
  refine ⟨by simp [f], by simp [f], ?_, ?_, residualUpdate_residualDifference f 0⟩ <;>
    simp [r, f, excessAt_def, Fintype.sum_sum_type, Assignment.single_apply]

end TauCeti
