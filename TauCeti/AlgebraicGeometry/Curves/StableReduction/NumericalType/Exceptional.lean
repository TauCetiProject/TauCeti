/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Fork
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Branch
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Star

/-!
# Exceptional configurations of `(-2)`-indices

This file continues the classification of connected proper subgraphs of `(-2)`-indices in a
numerical type with the exceptional diagram `E₇`.  A chain of six components with an extra leaf
at its fourth component is simply laced: all seven weights and all six displayed intersections
agree, and there are no other edges.  This is
[Stacks, Lemma 55.5.13](https://stacks.math.columbia.edu/tag/0C8J).

Extending the length-two arm of this diagram by one component produces the affine `E₇`
diagram.  Its marks `(1, 2, 3, 4, 3, 2, 1, 2)` form a positive kernel vector for the displayed
intersection matrix.  Negative definiteness on a proper family of components therefore rules
out this configuration, which is
[Stacks, Lemma 55.5.15](https://stacks.math.columbia.edu/tag/0C8N).

## Main results

* `TauCeti.NumericalType.exists_weight_intersection_branch_seven_eq`: the `E₇`
  configuration is simply laced.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.intersection_branch_eq_zero`:
  a distinct eighth `(-2)`-index cannot meet the middle component of the chain, excluding the
  affine `E₇` configuration.
-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-- A chain `c₁ - c₂ - c₃ - c₄ - c₅ - c₆` of `(-2)`-indices, together with a
seventh `(-2)`-index meeting `c₄`, is simply laced.  Thus all seven weights agree, every
displayed intersection is that common weight, and the seventh component meets no other component
of the chain.  Together with the chain's no-chord theorem, this gives the classification of the
proper `E₇` configuration in
[Stacks, Lemma 55.5.13](https://stacks.math.columbia.edu/tag/0C8J). -/
theorem exists_weight_intersection_branch_seven_eq
    {c : ℕ → T.Component} (hc : T.IsSelfIntersectionMinusTwoChain 6 c)
    {branch : T.Component} (hbranch_ne : ∀ i < 6, branch ≠ c i)
    (hbranch_self : T.intersection branch branch = -(2 * (T.weight branch : ℤ)))
    (hbranch_pos : 0 < T.intersection (c 3) branch) :
    ∃ w : ℕ+, (∀ i < 6, (T.weight (c i) : ℤ) = w) ∧
      (T.weight branch : ℤ) = w ∧
      (∀ i, i + 1 < 6 → T.intersection (c i) (c (i + 1)) = w) ∧
      T.intersection (c 3) branch = w ∧
      ∀ i < 6, i ≠ 3 → T.intersection (c i) branch = 0 := by
  -- The first five chain components and the extra leaf form a fork; its generic classification
  -- fixes all data except the final component `c 5`.
  have hf : T.IsSelfIntersectionMinusTwoFork 5 c branch := {
    toIsSelfIntersectionMinusTwoChain := hc.mono (by omega)
    two_lt := by omega
    branch_ne := fun i hi ↦ hbranch_ne i (by omega)
    branch_intersection_self := hbranch_self
    branch_intersection_pos := by norm_num; exact hbranch_pos }
  let f : Fin 7 → T.Component := fun i ↦ if (i : ℕ) = 6 then branch else c i
  have hf_injective : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_cases hi6 : (i : ℕ) = 6
    · by_cases hj6 : (j : ℕ) = 6
      · exact hi6.trans hj6.symm
      · exact (hbranch_ne j (by omega) (by simpa [f, hi6, hj6] using hij)).elim
    · by_cases hj6 : (j : ℕ) = 6
      · exact (hbranch_ne i (by omega) (by simpa [f, hi6, hj6] using hij.symm)).elim
      · exact hc.injOn i (by omega) j (by omega) (by simpa [f, hi6, hj6] using hij)
  have hcard : 6 < Fintype.card T.Component := by
    have := Fintype.card_le_of_injective f hf_injective
    have hseven : 7 ≤ Fintype.card T.Component := by simpa using this
    omega
  obtain ⟨w, hw, hwb, hedge, hab⟩ := hf.exists_weight_intersection_eq hcard
  -- The `E₆` subconfiguration on `c 1, …, c 5` and the same leaf supplies the final weight,
  -- edge, and non-edge.
  obtain ⟨w', hw₁, hw₂, hw₃, hw₄, hw₅, -, -, -, -, ha₄₅, -, -, -, -, -, -, -, -, -,
      -, hbranch5⟩ :=
    T.exists_weight_intersection_branch_six_eq (c₁ := c 1) (c₂ := c 2) (c₃ := c 3)
      (c₄ := c 4) (c₅ := c 5) (c₆ := branch) hcard
      (hc.intersection_self 1 (by omega)) (hc.intersection_self 2 (by omega))
      (hc.intersection_self 3 (by omega)) (hc.intersection_self 4 (by omega))
      (hc.intersection_self 5 (by omega)) hbranch_self
      (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega)) (hbranch_ne 1 (by omega)).symm
      (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega)) (hbranch_ne 2 (by omega)).symm
      (hc.ne (by omega) (by omega) (by omega))
      (hbranch_ne 4 (by omega)).symm (hbranch_ne 5 (by omega)).symm
      (hc.intersection_succ_pos 1 (by omega)) (hc.intersection_succ_pos 2 (by omega))
      (hc.intersection_succ_pos 3 (by omega)) (hc.intersection_succ_pos 4 (by omega))
      hbranch_pos
  have hww : (w' : ℤ) = w := hw₃.symm.trans (hw 3 (by omega))
  have hw5 : (T.weight (c 5) : ℤ) = w := hw₅.trans hww
  have ha45 : T.intersection (c 4) (c 5) = w := ha₄₅.trans hww
  refine ⟨w, ?_, hwb, ?_, hab, ?_⟩
  · intro i hi
    by_cases hi5 : i < 5
    · exact hw i hi5
    · have : i = 5 := by omega
      simpa [this] using hw5
  · intro i hi
    by_cases hi4 : i < 4
    · exact hedge i (by omega)
    · have : i = 4 := by omega
      simpa [this] using ha45
  · intro i hi hi3
    by_cases hi5 : i < 5
    · exact hf.branch_intersection_eq_zero hi5 (by omega)
    · have : i = 5 := by omega
      simpa [this] using hbranch5

namespace IsSelfIntersectionMinusTwoChain

/-- A distinct eighth `(-2)`-index cannot meet the middle component of a chain of seven
`(-2)`-indices when the numerical type has any further component.  This excludes the affine
`E₇` diagram as a proper subgraph, as in
[Stacks, Lemma 55.5.15](https://stacks.math.columbia.edu/tag/0C8N). -/
theorem intersection_branch_eq_zero {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain 7 c)
    (hcard : 8 < Fintype.card T.Component) {branch : T.Component}
    (hbranch_ne : ∀ i < 7, branch ≠ c i)
    (hbranch_self : T.intersection branch branch = -(2 * (T.weight branch : ℤ))) :
    T.intersection (c 3) branch = 0 := by
  by_contra hbranch_nonzero
  have hbranch_pos : 0 < T.intersection (c 3) branch :=
    (T.offDiagonal_nonneg _ _ (hbranch_ne 3 (by omega)).symm).lt_of_ne
      (Ne.symm hbranch_nonzero)
  -- Classify the two overlapping finite `E₇` subdiagrams obtained by omitting the right,
  -- respectively left, endpoint. This identifies every entry of the affine diagram.
  obtain ⟨w, hw, hwb, hedge, hab, hbranch_zero⟩ :=
    T.exists_weight_intersection_branch_seven_eq (hc.mono (by omega))
      (fun i hi ↦ hbranch_ne i (by omega)) hbranch_self hbranch_pos
  let r : ℕ → T.Component := fun i ↦ c (6 - i)
  have hr : T.IsSelfIntersectionMinusTwoChain 6 r := {
    injOn i hi j hj hij := by
      have h := hc.injOn (6 - i) (by omega) (6 - j) (by omega) hij
      omega
    intersection_self i hi := by
      exact hc.intersection_self (6 - i) (by omega)
    intersection_succ_pos i hi := by
      have h := hc.intersection_succ_pos (5 - i) (by omega)
      have hsucc : 5 - i + 1 = 6 - i := by omega
      have hrev : 6 - (i + 1) = 5 - i := by omega
      rw [hsucc] at h
      simpa only [r, hrev, T.intersection_comm] using h }
  have hrbranch_ne : ∀ i < 6, branch ≠ r i := by
    intro i hi
    exact hbranch_ne (6 - i) (by omega)
  obtain ⟨w', hwr, -, hredge, -, hrbranch_zero⟩ :=
    T.exists_weight_intersection_branch_seven_eq hr hrbranch_ne hbranch_self
      (by simpa [r] using hbranch_pos)
  have hww : (w' : ℤ) = w := (hwr 3 (by omega)).symm.trans (hw 3 (by omega))
  have hw6 : (T.weight (c 6) : ℤ) = w := by
    simpa [r, hww] using hwr 0 (by omega)
  have hedge56 : T.intersection (c 5) (c 6) = w := by
    rw [T.intersection_comm]
    simpa [r, hww] using hredge 0 (by omega)
  have hbranch6 : T.intersection (c 6) branch = 0 := by
    simpa [r] using hrbranch_zero 0 (by omega) (by omega)
  have hweight : ∀ i < 7, (T.weight (c i) : ℤ) = w := by
    intro i hi
    by_cases hi6 : i < 6
    · exact hw i hi6
    · have : i = 6 := by omega
      simpa [this] using hw6
  have hedge' : ∀ i, i + 1 < 7 → T.intersection (c i) (c (i + 1)) = w := by
    intro i hi
    by_cases hi5 : i < 5
    · exact hedge i (by omega)
    · have : i = 5 := by omega
      simpa [this] using hedge56
  have hzero : ∀ {i j}, i < 7 → j < 7 → i + 1 < j →
      T.intersection (c i) (c j) = 0 := by
    intro i j hi hj hij
    exact hc.intersection_eq_zero (by omega) hi hj (by omega) (by omega) (by omega)
  have hbranch_zero' : ∀ i < 7, i ≠ 3 → T.intersection (c i) branch = 0 := by
    intro i hi hi3
    by_cases hi6 : i < 6
    · exact hbranch_zero i hi6 hi3
    · have : i = 6 := by omega
      simpa [this] using hbranch6
  have hentry {i j : ℕ} (hi : i < 7) (hj : j < 7) :
      T.intersection (c i) (c j) =
        if i = j then -(2 * (w : ℤ))
        else if i + 1 = j ∨ j + 1 = i then w else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte]
      rw [hc.intersection_self i hi, hweight i hi]
    · simp only [hij, ↓reduceIte]
      by_cases hadj : i + 1 = j ∨ j + 1 = i
      · simp only [hadj, ↓reduceIte]
        rcases hadj with rfl | hji
        · exact hedge' i (by omega)
        · rw [T.intersection_comm]
          subst i
          exact hedge' j (by omega)
      · simp only [hadj, ↓reduceIte]
        rcases lt_or_gt_of_ne hij with hijlt | hjilt
        · exact hzero hi hj (by omega)
        · rw [T.intersection_comm]
          exact hzero hj hi (by omega)
  have hbranch_entry {i : ℕ} (hi : i < 7) :
      T.intersection (c i) branch = if i = 3 then (w : ℤ) else 0 := by
    by_cases hi3 : i = 3
    · subst i
      simp only [↓reduceIte]
      exact hab
    · simp only [hi3, ↓reduceIte]
      exact hbranch_zero' i hi hi3
  -- Index the configuration by the canonical three-armed star for affine `E₇`.
  let e := AffineDynkinType.starIndexEquivE7
  let d : StarIndex ![1, 3, 3] → T.Component
    | none => c 3
    | some v => if (v.1 : ℕ) = 0 then branch else if (v.1 : ℕ) = 1 then
        c (2 - v.2) else c (4 + v.2)
  have hcartan (i j : StarIndex ![1, 3, 3]) :
      AffineDynkinType.E7.cartanMatrix (e i) (e j) = starCartanMatrix ![1, 3, 3] i j := by
    exact congrFun (congrFun
      AffineDynkinType.starCartanMatrix_one_three_three_eq_submatrix_E7 i) j |>.symm
  have hintersection (i j : StarIndex ![1, 3, 3]) :
      T.intersection (d i) (d j) =
        -(w : ℤ) * AffineDynkinType.E7.cartanMatrix (e i) (e j) := by
    rw [hcartan]
    rcases i with _ | ⟨i, s⟩ <;> rcases j with _ | ⟨j, t⟩
    · simp only [d, starCartanMatrix_none_none]
      rw [hc.intersection_self 3 (by omega), hweight 3 (by omega)]
      ring
    · fin_cases j <;> dsimp only [d] <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
        Fin.mk_one, Fin.reduceFinMk, Fin.isValue, starCartanMatrix_none_some,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val, Int.reduceNeg, mul_ite,
        mul_neg, mul_one, neg_neg, mul_zero, Nat.reduceEqDiff, reduceCtorEq, ite_true,
        ite_false] at t ⊢
      · simpa using hab
      · rw [hentry (i := 3) (j := 2 - (t : ℕ)) (by omega) (by omega)]
        split_ifs <;> omega
      · rw [hentry (i := 3) (j := 4 + (t : ℕ)) (by omega) (by omega)]
        split_ifs <;> omega
    · rw [T.intersection_comm]
      fin_cases i <;> dsimp only [d] <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
        Fin.mk_one, Fin.reduceFinMk, Fin.isValue, starCartanMatrix_some_none,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val, Int.reduceNeg, mul_ite,
        mul_neg, mul_one, neg_neg, mul_zero, Nat.reduceEqDiff, reduceCtorEq, ite_true,
        ite_false] at s ⊢
      · simpa using hab
      · rw [hentry (i := 3) (j := 2 - (s : ℕ)) (by omega) (by omega)]
        split_ifs <;> omega
      · rw [hentry (i := 3) (j := 4 + (s : ℕ)) (by omega) (by omega)]
        split_ifs <;> omega
    · fin_cases i <;> fin_cases j <;> dsimp only [d] <;> simp only [Nat.succ_eq_add_one,
        Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
        starCartanMatrix_some_some, zero_ne_one, one_ne_zero, Fin.reduceEq,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val, Int.reduceNeg, mul_ite,
        neg_mul, mul_neg, mul_one, neg_neg, mul_zero, Nat.reduceEqDiff, reduceCtorEq,
        ite_true, ite_false] at s t ⊢
      · rw [hbranch_self, hwb]
        have hst : (s : ℕ) = t := congrArg Fin.val (Subsingleton.elim s t)
        simp only [hst, ite_true]
        ring
      · rw [T.intersection_comm, hbranch_entry (i := 2 - (t : ℕ)) (by omega)]
        split_ifs <;> omega
      · rw [T.intersection_comm, hbranch_entry (i := 4 + (t : ℕ)) (by omega)]
        split_ifs <;> omega
      · rw [hbranch_entry (i := 2 - (s : ℕ)) (by omega)]
        split_ifs <;> omega
      · rw [hentry (i := 2 - (s : ℕ)) (j := 2 - (t : ℕ)) (by omega) (by omega)]
        split_ifs <;> omega
      · rw [hentry (i := 2 - (s : ℕ)) (j := 4 + (t : ℕ)) (by omega) (by omega)]
        split_ifs <;> omega
      · rw [hbranch_entry (i := 4 + (s : ℕ)) (by omega)]
        split_ifs <;> omega
      · rw [hentry (i := 4 + (s : ℕ)) (j := 2 - (t : ℕ)) (by omega) (by omega)]
        split_ifs <;> omega
      · rw [hentry (i := 4 + (s : ℕ)) (j := 4 + (t : ℕ)) (by omega) (by omega)]
        split_ifs <;> omega
  have hrow (i : StarIndex ![1, 3, 3]) :
      ∑ j, T.intersection (d i) (d j) * AffineDynkinType.E7.marks (e j) = 0 := by
    calc
      _ = -(w : ℤ) * ∑ j, AffineDynkinType.E7.cartanMatrix (e i) (e j) *
          AffineDynkinType.E7.marks (e j) := by
        simp_rw [hintersection, mul_assoc, Finset.mul_sum]
      _ = -(w : ℤ) * ∑ j : Fin AffineDynkinType.E7.nodes,
          AffineDynkinType.E7.cartanMatrix (e i) j * AffineDynkinType.E7.marks j := by
        exact congrArg (-(w : ℤ) * ·) (e.sum_comp fun j ↦
          AffineDynkinType.E7.cartanMatrix (e i) j * AffineDynkinType.E7.marks j)
      _ = -(w : ℤ) *
          AffineDynkinType.E7.cartanMatrix.mulVec AffineDynkinType.E7.marks (e i) := by
        rfl
      _ = 0 := by
        rw [AffineDynkinType.cartanMatrix_mulVec_marks_eq_zero AffineDynkinType.valid_E7]
        simp
  let nodeEquiv : Fin 8 ≃ Fin AffineDynkinType.E7.nodes :=
    finCongr AffineDynkinType.nodes_E7.symm
  let d' : ℕ → T.Component := fun i ↦
    if hi : i < 8 then d (e.symm (nodeEquiv ⟨i, hi⟩)) else d none
  let y : ℕ → ℤ := fun i ↦
    if hi : i < 8 then AffineDynkinType.E7.marks (nodeEquiv ⟨i, hi⟩) else 0
  have hd_injective : Function.Injective d := by
    intro i j hij
    rcases i with _ | ⟨a, s⟩ <;> rcases j with _ | ⟨b, t⟩
    · rfl
    · fin_cases b <;> simp only [d, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk, Fin.isValue, reduceCtorEq] at t hij ⊢
      · exact (hbranch_ne 3 (by omega) hij.symm).elim
      · exact (hc.ne (by omega) (by omega) (by omega) hij).elim
      · have ht : (t : ℕ) < 3 := by simpa [Matrix.cons_val_two] using t.isLt
        exact (hc.ne (by omega) (by omega) (by omega) hij).elim
    · fin_cases a <;> simp only [d, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk, Fin.isValue, reduceCtorEq] at s hij ⊢
      · exact (hbranch_ne 3 (by omega) hij).elim
      · exact (hc.ne (by omega) (by omega) (by omega) hij.symm).elim
      · have hs : (s : ℕ) < 3 := by simpa [Matrix.cons_val_two] using s.isLt
        exact (hc.ne (by omega) (by omega) (by omega) hij.symm).elim
    · fin_cases a <;> fin_cases b <;> simp only [d, Nat.succ_eq_add_one, Nat.reduceAdd,
        Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Option.some.injEq,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_zero]
        at s t hij ⊢
      · congr 2
        exact Fin.ext (by omega)
      · exact (hbranch_ne (2 - t) (by omega) hij).elim
      · have ht : (t : ℕ) < 3 := by simpa [Matrix.cons_val_two] using t.isLt
        exact (hbranch_ne (4 + t) (by omega) hij).elim
      · exact (hbranch_ne (2 - s) (by omega) hij.symm).elim
      · congr 2
        exact Fin.ext (by
          have := hc.injOn (2 - s) (by omega) (2 - t) (by omega) hij
          omega)
      · have ht : (t : ℕ) < 3 := by simpa [Matrix.cons_val_two] using t.isLt
        exact (hc.ne (by omega) (by omega) (by omega) hij).elim
      · have hs : (s : ℕ) < 3 := by simpa [Matrix.cons_val_two] using s.isLt
        exact (hbranch_ne (4 + s) (by omega) hij.symm).elim
      · have hs : (s : ℕ) < 3 := by simpa [Matrix.cons_val_two] using s.isLt
        exact (hc.ne (by omega) (by omega) (by omega) hij).elim
      · congr 2
        exact Fin.ext (by
          have hs : (s : ℕ) < 3 := by simpa [Matrix.cons_val_two] using s.isLt
          have ht : (t : ℕ) < 3 := by simpa [Matrix.cons_val_two] using t.isLt
          have := hc.injOn (4 + s) (by omega) (4 + t) (by omega) hij
          omega)
  have hd_inj : ∀ i < 8, ∀ j < 8, d' i = d' j → i = j := by
    intro i hi j hj hij
    have hdij : d (e.symm (nodeEquiv ⟨i, hi⟩)) =
        d (e.symm (nodeEquiv ⟨j, hj⟩)) := by simpa [d', hi, hj] using hij
    have heij := congrArg e (hd_injective hdij)
    have hfin : (⟨i, hi⟩ : Fin 8) = ⟨j, hj⟩ := nodeEquiv.injective (by
      simpa only [Equiv.apply_symm_apply] using heij)
    exact congrArg Fin.val hfin
  refine T.not_forall_sum_intersection_mul_nonneg_of_pos hd_inj hcard (y := y) ?_ ?_ ?_
  · intro i hi
    simpa [y, hi] using
      (AffineDynkinType.marks_pos (nodeEquiv ⟨i, hi⟩)).le
  · refine ⟨0, by omega, ?_⟩
    simpa [y] using AffineDynkinType.marks_pos (nodeEquiv (0 : Fin 8))
  · intro i hi
    let ii : Fin AffineDynkinType.E7.nodes := nodeEquiv ⟨i, hi⟩
    have hsum :
        (∑ x : Fin AffineDynkinType.E7.nodes,
          T.intersection (d (e.symm ii)) (d (e.symm x)) * AffineDynkinType.E7.marks x) =
        ∑ j : StarIndex ![1, 3, 3],
          T.intersection (d (e.symm ii)) (d j) * AffineDynkinType.E7.marks (e j) := by
      symm
      simpa only [Equiv.symm_apply_apply] using e.sum_comp
        (fun x : Fin AffineDynkinType.E7.nodes ↦
          T.intersection (d (e.symm ii)) (d (e.symm x)) * AffineDynkinType.E7.marks x)
    have hcanonical : 0 ≤ ∑ x : Fin AffineDynkinType.E7.nodes,
        T.intersection (d (e.symm ii)) (d (e.symm x)) * AffineDynkinType.E7.marks x := by
      rw [hsum, hrow]
    rw [← Fin.sum_univ_eq_sum_range]
    have hd'i : d' i = d (e.symm ii) := by
      simp only [d', hi, dite_true]
      rw [show nodeEquiv ⟨i, _⟩ = ii by
        apply nodeEquiv.injective
        exact Fin.ext rfl]
    have hd'x (x : Fin 8) : d' x = d (e.symm (nodeEquiv x)) := by
      simp only [d', Fin.is_lt, dite_true]
    have hyx (x : Fin 8) : y x = AffineDynkinType.E7.marks (nodeEquiv x) := by
      simp only [y, Fin.is_lt, dite_true]
    have hnormalize :
        (∑ x : Fin 8, T.intersection (d' i) (d' x) * y x) =
          ∑ x : Fin AffineDynkinType.E7.nodes,
            T.intersection (d (e.symm ii)) (d (e.symm x)) * AffineDynkinType.E7.marks x := by
      calc
        _ = ∑ x : Fin 8, T.intersection (d (e.symm ii))
              (d (e.symm (nodeEquiv x))) * AffineDynkinType.E7.marks (nodeEquiv x) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [hd'i, hd'x, hyx]
        _ = _ := nodeEquiv.sum_comp fun x ↦
          T.intersection (d (e.symm ii)) (d (e.symm x)) * AffineDynkinType.E7.marks x
    rw [hnormalize]
    exact hcanonical

end IsSelfIntersectionMinusTwoChain

end NumericalType

end TauCeti
