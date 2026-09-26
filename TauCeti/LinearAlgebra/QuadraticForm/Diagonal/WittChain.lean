/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation

/-!
# Witt's chain theorem for diagonal quadratic forms

Witt's chain theorem connects two isometric diagonal forms by finitely many changes of two
coefficients at a time. This file proves the converse to `TauCeti.DiagonalChain.equivalent` for
forms of rank at least two. The key intermediate result says that a represented unit can be made
the first diagonal coefficient by such a chain. Witt cancellation then reduces the remaining
coefficients by induction.

The lower bound on the rank is necessary for the relation defined in
`TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Basic`: a binary step requires two distinct
coordinates, so in rank one a diagonal chain is equality of coefficients, whereas isometry only
determines their square classes. That boundary is recorded there by
`TauCeti.diagonalChain_fin_one_iff_eq`.

## Main results

* `TauCeti.exists_diagonalChain_first_eq_of_mem_unitValueSet`: a represented unit can be moved
  into the first coefficient of a diagonal form of rank at least two.
* `TauCeti.diagonalChain_iff_equivalent`: Witt's chain theorem in rank at least two.
* `TauCeti.diagonalChain_iff_equivalent_of_two_le`: the same statement in inequality form.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter I, Theorem 5.2.
-/

public section

open QuadraticMap

namespace TauCeti

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- Replace the first two coefficients of `w` by the binary normal form whose first coefficient
is the represented unit `c`. -/
private def replaceHeadPair {n : ℕ} (w : Fin (n + 2) → Kˣ) (c : Kˣ) :
    Fin (n + 2) → Kˣ :=
  Fin.cons c (Fin.cons (w 0 * w 1 * c) (Fin.tail (Fin.tail w)))

omit [Invertible (2 : K)] in
@[simp]
private theorem replaceHeadPair_zero {n : ℕ} (w : Fin (n + 2) → Kˣ) (c : Kˣ) :
    replaceHeadPair w c 0 = c := by
  simp [replaceHeadPair]

omit [Invertible (2 : K)] in
/-- A represented unit of the leading binary subform gives the corresponding head-replacement
binary step. -/
private theorem binaryStep_replaceHeadPair {n : ℕ} (w : Fin (n + 2) → Kˣ) (c : Kˣ)
    (hc : c ∈ unitValueSet (weightedSumSquares K ![(w 0 : K), (w 1 : K)])) :
    BinaryStep w (replaceHeadPair w c) := by
  refine BinaryStep.of_pair 0 1 Fin.zero_ne_one ?_ ?_
  · intro k
    refine Fin.cases ?_ (fun i ↦ ?_) k
    · intro hk0
      exact (hk0 rfl).elim
    · refine Fin.cases ?_ (fun j ↦ ?_) i
      · intro _ hk1
        exact (hk1 rfl).elim
      · intro _ _
        rfl
  · simpa [replaceHeadPair] using equivalent_binaryNormalForm_of_mem_unitValueSet hc

omit [Invertible (2 : K)] in
/-- A represented unit can be made the first coefficient of a diagonal form of rank at least two
by a diagonal chain.

This alignment of the leading coefficient is what lets `TauCeti.diagonalChain_iff_equivalent`
cancel a common line and induct on the remaining coefficients. -/
theorem exists_diagonalChain_first_eq_of_mem_unitValueSet {n : ℕ}
    (w : Fin (n + 2) → Kˣ) (c : Kˣ)
    (hc : c ∈ unitValueSet (weightedSumSquares K fun i ↦ (w i : K))) :
    ∃ w' : Fin (n + 2) → Kˣ, DiagonalChain w w' ∧ w' 0 = c := by
  induction n generalizing c with
  | zero =>
      have hpair : c ∈ unitValueSet (weightedSumSquares K ![(w 0 : K), (w 1 : K)]) := by
        have hw : (fun i : Fin 2 ↦ (w i : K)) = ![(w 0 : K), (w 1 : K)] := by
          funext i
          fin_cases i <;> rfl
        simpa only [hw] using hc
      refine ⟨replaceHeadPair w c, ?_, by simp⟩
      exact DiagonalChain.binary (binaryStep_replaceHeadPair w c hpair)
  | succ n ih =>
      rw [mem_unitValueSet, represents_iff, Set.mem_range] at hc
      obtain ⟨x, hx⟩ := hc
      let d : K := weightedSumSquares K (fun i ↦ (w (Fin.succ i) : K))
        (fun i ↦ x (Fin.succ i))
      have hsum : (w 0 : K) * (x 0 * x 0) + d = c := by
        simpa only [weightedSumSquares_apply, Fin.sum_univ_succ, smul_eq_mul, d] using hx
      by_cases hd : d = 0
      · have hhead : c ∈ unitValueSet
            (weightedSumSquares K ![(w 0 : K), (w 1 : K)]) := by
          rw [mem_unitValueSet, represents_iff, Set.mem_range]
          refine ⟨![x 0, 0], ?_⟩
          simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one, smul_eq_mul, mul_zero, add_zero]
          simpa only [hd, add_zero] using hsum
        refine ⟨replaceHeadPair w c, ?_, by simp⟩
        exact DiagonalChain.binary (binaryStep_replaceHeadPair w c hhead)
      · let d' : Kˣ := Units.mk0 d hd
        have htail : d' ∈ unitValueSet
            (weightedSumSquares K fun i ↦ (Fin.tail w i : K)) := by
          rw [mem_unitValueSet, represents_iff, Set.mem_range]
          exact ⟨fun i ↦ x (Fin.succ i), by
            simp only [d, d', Units.val_mk0, Fin.tail]⟩
        obtain ⟨u, hu, hu0⟩ := ih (Fin.tail w) d' htail
        let v : Fin (n + 3) → Kˣ := Fin.cons (w 0) u
        have hwv : DiagonalChain w v := by
          simpa only [v, Fin.cons_self_tail] using hu.cons (w 0)
        have hhead : c ∈ unitValueSet
            (weightedSumSquares K ![(v 0 : K), (v 1 : K)]) := by
          rw [mem_unitValueSet, represents_iff, Set.mem_range]
          refine ⟨![x 0, 1], ?_⟩
          simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one, smul_eq_mul, mul_one, v, Fin.cons_zero, Fin.cons_one, hu0]
          exact hsum
        refine ⟨replaceHeadPair v c, ?_, by simp⟩
        exact hwv.tail (DiagonalStep.binary (binaryStep_replaceHeadPair v c hhead))

/-- **Witt's chain theorem** in its nontrivial range: two diagonal forms of rank at least two are
isometric if and only if their coefficient families are connected by a diagonal chain. -/
@[simp]
theorem diagonalChain_iff_equivalent {n : ℕ} {w w' : Fin (n + 2) → Kˣ} :
    DiagonalChain w w' ↔
      (weightedSumSquares K fun i ↦ (w i : K)).Equivalent
        (weightedSumSquares K fun i ↦ (w' i : K)) := by
  refine ⟨DiagonalChain.equivalent, fun h ↦ ?_⟩
  induction n with
  | zero =>
      refine DiagonalChain.binary (BinaryStep.of_pair 0 1 Fin.zero_ne_one ?_ h)
      intro k hk0 hk1
      fin_cases k
      · exact (hk0 rfl).elim
      · exact (hk1 rfl).elim
  | succ n ih =>
      have hw0 : w 0 ∈ unitValueSet (weightedSumSquares K fun i ↦ (w i : K)) := by
        rw [mem_unitValueSet, represents_iff, Set.mem_range]
        refine ⟨Pi.single 0 1, ?_⟩
        rw [weightedSumSquares_apply, Finset.sum_eq_single 0]
        · simp
        · intro i _ hi
          rw [Pi.single_eq_of_ne hi]
          simp
        · simp
      have hw0' : w 0 ∈ unitValueSet (weightedSumSquares K fun i ↦ (w' i : K)) := by
        rw [← h.unitValueSet_eq]
        exact hw0
      obtain ⟨u, hwu, hu0⟩ := exists_diagonalChain_first_eq_of_mem_unitValueSet w' (w 0) hw0'
      have hwu_equiv : (weightedSumSquares K fun i ↦ (w i : K)).Equivalent
          (weightedSumSquares K fun i ↦ (u i : K)) :=
        h.trans hwu.equivalent
      have hprod :
          (((w 0 : K) • (QuadraticMap.sq : QuadraticForm K K)).prod
              (presentedForm ⟨n + 2, Fin.tail w⟩)).Equivalent
            (((w 0 : K) • (QuadraticMap.sq : QuadraticForm K K)).prod
              (presentedForm ⟨n + 2, Fin.tail u⟩)) := by
        have hwuPresented : (presentedForm ⟨n + 3, w⟩).Equivalent
            (presentedForm ⟨n + 3, u⟩) := by
          simpa only [presentedForm_eq_weightedSumSquares_coe] using hwu_equiv
        have hwcons :
            (((w 0 : K) • (QuadraticMap.sq : QuadraticForm K K)).prod
                (presentedForm ⟨n + 2, Fin.tail w⟩)).Equivalent
              (presentedForm ⟨n + 3, w⟩) :=
          ⟨presentedFormConsIsometryEquiv w⟩
        have hucons :
            (((w 0 : K) • (QuadraticMap.sq : QuadraticForm K K)).prod
                (presentedForm ⟨n + 2, Fin.tail u⟩)).Equivalent
              (presentedForm ⟨n + 3, u⟩) := by
          rw [← hu0]
          exact ⟨presentedFormConsIsometryEquiv u⟩
        exact hwcons.trans (hwuPresented.trans hucons.symm)
      have hspan : Submodule.span K {(1 : K)} = ⊤ :=
        (Submodule.span_singleton_eq_top_iff K (1 : K)).mpr fun x ↦ ⟨x, by simp⟩
      have htail :
          (weightedSumSquares K fun i ↦ (Fin.tail w i : K)).Equivalent
            (weightedSumSquares K fun i ↦ (Fin.tail u i : K)) := by
        have hpresented :=
          equivalent_of_equivalent_prod_of_span_singleton_eq_top hspan (by simp) hprod
        simpa only [presentedForm_eq_weightedSumSquares_coe] using hpresented
      have htailChain : DiagonalChain (Fin.tail w) (Fin.tail u) := ih htail
      have hconsChain : DiagonalChain w u := by
        convert htailChain.cons (w 0) using 1
        · exact (Fin.cons_self_tail w).symm
        · rw [← hu0]
          exact (Fin.cons_self_tail u).symm
      have huw : DiagonalChain u w' := hwu.symm
      exact hconsChain.trans huw

/-- For a fixed size at least two, Witt's chain theorem in inequality form. -/
theorem diagonalChain_iff_equivalent_of_two_le {n : ℕ} (hn : 2 ≤ n)
    {w w' : Fin n → Kˣ} :
    DiagonalChain w w' ↔
      (weightedSumSquares K fun i ↦ (w i : K)).Equivalent
        (weightedSumSquares K fun i ↦ (w' i : K)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact diagonalChain_iff_equivalent

end TauCeti
