/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain
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
`TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain`: a binary step requires two distinct
coordinates. In rank one, a diagonal chain is therefore equality of coefficients, whereas
isometry only determines their square classes. The theorem records this boundary explicitly.

## Main results

* `TauCeti.exists_diagonalChain_first_eq_of_mem_unitValueSet`: a represented unit can be moved
  into the first coefficient of a diagonal form of rank at least two.
* `TauCeti.diagonalChain_iff_equivalent`: Witt's chain theorem in rank at least two.
* `TauCeti.diagonalChain_iff_equivalent_fin_zero`: the chain theorem in rank zero.
* `TauCeti.diagonalChain_fin_one_iff`: in rank one, a chain is exactly equality of coefficient
  families.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter I, Theorem 5.2.
-/

public section

open QuadraticMap

namespace TauCeti

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

namespace BinaryStep

variable {R : Type u} [CommSemiring R]

/-- A binary step remains a binary step after adjoining a fixed first coefficient. -/
theorem cons {n : ℕ} {w w' : Fin n → Rˣ} (a : Rˣ) (h : BinaryStep w w') :
    BinaryStep (Fin.cons a w) (Fin.cons a w') := by
  unfold TauCeti.BinaryStep at h ⊢
  obtain ⟨i, j, hij, hrest, hpair⟩ := h
  refine ⟨i.succ, j.succ, fun hs ↦ hij (Fin.succ_inj.mp hs), ?_, ?_⟩
  · intro k
    refine Fin.cases ?_ (fun l ↦ ?_) k
    · intro _ _
      simp
    · intro hki hkj
      simp only [Fin.cons_succ]
      exact hrest l (fun hli ↦ hki (Fin.succ_inj.mpr hli))
        (fun hlj ↦ hkj (Fin.succ_inj.mpr hlj))
  · simpa only [Fin.cons_succ] using hpair

end BinaryStep

namespace DiagonalChain

variable {R : Type u} [CommSemiring R]

/-- A diagonal chain remains a diagonal chain after adjoining a fixed first coefficient. -/
theorem cons {n : ℕ} {w w' : Fin n → Rˣ} (a : Rˣ) (h : DiagonalChain w w') :
    DiagonalChain (Fin.cons a w) (Fin.cons a w') := by
  have toBinary {v v' : Fin n → Rˣ} (hstep : DiagonalStep v v') :
      Relation.ReflTransGen BinaryStep v v' := by
    unfold TauCeti.DiagonalStep at hstep
    exact hstep.elim PermutationStep.to_reflTransGen_binaryStep Relation.ReflTransGen.single
  have hbinary : Relation.ReflTransGen BinaryStep w w' := by
    unfold TauCeti.DiagonalChain at h
    exact Relation.ReflTransGen.trans_induction_on h
      (fun _ ↦ Relation.ReflTransGen.refl)
      (fun hstep ↦ toBinary hstep)
      (fun _ _ ih ih' ↦ ih.trans ih')
  have hlift : Relation.ReflTransGen BinaryStep (Fin.cons a w) (Fin.cons a w') :=
    (Relation.ReflTransGen.lift
      (r := fun v v' : Fin n → Rˣ ↦ BinaryStep v v')
      (p := fun v v' : Fin (n + 1) → Rˣ ↦ BinaryStep v v')
      (fun v ↦ Fin.cons a v) (fun _ _ hstep ↦ BinaryStep.cons a hstep)) w w' hbinary
  unfold TauCeti.DiagonalChain
  exact (Relation.ReflTransGen.mono
    (r := fun v v' : Fin (n + 1) → Rˣ ↦ BinaryStep v v')
    (p := fun v v' : Fin (n + 1) → Rˣ ↦ DiagonalStep v v')
    (fun _ _ hstep ↦ show DiagonalStep _ _ from Or.inr hstep)) _ _ hlift

end DiagonalChain

omit [Invertible (2 : K)] in
/-- A presented diagonal form is the scalar-coefficient weighted sum of squares. -/
private theorem presentedForm_eq_weightedSumSquares_coe {n : ℕ} (w : Fin n → Kˣ) :
    presentedForm ⟨n, w⟩ = weightedSumSquares K (fun i ↦ (w i : K)) := by
  rw [presentedForm_eq_weightedSumSquares]
  ext x
  simp only [weightedSumSquares_apply, Units.smul_def, smul_eq_mul]

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
  unfold TauCeti.BinaryStep
  refine ⟨0, 1, Fin.zero_ne_one, ?_, ?_⟩
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

This is the constructive heart of Witt's chain theorem. It repeatedly combines the first
coefficient with the nonzero value represented by the tail. If the tail value is zero, the
represented unit already belongs to the leading binary subform. -/
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
      unfold TauCeti.DiagonalChain
      exact Relation.ReflTransGen.single
        (show DiagonalStep _ _ from Or.inr (binaryStep_replaceHeadPair w c hpair))
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
        refine ⟨replaceHeadPair w c,
          ?_, by simp⟩
        unfold TauCeti.DiagonalChain
        exact Relation.ReflTransGen.single
          (show DiagonalStep _ _ from Or.inr (binaryStep_replaceHeadPair w c hhead))
      · let d' : Kˣ := Units.mk0 d hd
        have htail : d' ∈ unitValueSet
            (weightedSumSquares K fun i ↦ (Fin.tail w i : K)) := by
          rw [mem_unitValueSet, represents_iff, Set.mem_range]
          exact ⟨fun i ↦ x (Fin.succ i), rfl⟩
        obtain ⟨u, hu, hu0⟩ := ih (Fin.tail w) d' htail
        let v : Fin (n + 3) → Kˣ := Fin.cons (w 0) u
        have hwv : DiagonalChain w v := by
          simpa only [v, Fin.cons_self_tail] using hu.cons (w 0)
        have hhead : c ∈ unitValueSet
            (weightedSumSquares K ![(v 0 : K), (v 1 : K)]) := by
          rw [mem_unitValueSet, represents_iff, Set.mem_range]
          refine ⟨![x 0, 1], ?_⟩
          simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one, smul_eq_mul, mul_one]
          change (w 0 : K) * (x 0 * x 0) + (u 0 : K) = c
          rw [hu0]
          exact hsum
        refine ⟨replaceHeadPair v c,
          ?_, by simp⟩
        unfold TauCeti.DiagonalChain at hwv ⊢
        exact hwv.tail
          (show DiagonalStep _ _ from Or.inr (binaryStep_replaceHeadPair v c hhead))

/-- **Witt's chain theorem** in its nontrivial range: two diagonal forms of rank at least two are
isometric if and only if their coefficient families are connected by a diagonal chain. -/
theorem diagonalChain_iff_equivalent {n : ℕ} {w w' : Fin (n + 2) → Kˣ} :
    DiagonalChain w w' ↔
      (weightedSumSquares K fun i ↦ (w i : K)).Equivalent
        (weightedSumSquares K fun i ↦ (w' i : K)) := by
  refine ⟨DiagonalChain.equivalent, fun h ↦ ?_⟩
  induction n with
  | zero =>
      unfold TauCeti.DiagonalChain
      exact Relation.ReflTransGen.single (show DiagonalStep _ _ from Or.inr (by
        unfold TauCeti.BinaryStep
        exact ⟨0, 1, Fin.zero_ne_one, by
        intro k hk0 hk1
        fin_cases k
        · exact (hk0 rfl).elim
        · exact (hk1 rfl).elim, h⟩))
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
      unfold TauCeti.DiagonalChain at hconsChain huw ⊢
      exact hconsChain.trans huw

/-- For a fixed size at least two, Witt's chain theorem in inequality form. -/
theorem diagonalChain_iff_equivalent_of_two_le {n : ℕ} (hn : 2 ≤ n)
    {w w' : Fin n → Kˣ} :
    DiagonalChain w w' ↔
      (weightedSumSquares K fun i ↦ (w i : K)).Equivalent
        (weightedSumSquares K fun i ↦ (w' i : K)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact diagonalChain_iff_equivalent

/-- In rank zero, the unique coefficient families are connected by a diagonal chain and their
weighted sums of squares are isometric. -/
theorem diagonalChain_iff_equivalent_fin_zero {R : Type u} [CommSemiring R]
    {w w' : Fin 0 → Rˣ} :
    DiagonalChain w w' ↔
      (weightedSumSquares R fun i ↦ (w i : R)).Equivalent
        (weightedSumSquares R fun i ↦ (w' i : R)) := by
  constructor
  · exact DiagonalChain.equivalent
  · intro _
    have hww' : w = w' := Subsingleton.elim w w'
    subst w'
    unfold TauCeti.DiagonalChain
    exact Relation.ReflTransGen.refl

/-- In rank one a diagonal chain is equality of coefficient families. Thus the rank hypothesis in
`TauCeti.diagonalChain_iff_equivalent_of_two_le` cannot be removed: isometric one-dimensional
forms need only have coefficients in the same square class. -/
theorem diagonalChain_fin_one_iff {R : Type u} [CommSemiring R] {w w' : Fin 1 → Rˣ} :
    DiagonalChain w w' ↔ w = w' := by
  constructor
  · intro h
    unfold TauCeti.DiagonalChain at h
    induction h using Relation.ReflTransGen.trans_induction_on with
    | refl => rfl
    | single hstep =>
        unfold TauCeti.DiagonalStep at hstep
        rcases hstep with hperm | hbinary
        · unfold TauCeti.PermutationStep at hperm
          obtain ⟨σ, hσ⟩ := hperm
          funext i
          exact (congrArg _ (Subsingleton.elim i (σ i))).trans (hσ i).symm
        · unfold TauCeti.BinaryStep at hbinary
          obtain ⟨i, j, hij, _⟩ := hbinary
          exact (hij (Subsingleton.elim i j)).elim
    | trans _ _ ih ih' => exact ih.trans ih'
  · rintro rfl
    unfold TauCeti.DiagonalChain
    exact Relation.ReflTransGen.refl

end TauCeti
