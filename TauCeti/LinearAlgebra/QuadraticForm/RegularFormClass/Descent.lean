/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.WittChain

/-!
# Descending diagonal invariants to isometry classes

This file constructs functions on isometry classes of diagonal presentations from functions on
their coefficient tuples. Invariance under permutation and binary replacement handles ranks at
least two through Witt's chain theorem. In rank one, the coefficients of isometric forms can
differ by a square, so descent also requires invariance under that relation.

The chain theorem follows Lam, *Introduction to Quadratic Forms over Fields*, Chapter I,
Theorem 5.2.
-/

public section

namespace TauCeti

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)]

omit [Invertible (2 : K)] in
private theorem diagonalChain_invariant {α : Type v}
    (f : (p : RegularFormPresentation K) → α)
    (hperm : ∀ {n} {w w' : Fin n → Kˣ}, PermutationStep w w' →
      f ⟨n, w⟩ = f ⟨n, w'⟩)
    (hbin : ∀ {n} {w w' : Fin n → Kˣ}, BinaryStep w w' →
      f ⟨n, w⟩ = f ⟨n, w'⟩)
    {n : ℕ} {w w' : Fin n → Kˣ} (h : DiagonalChain w w') :
    f ⟨n, w⟩ = f ⟨n, w'⟩ := by
  apply h.inductionOn (P := fun v => f ⟨n, w⟩ = f ⟨n, v⟩) rfl
  intro v v' hstep hv
  exact hstep.elim (fun hp => hv.trans (hperm hp)) (fun hb => hv.trans (hbin hb))

private theorem lift_eq_of_equivalent {α : Type v}
    (f : (p : RegularFormPresentation K) → α)
    (hperm : ∀ {n} {w w' : Fin n → Kˣ}, PermutationStep w w' →
      f ⟨n, w⟩ = f ⟨n, w'⟩)
    (hbin : ∀ {n} {w w' : Fin n → Kˣ}, BinaryStep w w' →
      f ⟨n, w⟩ = f ⟨n, w'⟩)
    (hone : ∀ a b : Kˣ, IsSquare (a * b) →
      f ⟨1, fun _ => a⟩ = f ⟨1, fun _ => b⟩)
    {p q : RegularFormPresentation K} (h : (presentedForm p).Equivalent (presentedForm q)) :
    f p = f q := by
  cases p with
  | mk n w =>
    cases q with
    | mk m v =>
      have hn : n = m := fst_eq_of_presentedForm_equivalent h
      -- Reindex the second coefficient family along the rank equality so both presentations have
      -- the same index type.
      let r : RegularFormPresentation K := ⟨n, v ∘ Fin.cast hn⟩
      have hrq : (presentedForm r).Equivalent (presentedForm ⟨m, v⟩) := by
        rw [presentedForm_eq_weightedSumSquares, presentedForm_eq_weightedSumSquares]
        exact (equivalent_weightedSumSquares_comp (fun i => (v i : K)) (finCongr hn)).symm
      have hpr : (presentedForm ⟨n, w⟩).Equivalent (presentedForm r) := h.trans hrq.symm
      have hr : r = ⟨m, v⟩ := by
        apply RegularFormPresentation.ext hn
        intro i
        rfl
      by_cases h0 : n = 0
      · subst n
        have hm : m = 0 := by omega
        subst m
        have hpq : (⟨0, w⟩ : RegularFormPresentation K) = ⟨0, v⟩ := by
          apply RegularFormPresentation.ext (p := ⟨0, w⟩) (q := ⟨0, v⟩) rfl
          intro i
          exact Fin.elim0 i
        exact congrArg f hpq
      by_cases h1 : n = 1
      · subst n
        have hm : m = 1 := by omega
        subst m
        have hsq : IsSquare ((w 0) * (v 0)) := by
          have hprUnit : (QuadraticMap.weightedSumSquares K w).Equivalent
              (QuadraticMap.weightedSumSquares K r.2) := by
            simpa only [presentedForm_eq_weightedSumSquares] using hpr
          have := isSquare_prod_mul_prod_of_equivalent (R := K) (w := w) (v := r.2) hprUnit
          simpa [r] using this
        have hp : (⟨1, w⟩ : RegularFormPresentation K) = ⟨1, fun _ => w 0⟩ := by
          apply RegularFormPresentation.ext (p := ⟨1, w⟩) (q := ⟨1, fun _ => w 0⟩) rfl
          intro i
          fin_cases i
          rfl
        have hv : (⟨1, v⟩ : RegularFormPresentation K) = ⟨1, fun _ => v 0⟩ := by
          apply RegularFormPresentation.ext (p := ⟨1, v⟩) (q := ⟨1, fun _ => v 0⟩) rfl
          intro i
          fin_cases i
          rfl
        rw [hp, hv]
        exact hone _ _ hsq
      · have hn2 : 2 ≤ n := by omega
        have hprCoe : (QuadraticMap.weightedSumSquares K (fun i => (w i : K))).Equivalent
            (QuadraticMap.weightedSumSquares K (fun i => (r.2 i : K))) := by
          rw [← presentedForm_eq_weightedSumSquares_coe,
            ← presentedForm_eq_weightedSumSquares_coe]
          exact hpr
        have hchain : DiagonalChain w r.2 :=
          (diagonalChain_iff_equivalent_of_two_le hn2).mpr hprCoe
        calc
          f ⟨n, w⟩ = f r := diagonalChain_invariant f hperm hbin hchain
          _ = f ⟨m, v⟩ := congrArg f hr

/-- Lift a function on diagonal coefficient presentations to isometry classes when it is
invariant under coefficient permutations and binary replacements. The rank-one condition records
the necessary invariance under changing a coefficient by a square, since no binary replacement
is available in that rank. -/
def RegularFormClass.liftDiagonal {α : Type v} (f : (p : RegularFormPresentation K) → α)
    (hperm : ∀ {n} {w w' : Fin n → Kˣ}, PermutationStep w w' →
      f ⟨n, w⟩ = f ⟨n, w'⟩)
    (hbin : ∀ {n} {w w' : Fin n → Kˣ}, BinaryStep w w' →
      f ⟨n, w⟩ = f ⟨n, w'⟩)
    (hone : ∀ a b : Kˣ, IsSquare (a * b) →
      f ⟨1, fun _ => a⟩ = f ⟨1, fun _ => b⟩) :
    RegularFormClass K → α :=
  Quotient.lift f (fun _ _ h => lift_eq_of_equivalent f hperm hbin hone h)

/-- The lifted invariant agrees with its defining function on every diagonal presentation. -/
@[simp]
theorem RegularFormClass.liftDiagonal_mk {α : Type v}
    (f : (p : RegularFormPresentation K) → α)
    (hperm : ∀ {n} {w w' : Fin n → Kˣ}, PermutationStep w w' →
      f ⟨n, w⟩ = f ⟨n, w'⟩)
    (hbin : ∀ {n} {w w' : Fin n → Kˣ}, BinaryStep w w' →
      f ⟨n, w⟩ = f ⟨n, w'⟩)
    (hone : ∀ a b : Kˣ, IsSquare (a * b) →
      f ⟨1, fun _ => a⟩ = f ⟨1, fun _ => b⟩) (p : RegularFormPresentation K) :
    RegularFormClass.liftDiagonal f hperm hbin hone (Quotient.mk _ p) = f p := by
  rfl

/-- The lifted invariant is the unique function on isometry classes with the stated values on
diagonal presentations. -/
theorem RegularFormClass.liftDiagonal_unique {α : Type v}
    (f : (p : RegularFormPresentation K) → α)
    (hperm : ∀ {n} {w w' : Fin n → Kˣ}, PermutationStep w w' →
      f ⟨n, w⟩ = f ⟨n, w'⟩)
    (hbin : ∀ {n} {w w' : Fin n → Kˣ}, BinaryStep w w' →
      f ⟨n, w⟩ = f ⟨n, w'⟩)
    (hone : ∀ a b : Kˣ, IsSquare (a * b) →
      f ⟨1, fun _ => a⟩ = f ⟨1, fun _ => b⟩)
    (g : RegularFormClass K → α)
    (hg : ∀ p, g (Quotient.mk _ p) = f p) :
    g = RegularFormClass.liftDiagonal f hperm hbin hone := by
  funext x
  induction x using Quotient.inductionOn with
  | h p => rw [hg, RegularFormClass.liftDiagonal_mk]

end TauCeti
