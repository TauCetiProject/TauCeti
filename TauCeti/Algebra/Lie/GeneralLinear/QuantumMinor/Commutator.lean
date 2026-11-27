/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Basic
public import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.NoncommRing

/-!
# Infinitesimal covariance of quantum minors

A matrix unit acts on a quantum minor by replacing one row index at a time, minus the
corresponding column replacements. The spectral shift stays in the original column slot.
Together with row and column alternation, this is the commutator calculation for centrality
of the full quantum determinant (Molev–Nazarov–Olshanski, *Yangians and classical Lie algebras*,
§2, Theorem 2.10 and Remark 2.11).
-/

public section

namespace Matrix

open Equiv Equiv.Perm Function

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A] {n : ℕ}

/-- The shifted entries obey the same adjoint action as the unshifted matrix units: the two
contributions of the spectral scalar cancel. -/
private theorem lie_shifted_entry (E : Matrix ι ι A) {p q i j : ι}
    (hE : ⁅E p q, E i j⁆ = (if q = i then E p j else 0) - (if p = j then E i q else 0)) (v : K) :
    ⁅E p q, (if i = j then algebraMap K A v else 0) + E i j⁆ =
      (if q = i then (if p = j then algebraMap K A v else 0) + E p j else 0) -
        (if p = j then (if i = q then algebraMap K A v else 0) + E i q else 0) := by
  have hscalar : ⁅E p q, algebraMap K A v⁆ = 0 := by
    rw [Ring.lie_def, (Algebra.commute_algebraMap_right v (E p q)).eq, sub_self]
  have hz : ⁅E p q, if i = j then algebraMap K A v else 0⁆ = 0 := by
    split_ifs
    · exact hscalar
    · exact lie_zero (L := A) (M := A) _
  rw [lie_add (L := A) (M := A), hz, zero_add, hE]
  by_cases hi : q = i <;> by_cases hj : p = j <;>
    simp [hi, hj, eq_comm, add_sub_add_left_eq_sub]

/-- In one Leibniz term, replacing its `j`-th factor by its bracket is the difference between
changing the row tuple at `σ j` and changing the column tuple at `j`, when those indices match. -/
private theorem lie_quantumMinor_summand (E : Matrix ι ι A) {p q : ι}
    (u : K) (a b : Fin n → ι) (σ : Perm (Fin n)) (j : Fin n)
    (hE : ⁅E p q, E (a (σ j)) (b j)⁆ = (if q = a (σ j) then E p (b j) else 0) -
      (if p = b j then E (a (σ j)) q else 0)) :
    let T (k : Fin n) (i l : ι) :=
      (if i = l then algebraMap K A (u - (k.val : K)) else 0) + E i l
    let P (f : Fin n → A) := (List.ofFn f).prod
    P (update (fun k ↦ T k (a (σ k)) (b k)) j ⁅E p q, T j (a (σ j)) (b j)⁆) =
      (if q = a (σ j) then P (fun k ↦ T k (update a (σ j) p (σ k)) (b k)) else 0) -
        (if p = b j then P (fun k ↦ T k (a (σ k)) (update b j q k)) else 0) := by
  intro T P
  let f := fun k ↦ T k (a (σ k)) (b k)
  let l := if q = a (σ j) then T j p (b j) else 0
  let r := if p = b j then T j (a (σ j)) q else 0
  have hupdate_ite (c : Prop) [Decidable c] (x : A) :
      P (update f j (if c then x else 0)) = if c then P (update f j x) else 0 := by
    split_ifs
    · rfl
    · simpa only [P, MultilinearMap.mkPiAlgebraFin_apply] using
        (MultilinearMap.mkPiAlgebraFin ℤ n A).map_update_zero f j
  have hl : P (update f j l) =
      if q = a (σ j) then P (fun k ↦ T k (update a (σ j) p (σ k)) (b k)) else 0 := by
    simp only [l, hupdate_ite]
    congr 2
    funext k
    by_cases hk : k = j <;> simp [f, hk]
  have hr : P (update f j r) =
      if p = b j then P (fun k ↦ T k (a (σ k)) (update b j q k)) else 0 := by
    simp only [r, hupdate_ite]
    congr 2
    funext k
    by_cases hk : k = j <;> simp [f, hk]
  have hbracket : ⁅E p q, T j (a (σ j)) (b j)⁆ = l - r := by
    simpa only [T, l, r] using lie_shifted_entry E hE (u - (j.val : K))
  rw [hbracket, ← hl, ← hr]
  simpa only [P, MultilinearMap.mkPiAlgebraFin_apply] using
    (MultilinearMap.mkPiAlgebraFin ℤ n A).map_update_sub f j l r

/-- The commutator of a matrix unit with a quantum minor is the sum of the row-index
replacements minus the sum of the column-index replacements. Repeated indices are allowed,
and the relations are needed only between the acting entry `E p q` and the unshifted entries
of the minor. -/
theorem lie_quantumMinor (E : Matrix ι ι A) {p q : ι} (u : K) (a b : Fin n → ι)
    (hE : ∀ i j, ⁅E p q, E (a i) (b j)⁆ = (if q = a i then E p (b j) else 0) -
      (if p = b j then E (a i) q else 0)) :
    ⁅E p q, E.quantumMinor u a b⁆ =
      (∑ i, if q = a i then E.quantumMinor u (update a i p) b else 0) -
        ∑ j, if p = b j then E.quantumMinor u a (update b j q) else 0 := by
  let T (j : Fin n) (i k : ι) :=
    (if i = k then algebraMap K A (u - (j.val : K)) else 0) + E i k
  let P (f : Fin n → A) := (List.ofFn f).prod
  have hminor (c d : Fin n → ι) : E.quantumMinor u c d =
      ∑ σ : Perm (Fin n), sign σ • P (fun j ↦ T j (c (σ j)) (d j)) := by
    simp only [quantumMinor_eq_columnDet, columnDet_apply, of_apply, P, T]
  have hslot (σ : Perm (Fin n)) (j : Fin n) :
      P (update (fun k ↦ T k (a (σ k)) (b k)) j ⁅E p q, T j (a (σ j)) (b j)⁆) =
        (if q = a (σ j) then P (fun k ↦ T k (update a (σ j) p (σ k)) (b k)) else 0) -
          (if p = b j then P (fun k ↦ T k (a (σ k)) (update b j q k)) else 0) :=
    lie_quantumMinor_summand E u a b σ j (hE _ _)
  have hprod (f : Fin n → A) : ⁅E p q, P f⁆ = ∑ j, P (update f j ⁅E p q, f j⁆) := by
    apply TauCeti.map_prod_ofFn_of_leibniz (fun z ↦ ⁅(E p q : A), z⁆) _ f
    intro x y
    simp only [Ring.lie_def]
    noncomm_ring
  simp only [hminor, Units.smul_def]
  rw [lie_sum (L := A) (M := A)]
  simp_rw [lie_zsmul (L := A) (M := A), hprod, hslot, Finset.sum_sub_distrib, smul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp_rw [Finset.smul_sum, smul_ite, smul_zero]
    conv_lhs =>
      arg 2
      ext σ
      rw [Equiv.sum_comp σ (fun i ↦
        if q = a i then (sign σ).val • P (fun k ↦ T k (update a i p (σ k)) (b k)) else 0)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : q = a i <;> simp [h, P]
  · simp_rw [Finset.smul_sum, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : p = b j <;> simp [h, P]

/-- Diagonal matrix units commute with every principal quantum minor, including the full
quantum determinant. The principal tuple may repeat indices. -/
theorem lie_diagonal_quantumMinor_self (E : Matrix ι ι A) {p : ι} (u : K) (a : Fin n → ι)
    (hE : ∀ i j, ⁅E p p, E (a i) (a j)⁆ = (if p = a i then E p (a j) else 0) -
      (if p = a j then E (a i) p else 0)) : ⁅E p p, E.quantumMinor u a a⁆ = 0 := by
  rw [E.lie_quantumMinor u a a hE, sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ ↦ by
    by_cases hi : p = a i <;> simp [hi]

end Matrix
