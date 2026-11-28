/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Units
public import TauCeti.Data.Fintype.Fiber

/-!
# Signatures of the two theta-lift grids

Each grid node has base indices and two families of added blocks. The added entries are
positive, so the signature is determined by a parity condition on the base. On the diagonal,
the enlarged grid has the signature of the ordinary grid plus one line, whose sign alternates.

The sign convention and the diagonal comparison are those of `New.Data.gridSigns`,
`New.Data.negCount_gridSigns`, and `New.Data.gridDiagEquiv` in
`grh/src/New/UpperBound/Objects/Parameters.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

namespace TauCeti.ThetaLift

/-- Indices of the node `(i, j)`, with base rank `r` and block length `t`. In the enlarged
node there is one more base index, and the two block lengths are `t + 1` and `t - 1`. -/
abbrev GridIndex (enlarged : Bool) (r t i j : ℕ) :=
  Fin (r + enlarged.toNat) ⊕
    ((Fin i × Fin (t + enlarged.toNat)) ⊕ (Fin j × Fin (t - enlarged.toNat)))

/-- The sign on a base index `n`: for `a = n + 1 - k` (truncated subtraction), the exponent
of `-1` is `o + a + min (a - o) j`, where `o` is the offset. Added indices have sign `1`. -/
def gridSign {enlarged : Bool} {r t i j : ℕ} (k o : ℕ) : GridIndex enlarged r t i j → ℤˣ :=
  Sum.elim (fun n ↦
    let a := (n : ℕ) + 1 - k
    if Odd (o + a + min (a - o) j) then -1 else 1) (fun _ ↦ 1)

/-- The sign at a base index, expressed through the parity of its exponent. -/
@[simp] theorem gridSign_inl {enlarged : Bool} {r t i j : ℕ} (k o : ℕ)
    (n : Fin (r + enlarged.toNat)) :
    gridSign (t := t) (i := i) (j := j) k o (Sum.inl n) =
      if Odd (o + (n + 1 - k) + min (n + 1 - k - o) j : ℕ) then -1 else 1 := (rfl)

/-- The parity criterion for a negative base index, at arbitrary offset. -/
theorem gridSign_inl_eq_neg_one_iff {enlarged : Bool} {r t i j : ℕ} (k o : ℕ)
    (n : Fin (r + enlarged.toNat)) :
    gridSign (t := t) (i := i) (j := j) k o (Sum.inl n) = -1 ↔
      Odd (o + (n + 1 - k) + min (n + 1 - k - o) j : ℕ) := by
  have hsign : (1 : ℤˣ) ≠ -1 := by decide
  by_cases h : Odd (o + (n + 1 - k) + min (n + 1 - k - o) j : ℕ) <;>
    simp [h, hsign]

/-- Every entry in either family of added blocks is positive. -/
@[simp] theorem gridSign_inr {enlarged : Bool} {r t i j : ℕ} (k o : ℕ)
    (n : (Fin i × Fin (t + enlarged.toNat)) ⊕ (Fin j × Fin (t - enlarged.toNat))) :
    gridSign (r := r) k o (Sum.inr n) = 1 := (rfl)

/-- At offset zero the negative base entries occur at `k + j`, `k + j + 2`, and so on. -/
theorem gridSign_inl_eq_neg_one_iff_even {enlarged : Bool} {r t i j : ℕ} (k : ℕ)
    (n : Fin (r + enlarged.toNat)) :
    gridSign (t := t) (i := i) (j := j) k 0 (Sum.inl n) = -1 ↔
      k + j ≤ (n : ℕ) ∧ Even ((n : ℕ) - (k + j)) := by
  rw [gridSign_inl_eq_neg_one_iff, Nat.odd_iff, Nat.even_iff]
  omega

/-- At offset zero the number of negative entries depends only on the base length and the
number of down blocks, not on the number of up blocks or their lengths. -/
theorem occCount_gridSign_neg_one (enlarged : Bool) (r t i j k : ℕ) :
    Function.occCount (gridSign (enlarged := enlarged) (r := r) (t := t) (i := i) (j := j) k 0)
      (-1) = (r + enlarged.toNat + 1 - k - j) / 2 := by
  rw [Function.occCount_def]
  refine (Nat.card_congr (Equiv.symm ?_)).trans (Nat.card_fin _)
  refine Equiv.ofBijective (fun a : Fin ((r + enlarged.toNat + 1 - k - j) / 2) ↦
    ⟨Sum.inl ⟨k + j + 2 * (a : ℕ), by have := a.isLt; omega⟩,
      (gridSign_inl_eq_neg_one_iff_even k _).2 (by
        simp only [Nat.even_iff]
        omega)⟩) ⟨?_, ?_⟩
  · intro a b hab
    have h := Sum.inl.inj (congrArg Subtype.val hab)
    apply Fin.ext
    have he : k + j + 2 * (a : ℕ) = k + j + 2 * (b : ℕ) := congrArg Fin.val h
    omega
  · rintro ⟨n | n, hn⟩
    · obtain ⟨hle, heven⟩ := (gridSign_inl_eq_neg_one_iff_even k n).1 hn
      rw [Nat.even_iff] at heven
      refine ⟨⟨((n : ℕ) - (k + j)) / 2, by have := n.isLt; omega⟩, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inl
      have hval : k + j + 2 * (((n : ℕ) - (k + j)) / 2) = (n : ℕ) := by omega
      exact Fin.ext hval
    · exact False.elim ((by decide : (1 : ℤˣ) ≠ -1) ((gridSign_inr k 0 n).symm.trans hn))

/-- All signs at offset zero are positive exactly when the base length is at most `k + j`.
In particular, for `r + 1 = k + m` this holds in both grids as soon as `j ≥ m`. -/
theorem gridSign_eq_one_iff {enlarged : Bool} {r t i j k : ℕ} :
    gridSign (enlarged := enlarged) (r := r) (t := t) (i := i) (j := j) k 0 = 1 ↔
      r + enlarged.toNat ≤ k + j := by
  constructor
  · intro h
    by_contra! hlt
    let n : Fin (r + enlarged.toNat) := ⟨k + j, hlt⟩
    have hneg := (gridSign_inl_eq_neg_one_iff_even (t := t) (i := i) (j := j) k n).2
      (by simp [n])
    exact (by decide : (1 : ℤˣ) ≠ -1) ((congrFun h (Sum.inl n)).symm.trans hneg)
  · intro h
    funext x
    rcases Int.units_eq_one_or (gridSign k 0 x) with hx | hx
    · exact hx
    rcases x with n | n
    · have := (gridSign_inl_eq_neg_one_iff_even k n).1 hx
      have := n.isLt
      omega
    · exact gridSign_inr k 0 n

/-- On the diagonal and at offset zero, the enlarged node has the signature of the ordinary
node with one additional line of sign `(-1)^j`. The chain length `m` is even,
`r + 1 = k + m`, and `j` has not passed `m`. The comparison reindexes the full signed sets;
it does not assert that this reindexing preserves their doubled parameters. -/
theorem exists_gridIndex_diag_equiv (r t j k m : ℕ) (ht : 0 < t) (hm : Even m)
    (hr : r + 1 = k + m) (hj : j ≤ m) :
    ∃ e : (GridIndex false r t j j ⊕ Unit) ≃ GridIndex true r t j j,
      gridSign k 0 ∘ e = Sum.elim (gridSign k 0) (fun _ ↦ if Odd j then -1 else 1) := by
  classical
  apply Function.exists_equiv_of_occCount_eq
  let u : GridIndex false r t j j ⊕ Unit → ℤˣ :=
    Sum.elim (gridSign k 0) (fun _ ↦ if Odd j then -1 else 1)
  let v : GridIndex true r t j j → ℤˣ := gridSign k 0
  have hneg : Function.occCount u (-1) = Function.occCount v (-1) := by
    have hs : Function.occCount u (-1) =
        (m - j) / 2 + (if Odd j then 1 else 0) := by
      have hsign : (1 : ℤˣ) ≠ -1 := by decide
      have hu : Function.occCount u (-1) =
          Function.occCount (gridSign (enlarged := false) (r := r) (t := t) (i := j)
            (j := j) k 0) (-1) + (if Odd j then 1 else 0) := by
        by_cases h : Odd j <;>
          (simp [Function.occCount_eq_sum, Fintype.sum_sum_type, u, h, hsign]; rfl)
      rw [hu, occCount_gridSign_neg_one]
      simp only [Bool.toNat_false, Nat.add_zero]
      omega
    rw [hs, occCount_gridSign_neg_one]
    simp only [Bool.toNat_true]
    have hbase : r + 1 + 1 - k - j = m - j + 1 := by omega
    rw [hbase]
    rw [Nat.even_iff] at hm
    by_cases h : Odd j
    · have hmod := Nat.odd_iff.mp h
      simp only [h, ite_true]
      omega
    · have hmod := Nat.not_odd_iff.mp h
      simp only [h, ite_false]
      omega
  have hcard : Nat.card (GridIndex false r t j j ⊕ Unit) = Nat.card (GridIndex true r t j j) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    simp [GridIndex, Nat.card_eq_fintype_card, Nat.mul_add]
    omega
  have htotal (X : Type) [Finite X] (f : X → ℤˣ) :
      Function.occCount f 1 + Function.occCount f (-1) = Nat.card X := by
    have h := Function.sum_occCount_eq_card f (T := {1, -1}) fun x ↦ by
      simpa using Int.units_eq_one_or (f x)
    have hsign : (1 : ℤˣ) ≠ -1 := by decide
    rw [Finset.sum_insert (by simpa using hsign), Finset.sum_singleton] at h
    exact h
  intro a
  rcases Int.units_eq_one_or a with rfl | rfl
  · have hu := htotal _ u
    have hv := htotal _ v
    rw [hneg] at hu
    exact Nat.add_right_cancel (hu.trans (hcard.trans hv.symm))
  · exact hneg

end TauCeti.ThetaLift
