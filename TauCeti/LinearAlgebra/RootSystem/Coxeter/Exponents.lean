/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Range
public import TauCeti.LinearAlgebra.RootSystem.NumberOfRoots
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.Ring

/-!
# Coxeter numbers and exponent multisets of Dynkin types

This file attaches to every `TauCeti.DynkinType` its **Coxeter number** `t.coxeterNumber` and its
**exponent multiset** `t.exponents`, and proves their uniform combinatorial identities with `t.rank`
and `t.numRoots`, keeping complex-analytic imports out of purely algebraic consumers.

## Main definitions and results

* `TauCeti.DynkinType.coxeterNumber` and `TauCeti.DynkinType.exponents`.
* `TauCeti.DynkinType.numRoots_eq_rank_mul_coxeterNumber` and
  `TauCeti.DynkinType.coxeterNumber_eq_numRoots_div_rank`: `|Φ| = r · h` and `h = |Φ| / r`.
* `TauCeti.DynkinType.card_exponents`, `TauCeti.DynkinType.map_coxeterNumber_sub_exponents`, and
  `TauCeti.DynkinType.two_mul_sum_exponents_eq_numRoots`: `card = r`, `h - e` duality, and
  `2 ∑ eᵢ = |Φ|`.
* `TauCeti.DynkinType.one_mem_exponents`, `TauCeti.DynkinType.coxeterNumber_sub_one_mem_exponents`,
  `TauCeti.DynkinType.pos_of_mem_exponents`, and
  `TauCeti.DynkinType.lt_coxeterNumber_of_mem_exponents`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

namespace TauCeti.DynkinType

/-- The **Coxeter number** `h` of a Dynkin type. For valid types, this is the multiplicative order
of every Coxeter element (`TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType`). -/
def coxeterNumber : DynkinType → ℕ
  | .A n => n + 1
  | .B n | .C n => 2 * n
  | .D n => 2 * n - 2
  | .E6 => 12
  | .E7 => 18
  | .E8 => 30
  | .F4 => 12
  | .G2 => 6

@[simp] lemma coxeterNumber_A (n : ℕ) : (A n).coxeterNumber = n + 1 := (rfl)
@[simp] lemma coxeterNumber_B (n : ℕ) : (B n).coxeterNumber = 2 * n := (rfl)
@[simp] lemma coxeterNumber_C (n : ℕ) : (C n).coxeterNumber = 2 * n := (rfl)
@[simp] lemma coxeterNumber_D (n : ℕ) : (D n).coxeterNumber = 2 * n - 2 := (rfl)
@[simp] lemma coxeterNumber_E6 : E6.coxeterNumber = 12 := (rfl)
@[simp] lemma coxeterNumber_E7 : E7.coxeterNumber = 18 := (rfl)
@[simp] lemma coxeterNumber_E8 : E8.coxeterNumber = 30 := (rfl)
@[simp] lemma coxeterNumber_F4 : F4.coxeterNumber = 12 := (rfl)
@[simp] lemma coxeterNumber_G2 : G2.coxeterNumber = 6 := (rfl)

/-- Every valid Dynkin type has Coxeter number at least `2`. -/
theorem two_le_coxeterNumber {t : DynkinType} (ht : t.Valid) : 2 ≤ t.coxeterNumber := by
  cases t with
  | A n => have := valid_A.mp ht; simp; omega
  | B n => have := valid_B.mp ht; simp; omega
  | C n => have := valid_C.mp ht; simp; omega
  | D n => have := valid_D.mp ht; simp; omega
  | E6 | E7 | E8 | F4 | G2 => simp

/-- Every valid Dynkin type has positive Coxeter number. -/
theorem coxeterNumber_pos {t : DynkinType} (ht : t.Valid) : 0 < t.coxeterNumber :=
  lt_of_lt_of_le (by decide) (two_le_coxeterNumber ht)

/-- **The root count of a Dynkin type is its rank times its Coxeter number**: `|Φ| = r · h`. -/
theorem numRoots_eq_rank_mul_coxeterNumber (t : DynkinType) :
    t.numRoots = t.rank * t.coxeterNumber := by
  cases t with
  | A n => simp
  | B n | C n => simp; ring
  | D n =>
    rcases n with _ | n
    · simp
    · simp only [numRoots_D, rank_D, coxeterNumber_D]
      rw [show 2 * (n + 1) - 2 = 2 * n by omega, Nat.add_sub_cancel]; ring
  | E6 | E7 | E8 | F4 | G2 => simp

/-- For a valid Dynkin type, `h = |Φ| / r`. -/
theorem coxeterNumber_eq_numRoots_div_rank {t : DynkinType} (ht : t.Valid) :
    t.coxeterNumber = t.numRoots / t.rank := by
  rw [numRoots_eq_rank_mul_coxeterNumber, Nat.mul_div_right _ (rank_pos ht)]

/-- The **multiset of exponents** of a Dynkin type. In type `D₂ₙ` (`n ≥ 2`), the middle exponent
`2n - 1` occurs with multiplicity `2`, which is why the exponents form a `Multiset ℕ` rather than a
`Finset ℕ`. -/
def exponents : DynkinType → Multiset ℕ
  | .A n => (Multiset.range n).map (· + 1)
  | .B n | .C n => (Multiset.range n).map (2 * · + 1)
  | .D n => if n = 0 then 0 else (n - 1) ::ₘ (Multiset.range (n - 1)).map (2 * · + 1)
  | .E6 => {1, 4, 5, 7, 8, 11}
  | .E7 => {1, 5, 7, 9, 11, 13, 17}
  | .E8 => {1, 7, 11, 13, 17, 19, 23, 29}
  | .F4 => {1, 5, 7, 11}
  | .G2 => {1, 5}

@[simp] lemma exponents_A (n : ℕ) : (A n).exponents = (Multiset.range n).map (· + 1) := (rfl)
@[simp] lemma exponents_B (n : ℕ) : (B n).exponents = (Multiset.range n).map (2 * · + 1) := (rfl)
@[simp] lemma exponents_C (n : ℕ) : (C n).exponents = (Multiset.range n).map (2 * · + 1) := (rfl)
@[simp] lemma exponents_D (n : ℕ) :
    (D n).exponents =
      if n = 0 then 0 else (n - 1) ::ₘ (Multiset.range (n - 1)).map (2 * · + 1) := (rfl)
@[simp] lemma exponents_E6 : E6.exponents = {1, 4, 5, 7, 8, 11} := (rfl)
@[simp] lemma exponents_E7 : E7.exponents = {1, 5, 7, 9, 11, 13, 17} := (rfl)
@[simp] lemma exponents_E8 : E8.exponents = {1, 7, 11, 13, 17, 19, 23, 29} := (rfl)
@[simp] lemma exponents_F4 : F4.exponents = {1, 5, 7, 11} := (rfl)
@[simp] lemma exponents_G2 : G2.exponents = {1, 5} := (rfl)

/-- **A Dynkin type has `t.rank` exponents**, counted with multiplicity. -/
@[simp]
theorem card_exponents (t : DynkinType) : t.exponents.card = t.rank := by
  cases t with
  | D n => rcases n with _ | n <;> simp
  | _ => simp

/-- Every exponent of `t` is bounded above by `t.coxeterNumber`. -/
theorem le_coxeterNumber_of_mem_exponents {t : DynkinType} {e : ℕ} (he : e ∈ t.exponents) :
    e ≤ t.coxeterNumber := by
  cases t with
  | A n | B n | C n =>
    simp only [exponents_A, exponents_B, exponents_C, coxeterNumber_A, coxeterNumber_B,
      coxeterNumber_C, Multiset.mem_map, Multiset.mem_range] at he ⊢
    obtain ⟨k, _, rfl⟩ := he; omega
  | D n =>
    rcases n with _ | n
    · simp at he
    · simp only [exponents_D, Nat.succ_ne_zero, ↓reduceIte, coxeterNumber_D, Multiset.mem_cons,
        Multiset.mem_map, Multiset.mem_range] at he ⊢
      rcases he with rfl | ⟨k, _, rfl⟩ <;> omega
  | E6 | E7 | E8 | F4 | G2 => revert e; decide

private theorem map_sub_map_range (m h : ℕ) (f : ℕ → ℕ) (hf : ∀ k < m, h - f k = f (m - 1 - k)) :
    ((Multiset.range m).map f).map (h - ·) = (Multiset.range m).map f := by
  have hrev : (Multiset.range m).map (fun k => m - 1 - k) = Multiset.range m := by
    refine ((Multiset.Nodup.map_on (fun x hx y hy hxy => ?_) (Multiset.nodup_range m)).ext
      (Multiset.nodup_range m)).2 fun x => ?_
    · rw [Multiset.mem_range] at hx hy; omega
    · simp only [Multiset.mem_map, Multiset.mem_range]
      exact ⟨fun ⟨k, hk, hkx⟩ => by omega, fun hx => ⟨m - 1 - x, by omega, by omega⟩⟩
  rw [Multiset.map_map,
    Multiset.map_congr rfl fun k hk =>
      show ((h - ·) ∘ f) k = (f ∘ fun j => m - 1 - j) k from hf k (Multiset.mem_range.1 hk),
    ← Multiset.map_map, hrev]

/-- **Exponent duality**: replacing each exponent `e` by `h - e` preserves `t.exponents`. -/
theorem map_coxeterNumber_sub_exponents (t : DynkinType) :
    t.exponents.map (t.coxeterNumber - ·) = t.exponents := by
  cases t with
  | A n => exact map_sub_map_range n (n + 1) (· + 1) fun k hk => by omega
  | B n | C n => exact map_sub_map_range n (2 * n) (2 * · + 1) fun k hk => by omega
  | D n =>
    rcases n with _ | n
    · simp
    · simp only [exponents_D, Nat.succ_ne_zero, ↓reduceIte, coxeterNumber_D, Nat.add_sub_cancel,
        Multiset.map_cons]
      rw [show 2 * (n + 1) - 2 - n = n by omega,
        map_sub_map_range n (2 * (n + 1) - 2) (2 * · + 1) fun k hk => by omega]
  | E6 | E7 | E8 | F4 | G2 => decide

/-- **Twice the sum of the exponents of `t` equals its number of roots**: `2 ∑ eᵢ = |Φ|`. -/
theorem two_mul_sum_exponents_eq_numRoots (t : DynkinType) :
    2 * t.exponents.sum = t.numRoots := by
  have hpair : (t.exponents.map (fun e => e + (t.coxeterNumber - e))).sum =
      t.rank * t.coxeterNumber := by
    rw [Multiset.map_congr rfl fun e he => Nat.add_sub_of_le (le_coxeterNumber_of_mem_exponents he)]
    simp [card_exponents]
  rw [Multiset.sum_map_add, show t.exponents.map (fun e => e) = t.exponents by simp,
    map_coxeterNumber_sub_exponents] at hpair
  rw [two_mul, hpair, numRoots_eq_rank_mul_coxeterNumber]

/-- Every exponent of a valid Dynkin type is positive. -/
theorem pos_of_mem_exponents {t : DynkinType} (ht : t.Valid) {e : ℕ} (he : e ∈ t.exponents) :
    0 < e := by
  cases t with
  | A n | B n | C n =>
    simp only [exponents_A, exponents_B, exponents_C, Multiset.mem_map, Multiset.mem_range] at he
    obtain ⟨k, _, rfl⟩ := he; omega
  | D n =>
    have hn : 4 ≤ n := valid_D.mp ht
    simp only [exponents_D, show n ≠ 0 by omega, ↓reduceIte, Multiset.mem_cons, Multiset.mem_map,
      Multiset.mem_range] at he
    rcases he with rfl | ⟨k, _, rfl⟩ <;> omega
  | E6 | E7 | E8 | F4 | G2 => revert e; decide

/-- Every exponent of a valid Dynkin type is strictly less than its Coxeter number. -/
theorem lt_coxeterNumber_of_mem_exponents {t : DynkinType} (ht : t.Valid) {e : ℕ}
    (he : e ∈ t.exponents) : e < t.coxeterNumber := by
  have hpos := pos_of_mem_exponents ht (by
    rw [← map_coxeterNumber_sub_exponents t]; exact Multiset.mem_map.2 ⟨e, he, rfl⟩)
  omega

/-- **`1` is an exponent of every valid Dynkin type.** -/
theorem one_mem_exponents {t : DynkinType} (ht : t.Valid) : 1 ∈ t.exponents := by
  cases t with
  | A n => exact Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (valid_A.mp ht), rfl⟩
  | B n => have := valid_B.mp ht; exact Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), rfl⟩
  | C n => have := valid_C.mp ht; exact Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), rfl⟩
  | D n =>
    have := valid_D.mp ht
    simp only [exponents_D, show n ≠ 0 by omega, ↓reduceIte, Multiset.mem_cons]
    exact Or.inr (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), rfl⟩)
  | E6 | E7 | E8 | F4 | G2 => simp

/-- **`h - 1` is an exponent of every valid Dynkin type.** -/
theorem coxeterNumber_sub_one_mem_exponents {t : DynkinType} (ht : t.Valid) :
    t.coxeterNumber - 1 ∈ t.exponents := by
  rw [← map_coxeterNumber_sub_exponents t]; exact Multiset.mem_map.2 ⟨1, one_mem_exponents ht, rfl⟩

end TauCeti.DynkinType

end
