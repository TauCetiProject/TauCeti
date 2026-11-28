/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Mathlib.Data.Fin.Rev
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic.FieldSimp

/-!
# Index of the lower-triangular Borel subgroup of `GL_k(K)`

This file defines the lower-triangular Borel subgroup of `GL (Fin k) K` and bounds its index over
a finite field `K` by the `q`-factorial `∏ l : Fin k, (q ^ (l + 1) - 1) / (q - 1)`:

* `TauCeti.lowerTriangularGL`: the subgroup of lower-triangular matrices in `GL (Fin k) R`.
* `TauCeti.card_lowerTriangularGL_ge`: over a finite field `K`, the lower-triangular Borel
  subgroup has at least `∏ i : Fin k, (Nat.card K - 1) * Nat.card K ^ i.val` elements.
* `TauCeti.index_lowerTriangularGL_le`: over a finite field `K`, the index of
  `lowerTriangularGL K k` in `GL (Fin k) K` is at most
  `∏ l : Fin k, ((Nat.card K : ℝ) ^ (l.val + 1) - 1) / (Nat.card K - 1)`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/UpperBound/ElementaryDivisors/DefectCount.lean` (`New.index_borel_le`).
-/

public section

open Matrix Finset

namespace TauCeti

/-- The subgroup of lower-triangular matrices in `GL (Fin k) R`: matrices whose `(i, j)` entry
vanishes whenever `i < j`. -/
def lowerTriangularGL (R : Type*) [CommRing R] (k : ℕ) : Subgroup (GL (Fin k) R) where
  carrier := {g | ∀ i j : Fin k, i < j → (g : Matrix (Fin k) (Fin k) R) i j = 0}
  mul_mem' {a b} ha hb i j hij := by
    rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    obtain hil | hli := lt_or_ge i l
    · rw [ha i l hil, zero_mul]
    · rw [hb l j (hli.trans_lt hij), mul_zero]
  one_mem' i j hij := by simp [hij.ne]
  inv_mem' {a} ha := by
    have htri : (a : Matrix (Fin k) (Fin k) R).BlockTriangular OrderDual.toDual :=
      fun r c hrc ↦ ha r c hrc
    have hdet : IsUnit (∏ i : Fin k, (a : Matrix (Fin k) (Fin k) R) i i) := by
      rw [← Matrix.det_of_isLowerTriangular (a : Matrix (Fin k) (Fin k) R) htri]
      exact (Matrix.isUnit_iff_isUnit_det _).mp a.isUnit
    have hdiag (i : Fin k) : IsUnit ((a : Matrix (Fin k) (Fin k) R) i i) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j : Fin k ↦ (a : Matrix (Fin k) (Fin k) R) j j) (Finset.mem_univ i)] at hdet
      exact isUnit_of_mul_isUnit_left hdet
    refine wellFounded_lt.fix fun i ih j hij ↦ ?_
    have hmul : ((a : Matrix (Fin k) (Fin k) R) * (↑a⁻¹ : Matrix (Fin k) (Fin k) R)) i j = 0 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_ne hij.ne]
    rw [Matrix.mul_apply] at hmul
    have hsum : ∑ l : Fin k, (a : Matrix (Fin k) (Fin k) R) i l *
        (↑a⁻¹ : Matrix (Fin k) (Fin k) R) l j =
        (a : Matrix (Fin k) (Fin k) R) i i * (↑a⁻¹ : Matrix (Fin k) (Fin k) R) i j := by
      refine Finset.sum_eq_single i (fun l _ hne ↦ ?_) (by simp)
      obtain hlt | hgt := lt_or_gt_of_ne hne
      · rw [ih l hlt j (hlt.trans hij), mul_zero]
      · rw [ha i l hgt, zero_mul]
    rw [hsum] at hmul
    exact (hdiag i).mul_right_eq_zero.mp hmul

/-- Over a finite field `K`, the lower-triangular Borel subgroup of `GL (Fin k) K` has cardinality
at least `∏ i : Fin k, (Nat.card K - 1) * Nat.card K ^ i.val`. -/
theorem card_lowerTriangularGL_ge (K : Type*) [Field K] [Finite K] (k : ℕ) :
    ∏ i : Fin k, (Nat.card K - 1) * Nat.card K ^ i.val ≤ Nat.card (lowerTriangularGL K k) := by
  let Rows : Type _ := ∀ i : Fin k, Kˣ × (Set.Iio i → K)
  let low (x : Rows) : Matrix (Fin k) (Fin k) K :=
    Matrix.of fun i j ↦ if i < j then 0 else if h : j < i then (x i).snd ⟨j, h⟩ else (x i).fst
  let f (x : Rows) : lowerTriangularGL K k :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (low x) <| by
      have htri : (low x).BlockTriangular OrderDual.toDual := fun i j hij ↦ by
        have hlt : i < j := hij
        simp [low, hlt]
      rw [Matrix.det_of_isLowerTriangular (low x) htri]
      refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
      simp [low],
      fun i j hij ↦ by simp [low, hij]⟩
  have hf_inj : Function.Injective f := fun x y hxy ↦ by
    have h_low : low x = low y :=
      congrArg (fun g : lowerTriangularGL K k ↦ (g.val : Matrix (Fin k) (Fin k) K)) hxy
    funext i
    refine Prod.ext (Units.ext ?_) (funext fun j ↦ ?_)
    · simpa [low] using congrFun₂ h_low i i
    · have hj : j.val < i := j.property
      simpa [low, hj, hj.not_gt] using congrFun₂ h_low i j.val
  have hle := Nat.card_le_card_of_injective f hf_inj
  have hcard : Nat.card Rows = ∏ i : Fin k, (Nat.card K - 1) * Nat.card K ^ i.val := by
    simp [Rows, Nat.card_pi, Nat.card_units, Fin.card_Iio]
  rwa [hcard] at hle

/-- Over a finite field `K`, the index of the lower-triangular Borel subgroup in `GL (Fin k) K` is
at most `∏ l : Fin k, ((Nat.card K : ℝ) ^ (l.val + 1) - 1) / (Nat.card K - 1)`. -/
theorem index_lowerTriangularGL_le (K : Type*) [Field K] [Finite K] (k : ℕ) :
    ((lowerTriangularGL K k).index : ℝ) ≤
      ∏ l : Fin k, ((Nat.card K : ℝ) ^ (l.val + 1) - 1) / (Nat.card K - 1) := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  set B := lowerTriangularGL K k
  have hq1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have h_card : (B.index : ℝ) * ∏ i : Fin k, ((Nat.card K : ℝ) - 1) * (Nat.card K : ℝ) ^ i.val ≤
      Nat.card (GL (Fin k) K) := by
    have h1 : B.index * ∏ i : Fin k, (Nat.card K - 1) * Nat.card K ^ i.val ≤
        Nat.card (GL (Fin k) K) :=
      (Nat.mul_le_mul_left _ (card_lowerTriangularGL_ge K k)).trans B.index_mul_card.le
    have h1r : ((B.index * ∏ i : Fin k, (Nat.card K - 1) * Nat.card K ^ i.val : ℕ) : ℝ) ≤
        (Nat.card (GL (Fin k) K) : ℝ) := by exact_mod_cast h1
    simpa only [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow, Nat.cast_sub hq1, Nat.cast_one] using h1r
  have hgl : (Nat.card (GL (Fin k) K) : ℝ) =
      ∏ i : Fin k, ((Nat.card K : ℝ) ^ k - (Nat.card K : ℝ) ^ i.val) := by
    rw [Matrix.card_GL_field]
    simp only [Nat.card_eq_fintype_card, Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Nat.cast_sub (Nat.pow_le_pow_right Fintype.card_pos i.isLt.le), Nat.cast_pow, Nat.cast_pow]
  have hq : 1 < (Nat.card K : ℝ) := Nat.one_lt_cast.mpr Finite.one_lt_card
  have hpos : 0 < ∏ i : Fin k, ((Nat.card K : ℝ) - 1) * (Nat.card K : ℝ) ^ i.val :=
    Finset.prod_pos fun i _ ↦ mul_pos (sub_pos.mpr hq) (pow_pos (zero_lt_one.trans hq) _)
  rw [hgl] at h_card
  refine le_of_mul_le_mul_right (h_card.trans_eq ?_) hpos
  rw [← Finset.prod_mul_distrib]
  have hprod : ∏ i : Fin k, ((Nat.card K : ℝ) ^ k - (Nat.card K : ℝ) ^ i.val) =
      ∏ i : Fin k, ((Nat.card K : ℝ) ^ (i.val + 1) - 1) * (Nat.card K : ℝ) ^ i.val := by
    have hrev : ∏ i : Fin k, ((Nat.card K : ℝ) ^ k - (Nat.card K : ℝ) ^ i.val) =
        ∏ i : Fin k, ((Nat.card K : ℝ) ^ (k - i.val) - 1) * (Nat.card K : ℝ) ^ i.val := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel i.isLt.le]
    rw [hrev, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    congr 1
    refine Fintype.prod_equiv Fin.revPerm _ _ fun i ↦ ?_
    simp only [Fin.revPerm_apply, Fin.val_rev, sub_left_inj]
    congr 1
    omega
  rw [hprod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  field_simp [(sub_pos.mpr hq).ne']

end TauCeti
