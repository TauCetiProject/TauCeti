/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Fin

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Summing over vectors by their last nonzero coordinate

Let `κ` be a finite type with a distinguished zero element `0 : κ` and cardinality `q = |κ|`.
Given a subset `I : Finset (Fin N)` of coordinates that are required to be nonzero, we count the
vectors `c : Fin N → κ` that are nonzero on `I` and have last nonzero coordinate `j : Fin N`, and
evaluate the sum of `a j` over such vectors with `m ≤ j`.

## Main statements

* `TauCeti.card_filter_lastNonzeroCoord`: the number of vectors `c : Fin N → κ` nonzero on `I`
  with last nonzero coordinate `j` is `q ^ (j.val + 1 - #(insert j I)) * (q - 1) ^ #(insert j I)`
  when `I ⊆ Iic j`, and `0` otherwise.
* `TauCeti.sum_by_lastNonzeroCoord_nsmul`: the general additive-monoid summation formula over
  vectors grouped by their last nonzero coordinate `j ≥ m`.
* `TauCeti.sum_by_lastNonzeroCoord`: over a field `E` in which `(Fintype.card κ : E) ≠ 0`, the
  closed form `∑ j ≥ m with I ⊆ Iic j, q ^ N * ((1 - q⁻¹) ^ #(insert j I) / q ^ #(Ioi j)) * a j`.

## Provenance

Adapted from `New.sum_by_last_nonzero_coord` in
`grh/src/Lib/LocalGL/Iwahori/SphericalExponents.lean` of `grh-lean`
(<https://github.com/lsernau/grh-lean>, commit `72fead102f663d5c7a407964a13dc0cf9d977207`),
generalized from the residue field `𝓀[F]` and `ℂ` to an arbitrary finite type `κ` with zero and
an arbitrary field `E` (plus the `ℕ`-valued cardinality and `AddCommMonoid` versions).
-/

@[expose] public section

open Finset

namespace TauCeti

/-- The number of vectors `c : Fin N → κ` that are nonzero on `I` and have last nonzero
coordinate `j` equals
`∏ r : Fin N, if r ∈ insert j I then |κ| - 1 else if r ∈ Ioi j then 1 else |κ|`
when `I ⊆ Iic j`, and `0` otherwise. -/
theorem card_filter_lastNonzeroCoord {N : ℕ} {κ : Type*} [Fintype κ] [Zero κ] [DecidableEq κ]
    (I : Finset (Fin N)) (j : Fin N) :
    #{c : Fin N → κ | (∀ s ∈ I, c s ≠ 0) ∧ c j ≠ 0 ∧ ∀ r > j, c r = 0} =
      if I ⊆ Iic j then
        ∏ r : Fin N, if r ∈ insert j I then Fintype.card κ - 1 else if r ∈ Ioi j then 1 else
          Fintype.card κ
      else 0 := by
  split_ifs with hI
  · let allowed (r : Fin N) : Finset κ :=
      univ.filter fun x ↦ (r ∈ insert j I → x ≠ 0) ∧ (r ∈ Ioi j → x = 0)
    have h_eq : univ.filter (fun c : Fin N → κ ↦
        (∀ s ∈ I, c s ≠ 0) ∧ c j ≠ 0 ∧ ∀ r > j, c r = 0) = Fintype.piFinset allowed := by
      ext c
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, allowed, mem_insert,
        mem_Ioi]
      constructor
      · rintro ⟨h1, h2, h3⟩ r
        exact ⟨fun hr ↦ hr.elim (fun h ↦ h ▸ h2) (h1 r), h3 r⟩
      · intro h
        exact ⟨fun s hs ↦ (h s).left (.inr hs), (h j).left (.inl rfl), fun r hr ↦ (h r).right hr⟩
    rw [h_eq, Fintype.card_piFinset]
    refine prod_congr rfl fun r _ ↦ ?_
    have hdisj : ¬(r ∈ insert j I ∧ r ∈ Ioi j) := by
      rintro ⟨h1, h2⟩
      rw [mem_Ioi] at h2
      rcases mem_insert.mp h1 with rfl | h1
      · exact lt_irrefl _ h2
      · exact absurd (mem_Iic.mp (hI h1)) (not_le.mpr h2)
    split_ifs with h1 h2
    · have h2 : r ∉ Ioi j := fun h ↦ hdisj ⟨h1, h⟩
      simp only [allowed, h1, h2, true_implies, false_implies, and_true, filter_ne',
        card_erase_of_mem (mem_univ (0 : κ)), card_univ]
    · simp only [allowed, h1, h2, false_implies, true_implies, true_and, filter_eq',
        mem_univ, ↓reduceIte, card_singleton]
    · simp only [allowed, h1, h2, false_implies, and_self, filter_true, card_univ]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro c _ hc
    apply hI
    intro s hs
    rw [mem_Iic]
    by_contra hlt
    exact hc.left s hs (hc.right.right s (not_le.mp hlt))

/-- Summing `a j` over vectors `c : Fin N → κ` nonzero on `I` and their last nonzero coordinate
`j ≥ m`, in any additive commutative monoid `M`. -/
theorem sum_by_lastNonzeroCoord_nsmul {N : ℕ} {κ M : Type*} [Fintype κ] [Zero κ] [DecidableEq κ]
    [AddCommMonoid M] (m : Fin N) (a : Fin N → M) (I : Finset (Fin N)) :
    ∑ c : Fin N → κ with ∀ s ∈ I, c s ≠ 0,
      ∑ j : Fin N with m ≤ j ∧ c j ≠ 0 ∧ ∀ r > j, c r = 0, a j =
      ∑ j : Fin N with m ≤ j ∧ I ⊆ Iic j,
        (∏ r : Fin N, if r ∈ insert j I then Fintype.card κ - 1 else if r ∈ Ioi j then 1 else
          Fintype.card κ) • a j := by
  classical
  calc ∑ c : Fin N → κ with ∀ s ∈ I, c s ≠ 0,
        ∑ j : Fin N with m ≤ j ∧ c j ≠ 0 ∧ ∀ r > j, c r = 0, a j
      = ∑ j : Fin N with m ≤ j,
          ∑ _c : Fin N → κ with (∀ s ∈ I, _c s ≠ 0) ∧ _c j ≠ 0 ∧ ∀ r > j, _c r = 0, a j := by
        simp_rw [sum_filter]
        trans ∑ c : Fin N → κ, ∑ j : Fin N,
          if (∀ s ∈ I, c s ≠ 0) ∧ m ≤ j ∧ c j ≠ 0 ∧ ∀ r > j, c r = 0 then a j else 0
        · refine sum_congr rfl fun c _ ↦ ?_
          by_cases hc : ∀ s ∈ I, c s ≠ 0
          · rw [ite_eq_left hc]
            exact sum_congr rfl fun j _ ↦ if_congr (by tauto) rfl rfl
          · rw [ite_eq_right hc]
            exact (sum_eq_zero fun j _ ↦ ite_eq_right fun h ↦ hc h.left).symm
        · rw [Finset.sum_comm]
          refine sum_congr rfl fun j _ ↦ ?_
          by_cases hm : m ≤ j
          · rw [ite_eq_left hm]
            exact sum_congr rfl fun c _ ↦ if_congr (by tauto) rfl rfl
          · rw [ite_eq_right hm]
            exact sum_eq_zero fun c _ ↦ ite_eq_right fun h ↦ hm h.right.left
    _ = ∑ j : Fin N with m ≤ j,
          (if I ⊆ Iic j then
            ∏ r : Fin N, if r ∈ insert j I then Fintype.card κ - 1 else if r ∈ Ioi j then 1 else
              Fintype.card κ
          else 0) • a j := by
        refine sum_congr rfl fun j _ ↦ ?_
        rw [sum_const, card_filter_lastNonzeroCoord]
    _ = ∑ j : Fin N with m ≤ j ∧ I ⊆ Iic j,
          (∏ r : Fin N, if r ∈ insert j I then Fintype.card κ - 1 else if r ∈ Ioi j then 1 else
            Fintype.card κ) • a j := by
        rw [sum_filter, sum_filter]
        refine sum_congr rfl fun j _ ↦ ?_
        by_cases hm : m ≤ j <;> by_cases hI : I ⊆ Iic j <;> simp [hm, hI]

/-- Over a field `E` in which `q = (Fintype.card κ : E)` is nonzero, summing `a j` over vectors
`c : Fin N → κ` nonzero on `I` and their last nonzero coordinate `j ≥ m` yields
`∑ j ≥ m with I ⊆ Iic j, q ^ N * ((1 - q⁻¹) ^ #(insert j I) / q ^ #(Ioi j)) * a j`. -/
theorem sum_by_lastNonzeroCoord {N : ℕ} {κ E : Type*} [Fintype κ] [Zero κ] [DecidableEq κ]
    [Field E] (hq : (Fintype.card κ : E) ≠ 0) (m : Fin N) (a : Fin N → E) (I : Finset (Fin N)) :
    let q : E := Fintype.card κ
    ∑ c : Fin N → κ with ∀ s ∈ I, c s ≠ 0,
      ∑ j : Fin N with m ≤ j ∧ c j ≠ 0 ∧ ∀ r > j, c r = 0, a j =
      ∑ j : Fin N with m ≤ j ∧ I ⊆ Iic j,
        q ^ N * ((1 - q⁻¹) ^ #(insert j I) / q ^ #(Ioi j)) * a j := by
  classical
  intro q
  rw [sum_by_lastNonzeroCoord_nsmul]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [nsmul_eq_mul]
  congr 1
  have hcard_pos : 1 ≤ Fintype.card κ := Fintype.card_pos_iff.mpr ⟨0⟩
  have hI : I ⊆ Iic j := (mem_filter.mp hj).right.right
  have h_fac (r : Fin N) :
      ((if r ∈ insert j I then Fintype.card κ - 1 else if r ∈ Ioi j then 1 else
        Fintype.card κ : ℕ) : E) =
      q * ((if r ∈ insert j I then 1 - q⁻¹ else 1) / if r ∈ Ioi j then q else 1) := by
    have hdisj : ¬(r ∈ insert j I ∧ r ∈ Ioi j) := by
      rintro ⟨h1, h2⟩
      rw [mem_Ioi] at h2
      rcases mem_insert.mp h1 with rfl | h1
      · exact lt_irrefl _ h2
      · exact absurd (mem_Iic.mp (hI h1)) (not_le.mpr h2)
    split_ifs with h1 h2 h2
    · exact absurd ⟨h1, h2⟩ hdisj
    · rw [Nat.cast_sub hcard_pos, Nat.cast_one, div_one, mul_sub, mul_one, mul_inv_cancel₀ hq]
    · simp [q, mul_inv_cancel₀ hq]
    · simp [q]
  simp only [Nat.cast_prod, h_fac, prod_mul_distrib, prod_div_distrib, prod_const, card_univ,
    Fintype.card_fin, prod_ite_mem_eq]

end TauCeti
