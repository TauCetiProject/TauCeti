/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Hamming
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Combinatorics.SetFamily.ConstantWeight
import TauCeti.Data.Finset.Basic
import TauCeti.Data.Nat.Choose.Ratio
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Sparse Varshamov–Gilbert packing

The sparse binary cube contains a large family with constant Hamming weight and
pairwise Hamming distances strictly greater than the common weight. Such a family
provides separated parameters for minimax lower bounds. On the real binary cube,
squared Euclidean distance is Hamming distance.

The packing follows Giraud, *Introduction to High-Dimensional Statistics*, 2nd ed.,
Lemma 3.7, with a ball bound obtained by counting extensions of subsets shared with
the centre.
-/

public section

open Finset
open scoped symmDiff BigOperators

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean distance agrees with Hamming distance between real binary vectors. -/
theorem norm_toLp_sub_sq_eq_hammingDist_of_binary {x y : ι → ℝ}
    (hx : ∀ i, x i = 0 ∨ x i = 1) (hy : ∀ i, y i = 0 ∨ y i = 1) :
    ‖WithLp.toLp 2 x - WithLp.toLp 2 y‖ ^ 2 = (hammingDist x y : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq, hammingDist, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [PiLp.sub_apply]
  rcases hx i with h | h <;> rcases hy i with h' | h' <;> norm_num [h, h']

private theorem pow_le_card_mul_of_choose_le {n D m N : ℕ} (hm : m ≤ D) (hDm : D ≤ 2 * m)
    (hDn : D ≤ n) (hcard : n.choose m ≤ N * (D.choose m) ^ 2) :
    n ^ m ≤ N * (4 * D) ^ m := by
  have hchoose : D.choose m ≤ 4 ^ m := by
    calc
      D.choose m ≤ 2 ^ D := Nat.choose_le_two_pow _ _
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by decide) hDm
      _ = 4 ^ m := by rw [pow_mul]; rfl
  apply Nat.le_of_mul_le_mul_right (c := D.choose m) _ (Nat.choose_pos hm)
  calc
    n ^ m * D.choose m ≤ n.choose m * D ^ m := by
      rw [mul_comm (n ^ m)]
      exact Nat.choose_mul_pow_le_choose_mul_pow hDn m
    _ ≤ (N * (D.choose m) ^ 2) * D ^ m := Nat.mul_le_mul_right _ hcard
    _ = (N * (D.choose m * D ^ m)) * D.choose m := by rw [pow_two]; ac_rfl
    _ ≤ (N * (4 * D) ^ m) * D.choose m := by
      rw [mul_pow]
      gcongr

private theorem log_bound_of_pow_le_card_mul {p D m N : ℕ}
    (hm : D ≤ 2 * m) (hpow : p ^ m ≤ N * (4 * D) ^ m) :
    (D : ℝ) / 2 * Real.log (p / (4 * D)) ≤ Real.log N := by
  by_cases hD : D = 0
  · simpa [hD] using Real.log_natCast_nonneg N
  have hden : 0 < 4 * (D : ℝ) := mul_pos (by norm_num) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hD))
  let q := (p : ℝ) / (4 * D)
  by_cases hq : 1 ≤ q
  · have hm' : (D : ℝ) ≤ 2 * m := by exact_mod_cast hm
    have hqN : q ^ m ≤ N := by
      dsimp only [q]
      rw [div_pow, div_le_iff₀ (pow_pos hden _)]
      exact_mod_cast hpow
    calc
      _ ≤ (m : ℝ) * Real.log q :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg hq)
      _ = Real.log (q ^ m) := (Real.log_pow _ _).symm
      _ ≤ _ := Real.log_le_log (pow_pos (zero_lt_one.trans_le hq) _) hqN
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (Real.log_nonpos (by positivity : 0 ≤ q) (le_of_not_ge hq))).trans (Real.log_natCast_nonneg N)

/-- Sparse Varshamov–Gilbert packing with constant 4. Every member is a binary vector
with exactly D ones, and the Hamming distance between distinct members is greater than D.
The family is nonempty for every admissible weight, including zero. -/
theorem exists_sparse_packing {D : ℕ} (hD : D ≤ Fintype.card ι) :
    ∃ C : Finset (ι → ℝ), C.Nonempty ∧
      (∀ x ∈ C, (∀ i, x i = 0 ∨ x i = 1) ∧ hammingNorm x = D) ∧
      (C : Set (ι → ℝ)).Pairwise (fun x y ↦ D < hammingDist x y) ∧
      (D : ℝ) / 2 * Real.log (Fintype.card ι / (4 * D)) ≤ Real.log C.card := by
  classical
  let m := D - D / 2
  have hm : m ≤ D := Nat.sub_le _ _
  have hDm : D ≤ 2 * m := by omega
  have hDn : D ≤ (univ : Finset ι).card := by simpa using hD
  obtain ⟨T, hT, hsep, hcount⟩ :=
    (univ : Finset ι).exists_powersetCard_pairwise_lt_card_sdiff_choose_le hm hDn
  let indicator := fun t : Finset ι ↦ (t : Set ι).indicator (1 : ι → ℝ)
  have hinj : Function.Injective indicator := fun _ _ h ↦ coe_injective (Set.indicator_one_inj ℝ h)
  have hTpos : 0 < T.card := by
    have hpos := (Nat.choose_pos (hm.trans hDn)).trans_le hcount
    exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hpos
  refine ⟨T.map ⟨indicator, hinj⟩, (Finset.card_pos.mp hTpos).map, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hx
    refine ⟨fun i ↦ ?_, (hammingNorm_indicator_one t).trans (mem_powersetCard.mp (hT ht)).2⟩
    by_cases hi : i ∈ t <;> simp [indicator, hi]
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hy
    have hst : s ≠ t := fun h ↦ hxy (congrArg indicator h)
    have hsep' := hsep hs ht hst
    have hcard := (mem_powersetCard.mp (hT ht)).2.trans (mem_powersetCard.mp (hT hs)).2.symm
    have hstrict : D < hammingDist (indicator s) (indicator t) := by
      rw [hammingDist_indicator_one]
      have hsymm := card_symmDiff_add_two_mul_card_inter s t
      have hsum := card_sdiff_add_card_inter s t
      omega
    exact hstrict
  · rw [card_map]
    have hcount' : (Fintype.card ι).choose m ≤ T.card * (D.choose m) ^ 2 := by
      simpa only [card_univ] using hcount
    exact log_bound_of_pow_le_card_mul hDm (pow_le_card_mul_of_choose_le hm hDm hD hcount')

private theorem norm_smul_toLp_sub_sq_eq {a : ℝ} {x y : ι → ℝ}
    (hx : ∀ i, x i = 0 ∨ x i = 1) (hy : ∀ i, y i = 0 ∨ y i = 1) :
    ‖a • WithLp.toLp 2 x - a • WithLp.toLp 2 y‖ ^ 2 = a ^ 2 * (hammingDist x y : ℝ) := by
  rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_toLp_sub_sq_eq_hammingDist_of_binary hx hy]

/-- Scaled sparse packing in Euclidean space. All parameters have the same squared norm,
and distinct parameters have squared distance strictly greater than that norm. -/
theorem exists_sparse_euclidean_packing {D : ℕ} (hD : D ≤ Fintype.card ι) {a : ℝ} (ha : a ≠ 0) :
    ∃ C : Finset (EuclideanSpace ℝ ι), C.Nonempty ∧
      (∀ b ∈ C, hammingNorm (WithLp.ofLp b) = D ∧ ‖b‖ ^ 2 = a ^ 2 * D) ∧
      (C : Set (EuclideanSpace ℝ ι)).Pairwise (fun b b' ↦ a ^ 2 * D < ‖b - b'‖ ^ 2) ∧
      (D : ℝ) / 2 * Real.log (Fintype.card ι / (4 * D)) ≤ Real.log C.card := by
  obtain ⟨C, hne, hbinary, hsep, hcard⟩ := exists_sparse_packing hD
  let e : (ι → ℝ) ↪ EuclideanSpace ℝ ι :=
    ⟨fun v ↦ a • WithLp.toLp 2 v, fun _ _ h ↦
      WithLp.toLp_injective 2 ((smul_right_injective (M := EuclideanSpace ℝ ι) ha) h)⟩
  have he (v : ι → ℝ) : e v = a • WithLp.toLp 2 v := (rfl)
  refine ⟨C.map e, hne.map, ?_, ?_, by simpa only [card_map] using hcard⟩
  · intro b hb
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hb
    have hweight : hammingNorm (WithLp.ofLp (e v)) = hammingNorm v :=
      hammingNorm_smul (fun _ ↦ smul_right_injective (M := ℝ) ha) v
    have hnorm : ‖e v‖ ^ 2 = a ^ 2 * (hammingNorm v : ℝ) := by
      rw [he]
      simpa only [WithLp.toLp_zero, smul_zero, sub_zero, hammingDist_zero_right] using
        norm_smul_toLp_sub_sq_eq (a := a) (hbinary v hv).1 (y := 0) (by simp)
    rw [hweight, hnorm, (hbinary v hv).2]
    exact ⟨rfl, rfl⟩
  · intro b hb b' hb' hbb'
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hb
    obtain ⟨v', hv', rfl⟩ := mem_map.mp hb'
    have hdist := norm_smul_toLp_sub_sq_eq (a := a) (hbinary v hv).1 (hbinary v' hv').1
    have hlt : (D : ℝ) < hammingDist v v' := by
      exact_mod_cast hsep hv hv' (ne_of_apply_ne e hbb')
    exact (mul_lt_mul_of_pos_left hlt (sq_pos_iff.mpr ha)).trans_eq hdist.symm

end TauCeti
