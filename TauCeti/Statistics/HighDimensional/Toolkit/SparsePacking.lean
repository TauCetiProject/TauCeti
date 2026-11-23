/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.Hamming
public import TauCeti.InformationTheory.Hamming
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Combinatorics.SetFamily.ConstantWeight
import TauCeti.Data.Finset.Basic
import TauCeti.Data.Nat.Choose.Ratio
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Data.Nat.Choose.Sum
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
    have hcount' : (Fintype.card ι).choose m ≤ (T.card * D.choose m) * D.choose m := by
      simpa only [card_univ, pow_two, mul_assoc] using hcount
    have hchoose : D.choose m ≤ 4 ^ m :=
      (Nat.choose_le_choose m (hDm.trans (Nat.le_succ _))).trans (Nat.choose_middle_le_pow m)
    have hpow : Fintype.card ι ^ m ≤ T.card * (4 * D) ^ m := calc
      _ ≤ (T.card * D.choose m) * D ^ m := Nat.pow_le_mul_pow_of_choose_le_mul_choose hm hD hcount'
      _ ≤ T.card * (4 * D) ^ m := by
        rw [mul_pow, mul_assoc]
        gcongr
    have hm' : (D : ℝ) / 2 ≤ m := by
      rw [div_le_iff₀ (by norm_num), mul_comm]
      exact_mod_cast hDm
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      Real.mul_log_natCast_div_le_log_of_pow_le_mul_pow (by positivity) hm' hpow

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
    have hweight : hammingNorm (WithLp.ofLp (e v)) = hammingNorm v := by
      rw [he, WithLp.ofLp_smul, WithLp.ofLp_toLp]
      exact hammingNorm_smul (fun _ ↦ smul_right_injective (M := ℝ) ha) v
    have hnorm : ‖e v‖ ^ 2 = a ^ 2 * (hammingNorm v : ℝ) := by
      rw [he]
      simpa only [WithLp.toLp_zero, smul_zero, sub_zero, hammingDist_zero_right] using
        norm_smul_toLp_sub_sq_eq_mul_hammingDist_of_binary (a := a) (hbinary v hv).1 (y := 0)
          (by simp)
    rw [hweight, hnorm, (hbinary v hv).2]
    exact ⟨rfl, rfl⟩
  · intro b hb b' hb' hbb'
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hb
    obtain ⟨v', hv', rfl⟩ := mem_map.mp hb'
    have hdist :=
      norm_smul_toLp_sub_sq_eq_mul_hammingDist_of_binary (a := a)
        (hbinary v hv).1 (hbinary v' hv').1
    have hlt : (D : ℝ) < hammingDist v v' := by
      exact_mod_cast hsep hv hv' (ne_of_apply_ne e hbb')
    exact (mul_lt_mul_of_pos_left hlt (sq_pos_iff.mpr ha)).trans_eq hdist.symm

end TauCeti
