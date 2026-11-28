/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.PieriCone
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.MeasureTheory.Measure.Lebesgue.Weighted.Orthant
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Volume bounds for degree slabs

A degree slab is a product of unit-width slices of nonnegative orthants. Its volume is a
product of differences of simplex volumes. In dimension `k + 1` each factor is bounded by
`(max 0 D)^k / k!`, where `D` is the upper degree endpoint. This power of degree `k`, rather
than `k + 1`, lets one compare the volume with the count of homogeneous monomials.

The comparison is used in `New.FrobeniusCycle.index_mul_finrank_defectConditions_le` in
`grh/src/New/UpperBound/ElementaryDivisors/DefectCount.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at revision `72fead1`.
-/

public section

open Finset MeasureTheory Set

namespace TauCeti

/-- The unit-width slice of one block in a degree slab has volume equal to the difference
of the two simplex volumes, with negative endpoints clipped at zero. -/
private theorem volume_degreeSlab_block (k : ℕ) (D : ℝ) :
    volume {x : Fin (k + 1) → ℝ | (∀ b, 0 ≤ x b) ∧ ∑ b, x b ∈ Icc (D - 1) D} =
      ENNReal.ofReal (((max 0 D) ^ (k + 1) - (max 0 (D - 1)) ^ (k + 1)) /
        ((k + 1).factorial : ℝ)) := by
  let f (x : Fin (k + 1) → ℝ) := ∑ b, x b
  have hs (x : Fin (k + 1) → ℝ) (hx : ∀ b, 0 ≤ x b) : 0 ≤ f x := sum_nonneg fun b _ ↦ hx b
  by_cases hD : 0 ≤ D
  swap
  · have hEmpty : {x : Fin (k + 1) → ℝ | (∀ b, 0 ≤ x b) ∧ f x ∈ Icc (D - 1) D} = ∅ :=
      eq_empty_iff_forall_notMem.2 fun x hx ↦ hD ((hs x hx.1).trans hx.2.2)
    rw [hEmpty, measure_empty, max_eq_left (le_of_not_ge hD), max_eq_left (by linarith)]
    simp
  have hle := volume_setOf_forall_nonneg_and_sum_mul_le
    (ι := Fin (k + 1)) (a := fun _ ↦ 1) (fun _ ↦ zero_lt_one) hD
  simp only [one_mul, Fintype.card_fin, prod_const_one, mul_one] at hle
  by_cases hlow : 0 < D - 1
  · have hlt := volume_setOf_forall_nonneg_and_sum_mul_lt
      (ι := Fin (k + 1)) (a := fun _ ↦ 1) (fun _ ↦ zero_lt_one) hlow
    simp only [one_mul, Fintype.card_fin, prod_const_one, mul_one] at hlt
    have hset : {x : Fin (k + 1) → ℝ | (∀ b, 0 ≤ x b) ∧ f x ∈ Icc (D - 1) D} =
        {x | (∀ b, 0 ≤ x b) ∧ f x ≤ D} \ {x | (∀ b, 0 ≤ x b) ∧ f x < D - 1} := by
      ext x
      simp only [mem_ofPred_eq, mem_sdiff, Set.mem_Icc, not_and, not_lt]
      tauto
    have hsub : {x | (∀ b, 0 ≤ x b) ∧ f x < D - 1} ⊆ {x | (∀ b, 0 ≤ x b) ∧ f x ≤ D} :=
      fun _ hx ↦ ⟨hx.1, by linarith [hx.2]⟩
    have hf : Measurable f := by dsimp [f]; fun_prop
    have hmeas : MeasurableSet {x | (∀ b, 0 ≤ x b) ∧ f x < D - 1} := by
      simp only [ofPred_and, ofPred_forall]
      exact (MeasurableSet.iInter fun b ↦ measurableSet_le measurable_const
        (measurable_pi_apply b)).inter (measurableSet_lt hf measurable_const)
    have hfin : volume {x | (∀ b, 0 ≤ x b) ∧ f x < D - 1} ≠ ⊤ :=
      hlt.trans_ne ENNReal.ofReal_ne_top
    rw [hset, measure_sdiff hsub hmeas.nullMeasurableSet hfin, hle, hlt, max_eq_right hD,
      max_eq_right hlow.le, ← ENNReal.ofReal_sub _ (by positivity), sub_div]
  · have hset : {x : Fin (k + 1) → ℝ | (∀ b, 0 ≤ x b) ∧ f x ∈ Icc (D - 1) D} =
        {x | (∀ b, 0 ≤ x b) ∧ f x ≤ D} := by
      ext x
      exact ⟨fun hx ↦ ⟨hx.1, hx.2.2⟩, fun hx ↦ ⟨hx.1, (le_of_not_gt hlow).trans (hs x hx.1), hx.2⟩⟩
    rw [hset, hle, max_eq_right hD, max_eq_left (le_of_not_gt hlow), zero_pow (by omega), sub_zero]

/-- The volume of a degree slab in positive block dimension factors over the letters.
The formula also covers slabs meeting the boundary of the nonnegative orthant. -/
theorem volume_real_degreeSlab {T : Type*} [Fintype T] (k : ℕ) (D : T → ℝ) :
    volume.real (degreeSlab (k + 1) D) =
      ∏ j, ((max 0 (D j)) ^ (k + 1) - (max 0 (D j - 1)) ^ (k + 1)) /
        ((k + 1).factorial : ℝ) := by
  let swap := MeasurableEquiv.piCongrLeft (fun _ : T × Fin (k + 1) ↦ ℝ)
    (Equiv.prodComm (Fin (k + 1)) T)
  let e := swap.trans (MeasurableEquiv.curry T (Fin (k + 1)) ℝ)
  let S (j : T) := {x : Fin (k + 1) → ℝ | (∀ b, 0 ≤ x b) ∧ ∑ b, x b ∈ Icc (D j - 1) (D j)}
  have hc := measurePreserving_curry (fun (_ : T) (_ : Fin (k + 1)) ↦ (volume : Measure ℝ))
  simp only [← volume_pi] at hc
  have hpres : MeasurePreserving e volume volume := hc.comp
    (volume_measurePreserving_piCongrLeft _ (Equiv.prodComm (Fin (k + 1)) T))
  have hS : e.symm ⁻¹' degreeSlab (k + 1) D = univ.pi S := by
    ext x
    have he (p : Fin (k + 1) × T) : e.symm x p = x p.2 p.1 := rfl
    simp only [Set.mem_preimage, mem_degreeSlab, Pi.le_def, Pi.zero_apply, mem_univ_pi, S,
      mem_ofPred_eq, he]
    constructor
    · exact fun h j ↦ ⟨fun b ↦ h.1 (b, j), h.2 j⟩
    · exact fun h ↦ ⟨fun p ↦ (h p.2).1 p.1, fun j ↦ (h j).2⟩
  rw [measureReal_def, ← (hpres.symm e).measure_preimage_emb e.symm.measurableEmbedding,
    hS, volume_pi_pi, ENNReal.toReal_prod]
  refine prod_congr rfl fun j _ ↦ ?_
  have hblock : volume (S j) = _ := volume_degreeSlab_block k (D j)
  rw [hblock, ENNReal.toReal_ofReal]
  exact div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (le_max_left _ _) (by gcongr; linarith) _))
    (by positivity)

/-- A unit-width degree slab has at most the product of the maximum densities of the
block-degree sums. -/
theorem volume_real_degreeSlab_le {T : Type*} [Fintype T] (k : ℕ) (D : T → ℝ) :
    volume.real (degreeSlab (k + 1) D) ≤ ∏ j, (max 0 (D j)) ^ k / (k.factorial : ℝ) := by
  rw [volume_real_degreeSlab]
  refine prod_le_prod₀ (fun j _ ↦ ?_) fun j _ ↦ ?_
  · refine div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (le_max_left _ _) ?_ _)) (by positivity)
    gcongr
    linarith
  · set a := max 0 (D j - 1)
    set b := max 0 (D j)
    have ha : 0 ≤ a := le_max_left _ _
    have hb : a ≤ b := by dsimp only [a, b]; gcongr; linarith
    have hgap : b - a ≤ 1 := by
      dsimp only [a, b]
      rcases le_total (D j) 0 with h | h
      · rw [max_eq_left h, max_eq_left (by linarith)]; norm_num
      · rw [max_eq_right h]; linarith [le_max_right 0 (D j - 1)]
    have h := abs_pow_sub_pow_le b a (k + 1)
    rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha hb _)),
      abs_of_nonneg (sub_nonneg.mpr hb), abs_of_nonneg (ha.trans hb), abs_of_nonneg ha,
      max_eq_left hb, Nat.add_sub_cancel] at h
    have hfac : (0 : ℝ) < ↑(k + 1) * ↑k.factorial := by positivity
    rw [Nat.factorial_succ, Nat.cast_mul, div_le_iff₀ hfac]
    calc
      b ^ (k + 1) - a ^ (k + 1) ≤ (b - a) * ↑(k + 1) * b ^ k := h
      _ ≤ 1 * ↑(k + 1) * b ^ k := by gcongr
      _ = (b ^ k / (k.factorial : ℝ)) * (↑(k + 1) * ↑k.factorial) := by field_simp

/-- If the upper degree in each block is at most `n + A`, the volume of the slab is at
most `1 + θ` times the number of families of degree-`n` monomials in the blocks, provided
`2 * (# letters) * k * A ≤ θ * n` and `θ ≤ 1`. -/
theorem volume_real_degreeSlab_le_choose_pow {T : Type*} [Fintype T] {k n : ℕ}
    {D : T → ℝ} {A θ : ℝ} (hn : 0 < n) (hA : 0 ≤ A) (hθ : θ ≤ 1)
    (hD : ∀ j, D j ≤ n + A)
    (hsmall : 2 * (Fintype.card T : ℝ) * k * A ≤ θ * n) :
    volume.real (degreeSlab (k + 1) D) ≤ (1 + θ) * ((n + k).choose k : ℝ) ^ Fintype.card T := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbin : (n : ℝ) ^ k / (k.factorial : ℝ) ≤ (n + k).choose k := by
    have he : n + k + 1 - k = n + 1 := by omega
    have h := Nat.pow_le_choose (α := ℝ) k (n + k)
    calc
      _ ≤ ((n : ℝ) + 1) ^ k / (k.factorial : ℝ) := by gcongr; linarith
      _ ≤ _ := by simpa only [he, Nat.cast_add, Nat.cast_one] using h
  let u : ℝ := (Fintype.card T : ℝ) * k * (A / n)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huθ : 2 * u ≤ θ := by
    dsimp only [u]
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_iff₀ hn']
    simpa only [mul_assoc] using hsmall
  have hExp : Real.exp u ≤ 1 + θ := by
    calc
      _ ≤ (2 + u) / (2 - u) := Real.exp_le_two_add_div_two_sub hu (by linarith)
      _ ≤ 1 + 2 * u := by
        rw [div_le_iff₀ (by linarith)]
        have hu₁ : 0 ≤ 1 - u := by linarith
        nlinarith [mul_nonneg hu hu₁]
      _ ≤ _ := by linarith
  have hfactor (j : T) : (max 0 (D j)) ^ k / (k.factorial : ℝ) ≤
      Real.exp ((k : ℝ) * (A / n)) * ((n + k).choose k : ℝ) := by
    have hpow : max 0 (D j) ≤ (n : ℝ) * Real.exp (A / n) := calc
      _ ≤ n + A := max_le (by positivity) (hD j)
      _ = n * (A / n + 1) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hn'.le
    calc
      _ ≤ ((n : ℝ) * Real.exp (A / n)) ^ k / (k.factorial : ℝ) := by gcongr
      _ = Real.exp ((k : ℝ) * (A / n)) * ((n : ℝ) ^ k / (k.factorial : ℝ)) := by
        rw [mul_pow, Real.exp_natCast_mul, mul_comm, mul_div_assoc]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∏ j, (max 0 (D j)) ^ k / (k.factorial : ℝ) := volume_real_degreeSlab_le k D
    _ ≤ ∏ _ : T, Real.exp ((k : ℝ) * (A / n)) * ((n + k).choose k : ℝ) :=
      prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦ hfactor j
    _ = Real.exp u * ((n + k).choose k : ℝ) ^ Fintype.card T := by
      simp only [prod_const, card_univ, mul_pow, ← Real.exp_natCast_mul, u, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hExp (by positivity)

end TauCeti
