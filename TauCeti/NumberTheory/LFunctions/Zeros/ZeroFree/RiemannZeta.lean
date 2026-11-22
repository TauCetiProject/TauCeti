/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ThreeFourOne
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# The de la Vallée Poussin zero-free region for `riemannZeta`

We prove `TauCeti.riemannZeta_zeroFreeRegion`, establishing a positive absolute constant `c > 0`
such that `riemannZeta s ≠ 0` whenever `1 - c / log (|s.im| + 3) ≤ s.re`.

On the bounded box `|s.im| ≤ 2`, nonvanishing of `riemannZeta` on `Re s = 1` combined with
compactness of `1 + i [-2, 2]` and continuity of Mathlib's regularized function
`DirichletCharacter.LFunctionTrivChar₁ 1` yields a uniform open strip around `1 + i [-2, 2]`
(with `1 ≤ s.re` handled directly by `riemannZeta_ne_zero_of_one_le_re`).
For `|s.im| ≥ 2`, the `3-4-1` logarithmic-derivative inequality
(`threeFourOne_neg_re_logDeriv_riemannZeta_nonneg`) paired with the pole estimate near `s = 1`
(`exists_neg_re_logDeriv_riemannZeta_one_add_le`) and the vertical-strip bounds
(`neg_re_logDeriv_riemannZeta_le`) yields the classical de la Vallée Poussin bound.

## Main results

* `TauCeti.riemannZeta_zeroFreeRegion`: `ζ(s) ≠ 0` for `1 - c / Real.log (|s.im| + 3) ≤ s.re`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §13.
-/

public section

open Complex DirichletCharacter Metric Set

namespace TauCeti

private theorem exists_delta_riemannZeta_ne_zero_of_abs_im_le_two :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ s : ℂ, |s.im| ≤ 2 → 1 - δ₀ ≤ s.re → riemannZeta s ≠ 0 := by
  let K : Set ℂ := (fun t : ℝ ↦ (1 : ℂ) + t * I) '' Icc (-2) 2
  let U : Set ℂ := {z : ℂ | LFunctionTrivChar₁ 1 z ≠ 0}
  have mem_U_iff (z : ℂ) : z ∈ U ↔ LFunctionTrivChar₁ 1 z ≠ 0 := Iff.rfl
  have hreg {z : ℂ} (hz : z ≠ 1) : LFunctionTrivChar₁ 1 z = (z - 1) * riemannZeta z := by
    rw [LFunctionTrivChar₁, Function.update_of_ne hz, LFunctionTrivChar, LFunction_modOne_eq]
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen U := isOpen_ne.preimage (differentiable_LFunctionTrivChar₁ 1).continuous
  have hKU : K ⊆ U := by
    rintro _ ⟨t, _, rfl⟩
    dsimp only
    have hz1 : (1 : ℝ) ≤ ((1 : ℂ) + t * I).re := by simp
    rw [mem_U_iff]
    rcases eq_or_ne ((1 : ℂ) + t * I) 1 with h1 | hne
    · rw [h1]
      exact LFunctionTrivChar₁_apply_one_ne_zero 1
    · rw [hreg hne]
      exact mul_ne_zero (sub_ne_zero.mpr hne) (riemannZeta_ne_zero_of_one_le_re hz1)
  obtain ⟨δ₀, hδ₀, hthick⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ₀ / 2, half_pos hδ₀, fun s him hre ↦ ?_⟩
  by_cases hs_ge : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hs_ge
  push Not at hs_ge
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs_ge
  let w : ℂ := 1 + s.im * I
  have hdist : dist s w < δ₀ := by
    rw [Complex.dist_eq]
    have hsub : s - w = ((s.re - 1 : ℝ) : ℂ) := by apply Complex.ext <;> simp [w]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hsU : s ∈ U := hthick (mem_thickening_iff.mpr ⟨w, ⟨s.im, abs_le.mp him, rfl⟩, hdist⟩)
  rw [mem_U_iff, hreg hs1] at hsU
  exact right_ne_zero_of_mul hsU

private theorem riemannZeta_four_div_le_of_two_le_abs_im {C₀ C₁ β t : ℝ}
    (hC₀ : ∀ η : ℝ, 0 < η → η ≤ 1 → -(logDeriv riemannZeta (1 + η)).re ≤ 1 / η + C₀)
    (hC₁ : ∀ η : ℝ, 0 < η → ∀ t : ℝ, 2 ≤ |t| →
      -(logDeriv riemannZeta (1 + η + 2 * t * I)).re ≤ C₁ * Real.log |t| ∧
        ∀ β : ℝ, riemannZeta (β + t * I) = 0 →
          -(logDeriv riemannZeta (1 + η + t * I)).re ≤ -1 / (1 + η - β) + C₁ * Real.log |t|)
    {A : ℝ} (hA : 3 * max C₀ 0 + 5 * max C₁ 0 ≤ A)
    {η : ℝ} (hηpos : 0 < η) (hη1 : η ≤ 1) (ht_ge : (2 : ℝ) ≤ |t|)
    (hζ : riemannZeta (β + t * I) = 0) :
    4 / (1 + η - β) ≤ 3 / η + A * Real.log (|t| + 3) := by
  set L : ℝ := Real.log (|t| + 3)
  have hL1 : 1 < L := by
    have hlog5 : 1 < Real.log 5 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
    exact hlog5.trans_le (Real.log_le_log (by norm_num) (by linarith))
  have hLpos : 0 < L := zero_lt_one.trans hL1
  have h341 := threeFourOne_neg_re_logDeriv_riemannZeta_nonneg (σ := 1 + η) (by linarith) t
  simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.neg_re] at h341
  have hpole : -(logDeriv riemannZeta (1 + η)).re ≤ 1 / η + max C₀ 0 :=
    (hC₀ η hηpos hη1).trans (by linarith [le_max_left C₀ 0])
  obtain ⟨h2t, h1t⟩ := hC₁ η hηpos t ht_ge
  have hlogt_le : Real.log |t| ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hlogt_nonneg : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
  have hC1t : C₁ * Real.log |t| ≤ max C₁ 0 * L :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hlogt_nonneg).trans
      (mul_le_mul_of_nonneg_left hlogt_le (le_max_right _ _))
  have h1t_le : -(logDeriv riemannZeta (1 + η + t * I)).re ≤
      -(1 / (1 + η - β)) + max C₁ 0 * L := by
    have h1t_β := h1t β hζ
    rw [neg_div] at h1t_β
    linarith
  have hC0L : max C₀ 0 ≤ max C₀ 0 * L := le_mul_of_one_le_right (le_max_right _ _) hL1.le
  have hAL_le : 3 * max C₀ 0 + 5 * (max C₁ 0 * L) ≤ A * L := by
    have hmul : (3 * max C₀ 0 + 5 * max C₁ 0) * L ≤ A * L :=
      mul_le_mul_of_nonneg_right hA hLpos.le
    linarith
  have h3div : 3 * (1 / η) = 3 / η := by ring
  have h4div : 4 * (1 / (1 + η - β)) = 4 / (1 + η - β) := by ring
  linarith

private theorem exists_c_riemannZeta_ne_zero_of_two_le_abs_im :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ s : ℂ, 2 ≤ |s.im| → 1 - c₂ / Real.log (|s.im| + 3) ≤ s.re →
      riemannZeta s ≠ 0 := by
  obtain ⟨C₀, _, hC₀⟩ := exists_neg_re_logDeriv_riemannZeta_one_add_le
  obtain ⟨C₁, hC₁⟩ := neg_re_logDeriv_riemannZeta_le 2 one_lt_two
  let A : ℝ := max 1 (3 * max C₀ 0 + 5 * max C₁ 0)
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨1 / (40 * A), by positivity, fun s him hsre hζ ↦ ?_⟩
  have hre_lt : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
  set β : ℝ := s.re
  set t : ℝ := s.im
  have hs_eq : s = (β : ℂ) + t * I := (Complex.re_add_im s).symm
  rw [hs_eq] at hζ
  have ht_ge : (2 : ℝ) ≤ |t| := him
  set L : ℝ := Real.log (|t| + 3)
  have hL1 : 1 < L := by
    have hlog5 : 1 < Real.log 5 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
    exact hlog5.trans_le (Real.log_le_log (by norm_num) (by linarith))
  set η : ℝ := 1 / (8 * A * L)
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 := div_le_one_of_le₀ (by nlinarith) (by positivity)
  have hcomb := riemannZeta_four_div_le_of_two_le_abs_im hC₀ hC₁ (le_max_right 1 _)
    hηpos hη1 ht_ge hζ
  have hAL : A * L = 1 / (8 * η) := by dsimp [η]; field_simp
  have hre_lo : 1 - 1 / (40 * A) / L ≤ β := hsre
  have h1β : 1 - β ≤ η / 5 := by
    have hscale : 1 / (40 * A) / L = η / 5 := by dsimp [η]; ring
    linarith [hre_lo]
  have h1ηβ_pos : 0 < 1 + η - β := by linarith
  have hlo : 10 / (3 * η) ≤ 4 / (1 + η - β) := by
    rw [div_le_div_iff₀ (by positivity) h1ηβ_pos]
    linarith
  have hcon' : 10 / (3 * η) ≤ 25 / (8 * η) := by
    have hsum : 3 / η + 1 / (8 * η) = 25 / (8 * η) := by field_simp; ring
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hcon'
  linarith

/-- **The de la Vallée Poussin zero-free region for `riemannZeta`.** There is `c > 0` such that
`ζ(s) ≠ 0` whenever `Re s ≥ 1 − c / log (|Im s| + 3)` (Davenport §13). -/
theorem riemannZeta_zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨δ₀, hδ₀, hlow⟩ := exists_delta_riemannZeta_ne_zero_of_abs_im_le_two
  obtain ⟨c₂, hc₂, hhigh⟩ := exists_c_riemannZeta_ne_zero_of_two_le_abs_im
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨min (δ₀ * Real.log 3) c₂, lt_min (mul_pos hδ₀ hlog3) hc₂, fun s hsre ↦ ?_⟩
  have hlog_ge : Real.log 3 ≤ Real.log (|s.im| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlog_pos : 0 < Real.log (|s.im| + 3) := hlog3.trans_le hlog_ge
  by_cases him : |s.im| ≤ 2
  · refine hlow s him ?_
    have hc_le : min (δ₀ * Real.log 3) c₂ / Real.log (|s.im| + 3) ≤ δ₀ := by
      calc
        min (δ₀ * Real.log 3) c₂ / Real.log (|s.im| + 3)
            ≤ (δ₀ * Real.log 3) / Real.log 3 :=
              div_le_div₀ (by positivity) (min_le_left _ _) hlog3 hlog_ge
        _ = δ₀ := by field_simp
    linarith
  · push Not at him
    refine hhigh s him.le ?_
    have hc_le : min (δ₀ * Real.log 3) c₂ / Real.log (|s.im| + 3) ≤
        c₂ / Real.log (|s.im| + 3) :=
      div_le_div_of_nonneg_right (min_le_right _ _) hlog_pos.le
    linarith

end TauCeti
