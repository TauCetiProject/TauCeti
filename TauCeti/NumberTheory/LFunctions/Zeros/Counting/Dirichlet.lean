/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Analysis.SpecialFunctions.Gamma.SectorialDigamma
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Window

/-!
# Weighted counts of Dirichlet zeros

A unit-height band contains `O(log (N (|t| + 2)))` zeros with multiplicity. Summing the counts
with a reciprocal height weight gives a logarithmic-square bound. The weight is capped at one
so that the estimate does not need a lower bound for the distance of a low zero from zero.

See Bennett and Siksek, *A conjecture of Erdős, supersingular primes and short character sums*,
§12, Proposition 12.2, for the use of these weights in the half-interval explicit formula.
-/

public section

open Complex Real Set
open scoped Nat

namespace DirichletCharacter

private theorem one_fifth_le_re_one_div_sub {t : ℝ} {ρ : ℂ}
    (hre : ρ.re ∈ Icc 0 1) (him : |ρ.im - t| ≤ 1) :
    (1 / (2 + (t : ℂ) * I - ρ)).re ≥ 1 / 5 := by
  rw [one_div, inv_re]
  have ha : 1 ≤ (2 : ℝ) - ρ.re := by linarith [hre.2]
  have hb : 0 ≤ ρ.re := hre.1
  have hc : (ρ.im - t) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) him 2).trans_eq (one_pow _)
  simp only [sub_re, add_re, mul_I_re, ofReal_im, neg_zero, add_zero, re_ofNat,
    normSq_apply, sub_im, add_im, mul_I_im, ofReal_re, im_ofNat, zero_add]
  have ha' : 0 < (2 : ℝ) - ρ.re := by linarith
  have hpos := add_pos_of_pos_of_nonneg (mul_pos ha' ha') (mul_self_nonneg (t - ρ.im))
  apply (le_div_iff₀ hpos).mpr
  nlinarith [mul_nonneg hb ha'.le]

private theorem exists_norm_logDeriv_gammaFactor_two_add_mul_I_le :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (t : ℝ),
      ‖logDeriv χ.gammaFactor (2 + (t : ℂ) * I)‖ ≤ G * Real.log (|t| + 2) := by
  obtain ⟨D, hD, hdig⟩ := Complex.exists_norm_digamma_le_log (a := 1) (b := 2) one_pos
  refine ⟨D / 2 + |Real.log π| / (2 * Real.log 2), by positivity, fun χ t ↦ ?_⟩
  let s : ℂ := 2 + (t : ℂ) * I
  have hs : s.re = 2 := by simp [s]
  classical
  let a : ℂ := if χ.Even then 0 else 1
  have ha : a = 0 ∨ a = 1 := by by_cases h : χ.Even <;> simp [a, h]
  have hre : ((s + a) / 2).re ∈ Icc 1 2 := by
    rcases ha with h | h <;> norm_num [h, hs]
  have him : ((s + a) / 2).im = t / 2 := by rcases ha with h | h <;> simp [h, s]
  have hlog : Real.log (|t / 2| + 2) ≤ Real.log (|t| + 2) := by
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [abs_nonneg t]
  have h2 : Real.log 2 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by simp)
  have hπ := mul_le_mul_of_nonneg_left h2
    (show 0 ≤ |Real.log π| / (2 * Real.log 2) by positivity)
  have hcancel : |Real.log π| / (2 * Real.log 2) * Real.log 2 = |Real.log π| / 2 := by
    field_simp
  rw [hcancel] at hπ
  rw [χ.logDeriv_gammaFactor_eq_digamma (χ.gammaFactor_ne_zero_of_re_pos (by simp))]
  refine (norm_sub_le ..).trans ?_
  simp only [norm_div, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
  have hd := (hdig ((s + a) / 2) hre).trans (mul_le_mul_of_nonneg_left (him ▸ hlog) hD.le)
  linarith

private theorem sum_analyticOrderNatAt_LFunction_le_band_of_ne_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {S : Finset ℂ} {t G : ℝ}
    (hS : ∀ ρ ∈ S, ρ.re ∈ Ioo 0 1 ∧ |ρ.im - t| ≤ 1)
    (hG : ‖logDeriv χ.gammaFactor (2 + (t : ℂ) * I)‖ ≤ G * Real.log (|t| + 2)) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) ≤
      5 * (-(logDeriv riemannZeta 2).re + Real.log N / 2 + G * Real.log (|t| + 2)) := by
  let s : ℂ := 2 + (t : ℂ) * I
  have hs : s.re = 2 := by simp [s]
  have h := χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor hχ hne
    (fun ρ hρ ↦ (hS ρ hρ).1.1) (s := s) (by simp [hs])
  have hL : (logDeriv χ.LFunction s).re ≤ -(logDeriv riemannZeta 2).re :=
    (re_le_norm _).trans
      (χ.norm_logDeriv_LFunction_le_of_le_re (s := s) (σ := 2) one_lt_two (by simp [hs]))
  have hγ : (logDeriv χ.gammaFactor s).re ≤ G * Real.log (|t| + 2) := (re_le_norm _).trans hG
  have hlow : (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ)) * (1 / 5) ≤
      ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun ρ hρ ↦ mul_le_mul_of_nonneg_left
      (one_fifth_le_re_one_div_sub ⟨(hS ρ hρ).1.1.le, (hS ρ hρ).1.2.le⟩ (hS ρ hρ).2) (by positivity)
  linarith

private theorem sum_analyticOrderNatAt_LFunction_le_band_level_one
    (χ : DirichletCharacter ℂ 1) {S : Finset ℂ} {t C : ℝ}
    (hS : ∀ ρ ∈ S, ρ.re ∈ Ioo 0 1 ∧ |ρ.im - t| ≤ 1)
    (hC : ∑ᶠ ρ : {z : ℂ // ‖z - (t : ℂ) * I‖ ≤ 2 ∧ riemannZeta z = 0},
      ((analyticOrderAt riemannZeta ρ.val).toNat : ℝ) ≤ C * Real.log (|t| + 2)) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) ≤ C * Real.log (|t| + 2) := by
  classical
  let Z := TauCeti.riemannZetaZerosClosedBall ((t : ℂ) * I) 2
  rw [finsum_subtype_eq_finsum_cond (f := fun z ↦ ((analyticOrderAt riemannZeta z).toNat : ℝ)),
    finsum_cond_eq_sum_of_cond_iff (t := Z) _
    (fun {_} _ ↦ TauCeti.mem_riemannZetaZerosClosedBall.symm)] at hC
  let m (ρ : ℂ) : ℝ := analyticOrderNatAt χ.LFunction ρ
  have hm (ρ : ℂ) : m ρ = ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
    simp only [m, analyticOrderNatAt, LFunction_modOne_eq]
  have hsub : ∀ ρ ∈ S, m ρ ≠ 0 → ρ ∈ Z := by
    intro ρ hρ hpos
    have hzero : χ.LFunction ρ = 0 :=
      (χ.one_le_analyticOrderNatAt_LFunction_iff.mp (Nat.one_le_iff_ne_zero.mpr (by
        exact fun h ↦ hpos (Nat.cast_eq_zero.mpr h)))).1
    refine TauCeti.mem_riemannZetaZerosClosedBall.mpr ⟨?_, LFunction_modOne_eq ▸ hzero⟩
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    simpa [abs_of_pos (hS ρ hρ).1.1, one_add_one_eq_two] using
      add_le_add (hS ρ hρ).1.2.le (hS ρ hρ).2
  calc
    ∑ ρ ∈ S, m ρ = ∑ ρ ∈ S ∩ Z, m ρ := by
      symm
      exact Finset.sum_subset Finset.inter_subset_left fun ρ hρ hnot ↦
        not_ne_iff.mp fun hn ↦ hnot (Finset.mem_inter.mpr ⟨hρ, hsub ρ hρ hn⟩)
    _ ≤ ∑ ρ ∈ Z, m ρ :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun _ _ _ ↦ by positivity
    _ ≤ _ := by simpa only [hm] using hC

/-- Uniform in the conductor and primitive character, the sum of analytic multiplicities in a
height band of radius one in the open critical strip is `O(log (N (|t| + 2)))`. The finite set
may include nonzeros, whose multiplicities contribute zero. -/
theorem exists_sum_analyticOrderNatAt_LFunction_le_band :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ (t : ℝ) (S : Finset ℂ), (∀ ρ ∈ S, ρ.re ∈ Ioo 0 1 ∧ |ρ.im - t| ≤ 1) →
        ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) ≤ C * Real.log (N * (|t| + 2)) := by
  obtain ⟨G, hG, hgamma⟩ := exists_norm_logDeriv_gammaFactor_two_add_mul_I_le
  obtain ⟨B, hB⟩ := TauCeti.exists_finsum_analyticOrderAt_riemannZeta_le 0 2
  let D := |(logDeriv riemannZeta 2).re| / Real.log 2
  let C := 5 * (D + 1 + G) + |B|
  refine ⟨C, by dsimp [C, D]; positivity, fun {N} _ χ hχ t S hS ↦ ?_⟩
  have ht : 0 < |t| + 2 := by positivity
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogt : Real.log 2 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by simp)
  have hlogt' : 0 ≤ Real.log (|t| + 2) := (Real.log_pos one_lt_two).le.trans hlogt
  rw [Real.log_mul (Nat.cast_ne_zero.mpr (NeZero.ne N)) ht.ne']
  by_cases hne : χ = 1
  · obtain rfl := hχ.eq_one_iff.mp hne
    simp only [Nat.cast_one, Real.log_one, zero_add]
    refine (sum_analyticOrderNatAt_LFunction_le_band_level_one χ (C := B) hS ?_).trans ?_
    · simpa using hB ((t : ℂ) * I) (by simp)
    · apply mul_le_mul_of_nonneg_right _ hlogt'
      dsimp [C, D]
      linarith [le_abs_self B, abs_nonneg (logDeriv riemannZeta 2).re,
        (by positivity : 0 ≤ |(logDeriv riemannZeta 2).re| / Real.log 2)]
  have hd : 0 ≤ D := by dsimp [D]; positivity
  have hζ : -(logDeriv riemannZeta 2).re ≤ D * Real.log (|t| + 2) := by
    refine (neg_le_abs _).trans ?_
    simpa only [D, div_mul_cancel₀ _ (by positivity : Real.log 2 ≠ 0)] using
      mul_le_mul_of_nonneg_left hlogt hd
  refine (sum_analyticOrderNatAt_LFunction_le_band_of_ne_one χ hχ hne hS (hgamma χ t)).trans ?_
  dsimp only [C]
  nlinarith [mul_nonneg hd hlogN, mul_nonneg hG hlogN, mul_nonneg (abs_nonneg B) hlogt',
    mul_nonneg (abs_nonneg B) hlogN]

private theorem min_one_inv_norm_le_two_div_floor_add_one (ρ : ℂ) :
    min 1 ‖ρ‖⁻¹ ≤ 2 / (⌊|ρ.im|⌋₊ + 1 : ℝ) := by
  let k := ⌊|ρ.im|⌋₊
  have hk : (k : ℝ) ≤ ‖ρ‖ := (Nat.floor_le (abs_nonneg _)).trans (abs_im_le_norm _)
  rcases Nat.eq_zero_or_pos k with hz | hp
  · have hf : ⌊|ρ.im|⌋₊ = 0 := hz
    exact (min_le_left _ _).trans (by norm_num [hf])
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr hp
  calc
    min 1 ‖ρ‖⁻¹ ≤ (k : ℝ)⁻¹ := (min_le_right ..).trans (inv_anti₀ hk' hk)
    _ ≤ 2 / ((k : ℝ) + 1) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hk' (by positivity)]
      have : (1 : ℝ) ≤ k := by exact_mod_cast hp
      linarith

private theorem sum_order_mul_min_inv_norm_le_harmonic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {S : Finset ℂ} {T B : ℝ}
    (hS : ∀ ρ ∈ S, |ρ.im| ≤ T)
    (hcount : ∀ k < ⌊T⌋₊ + 1, ∑ ρ ∈ S with ⌊|ρ.im|⌋₊ = k,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) ≤ B) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * min 1 ‖ρ‖⁻¹ ≤
      2 * B * (harmonic (⌊T⌋₊ + 1) : ℝ) := by
  let k (ρ : ℂ) := ⌊|ρ.im|⌋₊
  let m (ρ : ℂ) : ℝ := analyticOrderNatAt χ.LFunction ρ
  have hmaps : ∀ ρ ∈ S, k ρ ∈ Finset.range (⌊T⌋₊ + 1) := fun ρ hρ ↦
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (hS ρ hρ)))
  calc
    ∑ ρ ∈ S, m ρ * min 1 ‖ρ‖⁻¹ ≤ ∑ ρ ∈ S, m ρ * (2 / (k ρ + 1 : ℝ)) :=
      Finset.sum_le_sum fun ρ _ ↦ mul_le_mul_of_nonneg_left
        (min_one_inv_norm_le_two_div_floor_add_one ρ) (by positivity)
    _ = ∑ j ∈ Finset.range (⌊T⌋₊ + 1), ∑ ρ ∈ S with k ρ = j, m ρ * (2 / (k ρ + 1 : ℝ)) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ j ∈ Finset.range (⌊T⌋₊ + 1), 2 * B * ((j : ℝ) + 1)⁻¹ := by
      refine Finset.sum_le_sum fun j hj ↦ ?_
      have heq (ρ : ℂ) (hρ : ρ ∈ S.filter (fun ρ ↦ k ρ = j)) :
          m ρ * (2 / (k ρ + 1 : ℝ)) = m ρ * (2 / (j + 1 : ℝ)) := by
        rw [(Finset.mem_filter.mp hρ).2]
      rw [Finset.sum_congr rfl heq, ← Finset.sum_mul]
      simpa only [div_eq_mul_inv, mul_left_comm B 2, mul_assoc] using
        mul_le_mul_of_nonneg_right (hcount j (Finset.mem_range.mp hj))
          (by positivity : 0 ≤ 2 / (j + 1 : ℝ))
    _ = _ := by simp [harmonic, Finset.mul_sum]

private theorem sum_order_floor_band_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {S : Finset ℂ} {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hS : ∀ ρ ∈ S, ρ.re ∈ Ioo 0 1)
    (hband : ∀ t : ℝ, ∀ V : Finset ℂ,
      (∀ ρ ∈ V, ρ.re ∈ Ioo 0 1 ∧ |ρ.im - t| ≤ 1) →
        ∑ ρ ∈ V, (analyticOrderNatAt χ.LFunction ρ : ℝ) ≤ C * Real.log (N * (|t| + 2)))
    {k : ℕ} (hk : k < ⌊T⌋₊ + 1) :
    ∑ ρ ∈ S with ⌊|ρ.im|⌋₊ = k, (analyticOrderNatAt χ.LFunction ρ : ℝ) ≤
      2 * C * Real.log (N * (T + 2)) := by
  let V := S.filter fun ρ ↦ ⌊|ρ.im|⌋₊ = k
  have hb (ρ : ℂ) (hρ : ρ ∈ V) : (k : ℝ) ≤ |ρ.im| ∧ |ρ.im| < (k : ℝ) + 1 := by
    have he := (Finset.mem_filter.mp hρ).2
    exact ⟨he ▸ Nat.floor_le (abs_nonneg _), he ▸ Nat.lt_floor_add_one _⟩
  have hp (ρ : ℂ) (hρ : ρ ∈ V) : ρ.re ∈ Ioo 0 1 := hS ρ (Finset.mem_filter.mp hρ).1
  have hplus := hband k (V.filter fun ρ ↦ 0 ≤ ρ.im) (by
    intro ρ hρ
    obtain ⟨hρ, hpos⟩ := Finset.mem_filter.mp hρ
    have h := hb ρ hρ
    rw [abs_of_nonneg hpos] at h
    exact ⟨hp ρ hρ, abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩⟩)
  have hminus := hband (-(k : ℝ)) (V.filter fun ρ ↦ ¬ 0 ≤ ρ.im) (by
    intro ρ hρ
    obtain ⟨hρ, hneg⟩ := Finset.mem_filter.mp hρ
    have h := hb ρ hρ
    rw [abs_of_neg (lt_of_not_ge hneg)] at h
    exact ⟨hp ρ hρ, abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩⟩)
  have hkt : (k : ℝ) ≤ T := (by exact_mod_cast Nat.lt_succ_iff.mp hk : (k : ℝ) ≤ ⌊T⌋₊).trans
    (Nat.floor_le hT)
  have hlog : Real.log (N * ((k : ℝ) + 2)) ≤ Real.log (N * (T + 2)) :=
    Real.log_le_log (mul_pos (Nat.cast_pos.mpr (NeZero.pos N)) (by positivity)) (by gcongr)
  simp only [abs_neg, Nat.abs_cast] at hplus hminus
  have he := Finset.sum_filter_add_sum_filter_not V (fun ρ ↦ 0 ≤ ρ.im)
    (fun ρ ↦ (analyticOrderNatAt χ.LFunction ρ : ℝ))
  linarith [mul_le_mul_of_nonneg_left hlog hC]

/-- For every primitive Dirichlet character of conductor `N`, the sum of analytic multiplicities
weighted by `min(1, 1/‖ρ‖)` over any finite set in `0 < Re ρ < 1`, `|Im ρ| ≤ T`, is at most
`C log²(N (T + 2))`, with an absolute `C`. Points that are not zeros contribute zero. -/
theorem exists_sum_analyticOrderNatAt_LFunction_mul_min_inv_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ (T : ℝ) (S : Finset ℂ), (∀ ρ ∈ S, ρ.re ∈ Ioo 0 1 ∧ |ρ.im| ≤ T) →
        ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * min 1 ‖ρ‖⁻¹ ≤
          C * Real.log (N * (T + 2)) ^ 2 := by
  obtain ⟨A, hA, hband⟩ := exists_sum_analyticOrderNatAt_LFunction_le_band
  refine ⟨4 * A * (1 + (Real.log 2)⁻¹), by positivity, fun {N} _ χ hχ T S hS ↦ ?_⟩
  obtain rfl | ⟨ρ, hρ⟩ := S.eq_empty_or_nonempty
  · rw [Finset.sum_empty]
    positivity
  have hT := (abs_nonneg _).trans (hS ρ hρ).2
  let L := Real.log (N * (T + 2))
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have h2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hL : 0 ≤ L := (Real.log_pos one_lt_two).le.trans h2
  have hlog : Real.log (↑(⌊T⌋₊ + 1) : ℝ) ≤ L := by
    apply Real.log_le_log (by positivity)
    push_cast
    have hf := Nat.floor_le hT
    nlinarith
  have hh := (harmonic_le_one_add_log (⌊T⌋₊ + 1)).trans (add_le_add_right hlog 1)
  have hone : 1 ≤ (Real.log 2)⁻¹ * L := by
    rw [inv_mul_eq_div, le_div_iff₀ (Real.log_pos one_lt_two), one_mul]
    exact h2
  have hcount (k : ℕ) (hk : k < ⌊T⌋₊ + 1) :=
    sum_order_floor_band_le χ hT hA.le (fun ρ hρ ↦ (hS ρ hρ).1) (hband χ hχ) hk
  refine (sum_order_mul_min_inv_norm_le_harmonic χ (fun ρ hρ ↦ (hS ρ hρ).2) hcount).trans ?_
  calc
    _ ≤ 2 * (2 * A * L) * ((1 + (Real.log 2)⁻¹) * L) := by
      gcongr
      linarith
    _ = _ := by ring

/-- The logarithmic-square bound summed over all nontrivial zeros up to the given absolute
height, with analytic multiplicity. This includes real zeros and the conductor-one case. -/
theorem exists_finsum_analyticOrderNatAt_LFunction_mul_min_inv_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ T : ℝ,
        (∑ᶠ ρ : {z : ℂ // χ.LFunction z = 0 ∧ z.re ∈ Ioo 0 1 ∧ |z.im| ≤ T},
          (analyticOrderNatAt χ.LFunction ρ.val : ℝ) * min 1 ‖ρ.val‖⁻¹) ≤
          C * Real.log (N * (T + 2)) ^ 2 := by
  open TauCeti.LFunctions in
  obtain ⟨C, hC, hbound⟩ := exists_sum_analyticOrderNatAt_LFunction_mul_min_inv_norm_le
  refine ⟨C, hC, fun {N} _ χ hχ T ↦ ?_⟩
  let P (z : ℂ) : Prop := χ.LFunction z = 0 ∧ z.re ∈ Ioo 0 1 ∧ |z.im| ≤ T
  let m (z : ℂ) : ℝ := (analyticOrderNatAt χ.LFunction z : ℝ) * min 1 ‖z‖⁻¹
  let D := MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion univ
  have hfinite : {z | P z}.Finite := by
    let K := Metric.closedBall (0 : ℂ) (1 + T)
    refine ((D.restrict (subset_univ K)).finiteSupport (isCompact_closedBall ..)).subset ?_
    intro z hz
    have ⟨hzero, hre, him⟩ : P z := hz
    have hzK : z ∈ K := Metric.mem_closedBall.mpr (by
      rw [dist_zero_right]
      exact (norm_le_abs_re_add_abs_im z).trans
        (add_le_add (by simpa [abs_of_pos hre.1] using hre.2.le) him))
    rw [Function.mem_support, Function.locallyFinsuppWithin.restrict_apply, ite_eq_left hzK]
    exact ((zero_lt_divisor_dirichletData_entireCompletion_iff χ hχ).mpr ⟨hzero, hre⟩).ne'
  rw [finsum_subtype_eq_finsum_cond (f := m) P,
    finsum_cond_eq_sum_of_cond_iff m (t := hfinite.toFinset) (by simp)]
  exact hbound χ hχ T hfinite.toFinset fun z hz ↦ (hfinite.mem_toFinset.mp hz).2

end DirichletCharacter
