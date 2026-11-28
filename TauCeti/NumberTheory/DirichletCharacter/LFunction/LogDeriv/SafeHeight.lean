/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.Data.Real.Pigeonhole
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard

/-!
# Simultaneous separation from Dirichlet zero ordinates

A height in the upper half of `[T, T + 1]` can be chosen so that both horizontal contour
edges avoid the zeros. The separation is quantified in terms of the two real logarithmic
derivatives of the entire completion at `2 ± iT`. There is no assumption of conjugation
symmetry for the zeros of an individual character.

See Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 11.4 and the proof of
Theorem 5.1, for the use of separated heights in the explicit formula.
-/

public section

open Complex Set TauCeti TauCeti.LFunctions

namespace DirichletCharacter

/-- Count distinct divisor points in a radius-three disc using the positive Hadamard kernel
at its centre. -/
private theorem card_le_nine_mul_re_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hp : χ.IsPrimitive) (t : ℝ) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 0 < MeromorphicOn.divisor (dirichletData χ hp).entireCompletion univ ρ ∧
      ‖(2 : ℂ) + t * I - ρ‖ ≤ 3) :
    (S.card : ℝ) ≤ 9 * (logDeriv (dirichletData χ hp).entireCompletion (2 + t * I)).re := by
  let w : ℂ := 2 + t * I
  have hw : w.re = 2 := by simp [w]
  have hsum := sum_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub_le
    χ hp (s := w) (by rw [hw]; norm_num) S
  have hterm (ρ) (hρ : ρ ∈ S) : 1 ≤
      9 * (analyticOrderNatAt (dirichletData χ hp).entireCompletion ρ : ℝ) * (1 / (w - ρ)).re := by
    obtain ⟨hpos, hd⟩ := hS ρ hρ
    have hρre := (re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hp hpos).2
    have hm := dirichletData_hasMeromorphicContinuation χ hp
    rw [hm.meromorphicOn_entireCompletion.divisor_eq_analyticOrderNatAt
      (hm.analyticAt_entireCompletion ρ) (mem_univ ρ)] at hpos
    have hmult : (1 : ℝ) ≤ analyticOrderNatAt (dirichletData χ hp).entireCompletion ρ := by
      exact_mod_cast (by omega : 1 ≤ analyticOrderNatAt (dirichletData χ hp).entireCompletion ρ)
    have hre : 1 ≤ (w - ρ).re := by simp only [sub_re, hw]; linarith
    have hn : w - ρ ≠ 0 := by intro h; rw [h, zero_re] at hre; norm_num at hre
    simp only [one_div, inv_re]
    rw [← mul_div_assoc, le_div_iff₀ (normSq_pos.mpr hn), one_mul, normSq_eq_norm_sq]
    have hprod := mul_le_mul hmult hre zero_le_one (by positivity :
      0 ≤ (analyticOrderNatAt (dirichletData χ hp).entireCompletion ρ : ℝ))
    have hd' : ‖w - ρ‖ ≤ 3 := hd
    nlinarith only [hd', hprod, norm_nonneg (w - ρ)]
  calc
    (S.card : ℝ) = ∑ _ρ ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ ρ ∈ S, 9 * ((analyticOrderNatAt (dirichletData χ hp).entireCompletion ρ : ℝ) *
        (1 / (w - ρ)).re) := Finset.sum_le_sum fun ρ hρ ↦ by rw [← mul_assoc]; exact hterm ρ hρ
    _ ≤ _ := by rw [← Finset.mul_sum]; gcongr

/-- A critical-strip point whose absolute ordinate is within one unit of the chosen height
belongs to one of the two counting discs. -/
private theorem norm_sub_le_three_of_abs_im_near {T t : ℝ} {ρ : ℂ}
    (ht : t ∈ Icc T (T + 1)) (hre : ρ.re ∈ Ioo 0 1) (hnear : |t - (|ρ.im|)| ≤ 1) :
    ‖2 + ((if ρ.im < 0 then -T else T : ℝ) : ℂ) * I - ρ‖ ≤ 3 := by
  let u := if ρ.im < 0 then -T else T
  have hu : |ρ.im - u| ≤ 2 := by
    have hi := abs_le.mp hnear
    by_cases hn : ρ.im < 0
    · rw [abs_of_neg hn] at hi
      simp only [u, ite_eq_left hn]
      exact abs_le.mpr (by constructor <;> linarith [ht.1, ht.2, hi.1, hi.2])
    · rw [abs_of_nonneg (le_of_not_gt hn)] at hi
      simp only [u, ite_eq_right hn]
      exact abs_le.mpr (by constructor <;> linarith [ht.1, ht.2, hi.1, hi.2])
  have hreal : (2 + (u : ℂ) * I - ρ).re = 2 - ρ.re := by simp
  have himag : (2 + (u : ℂ) * I - ρ).im = u - ρ.im := by simp
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, normSq_apply, hreal, himag]
  nlinarith [hre.1, hre.2, (abs_le.mp hu).1, (abs_le.mp hu).2,
    mul_nonneg hre.1.le (by linarith [hre.2] : 0 ≤ 4 - ρ.re),
    mul_nonneg (by linarith [abs_le.mp hu] : 0 ≤ 2 - (u - ρ.im))
      (by linarith [abs_le.mp hu] : 0 ≤ 2 + (u - ρ.im))]

/-- A single height strictly above `T` avoids the absolute ordinates of all nontrivial zeros
of a primitive Dirichlet character. The separation is at least `1 / (4 * (9 * K + 1))`, where
`K` is the sum of the real logarithmic derivatives of the entire completion at `2 + iT` and
`2 - iT`. The completion used here includes the pole clearing for conductor one. -/
theorem exists_height_separated_from_LFunction_zeros {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) (T : ℝ) :
    let f := (dirichletData χ hp).entireCompletion
    let K := (logDeriv f (2 + T * I)).re + (logDeriv f (2 - T * I)).re
    ∃ t ∈ Ioc T (T + 1), 0 < (4 * (9 * K + 1))⁻¹ ∧
      ∀ ρ : ℂ, χ.LFunction ρ = 0 → ρ.re ∈ Ioo 0 1 →
        (4 * (9 * K + 1))⁻¹ ≤ |t - (|ρ.im|)| := by
  classical
  intro f K
  let D := MeromorphicOn.divisor f univ
  have hfin := Function.locallyFinsupp.locallyFiniteSupport D
  let S (u : ℝ) := (hfin.finite_inter_support_of_isCompact
    (isCompact_closedBall (2 + (u : ℂ) * I) 3)).toFinset
  have hS (u : ℝ) (ρ : ℂ) : ρ ∈ S u ↔ ‖2 + (u : ℂ) * I - ρ‖ ≤ 3 ∧ 0 < D ρ := by
    have hf : AnalyticOnNhd ℂ f univ :=
      fun z _ ↦ (dirichletData_hasMeromorphicContinuation χ hp).analyticAt_entireCompletion z
    have hnonneg : 0 ≤ D ρ := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf ρ
    simp [S, Metric.mem_closedBall, dist_eq_norm', Function.mem_support, D,
      lt_iff_le_and_ne, hnonneg, ne_comm]
  let U := (S T ∪ S (-T)).image fun ρ ↦ |ρ.im|
  have hcard (u : ℝ) : ((S u).card : ℝ) ≤ 9 * (logDeriv f (2 + u * I)).re :=
    card_le_nine_mul_re_logDeriv χ hp u _ fun ρ hρ ↦ ((hS u ρ).1 hρ).symm
  have hU : (U.card : ℝ) ≤ 9 * K := by
    have hle : (U.card : ℝ) ≤ (S T).card + (S (-T)).card := by
      exact_mod_cast Finset.card_image_le.trans (Finset.card_union_le (S T) (S (-T)))
    have hneg := hcard (-T)
    rw [ofReal_neg, neg_mul, ← sub_eq_add_neg] at hneg
    dsimp [K]
    linarith [hcard T, hneg]
  have hK : 0 ≤ 9 * K := (Nat.cast_nonneg _).trans hU
  obtain ⟨t, ht, hsep⟩ := exists_mem_Icc_forall_le_abs_sub U (by linarith : T + 1 / 2 ≤ T + 1)
  refine ⟨t, ⟨by linarith [ht.1], ht.2⟩, by positivity, fun ρ hρ hre ↦ ?_⟩
  have hδ : (4 * (9 * K + 1))⁻¹ ≤ 1 := by rw [inv_le_one₀ (by positivity)]; linarith
  by_cases hnear : |t - (|ρ.im|)| ≤ 1
  · let u := if ρ.im < 0 then -T else T
    have hpρ : 0 < D ρ := (zero_lt_divisor_dirichletData_entireCompletion_iff χ hp).mpr ⟨hρ, hre⟩
    have hb := norm_sub_le_three_of_abs_im_near ⟨by linarith [ht.1], ht.2⟩ hre hnear
    have hm := (hS u ρ).2 ⟨hb, hpρ⟩
    have hmem : |ρ.im| ∈ U := Finset.mem_image_of_mem _ (by
      by_cases hn : ρ.im < 0
      · exact Finset.mem_union_right _ (by simpa [u, hn] using hm)
      · exact Finset.mem_union_left _ (by simpa [u, hn] using hm))
    refine le_trans ?_ (hsep _ hmem)
    have he : T + 1 - (T + 1 / 2) = 1 / 2 := by ring
    rw [he, div_div, ← one_div, ← mul_assoc]
    norm_num
    gcongr
  · exact hδ.trans (le_of_lt (lt_of_not_ge hnear))

end DirichletCharacter
