/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Algebra.BigOperators.Finset.Filter
import TauCeti.GroupTheory.Coset.Fiber
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Lipschitz

/-!
# Riesz sums with two cutoffs on a group of places

A family of translates of a two-valued cap gives two Riesz cutoffs. When summing over
one kernel of a class map, every translate that reaches the prescribed class meets the
same number of exceptional places. After subtraction of the logarithmic main term,
the short-cutoff correction is a difference of remainders in one residue class.

The prime-sum identity is the one in `New.Data.totalRemainder_eq` of the shorter GRH
formalization (`lsernau/grh-lean`, `72fead1`, `New/Reduction/PrimeSums.lean`).
-/

public section

open Finset TauCeti

namespace MonoidHom

variable {G H : Type*} [Group G] [Fintype G] [DecidableEq G] [DecidableEq H]

/-- Sum capped ramps over the kernel of a class map. The default cutoff is `X`; the
correction for cutoff `x` occurs `#B` times at each index whose translate has class `c`.
The coefficients may have either sign, and the two cutoffs need not be ordered. -/
theorem sum_sum_mul_max_eq_rieszSum [MulOneClass H] (π : G →* H) (B : Finset G) {c : H}
    (hB : ∀ b ∈ B, π b = c) (g : ℕ → G) (w : ℕ → ℝ) {a x X : ℝ} {N : ℕ}
    (ha : 0 ≤ a) (hx : 0 < x) (hX : 0 < X) (hN : ⌊max x X⌋₊ ≤ N) :
    let A := univ.filter fun t : G ↦ π t = 1
    let κ := fun t ↦ if t ∈ B then a / x else a / X
    let W := fun n ↦ if π (g n) = c then (w n : ℂ) else 0
    ∑ t ∈ A, ∑ n ∈ Icc 1 N, w n * max (a / n - κ (g n * t)) 0 =
      a * ((A.card : ℝ) * (rieszSum (fun n ↦ (w n : ℂ)) X).re / X +
        (B.card : ℝ) * ((rieszSum W x).re / x - (rieszSum W X).re / X)) := by
  dsimp only
  let A := univ.filter fun t : G ↦ π t = 1
  let W := fun n ↦ if π (g n) = c then (w n : ℂ) else 0
  have hscaled (v : ℕ → ℝ) {y : ℝ} (hy : 0 < y) (hyN : ⌊y⌋₊ ≤ N) :
      ∑ n ∈ Icc 1 N, v n * max (a / n - a / y) 0 =
        a * (rieszSum (fun n ↦ (v n : ℂ)) y).re / y := by
    obtain rfl | ha := ha.eq_or_lt
    · simp
    have hcut : a / (a / y) = y := by field_simp
    have h := mul_rieszSum_div_eq_sum_max (fun n ↦ (v n : ℂ)) (a := a) (div_pos ha hy) le_rfl
    rw [hcut] at h
    have hre := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.re_sum] at hre
    rw [mul_div_right_comm, hre]
    -- The extra indices above the natural floor of the cutoff contribute zero.
    refine (sum_subset (Icc_subset_Icc_right hyN) ?_).symm
    intro n hn hny
    have hyn : y ≤ n := by
      apply (Nat.lt_of_floor_lt ?_).le
      exact lt_of_not_ge fun hle ↦ hny (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, hle⟩)
    have hdiv := div_le_div_of_nonneg_left ha.le hy hyn
    simp [max_eq_right (sub_nonpos.mpr hdiv)]
  rw [sum_comm]
  have hs (n : ℕ) :
      (∑ t ∈ A, w n * max (a / n - (if g n * t ∈ B then a / x else a / X)) 0) =
        (A.card : ℝ) * (w n * max (a / n - a / X) 0) +
          (B.card : ℝ) * ((if π (g n) = c then w n else 0) *
            (max (a / n - a / x) 0 - max (a / n - a / X) 0)) := by
    simp_rw [apply_ite (fun u : ℝ ↦ max (a / n - u) 0)]
    rw [← mul_sum, π.sum_ite_mul_mem_over_ker B hB, nsmul_eq_mul, nsmul_eq_mul]
    split_ifs <;> ring
  rw [sum_congr rfl (fun n _ ↦ hs n)]
  simp only [sum_add_distrib, ← mul_sum]
  simp only [mul_sub, sum_sub_distrib]
  rw [hscaled w hX ((Nat.floor_mono (le_max_right _ _)).trans hN),
    hscaled _ hx ((Nat.floor_mono (le_max_left _ _)).trans hN),
    hscaled _ hX ((Nat.floor_mono (le_max_right _ _)).trans hN)]
  have hW : (fun n ↦ ((if π (g n) = c then w n else 0 : ℝ) : ℂ)) = W := by
    funext n
    by_cases hn : π (g n) = c <;> simp [W, hn]
  rw [hW]
  ring

/-- After subtracting the logarithmic main term, the capped sum over the kernel is
`a` times the sum of the baseline remainder at `X` and the residue-class correction
`R_c(x) - R_c(X)`, weighted by the sizes of the kernel and `B` respectively.
Here `C` is the baseline constant. The constant `Cc` for the residue class cancels in
`R_c(x) - R_c(X)`, so it can be chosen independently. -/
theorem sum_sub_log_eq_rieszSum_sub_log [MulOneClass H] (π : G →* H) [Fintype H]
    (hπ : Function.Surjective π) (B : Finset G) {c : H} (hB : ∀ b ∈ B, π b = c)
    (g : ℕ → G) (w : ℕ → ℝ) (C Cc : ℝ) {a x X : ℝ} {N : ℕ} (ha : 0 ≤ a) (hx : 0 < x) (hX : 0 < X)
    (hN : ⌊max x X⌋₊ ≤ N) :
    let A := univ.filter fun t : G ↦ π t = 1
    let κ := fun t ↦ if t ∈ B then a / x else a / X
    let R := fun y ↦ (rieszSum (fun n ↦ (w n : ℂ)) y).re / y - Real.log y - C
    let Rc := fun y ↦ (rieszSum (fun n ↦ if π (g n) = c then (w n : ℂ) else 0) y).re / y -
      Real.log y / (Fintype.card H : ℝ) - Cc
    ∑ t ∈ A, ((∑ n ∈ Icc 1 N, w n * max (a / n - κ (g n * t)) 0) -
      a * (Real.log a - (∑ b : G, Real.log (κ b)) / (Fintype.card G : ℝ) + C)) =
        a * ((B.card : ℝ) * (Rc x - Rc X) + (A.card : ℝ) * R X) := by
  dsimp only
  obtain rfl | ha := ha.eq_or_lt
  · simp
  let A := univ.filter fun t : G ↦ π t = 1
  have hA : A.card * Fintype.card H = Fintype.card G := by
    have hker : A.card = Nat.card π.ker := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact congrArg Finset.card (Finset.filter_congr fun t _ ↦ (π.mem_ker (x := t)).symm)
    rw [hker, ← Nat.card_eq_fintype_card (α := H), ← Nat.card_eq_fintype_card (α := G)]
    simpa [mul_comm] using (π.natCard_preimage_of_surjective hπ Set.univ).symm
  have hG : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hH : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hratio : (A.card : ℝ) / Fintype.card G = 1 / Fintype.card H := by
    apply (div_eq_div_iff hG hH).mpr
    simpa using congrArg (fun n : ℕ ↦ (n : ℝ)) hA
  have hlog : ∑ b : G, Real.log (if b ∈ B then a / x else a / X) =
      (Fintype.card G : ℝ) * (Real.log a - Real.log X) +
        (B.card : ℝ) * (Real.log X - Real.log x) := by
    simp_rw [apply_ite Real.log, Real.log_div ha.ne' hx.ne', Real.log_div ha.ne' hX.ne']
    rw [sum_ite_eq_card_nsmul_add]
    simp only [card_univ, filter_mem_eq_inter, univ_inter, nsmul_eq_mul]
    ring
  rw [sum_sub_distrib, sum_sum_mul_max_eq_rieszSum π B hB g w ha.le hx hX hN, sum_const,
    nsmul_eq_mul, hlog, add_div, mul_div_cancel_left₀ _ hG]
  -- Regroup the main term to expose the kernel-to-group ratio.
  have hmain : (A.card : ℝ) * (a * (Real.log a - (Real.log a - Real.log X +
      B.card * (Real.log X - Real.log x) / Fintype.card G) + C)) =
      a * (A.card * (Real.log X + C) -
        ((A.card : ℝ) / Fintype.card G) * B.card * (Real.log X - Real.log x)) := by ring
  rw [hmain, hratio]
  ring

end MonoidHom
