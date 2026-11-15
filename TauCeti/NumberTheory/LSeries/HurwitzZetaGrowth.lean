/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.MellinGrowth
public import Mathlib.NumberTheory.LSeries.ZMod
public import TauCeti.Analysis.Complex.VerticalStripGrowth

/-!
# Growth of the entire completed Hurwitz and periodic zeta functions

Mathlib's completed Hurwitz zeta functions are Mellin continuations of the functional-equation
pairs `hurwitzEvenFEPair a` and `hurwitzOddFEPair a`. Their kernel tails decay exponentially, so
the split Mellin estimates for `WeakFEPair` apply. Hence the entire functions
`completedHurwitzZetaEven₀ a` and `completedHurwitzZetaOdd a` satisfy
`‖F s‖ ≤ exp (C (1 + ‖s‖) Real.log (2 + ‖s‖))` and are bounded on every closed vertical strip.

The entire completed L-function `ZMod.completedLFunction₀ Φ` of a function `Φ : ZMod N → ℂ` is
`N ^ (-s)` times a finite combination of these functions. It inherits both estimates, so it has
order at most one and vertical-strip growth. For a nonprincipal Dirichlet character it is the
completed Dirichlet L-function.

Mathlib's exponential decay statements hold eventually. Continuity of the kernels extends them
to all `u ≥ 1` after enlarging the constant. The Hurwitz theory and its functional-equation pairs
are David Loeffler's work in Mathlib.

## Main results

* `HurwitzZeta.exists_norm_completedHurwitzZetaEven₀_le_exp_mul_log` and
  `HurwitzZeta.exists_norm_completedHurwitzZetaOdd_le_exp_mul_log`: global logarithmic-exponential
  bounds.
* `HurwitzZeta.hasVerticalStripGrowth_completedHurwitzZetaEven₀` and
  `HurwitzZeta.hasVerticalStripGrowth_completedHurwitzZetaOdd`: vertical-strip growth.
* `ZMod.exists_norm_completedLFunction₀_le_exp_mul_log`, `ZMod.orderLE_completedLFunction₀`
  and `ZMod.hasVerticalStripGrowth_completedLFunction₀`: the same for periodic completions.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

open Complex Real Set Filter Topology Asymptotics

namespace HurwitzZeta

open TauCeti

/-- The even Hurwitz kernel minus its constant term decays exponentially on `(1, ∞)`. -/
theorem exists_norm_hurwitzEvenFEPair_f_sub_le (a : UnitAddCircle) :
    ∃ C ≥ 0, ∃ c > 0, ∀ u ∈ Ioi 1, ‖(hurwitzEvenFEPair a).f u - (hurwitzEvenFEPair a).f₀‖ ≤
      C * Real.exp (-c * u ^ (1 : ℝ)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub a
  obtain ⟨C, hC, hb⟩ := exists_norm_le_mul_exp_neg_mul_rpow_one_of_isBigO
    (((continuousOn_evenKernel a).mono fun u hu ↦ zero_lt_one.trans_le hu).sub
      continuousOn_const) hO
  refine ⟨C, hC, p, hp, fun u hu ↦ le_of_eq_of_le ?_ (hb u hu)⟩
  simp only [hurwitzEvenFEPair, Function.comp_apply]
  split_ifs <;> simp [← ofReal_one, ← ofReal_sub, norm_real]

/-- The dual even Hurwitz kernel minus its constant term decays exponentially on `(1, ∞)`. -/
theorem exists_norm_hurwitzEvenFEPair_g_sub_le (a : UnitAddCircle) :
    ∃ C ≥ 0, ∃ c > 0, ∀ u ∈ Ioi 1, ‖(hurwitzEvenFEPair a).g u - (hurwitzEvenFEPair a).g₀‖ ≤
      C * Real.exp (-c * u ^ (1 : ℝ)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_cosKernel_sub a
  obtain ⟨C, hC, hb⟩ := exists_norm_le_mul_exp_neg_mul_rpow_one_of_isBigO
    (((continuousOn_cosKernel a).mono fun u hu ↦ zero_lt_one.trans_le hu).sub
      continuousOn_const) hO
  refine ⟨C, hC, p, hp, fun u hu ↦ le_of_eq_of_le ?_ (hb u hu)⟩
  simp [hurwitzEvenFEPair, ← ofReal_one, ← ofReal_sub, norm_real]

/-- The odd Hurwitz kernel decays exponentially on `(1, ∞)`. -/
theorem exists_norm_hurwitzOddFEPair_f_sub_le (a : UnitAddCircle) :
    ∃ C ≥ 0, ∃ c > 0, ∀ u ∈ Ioi 1, ‖(hurwitzOddFEPair a).f u - (hurwitzOddFEPair a).f₀‖ ≤
      C * Real.exp (-c * u ^ (1 : ℝ)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_oddKernel a
  obtain ⟨C, hC, hb⟩ := exists_norm_le_mul_exp_neg_mul_rpow_one_of_isBigO
    ((continuousOn_oddKernel a).mono fun u hu ↦ zero_lt_one.trans_le hu) hO
  refine ⟨C, hC, p, hp, fun u hu ↦ le_of_eq_of_le ?_ (hb u hu)⟩
  simp [hurwitzOddFEPair, norm_real]

/-- The dual odd Hurwitz kernel decays exponentially on `(1, ∞)`. -/
theorem exists_norm_hurwitzOddFEPair_g_sub_le (a : UnitAddCircle) :
    ∃ C ≥ 0, ∃ c > 0, ∀ u ∈ Ioi 1, ‖(hurwitzOddFEPair a).g u - (hurwitzOddFEPair a).g₀‖ ≤
      C * Real.exp (-c * u ^ (1 : ℝ)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_sinKernel a
  obtain ⟨C, hC, hb⟩ := exists_norm_le_mul_exp_neg_mul_rpow_one_of_isBigO
    ((continuousOn_sinKernel a).mono fun u hu ↦ zero_lt_one.trans_le hu) hO
  refine ⟨C, hC, p, hp, fun u hu ↦ le_of_eq_of_le ?_ (hb u hu)⟩
  simp [hurwitzOddFEPair, norm_real]

/-- The odd pair has no constant terms, so the completed odd Hurwitz zeta function is given by
the entire part of its Mellin continuation. -/
theorem completedHurwitzZetaOdd_eq_Λ₀ (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd a s = (hurwitzOddFEPair a).Λ₀ ((s + 1) / 2) / 2 := by
  simp [completedHurwitzZetaOdd, WeakFEPair.Λ₀_eq]

/-- The entire completed even Hurwitz zeta function has logarithmic-exponential growth. -/
theorem exists_norm_completedHurwitzZetaEven₀_le_exp_mul_log (a : UnitAddCircle) :
    ∃ C > 0, ∀ s : ℂ, ‖completedHurwitzZetaEven₀ a s‖ ≤
      Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C₁, hC₁, c₁, hc₁, hf⟩ := exists_norm_hurwitzEvenFEPair_f_sub_le a
  obtain ⟨C₂, hC₂, c₂, hc₂, hg⟩ := exists_norm_hurwitzEvenFEPair_g_sub_le a
  obtain ⟨C, hC, hΛ⟩ := (hurwitzEvenFEPair a).exists_norm_Λ₀_le_exp_mul_log hC₁ hc₁ one_pos
    hC₂ hc₂ one_pos hf hg
  refine ⟨21 * C, by positivity, fun s ↦ ?_⟩
  rw [completedHurwitzZetaEven₀, norm_div, Complex.norm_two]
  refine (div_le_self (norm_nonneg _) one_le_two).trans
    (norm_le_exp_mul_log_of_norm_le_one_add hC.le hΛ ?_)
  rw [norm_div, Complex.norm_two]
  linarith [norm_nonneg s]

/-- The entire completed odd Hurwitz zeta function has logarithmic-exponential growth. -/
theorem exists_norm_completedHurwitzZetaOdd_le_exp_mul_log (a : UnitAddCircle) :
    ∃ C > 0, ∀ s : ℂ, ‖completedHurwitzZetaOdd a s‖ ≤
      Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C₁, hC₁, c₁, hc₁, hf⟩ := exists_norm_hurwitzOddFEPair_f_sub_le a
  obtain ⟨C₂, hC₂, c₂, hc₂, hg⟩ := exists_norm_hurwitzOddFEPair_g_sub_le a
  obtain ⟨C, hC, hΛ⟩ := (hurwitzOddFEPair a).exists_norm_Λ₀_le_exp_mul_log hC₁ hc₁ one_pos
    hC₂ hc₂ one_pos hf hg
  refine ⟨21 * C, by positivity, fun s ↦ ?_⟩
  rw [completedHurwitzZetaOdd_eq_Λ₀, norm_div, Complex.norm_two]
  refine (div_le_self (norm_nonneg _) one_le_two).trans
    (norm_le_exp_mul_log_of_norm_le_one_add hC.le hΛ ?_)
  rw [norm_div, Complex.norm_two]
  linarith [norm_add_le s 1, norm_one (α := ℂ), norm_nonneg s]

/-- The entire completed even Hurwitz zeta function has vertical-strip growth. -/
theorem hasVerticalStripGrowth_completedHurwitzZetaEven₀ (a : UnitAddCircle) :
    HasVerticalStripGrowth (completedHurwitzZetaEven₀ a) := by
  obtain ⟨C₁, -, c₁, hc₁, hf⟩ := exists_norm_hurwitzEvenFEPair_f_sub_le a
  obtain ⟨C₂, -, c₂, hc₂, hg⟩ := exists_norm_hurwitzEvenFEPair_g_sub_le a
  refine hasVerticalStripGrowth_of_forall_bound fun x y ↦ ?_
  obtain ⟨M, hM⟩ := (hurwitzEvenFEPair a).exists_norm_Λ₀_le_of_re_mem_Icc hc₁ one_pos hc₂
    one_pos hf hg (x / 2) (y / 2)
  refine ⟨M, fun s hs ↦ ?_⟩
  rw [completedHurwitzZetaEven₀, norm_div, Complex.norm_two]
  refine (div_le_self (norm_nonneg _) one_le_two).trans (hM _ ?_)
  rw [Complex.div_ofNat_re]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- The entire completed odd Hurwitz zeta function has vertical-strip growth. -/
theorem hasVerticalStripGrowth_completedHurwitzZetaOdd (a : UnitAddCircle) :
    HasVerticalStripGrowth (completedHurwitzZetaOdd a) := by
  obtain ⟨C₁, -, c₁, hc₁, hf⟩ := exists_norm_hurwitzOddFEPair_f_sub_le a
  obtain ⟨C₂, -, c₂, hc₂, hg⟩ := exists_norm_hurwitzOddFEPair_g_sub_le a
  refine hasVerticalStripGrowth_of_forall_bound fun x y ↦ ?_
  obtain ⟨M, hM⟩ := (hurwitzOddFEPair a).exists_norm_Λ₀_le_of_re_mem_Icc hc₁ one_pos hc₂
    one_pos hf hg ((x + 1) / 2) ((y + 1) / 2)
  refine ⟨M, fun s hs ↦ ?_⟩
  rw [completedHurwitzZetaOdd_eq_Λ₀, norm_div, Complex.norm_two]
  refine (div_le_self (norm_nonneg _) one_le_two).trans (hM _ ?_)
  rw [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

end HurwitzZeta

namespace ZMod

open HurwitzZeta TauCeti

variable {N : ℕ} [NeZero N]

/-- The entire completed L-function of a function on `ZMod N` has logarithmic-exponential
growth. -/
theorem exists_norm_completedLFunction₀_le_exp_mul_log (Φ : ZMod N → ℂ) :
    ∃ C > 0, ∀ s : ℂ, ‖completedLFunction₀ Φ s‖ ≤
      Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  choose CE hCE hE using fun j : ZMod N ↦
    exists_norm_completedHurwitzZetaEven₀_le_exp_mul_log (toAddCircle j)
  choose CO hCO hO using fun j : ZMod N ↦
    exists_norm_completedHurwitzZetaOdd_le_exp_mul_log (toAddCircle j)
  -- `K` dominates every Hurwitz constant and `S` is the total mass of `Φ`.
  set K := ∑ j, (CE j + CO j)
  set S := ∑ j, ‖Φ j‖
  have hpos : ∀ j ∈ Finset.univ, 0 ≤ CE j + CO j := fun j _ ↦ (add_pos (hCE j) (hCO j)).le
  have hK : 0 ≤ K := Finset.sum_nonneg hpos
  have hEK : ∀ j ∈ Finset.univ, CE j ≤ K := fun j hj ↦
    (le_add_of_nonneg_right (hCO j).le).trans (Finset.single_le_sum hpos hj)
  have hOK : ∀ j ∈ Finset.univ, CO j ≤ K := fun j hj ↦
    (le_add_of_nonneg_left (hCE j).le).trans (Finset.single_le_sum hpos hj)
  refine ⟨2 * Real.log N + K + 4 * S + 1, by positivity, fun s ↦ ?_⟩
  have hpow : ‖(N : ℂ) ^ (-s)‖ ≤ Real.exp (2 * Real.log N * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    simpa using norm_natCast_cpow_ofReal_mul_le_exp_mul_log (NeZero.ne N) (-1) s
  have hsE := norm_sum_mul_le_mul_exp_mul_log (a := Φ) hEK fun j _ ↦ hE j s
  have hsO := norm_sum_mul_le_mul_exp_mul_log (a := Φ) hOK fun j _ ↦ hO j s
  calc
    ‖completedLFunction₀ Φ s‖ ≤
        ‖(N : ℂ) ^ (-s)‖ * ‖∑ j, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s‖ +
          ‖(N : ℂ) ^ (-s)‖ * ‖∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s‖ := by
      rw [completedLFunction₀, ← norm_mul, ← norm_mul]
      exact norm_add_le _ _
    _ ≤ Real.exp (2 * Real.log N * (1 + ‖s‖) * Real.log (2 + ‖s‖)) *
          (S * Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖))) +
        Real.exp (2 * Real.log N * (1 + ‖s‖) * Real.log (2 + ‖s‖)) *
          (S * Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖))) := by gcongr
    _ = 2 * S * Real.exp ((2 * Real.log N + K) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
      rw [add_mul, add_mul, Real.exp_add]
      ring
    _ ≤ Real.exp ((2 * Real.log N + K + 2 * (2 * S)) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) :=
      Real.mul_exp_mul_one_add_mul_log_two_add_le (by positivity) (norm_nonneg s)
    _ ≤ _ := Real.exp_mul_one_add_mul_log_two_add_le_of_le (by linarith) (norm_nonneg s)

/-- The entire completed L-function of a function on `ZMod N` has order at most one. -/
theorem orderLE_completedLFunction₀ (Φ : ZMod N → ℂ) : OrderLE (completedLFunction₀ Φ) 1 := by
  obtain ⟨C, -, hC⟩ := exists_norm_completedLFunction₀_le_exp_mul_log Φ
  exact orderLE_one_of_norm_le_exp_mul_log hC

/-- The entire completed L-function of a function on `ZMod N` has vertical-strip growth. -/
theorem hasVerticalStripGrowth_completedLFunction₀ (Φ : ZMod N → ℂ) :
    HasVerticalStripGrowth (completedLFunction₀ Φ) := by
  have hpow : HasVerticalStripGrowth fun s : ℂ ↦ (N : ℂ) ^ (-s) := by
    simpa using hasVerticalStripGrowth_natCast_cpow_ofReal_mul (NeZero.ne N) (-1)
  refine (hasVerticalStripGrowth_congr (completedLFunction₀.eq_1 Φ)).mpr ?_
  exact (hpow.mul (HasVerticalStripGrowth.sum (t := Finset.univ) fun j _ ↦
      (hasVerticalStripGrowth_completedHurwitzZetaEven₀ (toAddCircle j)).const_mul (Φ j))).add
    (hpow.mul (HasVerticalStripGrowth.sum (t := Finset.univ) fun j _ ↦
      (hasVerticalStripGrowth_completedHurwitzZetaOdd (toAddCircle j)).const_mul (Φ j)))

end ZMod
