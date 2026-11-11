/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.MellinGrowth
public import Mathlib.NumberTheory.LSeries.ZMod
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

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
  `HurwitzZeta.hasVerticalStripGrowth_completedHurwitzZetaOdd`: vertical-strip growth, from
  boundedness on each closed strip.
* `ZMod.exists_norm_completedLFunction₀_le_exp_mul_log`, `ZMod.orderLE_completedLFunction₀`
  and `ZMod.hasVerticalStripGrowth_completedLFunction₀`: the same for periodic completions.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

open Complex Real Set Filter Topology Asymptotics

namespace TauCeti

/-- A function continuous on `[1, ∞)` with an eventual bound `O(exp (-p u))` satisfies
`‖f u‖ ≤ C exp (-p u ^ 1)` for every `u > 1`, with `C ≥ 0`. The exponent `u ^ 1` is the shape
consumed by the split Mellin estimates. -/
theorem exists_norm_le_mul_exp_neg_mul_rpow_one_of_isBigO {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {p : ℝ} (hf : ContinuousOn f (Ici 1))
    (h : f =O[atTop] fun u ↦ Real.exp (-p * u)) :
    ∃ C ≥ 0, ∀ u ∈ Ioi 1, ‖f u‖ ≤ C * Real.exp (-p * u ^ (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := isBigO_principal.mp (h.isBigO_principal_Ici_of_continuousOn hf
    (by fun_prop) fun u _ ↦ (Real.exp_pos _).ne')
  refine ⟨max C 0, le_max_right _ _, fun u hu ↦ ?_⟩
  have hCu := hC u (mem_Ici.mpr (le_of_lt hu))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hCu
  rw [Real.rpow_one]
  exact hCu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/-- A logarithmic-exponential bound transfers to arguments `t` with `‖t‖ ≤ 1 + ‖s‖`, at the
cost of the factor `21` in the constant. -/
theorem norm_le_exp_mul_log_of_norm_le_one_add {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ t, ‖F t‖ ≤ Real.exp (C * (1 + ‖t‖) * Real.log (2 + ‖t‖))) {s t : ℂ}
    (ht : ‖t‖ ≤ 1 + ‖s‖) :
    ‖F t‖ ≤ Real.exp (21 * C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  have hscale := add_one_mul_log_add_two_le (norm_nonneg s) (norm_nonneg t) zero_le_one
    (by linarith)
  norm_num at hscale
  refine (hF t).trans (Real.exp_le_exp.mpr ?_)
  have := mul_le_mul_of_nonneg_left hscale hC
  linarith

end TauCeti

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

/-- The entire completed even Hurwitz zeta function has vertical-strip growth. The proof bounds it
on each closed strip. -/
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

/-- The entire completed odd Hurwitz zeta function has vertical-strip growth. The proof bounds it
on each closed strip. -/
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
  set K := ∑ j, (CE j + CO j)
  set S := ∑ j, ‖Φ j‖
  set L := Real.log N
  have hL : 0 ≤ L := Real.log_natCast_nonneg N
  have hpos : ∀ j ∈ Finset.univ, 0 ≤ CE j + CO j := fun j _ ↦ (add_pos (hCE j) (hCO j)).le
  have hK : 0 ≤ K := Finset.sum_nonneg hpos
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  have hEK : ∀ j, CE j ≤ K := fun j ↦ (le_add_of_nonneg_right (hCO j).le).trans
    (Finset.single_le_sum hpos (Finset.mem_univ j))
  have hOK : ∀ j, CO j ≤ K := fun j ↦ (le_add_of_nonneg_left (hCE j).le).trans
    (Finset.single_le_sum hpos (Finset.mem_univ j))
  refine ⟨2 * L + K + 4 * S + 1, by positivity, fun s ↦ ?_⟩
  have hlog := Real.one_half_le_log_two_add (norm_nonneg s)
  have hW : ‖s‖ ≤ 2 * ((1 + ‖s‖) * Real.log (2 + ‖s‖)) := by nlinarith [norm_nonneg s]
  have hscale : ∀ {A B : ℝ}, A ≤ B →
      A * (1 + ‖s‖) * Real.log (2 + ‖s‖) ≤ B * (1 + ‖s‖) * Real.log (2 + ‖s‖) :=
    fun hAB ↦ mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAB (by positivity))
      (by linarith)
  have hpow : ‖(N : ℂ) ^ (-s)‖ ≤ Real.exp (2 * L * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    rw [show -s = ((-1 : ℝ) : ℂ) * s by push_cast; ring, natCast_cpow_ofReal_mul (NeZero.ne N)]
    refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, neg_one_mul, abs_neg, abs_of_nonneg hL]
    nlinarith [mul_le_mul_of_nonneg_left hW hL]
  have hsum : ∀ (F : ZMod N → ℂ → ℂ) (c : ZMod N → ℝ), (∀ j, c j ≤ K) →
      (∀ j, ‖F j s‖ ≤ Real.exp (c j * (1 + ‖s‖) * Real.log (2 + ‖s‖))) →
      ‖∑ j, Φ j * F j s‖ ≤ S * Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    intro F c hcK hF
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ ↦ ?_).trans_eq
      (Finset.sum_mul _ _ _).symm)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((hF j).trans (Real.exp_le_exp.mpr (hscale (hcK j))))
      (norm_nonneg _)
  have hsE := hsum (fun j ↦ completedHurwitzZetaEven₀ (toAddCircle j)) CE hEK (hE · s)
  have hsO := hsum (fun j ↦ completedHurwitzZetaOdd (toAddCircle j)) CO hOK (hO · s)
  calc
    ‖completedLFunction₀ Φ s‖ ≤
        ‖(N : ℂ) ^ (-s)‖ * ‖∑ j, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s‖ +
          ‖(N : ℂ) ^ (-s)‖ * ‖∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s‖ := by
      rw [completedLFunction₀, ← norm_mul, ← norm_mul]
      exact norm_add_le _ _
    _ ≤ Real.exp (2 * L * (1 + ‖s‖) * Real.log (2 + ‖s‖)) *
          (S * Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖))) +
        Real.exp (2 * L * (1 + ‖s‖) * Real.log (2 + ‖s‖)) *
          (S * Real.exp (K * (1 + ‖s‖) * Real.log (2 + ‖s‖))) := by gcongr
    _ = 2 * S * Real.exp ((2 * L + K) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
      rw [add_mul, add_mul, Real.exp_add]
      ring
    _ ≤ Real.exp ((2 * L + K + 2 * (2 * S)) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) :=
      Real.mul_exp_mul_one_add_mul_log_two_add_le (by positivity) (norm_nonneg s)
    _ ≤ _ := Real.exp_le_exp.mpr (hscale (by linarith))

/-- The entire completed L-function of a function on `ZMod N` has order at most one. -/
theorem orderLE_completedLFunction₀ (Φ : ZMod N → ℂ) : OrderLE (completedLFunction₀ Φ) 1 := by
  obtain ⟨C, -, hC⟩ := exists_norm_completedLFunction₀_le_exp_mul_log Φ
  exact orderLE_one_of_norm_le_exp_mul_log hC

/-- The entire completed L-function of a function on `ZMod N` has vertical-strip growth. -/
theorem hasVerticalStripGrowth_completedLFunction₀ (Φ : ZMod N → ℂ) :
    HasVerticalStripGrowth (completedLFunction₀ Φ) := by
  have hpow : HasVerticalStripGrowth fun s : ℂ ↦ (N : ℂ) ^ (-s) := by
    refine (hasVerticalStripGrowth_congr fun s ↦ ?_).mpr
      (hasVerticalStripGrowth_cexp_ofReal_mul (r := -1 * Real.log N))
    rw [show -s = ((-1 : ℝ) : ℂ) * s by push_cast; ring, natCast_cpow_ofReal_mul (NeZero.ne N)]
  have h := (hpow.mul (HasVerticalStripGrowth.sum (t := Finset.univ) fun j _ ↦
      (hasVerticalStripGrowth_completedHurwitzZetaEven₀ (toAddCircle j)).const_mul (Φ j))).add
    (hpow.mul (HasVerticalStripGrowth.sum (t := Finset.univ) fun j _ ↦
      (hasVerticalStripGrowth_completedHurwitzZetaOdd (toAddCircle j)).const_mul (Φ j)))
  exact h

end ZMod
