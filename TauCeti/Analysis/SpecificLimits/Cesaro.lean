/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Cesàro averages along residue classes

Splitting a partial sum over `Finset.range (q * k)` by residue classes modulo `q` expresses the
Cesàro average of a sequence in a real seminormed vector space as the uniform average of the
Cesàro averages along each residue class `m ↦ g (q * m + r)`, plus a boundary remainder of fewer
than `q` terms. Because convergence of a Cesàro average already forces the individual terms to be
`o(n)` (`TauCeti.tendsto_inv_smul_zero_of_tendsto_cesaro`), that boundary remainder vanishes
asymptotically with no boundedness assumption on the sequence.

## Main results

* `TauCeti.sum_range_mul_eq_sum_fin`: decomposition of a sum over `Finset.range (q * k)` into the
  `q` residue classes modulo `q`.
* `TauCeti.tendsto_inv_smul_zero_of_tendsto_cesaro`: if the Cesàro averages of `a : ℕ → E`
  converge, then `(n + 1)⁻¹ • a n → 0`.
* `TauCeti.tendsto_cesaro_of_mod_classes`: if the Cesàro averages of `g : ℕ → E` converge along
  every residue class modulo `q > 0` to `L r`, then the full Cesàro averages converge to
  `q⁻¹ • ∑ r, L r`.
-/

public section

open Filter Topology

namespace TauCeti

/-- Splitting a sum over `Finset.range (q * k)` by residue classes modulo `q`. -/
theorem sum_range_mul_eq_sum_fin {M : Type*} [AddCommMonoid M] (g : ℕ → M) (q k : ℕ) :
    ∑ i ∈ Finset.range (q * k), g i = ∑ r : Fin q, ∑ m ∈ Finset.range k, g (q * m + r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib, ← Fin.sum_univ_eq_sum_range]

/-- The quotient `⌊(n + 1) / q⌋ / (n + 1)` tends to `q⁻¹` as `n → ∞` for `0 < q`. -/
private theorem tendsto_div_nat_div {q : ℕ} (hq : 0 < q) :
    Tendsto (fun n : ℕ ↦ (((n + 1) / q : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (q : ℝ)⁻¹) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.2 hq
  have hlow : Tendsto (fun n : ℕ ↦ (q : ℝ)⁻¹ - 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (q : ℝ)⁻¹) := by
    simpa only [sub_zero, Function.comp_def] using
      (tendsto_const_nhds (x := (q : ℝ)⁻¹)).sub
        ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n ↦ ?_) (fun n ↦ ?_)
  · have hpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hlt : (n + 1 : ℕ) < q * ((n + 1) / q + 1) := by
      rw [Nat.mul_add, mul_one]
      have := Nat.div_add_mod (n + 1) q
      have := Nat.mod_lt (n + 1) hq
      omega
    have hltR : ((n + 1 : ℕ) : ℝ) < (q : ℝ) * (((n + 1) / q : ℕ) + 1) := by exact_mod_cast hlt
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hpos, inv_mul_le_iff₀ hqR]
    linarith
  · have hpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hleR : (q : ℝ) * (((n + 1) / q : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_div_le (n + 1) q
    rw [div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ hqR]
    linarith

section Cesaro

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- If the Cesàro averages of `a : ℕ → E` converge, then `(n + 1)⁻¹ • a n → 0`. -/
theorem tendsto_inv_smul_zero_of_tendsto_cesaro {a : ℕ → E} {l : E}
    (ha : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (n + 1), a i)
      atTop (𝓝 l)) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • a n) atTop (𝓝 0) := by
  have hratio : Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hrew (n : ℕ) : (n : ℝ) / ((n + 1 : ℕ) : ℝ) = 1 - ((n + 1 : ℕ) : ℝ)⁻¹ := by
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast; field_simp [hn]; ring
    simp_rw [hrew]
    simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)))
  have hprev := hratio.smul (ha.comp (Filter.tendsto_sub_atTop_nat 1))
  have hdiff := ha.sub hprev
  rw [one_smul, sub_self] at hdiff
  refine hdiff.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hscal : (n : ℝ) / ((n + 1 : ℕ) : ℝ) * (n : ℝ)⁻¹ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
    rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hn0, one_mul]
  simp only [Function.comp_apply, hsub, smul_smul, hscal, ← smul_sub]
  rw [Finset.sum_range_succ, add_sub_cancel_left]

/-- Tail remainder from splitting a Cesàro average into residue classes modulo `q > 0` vanishes
whenever each residue class has convergent Cesàro averages. -/
private theorem tendsto_cesaro_mod_tail {g : ℕ → E} {q : ℕ} (hq : 0 < q) {L : Fin q → E}
    (hL : ∀ r : Fin q, Tendsto (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), g (q * j + r)) atTop (𝓝 (L r))) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
      ∑ i ∈ Finset.range ((n + 1) % q), g (q * ((n + 1) / q) + i)) atTop (𝓝 0) := by
  have hk_top : Tendsto (fun n : ℕ ↦ (n + 1) / q) atTop atTop :=
    Filter.tendsto_atTop.2 fun b ↦ eventually_atTop.2 ⟨q * b, fun n hn ↦
      (Nat.le_div_iff_mul_le hq).2 (mul_comm b q ▸ hn.trans (Nat.le_succ n))⟩
  have hratio : Tendsto (fun n : ℕ ↦ ((((n + 1) / q + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (q : ℝ)⁻¹) := by
    have hrew (n : ℕ) : ((((n + 1) / q + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) =
        (((n + 1) / q : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ)⁻¹ := by
      push_cast; rw [add_div, one_div]
    simp_rw [hrew]
    simpa using (tendsto_div_nat_div hq).add (tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)))
  have hterm (r : Fin q) : Tendsto (fun n : ℕ ↦
      ‖((n + 1 : ℕ) : ℝ)⁻¹ • g (q * ((n + 1) / q) + r)‖) atTop (𝓝 0) := by
    have hsmul := hratio.smul ((tendsto_inv_smul_zero_of_tendsto_cesaro (hL r)).comp hk_top)
    rw [smul_zero] at hsmul
    have hcongr : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • g (q * ((n + 1) / q) + r))
        atTop (𝓝 0) := by
      refine hsmul.congr fun n ↦ ?_
      have hk0 : ((((n + 1) / q + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hscal : ((((n + 1) / q + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
          ((((n + 1) / q + 1 : ℕ) : ℝ))⁻¹ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
        rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hk0, one_mul]
      simp only [Function.comp_apply, smul_smul, hscal]
    simpa using hcongr.norm
  have hsum : Tendsto (fun n : ℕ ↦
      ∑ r : Fin q, ‖((n + 1 : ℕ) : ℝ)⁻¹ • g (q * ((n + 1) / q) + r)‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun r _ ↦ hterm r
  refine squeeze_zero_norm (fun n ↦ ?_) hsum
  rw [Finset.smul_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ ‖((n + 1 : ℕ) : ℝ)⁻¹ • g (q * ((n + 1) / q) + i)‖)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.mod_lt (n + 1) hq).le)
    fun _ _ _ ↦ norm_nonneg _

/-- If the Cesàro averages of `g : ℕ → E` along each residue class `m ↦ g (q * m + r)` modulo
`q > 0` converge to `L r`, then the Cesàro averages of `g` converge to `q⁻¹ • ∑ r, L r`. -/
theorem tendsto_cesaro_of_mod_classes {g : ℕ → E} {q : ℕ} (hq : 0 < q) {L : Fin q → E}
    (hL : ∀ r : Fin q, Tendsto (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), g (q * j + r)) atTop (𝓝 (L r))) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (n + 1), g i)
      atTop (𝓝 ((q : ℝ)⁻¹ • ∑ r : Fin q, L r)) := by
  have hk_top : Tendsto (fun n : ℕ ↦ (n + 1) / q) atTop atTop :=
    Filter.tendsto_atTop.2 fun b ↦ eventually_atTop.2 ⟨q * b, fun n hn ↦
      (Nat.le_div_iff_mul_le hq).2 (mul_comm b q ▸ hn.trans (Nat.le_succ n))⟩
  have hcls (r : Fin q) : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
      ∑ j ∈ Finset.range ((n + 1) / q), g (q * j + r)) atTop (𝓝 ((q : ℝ)⁻¹ • L r)) := by
    have hprod := (tendsto_div_nat_div hq).smul
      ((hL r).comp ((Filter.tendsto_sub_atTop_nat 1).comp hk_top))
    refine hprod.congr' ?_
    filter_upwards [hk_top.eventually_ge_atTop 1] with n hn
    have hsub : (n + 1) / q - 1 + 1 = (n + 1) / q := Nat.sub_add_cancel hn
    have hk0 : (((n + 1) / q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hscal : ((((n + 1) / q : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
        (((n + 1) / q : ℕ) : ℝ)⁻¹ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
      rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hk0, one_mul]
    simp only [Function.comp_apply, hsub, smul_smul, hscal]
  have hmain := tendsto_finsetSum Finset.univ fun r _ ↦ hcls r
  rw [← Finset.smul_sum] at hmain
  have htot := hmain.add (tendsto_cesaro_mod_tail hq hL)
  rw [add_zero] at htot
  refine htot.congr fun n ↦ ?_
  rw [← Finset.smul_sum, ← sum_range_mul_eq_sum_fin, ← smul_add, ← Finset.sum_range_add,
    Nat.div_add_mod]

end Cesaro

end TauCeti
