/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic
import TauCeti.Data.Real.NegNatSeparation
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# The Gamma function on vertical strips

For real `u`, `v` and `η > 0` there are `C > 0` and `K : ℕ` with

`‖Γ(x + i y)‖ ≤ C (1 + |y|) ^ K exp (-π |y| / 2)`

whenever `u ≤ x ≤ v` and `x + i y` keeps the distance `η` from every pole `-n` of `Γ`. For large
`|y|` this is Stirling's formula on vertical strips ([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9),
`exists_abs_log_norm_Gamma_vertical_sub_le`) after exponentiation: the factor
`|y| ^ (x - 1/2)` is at most `(1 + |y|) ^ K` once `K ≥ v - 1/2`, and the bounded remainder goes
into `C`. On the remaining bounded part of the strip the separation from the poles makes the set
of admissible points compact, and `Γ` is continuous on it.

The separation hypothesis holds automatically on a closed strip in the right half-plane, at
heights `|y| ≥ 1`, and on a vertical line through a point that is not a pole. On such a line,
`Γ(x + i y) exp (θ |y|)` is integrable for every `θ < π / 2`.

## Main results

* `TauCeti.exists_norm_Gamma_le`: the bound on a strip, away from the poles.
* `TauCeti.exists_norm_Gamma_le_of_pos`: the bound at all heights on a strip `0 < u ≤ x ≤ v`.
* `TauCeti.exists_norm_Gamma_le_of_one_le_abs`: the bound at heights `|y| ≥ 1` on any strip.
* `TauCeti.exists_norm_Gamma_le_of_forall_ne_neg_natCast`: the bound at all heights on a vertical
  line `Re z = x` with `x` not a nonpositive integer.
* `TauCeti.verticalIntegrable_Gamma_mul_exp_mul_abs_im`: `Γ(z) exp (θ |Im z|)` is integrable on
  every such line, for `θ < π / 2`.

The proofs are new. The statements follow the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/Gamma/VerticalStrips.lean`, whose proofs
go through the product formula for `|Γ|` instead of Stirling's formula.
-/

public section

open Real Set Filter MeasureTheory

namespace TauCeti

open Complex

/-- At large heights Stirling's formula gives the bound on the whole strip, poles or not. -/
private theorem exists_norm_Gamma_le_of_le_abs (u v : ℝ) :
    ∃ C > 0, ∃ K : ℕ, ∃ T : ℝ, ∀ x y : ℝ, u ≤ x → x ≤ v → T ≤ |y| →
      ‖Gamma (x + y * I)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le u v
  set K := ⌈v - 1 / 2⌉₊
  refine ⟨Real.exp (|C| + Real.log (2 * π) / 2), Real.exp_pos _, K, max T 1,
    fun x y hux hxv hy ↦ ?_⟩
  have h1 : 1 ≤ |y| := le_of_max_le_right hy
  have hs := h (x + y * I) (by simpa using And.intro hux hxv)
    (by simpa using le_of_max_le_left hy)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_im, mul_im, zero_add, add_zero] at hs
  rcases (norm_nonneg (Gamma (x + y * I))).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  have hlog : (x - 1 / 2) * Real.log |y| ≤ K * Real.log (1 + |y|) :=
    calc (x - 1 / 2) * Real.log |y| ≤ K * Real.log |y| :=
          mul_le_mul_of_nonneg_right (by linarith [Nat.le_ceil (v - 1 / 2)]) (Real.log_nonneg h1)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith))
          (Nat.cast_nonneg _)
  have hC : C / |y| ≤ |C| :=
    (div_le_div_of_nonneg_right (le_abs_self C) (by linarith)).trans
      (div_le_self (abs_nonneg C) h1)
  calc ‖Gamma (x + y * I)‖ = Real.exp (Real.log ‖Gamma (x + y * I)‖) :=
        (Real.exp_log hpos).symm
    _ ≤ Real.exp (|C| + Real.log (2 * π) / 2 + Real.log ((1 + |y|) ^ K) + -(π * |y|) / 2) := by
        rw [Real.log_pow]
        exact Real.exp_le_exp.2 (by linarith [(abs_le.1 hs).2])
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity)]

/-- On a bounded part of the strip, away from the poles, `Γ` is bounded: the admissible points
form a compact set on which `Γ` is continuous. -/
private theorem exists_norm_Gamma_le_of_abs_le {u v η : ℝ} (hη : 0 < η) (T : ℝ) :
    ∃ M, ∀ x y : ℝ, u ≤ x → x ≤ v → |y| ≤ T → (∀ n : ℕ, η ≤ ‖(x : ℂ) + y * I + n‖) →
      ‖Gamma (x + y * I)‖ ≤ M := by
  set S : Set (ℝ × ℝ) :=
    (Icc u v ×ˢ Icc (-T) T) ∩ ⋂ n : ℕ, {p | η ≤ ‖(p.1 : ℂ) + p.2 * I + n‖}
  have hS : IsCompact S :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_iInter fun n ↦ isClosed_le continuous_const (by fun_prop))
  have hc : ContinuousOn (fun p : ℝ × ℝ ↦ Gamma (p.1 + p.2 * I)) S := by
    refine fun p hp ↦ ContinuousAt.continuousWithinAt ?_
    refine (differentiableAt_Gamma _ fun m hm ↦ ?_).continuousAt.comp (by fun_prop)
    have := mem_iInter.1 hp.2 m
    simp only [mem_ofPred_eq, hm, neg_add_cancel, norm_zero] at this
    linarith
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc
  exact ⟨M, fun x y hux hxv hy hsep ↦
    hM (x, y) ⟨⟨⟨hux, hxv⟩, abs_le.1 hy⟩, mem_iInter.2 hsep⟩⟩

/-- **The Gamma function on vertical strips.** For real `u`, `v` and `η > 0` there are `C > 0`
and `K : ℕ` such that `‖Γ(x + i y)‖ ≤ C (1 + |y|) ^ K exp (-π |y| / 2)` whenever `u ≤ x ≤ v`
and `‖x + i y + n‖ ≥ η` for every `n : ℕ`. -/
theorem exists_norm_Gamma_le {u v η : ℝ} (hη : 0 < η) :
    ∃ C > 0, ∃ K : ℕ, ∀ x y : ℝ, u ≤ x → x ≤ v → (∀ n : ℕ, η ≤ ‖(x : ℂ) + y * I + n‖) →
      ‖Gamma (x + y * I)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  obtain ⟨C, hC, K, T, hlarge⟩ := exists_norm_Gamma_le_of_le_abs u v
  obtain ⟨M, hsmall⟩ := exists_norm_Gamma_le_of_abs_le (u := u) (v := v) hη T
  refine ⟨C + |M| * Real.exp (π * T / 2), by positivity, K, fun x y hux hxv hsep ↦ ?_⟩
  have hB : 0 ≤ (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by positivity
  rcases le_total T |y| with hy | hy
  · calc ‖Gamma (x + y * I)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) :=
          hlarge x y hux hxv hy
      _ ≤ _ := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hB
  · have hone : 1 ≤ (1 + |y|) ^ K * (Real.exp (π * T / 2) * Real.exp (-(π * |y|) / 2)) := by
      rw [← Real.exp_add]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [abs_nonneg y]))
        (Real.one_le_exp (by nlinarith [pi_pos]))
    calc ‖Gamma (x + y * I)‖ ≤ |M| := (hsmall x y hux hxv hy hsep).trans (le_abs_self M)
      _ ≤ |M| * ((1 + |y|) ^ K * (Real.exp (π * T / 2) * Real.exp (-(π * |y|) / 2))) :=
          le_mul_of_one_le_right (abs_nonneg M) hone
      _ = |M| * Real.exp (π * T / 2) * ((1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) := by ring
      _ ≤ _ := by
          rw [mul_assoc (C + _)]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) hB

/-- On a closed strip `0 < u ≤ x ≤ v` in the right half-plane the bound of
`TauCeti.exists_norm_Gamma_le` holds at all heights. -/
theorem exists_norm_Gamma_le_of_pos {u v : ℝ} (hu : 0 < u) :
    ∃ C > 0, ∃ K : ℕ, ∀ x y : ℝ, u ≤ x → x ≤ v →
      ‖Gamma (x + y * I)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  obtain ⟨C, hC, K, h⟩ := exists_norm_Gamma_le (u := u) (v := v) hu
  refine ⟨C, hC, K, fun x y hux hxv ↦ h x y hux hxv fun n ↦ ?_⟩
  refine le_trans ?_ (abs_re_le_norm _)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero, natCast_re]
  exact le_abs.2 (Or.inl (by linarith [n.cast_nonneg (α := ℝ)]))

/-- At heights `|y| ≥ 1` the bound of `TauCeti.exists_norm_Gamma_le` holds on every bounded
strip `u ≤ x ≤ v`. -/
theorem exists_norm_Gamma_le_of_one_le_abs {u v : ℝ} :
    ∃ C > 0, ∃ K : ℕ, ∀ x y : ℝ, u ≤ x → x ≤ v → 1 ≤ |y| →
      ‖Gamma (x + y * I)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  obtain ⟨C, hC, K, h⟩ := exists_norm_Gamma_le (u := u) (v := v) one_pos
  refine ⟨C, hC, K, fun x y hux hxv hy ↦ h x y hux hxv fun n ↦ hy.trans ?_⟩
  simpa using abs_im_le_norm ((x : ℂ) + y * I + n)

/-- On a vertical line `Re z = x` with `x` not a nonpositive integer the bound of
`TauCeti.exists_norm_Gamma_le` holds at all heights. -/
theorem exists_norm_Gamma_le_of_forall_ne_neg_natCast {x : ℝ} (hx : ∀ n : ℕ, x ≠ -n) :
    ∃ C > 0, ∃ K : ℕ, ∀ y : ℝ,
      ‖Gamma (x + y * I)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  obtain ⟨η, hη, hsep⟩ := Real.exists_pos_forall_le_abs_add_natCast hx
  obtain ⟨C, hC, K, h⟩ := exists_norm_Gamma_le (u := x) (v := x) hη
  refine ⟨C, hC, K, fun y ↦ h x y le_rfl le_rfl fun n ↦ (hsep n).trans ?_⟩
  simpa using abs_re_le_norm ((x : ℂ) + y * I + n)

/-- On a vertical line `Re z = x` with `x` not a nonpositive integer, `Γ(z) exp (θ |Im z|)` is
integrable for every `θ < π / 2`. -/
theorem verticalIntegrable_Gamma_mul_exp_mul_abs_im {x θ : ℝ} (hx : ∀ n : ℕ, x ≠ -n)
    (hθ : θ < π / 2) :
    VerticalIntegrable (fun z ↦ Gamma z * (Real.exp (θ * |z.im|) : ℂ)) x := by
  obtain ⟨C, hC, K, h⟩ := exists_norm_Gamma_le_of_forall_ne_neg_natCast hx
  set c := (π / 2 - θ) / 2
  have hc : 0 < c := by simp only [c]; linarith
  obtain ⟨M, -, hM⟩ := exists_rpow_mul_exp_neg_mul_le (Nat.cast_nonneg K) hc
  refine ((integrable_exp_neg_mul_abs hc).const_mul (C * M * Real.exp c)).mono'
    ((verticalIntegrable_Gamma hx).aestronglyMeasurable.mul (by fun_prop))
    (Eventually.of_forall fun y ↦ ?_)
  have hM' := hM (1 + |y|) (by positivity)
  rw [Real.rpow_natCast] at hM'
  have hsplit : Real.exp (-(π * |y|) / 2) * Real.exp (θ * |y|) =
      Real.exp (-(c * (1 + |y|))) * Real.exp c * Real.exp (-(c * |y|)) := by
    simp only [← Real.exp_add, c]
    ring_nf
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add, norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp]
  calc ‖Gamma (x + y * I)‖ * Real.exp (θ * |y|)
      ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) * Real.exp (θ * |y|) :=
        mul_le_mul_of_nonneg_right (h y) (Real.exp_pos _).le
    _ = C * ((1 + |y|) ^ K * Real.exp (-(c * (1 + |y|)))) * Real.exp c *
          Real.exp (-(c * |y|)) := by
        rw [mul_assoc, hsplit]
        ring
    _ ≤ C * M * Real.exp c * Real.exp (-(c * |y|)) := by gcongr

end TauCeti
