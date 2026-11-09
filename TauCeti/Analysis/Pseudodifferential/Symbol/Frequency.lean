/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Examples of frequency-only symbols

A smooth coefficient `b(ξ)` with `‖D^k b(ξ)‖ ≤ C_k ⟨ξ⟩ ^ (m - k)` is a symbol of order `m`
(`TauCeti.Symbol.ofFrequency`). This file constructs two such symbols on `ℝⁿ`:

* `TauCeti.Symbol.besselPotential`: the Bessel weight `(1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular
  frequency `ξ`, a uniform symbol of order `s`;
* `TauCeti.Symbol.ofInner`: the linear coefficient `⟪ξ, v⟫`, a uniform symbol of order `1`. For
  `v ≠ 0` and a nontrivial fibre it has no smaller order
  (`TauCeti.Symbol.not_exists_coefficient_eq_ofInner_coefficient`).

Their quantizations, Mathlib's Bessel potential and the derivative `-i ∂_v`, are identified in
`TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (1.4).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped RealInnerProductSpace ContDiff
open Real

noncomputable section

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {m : ℝ}

/-- The Bessel weight `(1 + ‖ξ / 2π‖²) ^ (s / 2)` satisfies the symbol estimates of order `s`. -/
private theorem exists_norm_iteratedFDeriv_besselWeight_le (s : ℝ) (k : ℕ) :
    ∃ C, ∀ ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (fun ξ : CoordinateSpace n ↦ (1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2)) ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((s - k) / 2) := by
  rw [sub_div]
  exact exists_norm_iteratedFDeriv_one_add_norm_smul_sq_rpow_le (by positivity) (s / 2) k

/-- The Bessel weight `⟨ξ / 2π⟩ ^ s = (1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency, a
uniform symbol of order `s` (`TauCeti.Symbol.isUniform_besselPotential`). Its quantization is
Mathlib's Fourier multiplier `(1 + ‖ζ‖²) ^ (s / 2)` in the frequency `ζ = ξ / 2π`
(`TauCeti.Symbol.quantizeSchwartzValue_besselPotential`), which as a tempered distribution is
Mathlib's Bessel potential `TemperedDistribution.besselPotential`
(`TauCeti.toTemperedDistribution_quantizeFrequencyCLM_besselPotential`). -/
def besselPotential (s : ℝ) : Symbol n V V s :=
  ofFrequency (fun ξ ↦ (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V)
    ((Complex.ofRealCLM.contDiff.comp
      (Function.hasTemperateGrowth_one_add_norm_smul_sq_rpow _ _).1).smul contDiff_const)
    fun k ↦ by
      simpa only [ContinuousLinearMap.smulRight_apply, Complex.ofRealCLM_apply] using
        ContinuousLinearMap.exists_norm_iteratedFDeriv_comp_left_le_one_add_norm_sq_rpow
          (Complex.ofRealCLM.smulRight (ContinuousLinearMap.id ℂ V))
          ((Function.hasTemperateGrowth_one_add_norm_smul_sq_rpow _ _).1.of_le (mod_cast le_top))
          (exists_norm_iteratedFDeriv_besselWeight_le s k)

@[simp]
theorem coefficient_besselPotential (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n) :
    (besselPotential s : Symbol n V V s).coefficient p =
      (((1 + ‖(2 * π)⁻¹ • p.2‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V :=
  coefficient_ofFrequency _ _ p

theorem isUniform_besselPotential (s : ℝ) : (besselPotential s : Symbol n V V s).IsUniform :=
  isUniform_ofFrequency _ _


/-- The linear function `⟪ξ, v⟫` satisfies the symbol estimates of order `1`. -/
private theorem exists_norm_iteratedFDeriv_inner_le (v : CoordinateSpace n) (k : ℕ) :
    ∃ C, ∀ ξ : CoordinateSpace n, ‖iteratedFDeriv ℝ k (fun ξ : CoordinateSpace n ↦ ⟪ξ, v⟫) ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (((1 : ℝ) - k) / 2) := by
  have h : (fun ξ : CoordinateSpace n ↦ ⟪ξ, v⟫) = innerSL ℝ v := by
    funext ξ
    rw [innerSL_apply_apply, real_inner_comm]
  rw [h]
  exact ⟨_, (innerSL ℝ v).norm_iteratedFDeriv_le_one_add_norm_sq_rpow k⟩

/-- The coefficient `⟪ξ, v⟫` of `D_v = -i ∂_v` (`TauCeti.Symbol.quantizeSchwartzValue_ofInner`),
a uniform symbol of order `1` (`TauCeti.Symbol.isUniform_ofInner`). For `v ≠ 0` and a nontrivial
fibre `V` it is not a symbol of any order `m < 1`
(`TauCeti.Symbol.not_exists_coefficient_eq_ofInner_coefficient`). -/
def ofInner (v : CoordinateSpace n) : Symbol n V V 1 :=
  ofFrequency (fun ξ ↦ ((⟪ξ, v⟫ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V)
    ((Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)).smul contDiff_const)
    fun k ↦ by
      simpa only [ContinuousLinearMap.smulRight_apply, Complex.ofRealCLM_apply] using
        ContinuousLinearMap.exists_norm_iteratedFDeriv_comp_left_le_one_add_norm_sq_rpow
          (Complex.ofRealCLM.smulRight (ContinuousLinearMap.id ℂ V)) (g := fun ξ ↦ ⟪ξ, v⟫)
          ((contDiff_id.inner ℝ contDiff_const).of_le (mod_cast le_top))
          (exists_norm_iteratedFDeriv_inner_le v k)

@[simp]
theorem coefficient_ofInner (v : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    (ofInner v : Symbol n V V 1).coefficient p =
      ((⟪p.2, v⟫ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V :=
  coefficient_ofFrequency _ _ p

theorem isUniform_ofInner (v : CoordinateSpace n) : (ofInner v : Symbol n V V 1).IsUniform :=
  isUniform_ofFrequency _ _

/-- `⟪ξ, v⟫` has no order below `1`: for `v ≠ 0`, a nonzero fibre and `m < 1`, no symbol of
order `m` has this coefficient, since along the ray `ξ = t v` it grows like `t`, faster than
`⟨ξ⟩ ^ m`. -/
theorem not_exists_coefficient_eq_ofInner_coefficient [Nontrivial V] {v : CoordinateSpace n}
    (hv : v ≠ 0) (hm : m < 1) :
    ¬∃ a : Symbol n V V m, a.coefficient = (ofInner v : Symbol n V V 1).coefficient := by
  rintro ⟨a, ha⟩
  obtain ⟨C, -, hC⟩ := a.exists_bound {0} isCompact_singleton [] []
  set m₀ := max m 0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hp : 0 < 1 - m₀ := sub_pos.2 (max_lt hm one_pos)
  -- Choose `S ≥ 2` with `S ^ (1 - m₀) > 2 |C| / ‖v‖`; test the bound at `ξ = (S / 2) v / ‖v‖`.
  obtain ⟨S, hS, hS2⟩ := (((tendsto_rpow_atTop hp).eventually_gt_atTop (2 * |C| / ‖v‖)).and
    (Filter.eventually_ge_atTop 2)).exists
  have hS0 : 0 < S := by linarith
  set ξ : CoordinateSpace n := (S / (2 * ‖v‖)) • v
  have hξ : ‖ξ‖ = S / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hinner : ⟪ξ, v⟫ = S / 2 * ‖v‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have h : S / 2 * ‖v‖ ≤ C * (1 + (S / 2) ^ 2) ^ (m / 2) := by
    simpa [ha, norm_smul, hinner, hξ, abs_of_pos hS0] using hC 0 rfl ξ
  -- The weight is at most `(1 + S / 2) ^ m₀ ≤ S ^ m₀`.
  have hweight : (1 + (S / 2) ^ 2) ^ (m / 2) ≤ S ^ m₀ :=
    calc (1 + (S / 2) ^ 2) ^ (m / 2) ≤ (1 + (S / 2) ^ 2) ^ (m₀ / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by linarith [le_max_left m 0])
      _ ≤ (1 + S / 2) ^ m₀ := by
          simpa [abs_of_nonneg hS0.le] using
            one_add_norm_sq_rpow_half_le_one_add_norm_rpow (S / 2) (le_max_right m 0)
      _ ≤ S ^ m₀ := Real.rpow_le_rpow (by positivity) (by linarith) (le_max_right m 0)
  have hbound : C * (1 + (S / 2) ^ 2) ^ (m / 2) ≤ |C| * S ^ m₀ :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hweight (abs_nonneg C))
  have key : 2 * |C| * S ^ m₀ < S * ‖v‖ :=
    calc 2 * |C| * S ^ m₀ < S ^ (1 - m₀) * ‖v‖ * S ^ m₀ :=
          mul_lt_mul_of_pos_right ((div_lt_iff₀ hvpos).1 hS) (Real.rpow_pos_of_pos hS0 _)
      _ = S * ‖v‖ := by
          rw [mul_right_comm, ← Real.rpow_add hS0, sub_add_cancel, Real.rpow_one]
  linarith


end Symbol

end TauCeti
