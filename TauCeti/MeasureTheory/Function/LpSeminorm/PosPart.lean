/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# `Lᵖ` seminorms of positive parts and deviations from a level

The positive part `f⁺` of a real function satisfies `‖f⁺‖ ≤ ‖f‖`, so taking the positive part
preserves `Lᵖ` (`MeasureTheory.MemLp.posPart`), and scales homogeneously under multiplication by a
nonnegative constant (`MeasureTheory.eLpNorm_posPart_const_mul`), which transfers a smallness
assumption on `ρ ‖f⁺‖_p` to the rescaled function `(s⁻¹ f)⁺`
(`TauCeti.ofReal_mul_eLpNorm_posPart_inv_mul_le`).

The deviation `f - m` of a real function from a level `m` is the difference of its parts
`(f - m)⁺` above and `(m - f)⁺` below the level. For `q ≥ 1` the triangle inequality bounds its
`L^q` seminorm by the sum of theirs. Level-set arguments estimate the two parts separately, for
instance around a median `m`, where each of them vanishes on a set of at least half the measure.

## Main declarations

* `MeasureTheory.MemLp.posPart`: `f ∈ Lᵖ(μ)` implies `f⁺ ∈ Lᵖ(μ)`.
* `MeasureTheory.eLpNorm_posPart_const_mul`: `‖(c f)⁺‖_p = c ‖f⁺‖_p` for `c ≥ 0`.
* `TauCeti.ofReal_mul_eLpNorm_posPart_inv_mul_le`: if `‖f⁺‖_p ≤ F` and `ρ F ≤ b s` with `ρ ≥ 0`
  and `s > 0`, then `ρ ‖(s⁻¹ f)⁺‖_p ≤ b`.
* `TauCeti.eLpNorm_sub_const_le_add`: `‖f - m‖_q ≤ ‖(f - m)⁺‖_q + ‖(m - f)⁺‖_q` for `q ≥ 1`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

/-- The positive part of a function in `Lᵖ` lies in `Lᵖ`. -/
theorem MemLp.posPart {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} {f : α → ℝ}
    (hf : MemLp f p μ) : MemLp (fun x => (f x)⁺) p μ :=
  hf.mono (continuous_posPart.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (posPart_nonneg _), Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _))

/-- Scaling a real function by a nonnegative constant scales the `Lᵖ` seminorm of its positive part
by the same constant. -/
theorem eLpNorm_posPart_const_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {c : ℝ} (hc : 0 ≤ c) (f : α → ℝ) :
    eLpNorm (fun x => (c * f x)⁺) p μ = ENNReal.ofReal c * eLpNorm (fun x => (f x)⁺) p μ := by
  have h : (fun x => (c * f x)⁺) = c • fun x => (f x)⁺ := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, posPart_def, mul_max_of_nonneg _ _ hc, mul_zero]
  rw [h, eLpNorm_const_smul, Real.eNorm_eq_ofReal hc]

end MeasureTheory

namespace TauCeti

/-- **Smallness of the rescaled positive part.** If `‖f⁺‖_{Lᵖ} ≤ F` and `ρ F ≤ b s` with `ρ ≥ 0`
and `s > 0`, then `ρ ‖(s⁻¹ f)⁺‖_{Lᵖ} ≤ b`. -/
theorem ofReal_mul_eLpNorm_posPart_inv_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {f : α → ℝ} {ρ s F b : ℝ} (hρ : 0 ≤ ρ) (hs : 0 < s)
    (hf : eLpNorm (fun x => (f x)⁺) p μ ≤ ENNReal.ofReal F) (hsF : ρ * F ≤ b * s) :
    ENNReal.ofReal ρ * eLpNorm (fun x => (s⁻¹ * f x)⁺) p μ ≤ ENNReal.ofReal b := by
  rw [eLpNorm_posPart_const_mul (inv_nonneg.2 hs.le)]
  calc ENNReal.ofReal ρ * (ENNReal.ofReal s⁻¹ * eLpNorm (fun x => (f x)⁺) p μ)
      ≤ ENNReal.ofReal ρ * (ENNReal.ofReal s⁻¹ * ENNReal.ofReal F) := by gcongr
    _ = ENNReal.ofReal (ρ * (s⁻¹ * F)) := by
      rw [ENNReal.ofReal_mul hρ, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal b := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← div_eq_inv_mul, mul_div_assoc', div_le_iff₀ hs]
      exact hsF

/-- The deviation of `f` from a level `m` is the difference of `(f - m)⁺` and `(m - f)⁺`, so its
`L^q` seminorm is at most the sum of theirs for `q ≥ 1`. -/
theorem eLpNorm_sub_const_le_add {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (m : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (fun x => f x - m) q ν ≤
      eLpNorm (fun x => max (f x - m) 0) q ν + eLpNorm (fun x => max (m - f x) 0) q ν := by
  have heq : (fun x => f x - m) =
      (fun x => max (f x - m) 0) - fun x => max (m - f x) 0 := by
    funext x
    simp only [Pi.sub_apply]
    rcases le_total (f x) m with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), sub_zero]
  rw [heq]
  exact eLpNorm_sub_le hq

end TauCeti
