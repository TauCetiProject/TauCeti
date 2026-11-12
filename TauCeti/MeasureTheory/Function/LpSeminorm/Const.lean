/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# A constant bounded almost everywhere by a function in `Lᵖ`

If a real number `t` satisfies `t ≤ ‖u y‖ + A` for almost every `y` in a set `s` of positive
finite measure, then taking `Lᵖ(s)` seminorms of both sides gives
`t ≤ μ(s)^{-1/p} ‖u‖_{Lᵖ(s)} + A` (`TauCeti.le_toReal_eLpNorm_div_add_of_ae_le`). This is the
averaging step that turns a pointwise oscillation bound into a sup bound.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F] {p : ℝ≥0∞}

/-- **A constant bounded by `‖u‖ + A` almost everywhere.** Let `1 ≤ p`, let `s` have positive
finite measure and let `u ∈ Lᵖ(s)`. If `t ≤ ‖u y‖ + A` for almost every `y ∈ s`, with `0 ≤ A`, then
`t ≤ ‖u‖_{Lᵖ(s)} / μ(s)^{1/p} + A`. -/
theorem le_toReal_eLpNorm_div_add_of_ae_le (hp : 1 ≤ p) {s : Set X} (h0 : μ s ≠ 0)
    (htop : μ s ≠ ∞) {u : X → F} (hu : MemLp u p (μ.restrict s)) {t A : ℝ} (hA : 0 ≤ A)
    (h : ∀ᵐ y ∂μ.restrict s, t ≤ ‖u y‖ + A) :
    t ≤ (eLpNorm u p (μ.restrict s)).toReal / (μ s).toReal ^ (1 / p.toReal) + A := by
  have hV : 0 < (μ s).toReal ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (ENNReal.toReal_pos h0 htop) _
  rcases lt_or_ge t 0 with ht | ht
  · linarith [div_nonneg ENNReal.toReal_nonneg hV.le (a := (eLpNorm u p (μ.restrict s)).toReal)]
  have hμ : μ.restrict s ≠ 0 := by
    rwa [Ne, Measure.restrict_eq_zero]
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hle : eLpNorm (fun _ : X => t) p (μ.restrict s) ≤
      eLpNorm u p (μ.restrict s) + eLpNorm (fun _ : X => A) p (μ.restrict s) :=
    calc _ ≤ eLpNorm (fun y => ‖u y‖ + A) p (μ.restrict s) :=
          eLpNorm_mono_ae_real aestronglyMeasurable_const
            (h.mono fun y hy => by rwa [Real.norm_of_nonneg ht])
      _ ≤ eLpNorm (fun y => ‖u y‖) p (μ.restrict s) +
          eLpNorm (fun _ : X => A) p (μ.restrict s) :=
          eLpNorm_add_le hp
      _ = _ := by rw [eLpNorm_norm _ hu.aestronglyMeasurable]
  rw [eLpNorm_const _ hp0 hμ, eLpNorm_const _ hp0 hμ, Measure.restrict_apply_univ] at hle
  have hsfin : μ s ^ (1 / p.toReal) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) htop
  have hfin := ENNReal.mul_ne_top (enorm_ne_top (x := A)) hsfin
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hu.eLpNorm_ne_top, hfin⟩) hle
  simp only [ENNReal.toReal_add hu.eLpNorm_ne_top hfin, ENNReal.toReal_mul, toReal_enorm,
    Real.norm_of_nonneg ht, Real.norm_of_nonneg hA, ← ENNReal.toReal_rpow] at hreal
  have key : t - A ≤ (eLpNorm u p (μ.restrict s)).toReal / (μ s).toReal ^ (1 / p.toReal) := by
    rw [le_div_iff₀ hV]
    linarith
  linarith

end TauCeti
