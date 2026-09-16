/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic
import TauCeti.MeasureTheory.OuterMeasure.SymmDiff
import TauCeti.Algebra.Order.Ring.Abs
import Mathlib.Algebra.GroupWithZero.Idempotent

/-!
# A zero-one criterion from factoring approximants

Under a finite outer measure, a set admitting arbitrarily close pairs of approximants whose
intersection mass factors has outer measure `0` or `1`. Neither additivity nor measurability
of the sets is required.

This is the approximation step of the Hewitt–Savage zero-one law, also used for the ergodicity
of dissociated exchangeable arrays.

## Main result

* `TauCeti.MeasureTheory.measure_eq_zero_or_one_of_forall_exists_symmDiff_lt_inter_eq_mul`

## References

* Edwin Hewitt and Leonard J. Savage, *Symmetric measures on Cartesian products*, Transactions of
  the American Mathematical Society **80** (1955), 470–501, <https://doi.org/10.2307/1992999>.
* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1.
-/

public section

open MeasureTheory Set
open scoped ENNReal symmDiff

namespace TauCeti.MeasureTheory

/-- Two approximants within `e ≤ 1` of `s` whose intersection mass factors force
`|μ s - (μ s)²| ≤ e (2 μ s + 3)`. -/
private theorem abs_toReal_sub_mul_self_le_of_symmDiff_le
    {Ω F : Type*} [FunLike F (Set Ω) ℝ≥0∞] [OuterMeasureClass F Ω] {μ : F}
    (hμ : μ univ ≠ ∞) {t t' s : Set Ω} {e : ℝ} (he : e ≤ 1) (h1 : (μ (symmDiff t s)).toReal ≤ e)
    (h2 : (μ (symmDiff t' s)).toReal ≤ e)
    (hinter : (μ (t ∩ t')).toReal = (μ t).toReal * (μ t').toReal) :
    |(μ s).toReal - (μ s).toReal * (μ s).toReal| ≤ e * (2 * (μ s).toReal + 3) := by
  have hbt : |(μ t).toReal - (μ s).toReal| ≤ e :=
    (abs_toReal_sub_le_toReal_symmDiff hμ).trans h1
  have hbt' : |(μ t').toReal - (μ s).toReal| ≤ e :=
    (abs_toReal_sub_le_toReal_symmDiff hμ).trans h2
  have he0 : 0 ≤ e := (abs_nonneg _).trans hbt
  have hbi : |(μ (t ∩ t')).toReal - (μ s).toReal| ≤ 2 * e :=
    (abs_toReal_inter_sub_le_toReal_symmDiff_add hμ).trans (by linarith)
  have hprod : |(μ t).toReal * (μ t').toReal - (μ s).toReal * (μ s).toReal| ≤
      e * (2 * (μ s).toReal + e) :=
    TauCeti.abs_mul_sub_mul_self_le hbt hbt' ENNReal.toReal_nonneg
  rw [hinter] at hbi
  have hsplit : (μ s).toReal - (μ s).toReal * (μ s).toReal =
      ((μ s).toReal - (μ t).toReal * (μ t').toReal) +
        ((μ t).toReal * (μ t').toReal - (μ s).toReal * (μ s).toReal) := by ring
  calc |(μ s).toReal - (μ s).toReal * (μ s).toReal|
      ≤ |(μ s).toReal - (μ t).toReal * (μ t').toReal| +
          |(μ t).toReal * (μ t').toReal - (μ s).toReal * (μ s).toReal| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ 2 * e + e * (2 * (μ s).toReal + e) := by rw [abs_sub_comm]; linarith
    _ ≤ e * (2 * (μ s).toReal + 3) := by nlinarith [ENNReal.toReal_nonneg (a := μ s)]

/-- **Arbitrarily close factoring approximants force a zero-one event.** Suppose that for every
`ε > 0`, the event `s` is within `ε` in symmetric-difference measure of two events `t` and `t'`
whose intersection mass factors. Then `s` has outer measure `0` or `1`. No measurable space or
measurability of the sets is needed.

The two approximants need not have the same measure and need not themselves be independent as
random objects; only the displayed factorization of their intersection is used. -/
theorem measure_eq_zero_or_one_of_forall_exists_symmDiff_lt_inter_eq_mul {Ω : Type*}
    {F : Type*} [FunLike F (Set Ω) ℝ≥0∞] [OuterMeasureClass F Ω] {μ : F}
    (hμ : μ univ ≠ ∞) {s : Set Ω}
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ t t' : Set Ω,
        (μ (symmDiff t s)).toReal < ε ∧ (μ (symmDiff t' s)).toReal < ε ∧
        (μ (t ∩ t')).toReal = (μ t).toReal * (μ t').toReal) :
    μ s = 0 ∨ μ s = 1 := by
  have hsq : (μ s).toReal = (μ s).toReal * (μ s).toReal := by
    by_contra hne
    set d : ℝ := |(μ s).toReal - (μ s).toReal * (μ s).toReal| with hd
    have hd0 : 0 < d := hd ▸ abs_pos.mpr (sub_ne_zero.mpr hne)
    have hq0 : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
    -- an `ε` at most `1` and small enough that `ε (2 μ s + 3) < d`
    set e : ℝ := min 1 (d / (2 * (2 * (μ s).toReal + 3))) with he
    have he0 : 0 < e := lt_min one_pos (by positivity)
    obtain ⟨t, t', h1, h2, hinter⟩ := happrox e he0
    have hfinal := abs_toReal_sub_mul_self_le_of_symmDiff_le hμ (min_le_left _ _)
      h1.le h2.le hinter
    rw [← hd] at hfinal
    have hle : e * (2 * (μ s).toReal + 3) ≤ d / 2 := by
      calc e * (2 * (μ s).toReal + 3) ≤
          d / (2 * (2 * (μ s).toReal + 3)) * (2 * (μ s).toReal + 3) := by
            gcongr; exact min_le_right _ _
        _ = d / 2 := by field_simp
    linarith
  have hfin : μ s ≠ ∞ := ne_top_of_le_ne_top hμ (measure_mono (subset_univ s))
  have h01 : (μ s).toReal = 0 ∨ (μ s).toReal = 1 :=
    IsIdempotentElem.iff_eq_zero_or_one.mp hsq.symm
  rcases h01 with h0 | h1
  · exact Or.inl (((ENNReal.toReal_eq_zero_iff (μ s)).mp h0).resolve_right hfin)
  · exact Or.inr ((ENNReal.toReal_eq_one_iff (μ s)).mp h1)

end TauCeti.MeasureTheory
