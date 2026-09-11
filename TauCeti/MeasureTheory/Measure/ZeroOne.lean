/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
import TauCeti.Algebra.Order.Ring.Abs
import Mathlib.Algebra.GroupWithZero.Idempotent
import TauCeti.MeasureTheory.Measure.SymmDiff

/-!
# Zero-one criteria and almost surely constant maps

A zero-one measure gives every measurable set mass `0` or `1`. Mathlib's
`MeasureTheory.IsZeroOneMeasure.exists_eq_dirac` identifies such a measure with a Dirac mass, but
only when the carrier is standard Borel. This file records the form that survives on an arbitrary
carrier: a measurable map *into* a standard Borel space is almost surely constant, because its
pushforward is again a zero-one probability measure and is therefore Dirac.

The carrier itself needs no Borel structure, so this applies to a space that carries a measurable
map into a standard Borel space without being one — for instance `ProbabilityMeasure α` for a
countably generated `α`, which
`TauCeti.MeasureTheory.IsZeroOneMeasure.exists_eq_dirac_probabilityMeasure` evaluates into a
countable power of `ℝ≥0∞`.

## Main results

* `TauCeti.MeasureTheory.measure_eq_zero_or_one_of_forall_exists_measureReal_inter_eq_mul`:
  under a finite measure, a null-measurable event admitting arbitrarily close pairs whose
  intersection mass factors has mass `0` or `1`;
* `TauCeti.MeasureTheory.IsZeroOneMeasure.exists_ae_eq_const`: under a zero-one measure, an
  almost-everywhere measurable map into a standard Borel space agrees almost everywhere with a
  single value.

## References

* Edwin Hewitt and Leonard J. Savage, *Symmetric measures on Cartesian products*, Transactions of
  the American Mathematical Society **80** (1955), 470–501, <https://doi.org/10.2307/1992999>.
* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1.

The approximation criterion is the final step of the Hewitt–Savage zero-one law, extracted from
`Probability/Exchangeability/PathSpace/HewittSavage.lean`, which now consumes it: there an
exchangeable event is approximated by a cylinder and its block-swapped copy, and the criterion
turns the factorization of their intersection into triviality of the event.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal symmDiff

namespace TauCeti

namespace MeasureTheory

/-- Two approximants within `e ≤ 1` of `s` whose intersection mass factors force
`|μ s - (μ s)²| ≤ e (2 μ s + 3)`. -/
private theorem abs_measureReal_sub_mul_self_le_of_symmDiff_lt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {t t' s : Set Ω} (ht : NullMeasurableSet t μ) (ht' : NullMeasurableSet t' μ)
    (hs : NullMeasurableSet s μ) {e : ℝ} (he : e ≤ 1) (h1 : μ.real (symmDiff t s) ≤ e)
    (h2 : μ.real (symmDiff t' s) ≤ e)
    (hinter : μ.real (t ∩ t') = μ.real t * μ.real t') :
    |μ.real s - μ.real s * μ.real s| ≤ e * (2 * μ.real s + 3) := by
  have hbt : |μ.real t - μ.real s| ≤ e :=
    (abs_measureReal_sub_le_measureReal_symmDiff ht hs).trans h1
  have hbt' : |μ.real t' - μ.real s| ≤ e :=
    (abs_measureReal_sub_le_measureReal_symmDiff ht' hs).trans h2
  have he0 : 0 ≤ e := (abs_nonneg _).trans hbt
  have hbi : |μ.real (t ∩ t') - μ.real s| ≤ 2 * e :=
    (abs_measureReal_inter_sub_le_of_measureReal_symmDiff ht ht' hs).trans (by linarith)
  have hprod : |μ.real t * μ.real t' - μ.real s * μ.real s| ≤ e * (2 * μ.real s + e) :=
    TauCeti.abs_mul_sub_mul_self_le hbt hbt' measureReal_nonneg measureReal_nonneg
  rw [hinter] at hbi
  have hsplit : μ.real s - μ.real s * μ.real s =
      (μ.real s - μ.real t * μ.real t') + (μ.real t * μ.real t' - μ.real s * μ.real s) := by ring
  calc |μ.real s - μ.real s * μ.real s|
      ≤ |μ.real s - μ.real t * μ.real t'| + |μ.real t * μ.real t' - μ.real s * μ.real s| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ 2 * e + e * (2 * μ.real s + e) := by rw [abs_sub_comm]; linarith
    _ ≤ e * (2 * μ.real s + 3) := by nlinarith [measureReal_nonneg (μ := μ) (s := s)]

/-- **Arbitrarily close factoring approximants force a zero-one event.** Suppose that for every
`ε > 0`, the event `s` is within `ε` in symmetric-difference measure of two events `t` and `t'`
whose intersection mass factors. Then `s` has measure `0` or `1`; the measure need only be finite.

The two approximants need not have the same measure and need not themselves be independent as
random objects; only the displayed factorization of their intersection is used. -/
theorem measure_eq_zero_or_one_of_forall_exists_measureReal_inter_eq_mul {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} (hs : NullMeasurableSet s μ)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ t t' : Set Ω, NullMeasurableSet t μ ∧ NullMeasurableSet t' μ ∧
        μ.real (symmDiff t s) < ε ∧ μ.real (symmDiff t' s) < ε ∧
        μ.real (t ∩ t') = μ.real t * μ.real t') :
    μ s = 0 ∨ μ s = 1 := by
  have hsq : μ.real s = μ.real s * μ.real s := by
    by_contra hne
    set d : ℝ := |μ.real s - μ.real s * μ.real s| with hd
    have hd0 : 0 < d := hd ▸ abs_pos.mpr (sub_ne_zero.mpr hne)
    have hq0 : 0 ≤ μ.real s := measureReal_nonneg
    -- an `ε` at most `1` and small enough that `ε (2 μ s + 3) < d`
    set e : ℝ := min 1 (d / (2 * (2 * μ.real s + 3))) with he
    have he0 : 0 < e := lt_min one_pos (by positivity)
    obtain ⟨t, t', ht, ht', h1, h2, hinter⟩ := happrox e he0
    have hfinal := abs_measureReal_sub_mul_self_le_of_symmDiff_lt ht ht' hs (min_le_left _ _)
      h1.le h2.le hinter
    rw [← hd] at hfinal
    have hle : e * (2 * μ.real s + 3) ≤ d / 2 := by
      calc e * (2 * μ.real s + 3) ≤ d / (2 * (2 * μ.real s + 3)) * (2 * μ.real s + 3) := by
            gcongr; exact min_le_right _ _
        _ = d / 2 := by field_simp
    linarith
  have hfin : μ s ≠ ∞ := measure_ne_top μ s
  have h01 : μ.real s = 0 ∨ μ.real s = 1 :=
    IsIdempotentElem.iff_eq_zero_or_one.mp hsq.symm
  rw [measureReal_def] at h01
  rcases h01 with h0 | h1
  · exact Or.inl (((ENNReal.toReal_eq_zero_iff (μ s)).mp h0).resolve_right hfin)
  · exact Or.inr ((ENNReal.toReal_eq_one_iff (μ s)).mp h1)

/-- **A zero-one law is almost surely constant along a measurable map.** The pushforward of a
nonzero zero-one measure along `f` is again a zero-one probability measure; on a standard Borel
space it is therefore a Dirac mass at some `q`, and `f` equals `q` almost everywhere.

The carrier `Ω` needs no topological or Borel structure of its own, and `f` need only be
almost-everywhere measurable. -/
theorem IsZeroOneMeasure.exists_ae_eq_const {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [StandardBorelSpace β] {π : Measure Ω} [NeZero π] [_root_.MeasureTheory.IsZeroOneMeasure π]
    {f : Ω → β} (hf : AEMeasurable f π) :
    ∃ q : β, ∀ᵐ ω ∂π, f ω = q := by
  have : IsProbabilityMeasure π := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := π) with (h | h)
    · simp_all
    · exact ⟨h⟩
  have : _root_.MeasureTheory.IsZeroOneMeasure (π.map f) := {
    zero_one₀ := fun s hs => by
      rw [Measure.map_apply_of_aemeasurable hf hs]
      exact _root_.MeasureTheory.Measure.zero_one π (f ⁻¹' s) }
  obtain ⟨q, hq⟩ := _root_.MeasureTheory.IsZeroOneMeasure.exists_eq_dirac (μ := π.map f)
  refine ⟨q, ae_of_ae_map (p := fun y => y = q) hf ?_⟩
  rw [hq]
  simp

end MeasureTheory

end TauCeti
