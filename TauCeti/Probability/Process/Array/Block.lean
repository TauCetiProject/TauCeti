/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Rectangular blocks of array processes

`arrayBlock X e f` selects the entries of a two-index process along arbitrary index maps
`e` and `f`. `arrayBlockPair` retains each selected entry together with its transpose, which
allows oriented data to be read without discarding the reverse orientation.

This file supplies coordinate equations, entrywise almost-everywhere measurability, and
measurability of the corresponding read-offs from array path space. No injectivity or symmetry
is required; exchangeability of selected blocks is developed separately in
`TauCeti.Probability.Exchangeability.Arrays.Block.Basic`.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* D. Aldous, *Representations for partially exchangeable arrays of random variables*, Journal of
  Multivariate Analysis 11 (1981), 581–598.
-/

public section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α Ω : Type*}

/-! ## Blocks of an array -/

/-- The rectangular block of the array `X` along the index maps `e` and `f`: its `(i, j)`-entry is
the `(e i, f j)`-entry of `X`. -/
def arrayBlock (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) : ℕ × ℕ → Ω → α :=
  fun p ↦ X (e p.1, f p.2)

@[simp]
theorem arrayBlock_apply (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) (p : ℕ × ℕ) :
    arrayBlock X e f p = X (e p.1, f p.2) :=
  (rfl)

/-- The rectangular block of `X` along `e` and `f`, read together with its transpose: its
`(i, j)`-entry is the pair of the `(e i, f j)`-entry and the `(f j, e i)`-entry of `X`. -/
def arrayBlockPair (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) : ℕ × ℕ → Ω → α × α :=
  fun p ω ↦ (X (e p.1, f p.2) ω, X (f p.2, e p.1) ω)

@[simp]
theorem arrayBlockPair_apply (X : ℕ × ℕ → Ω → α) (e f : ℕ → ℕ) (p : ℕ × ℕ) (ω : Ω) :
    arrayBlockPair X e f p ω = (X (e p.1, f p.2) ω, X (f p.2, e p.1) ω) :=
  (rfl)

variable [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ × ℕ → Ω → α} {e f : ℕ → ℕ}

/-- Entrywise measurability passes to a block: the `p`-entry of `arrayBlock X e f` is the
`(e p.1, f p.2)`-entry of `X`. -/
theorem aemeasurable_arrayBlock (hX : ∀ p, AEMeasurable (X p) μ) (p : ℕ × ℕ) :
    AEMeasurable (arrayBlock X e f p) μ := by
  simpa only [arrayBlock_apply] using hX (e p.1, f p.2)

/-- Entrywise measurability passes to a block read together with its transpose: the `p`-entry of
`arrayBlockPair X e f` pairs two entries of `X`. -/
theorem aemeasurable_arrayBlockPair (hX : ∀ p, AEMeasurable (X p) μ) (p : ℕ × ℕ) :
    AEMeasurable (arrayBlockPair X e f p) μ := by
  have hread : arrayBlockPair X e f p =
      fun ω ↦ (X (e p.1, f p.2) ω, X (f p.2, e p.1) ω) :=
    funext fun ω ↦ arrayBlockPair_apply X e f p ω
  rw [hread]
  exact (hX (e p.1, f p.2)).prodMk (hX (f p.2, e p.1))

/-- Reading a block off an array's sample path is measurable. -/
theorem measurable_blockReadOff (e f : ℕ → ℕ) :
    Measurable fun x : ℕ × ℕ → α ↦ fun p : ℕ × ℕ ↦ x (e p.1, f p.2) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- Reading a block together with its transpose off an array's sample path is measurable. -/
theorem measurable_blockPairReadOff (e f : ℕ → ℕ) :
    Measurable fun x : ℕ × ℕ → α ↦ fun p : ℕ × ℕ ↦ (x (e p.1, f p.2), x (f p.2, e p.1)) :=
  Measurable.of_eval fun _ ↦ (measurable_pi_apply _).prodMk (measurable_pi_apply _)

end Probability

end TauCeti
