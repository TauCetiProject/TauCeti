/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.BlockAverage.Measurable
public import TauCeti.Probability.Process.Tail.Basic

/-!
# Future measurability of block averages

An observable averaged over coordinates at or beyond a cutoff is measurable with respect to the
process's future σ-algebra at that cutoff. This is the measurability input for placing limits of
moving block averages on the process tail. It applies to arbitrary processes, without an ambient
measurable space or a measure on the sample space.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Probability

variable {Ω α : Type*} [MeasurableSpace α]

/-- A measurable observable averaged over indices at least `r` is `tailFamily X r`-measurable.
The selection may repeat coordinates or be empty; no ambient measurability of `X` is needed. -/
theorem measurable_tailFamily_blockAverage {X : ℕ → Ω → α} {f : α → ℝ}
    (hf : Measurable f) {r n : ℕ} {k : Fin n → ℕ} (hk : ∀ j, r ≤ k j) :
    Measurable[tailFamily X r] (blockAverage (fun i ω => f (X i ω)) k) :=
  measurable_blockAverage (mΩ := tailFamily X r) k fun j =>
    hf.comp (measurable_tailFamily_of_le (hk j))

end TauCeti.Probability
