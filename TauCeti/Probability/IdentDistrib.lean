/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.IdentDistrib

/-!
# Measurable modifications of identically distributed random variables

An `IdentDistrib f g μ ν` witness supplies almost-everywhere measurability of both `f` and `g`, so
`AEMeasurable.mk` produces genuine measurable representatives on either side. Because
`AEMeasurable` is a `Prop`, `hf.mk f` is definitionally independent of the proof `hf`, allowing one
to upgrade identically distributed families to measurable modifications without tracking proof
equality.

## Main results

* `ProbabilityTheory.IdentDistrib.mk_fst`, `ProbabilityTheory.IdentDistrib.mk_snd`: replacing the
  first or second random variable by its canonical measurable modification preserves
  `IdentDistrib`.
* `ProbabilityTheory.IdentDistrib.aemeasurable_mk`: replacing both random variables by their
  canonical measurable modifications preserves `IdentDistrib`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.IdentDistrib

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {ν : Measure β} {f : α → γ} {g : β → γ}

/-- Replacing the first random variable in `h : IdentDistrib f g μ ν` by its canonical measurable
modification preserves `IdentDistrib`. -/
theorem mk_fst (h : IdentDistrib f g μ ν) :
    IdentDistrib (h.aemeasurable_fst.mk f) g μ ν :=
  h.aemeasurable_fst.identDistrib_mk.symm.trans h

/-- Replacing the second random variable in `h : IdentDistrib f g μ ν` by its canonical measurable
modification preserves `IdentDistrib`. -/
theorem mk_snd (h : IdentDistrib f g μ ν) :
    IdentDistrib f (h.aemeasurable_snd.mk g) μ ν :=
  h.trans h.aemeasurable_snd.identDistrib_mk

/-- Replacing both random variables in `h : IdentDistrib f g μ ν` by their canonical measurable
modifications preserves `IdentDistrib`. By proof irrelevance of `AEMeasurable`, this applies
definitionally to `hf.mk f` and `hg.mk g` for any witnesses `hf` and `hg`. -/
theorem aemeasurable_mk (h : IdentDistrib f g μ ν) :
    IdentDistrib (h.aemeasurable_fst.mk f) (h.aemeasurable_snd.mk g) μ ν :=
  h.mk_fst.trans h.aemeasurable_snd.identDistrib_mk

end ProbabilityTheory.IdentDistrib
