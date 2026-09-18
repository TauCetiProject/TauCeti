/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability of finite lattice extrema

The supremum of a nonempty finite family of measurable functions into a semilattice with
measurable join is measurable, and so is the infimum into a semilattice with measurable meet;
both hold almost everywhere for almost-everywhere measurable functions. In a linear order these
are the maximum and the minimum, which is what lets the two extremes of a finite family of random
variables — and hence their range — be treated as random variables in their own right: their
laws are pushforwards, and their distribution functions are computed from those of the family.

Mathlib proves the measurable supremum, `Finset.measurable_sup'`; this file adds the measurable
infimum and the almost-everywhere supremum and infimum. All are registered with `fun_prop`, which
then also discharges the coordinatewise spellings `x ↦ sup' (fun n => f n x)` and
`x ↦ inf' (fun n => f n x)` that consumers meet.
-/

public section

namespace Finset

open MeasureTheory

variable {ι α δ : Type*} [MeasurableSpace α] [MeasurableSpace δ] {μ : Measure δ}
  {s : Finset ι} {f : ι → δ → α}

/-- The infimum of a nonempty finite family of measurable functions is measurable, the infimum
counterpart of Mathlib's `Finset.measurable_sup'`. -/
@[fun_prop]
theorem measurable_inf' [SemilatticeInf α] [MeasurableInf₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, Measurable (f n)) : Measurable (s.inf' hs f) :=
  Finset.inf'_induction (p := fun g : δ → α => Measurable g) hs f (fun _ h₁ _ h₂ => h₁.inf h₂)
    fun n hn => hf n hn

/-- The supremum of a nonempty finite family of a.e.-measurable functions is a.e. measurable. -/
@[fun_prop]
theorem aemeasurable_sup' [SemilatticeSup α] [MeasurableSup₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (s.sup' hs f) μ :=
  Finset.sup'_induction (p := fun g : δ → α => AEMeasurable g μ) hs f (fun _ h₁ _ h₂ => h₁.sup h₂)
    fun n hn => hf n hn

/-- The infimum of a nonempty finite family of a.e.-measurable functions is a.e. measurable. -/
@[fun_prop]
theorem aemeasurable_inf' [SemilatticeInf α] [MeasurableInf₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (s.inf' hs f) μ :=
  Finset.inf'_induction (p := fun g : δ → α => AEMeasurable g μ) hs f (fun _ h₁ _ h₂ => h₁.inf h₂)
    fun n hn => hf n hn

end Finset
