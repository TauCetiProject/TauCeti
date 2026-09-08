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
measurable join is again measurable, and likewise for almost-everywhere measurable ones. In a
linear order the supremum is the maximum, and this is what lets the extremes of a finite family
of random variables — order statistics, the range, the first arrival among finitely many
exponential clocks — be treated as random variables in their own right: their laws are
pushforwards, and their distribution functions are computed from those of the family.

Mathlib proves `Finset.measurable_sup'`; this file adds the almost-everywhere version and its
coordinatewise form. Infima are the suprema of the order dual, so the infimum (in a linear order,
the minimum) of a family is obtained by instantiating these at `OrderDual α`, exactly as
`Finset.measurable_sup'` is used for `Finset.inf'`.
-/

public section

namespace Finset

open MeasureTheory

variable {ι α δ : Type*} [MeasurableSpace α] [MeasurableSpace δ] {μ : Measure δ}
  {s : Finset ι} {f : ι → δ → α} [SemilatticeSup α] [MeasurableSup₂ α]

/-- The supremum of a nonempty finite family of a.e.-measurable functions is a.e. measurable. -/
@[fun_prop]
theorem aemeasurable_sup' (hs : s.Nonempty) (hf : ∀ n ∈ s, AEMeasurable (f n) μ) :
    AEMeasurable (s.sup' hs f) μ :=
  Finset.sup'_induction (p := fun g : δ → α => AEMeasurable g μ) hs f (fun _ h₁ _ h₂ => h₁.sup h₂)
    fun n hn => hf n hn

/-- The coordinatewise form of `Finset.aemeasurable_sup'`: the pointwise supremum
`x ↦ sup' (fun n => f n x)` of a nonempty finite family of a.e.-measurable functions is a.e.
measurable. -/
@[fun_prop]
theorem aemeasurable_sup'_apply (hs : s.Nonempty) (hf : ∀ n ∈ s, AEMeasurable (f n) μ) :
    AEMeasurable (fun x => s.sup' hs fun n => f n x) μ :=
  (aemeasurable_sup' hs hf).congr (Filter.Eventually.of_forall fun x => Finset.sup'_apply hs f x)

end Finset
