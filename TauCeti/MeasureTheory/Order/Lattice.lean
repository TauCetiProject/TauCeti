/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Almost-everywhere measurability of finite lattice extrema

The supremum and infimum of a nonempty finite family of almost-everywhere measurable functions
into a semilattice with measurable join, resp. meet, are almost everywhere measurable. In a linear
order these are the maximum and the minimum, which is what lets the two extremes of a finite
family of random variables — and hence their range — be treated as random variables in their own
right: their laws are pushforwards, and their distribution functions are computed from those of
the family.

Mathlib proves the measurable supremum, `Finset.measurable_sup'`, and has no infimum counterpart;
this file supplies the almost-everywhere forms of both, each with its coordinatewise version
`x ↦ sup' (fun n => f n x)`. The infimum lemmas are the supremum lemmas at the order dual.
-/

public section

namespace Finset

open MeasureTheory

variable {ι α δ : Type*} [MeasurableSpace α] [MeasurableSpace δ] {μ : Measure δ}
  {s : Finset ι} {f : ι → δ → α}

/-- The supremum of a nonempty finite family of a.e.-measurable functions is a.e. measurable. -/
@[fun_prop]
theorem aemeasurable_sup' [SemilatticeSup α] [MeasurableSup₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (s.sup' hs f) μ :=
  Finset.sup'_induction (p := fun g : δ → α => AEMeasurable g μ) hs f (fun _ h₁ _ h₂ => h₁.sup h₂)
    fun n hn => hf n hn

/-- The coordinatewise form of `Finset.aemeasurable_sup'`: the pointwise supremum
`x ↦ sup' (fun n => f n x)` of a nonempty finite family of a.e.-measurable functions is a.e.
measurable. -/
@[fun_prop]
theorem aemeasurable_fun_sup' [SemilatticeSup α] [MeasurableSup₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (fun x => s.sup' hs fun n => f n x) μ :=
  (aemeasurable_sup' hs hf).congr (Filter.Eventually.of_forall fun x => Finset.sup'_apply hs f x)

/-- The infimum of a nonempty finite family of a.e.-measurable functions is a.e. measurable. -/
@[fun_prop]
theorem aemeasurable_inf' [SemilatticeInf α] [MeasurableInf₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (s.inf' hs f) μ :=
  -- the infimum is the supremum of the order dual: `Finset.toDual_sup'` is `rfl`
  aemeasurable_sup' (α := αᵒᵈ) hs hf

/-- The coordinatewise form of `Finset.aemeasurable_inf'`: the pointwise infimum
`x ↦ inf' (fun n => f n x)` of a nonempty finite family of a.e.-measurable functions is a.e.
measurable. -/
@[fun_prop]
theorem aemeasurable_fun_inf' [SemilatticeInf α] [MeasurableInf₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (fun x => s.inf' hs fun n => f n x) μ :=
  (aemeasurable_inf' hs hf).congr (Filter.Eventually.of_forall fun x => Finset.inf'_apply hs f x)

end Finset
