/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Almost-everywhere measurability of finite lattice extrema

The supremum of a nonempty finite family of almost-everywhere measurable functions into a
semilattice with measurable join is almost everywhere measurable, and so are the coordinatewise
supremum and infimum `x ↦ sup' (fun n => f n x)` and `x ↦ inf' (fun n => f n x)`. In a linear
order these are the maximum and the minimum, which is what lets the two extremes of a finite
family of random variables — and hence their range — be treated as random variables in their own
right: their laws are pushforwards, and their distribution functions are computed from those of
the family.

Mathlib proves the measurable supremum, `Finset.measurable_sup'`, and has no infimum counterpart;
this file supplies the infimum, the almost-everywhere forms of both, and the coordinatewise
versions `x ↦ sup' (fun n => f n x)` and `x ↦ inf' (fun n => f n x)` of all four, which is the
spelling their consumers use. Every lemma is registered with `fun_prop`, so extrema in either
spelling are discharged by automation.
-/

public section

namespace Finset

open MeasureTheory

variable {ι α δ : Type*} [MeasurableSpace α] [MeasurableSpace δ] {μ : Measure δ}
  {s : Finset ι} {f : ι → δ → α}

/-- The infimum of a nonempty finite family of measurable functions is measurable. -/
@[fun_prop]
theorem measurable_inf' [SemilatticeInf α] [MeasurableInf₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, Measurable (f n)) : Measurable (s.inf' hs f) :=
  Finset.measurable_sup' (α := αᵒᵈ) hs hf

/-- The coordinatewise form of `Finset.measurable_sup'`: the pointwise supremum
`x ↦ sup' (fun n => f n x)` of a nonempty finite family of measurable functions is measurable. -/
@[fun_prop]
theorem measurable_fun_sup' [SemilatticeSup α] [MeasurableSup₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, Measurable (f n)) : Measurable (fun x => s.sup' hs fun n => f n x) :=
  funext (Finset.sup'_apply hs f) ▸ Finset.measurable_sup' hs hf

/-- The coordinatewise form of `Finset.measurable_inf'`: the pointwise infimum
`x ↦ inf' (fun n => f n x)` of a nonempty finite family of measurable functions is measurable. -/
@[fun_prop]
theorem measurable_fun_inf' [SemilatticeInf α] [MeasurableInf₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, Measurable (f n)) : Measurable (fun x => s.inf' hs fun n => f n x) :=
  funext (Finset.inf'_apply hs f) ▸ measurable_inf' hs hf

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
  aemeasurable_sup' (α := αᵒᵈ) hs hf

/-- The coordinatewise form of `Finset.aemeasurable_sup'`: the pointwise supremum
`x ↦ sup' (fun n => f n x)` of a nonempty finite family of a.e.-measurable functions is a.e.
measurable. -/
@[fun_prop]
theorem aemeasurable_fun_sup' [SemilatticeSup α] [MeasurableSup₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (fun x => s.sup' hs fun n => f n x) μ :=
  funext (Finset.sup'_apply hs f) ▸ aemeasurable_sup' hs hf

/-- The coordinatewise form of `Finset.aemeasurable_inf'`: the pointwise infimum
`x ↦ inf' (fun n => f n x)` of a nonempty finite family of a.e.-measurable functions is a.e.
measurable. -/
@[fun_prop]
theorem aemeasurable_fun_inf' [SemilatticeInf α] [MeasurableInf₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (fun x => s.inf' hs fun n => f n x) μ :=
  funext (Finset.inf'_apply hs f) ▸ aemeasurable_inf' hs hf

end Finset
