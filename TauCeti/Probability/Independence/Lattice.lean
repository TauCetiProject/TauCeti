/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.Probability.HasLaw
import TauCeti.MeasureTheory.Order.Lattice

/-!
# Laws of finite infima and suprema of independent random variables

For an independent finite family of random variables valued in a measurable semilattice, the
pointwise infimum or supremum over any nonempty `s : Finset ι` has the pushforward of the product
law along the corresponding coordinatewise extremum.

## Main results

* `ProbabilityTheory.iIndepFun.hasLaw_inf'` — law of a nonempty finite infimum of independent
  coordinates in a measurable inf-semilattice;
* `ProbabilityTheory.iIndepFun.hasLaw_sup'` — law of a nonempty finite supremum of independent
  coordinates in a measurable sup-semilattice.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

/-- A nonempty finite infimum of independent random variables in a measurable inf-semilattice has
the pushforward of the product law along the coordinatewise infimum. -/
theorem iIndepFun.hasLaw_inf' {Ω ι α : Type*} {_ : MeasurableSpace Ω} [Fintype ι]
    [MeasurableSpace α] [SemilatticeInf α] [MeasurableInf₂ α]
    {P : Measure Ω} {μ : ι → Measure α} {X : ι → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P)
    (s : Finset ι) (hs : s.Nonempty) :
    HasLaw (fun ω ↦ s.inf' hs fun i ↦ X i ω)
      ((Measure.pi μ).map fun x ↦ s.inf' hs fun i ↦ x i) P :=
  (hasLaw_map (Finset.measurable_inf'' hs fun i _ ↦ measurable_pi_apply i).aemeasurable).comp
    (hindep.hasLaw_pi hX)

/-- A nonempty finite supremum of independent random variables in a measurable sup-semilattice has
the pushforward of the product law along the coordinatewise supremum. -/
theorem iIndepFun.hasLaw_sup' {Ω ι α : Type*} {_ : MeasurableSpace Ω} [Fintype ι]
    [MeasurableSpace α] [SemilatticeSup α] [MeasurableSup₂ α]
    {P : Measure Ω} {μ : ι → Measure α} {X : ι → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P)
    (s : Finset ι) (hs : s.Nonempty) :
    HasLaw (fun ω ↦ s.sup' hs fun i ↦ X i ω)
      ((Measure.pi μ).map fun x ↦ s.sup' hs fun i ↦ x i) P :=
  (hasLaw_map (Finset.measurable_sup'' hs fun i _ ↦ measurable_pi_apply i).aemeasurable).comp
    (hindep.hasLaw_pi hX)

end ProbabilityTheory
