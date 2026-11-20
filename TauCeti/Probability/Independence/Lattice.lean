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

For an independent family of random variables valued in a measurable semilattice, the pointwise
infimum or supremum over a nonempty finite index type or a nonempty `s : Finset ι` has the
pushforward of the product law along the corresponding coordinatewise extremum.

## Main results

* `ProbabilityTheory.iIndepFun.hasLaw_inf'` — law of the infimum over a nonempty finite index type
  in a measurable inf-semilattice;
* `ProbabilityTheory.iIndepFun.hasLaw_sup'` — law of the supremum over a nonempty finite index type
  in a measurable sup-semilattice;
* `ProbabilityTheory.iIndepFun.hasLaw_finset_inf'` — law of the infimum over a nonempty `Finset`
  without a `Fintype` assumption on the ambient index type;
* `ProbabilityTheory.iIndepFun.hasLaw_finset_sup'` — law of the supremum over a nonempty `Finset`
  without a `Fintype` assumption on the ambient index type.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

/-- The infimum of a nonempty finite independent family of random variables in a measurable
inf-semilattice has the pushforward of the product law along the coordinatewise infimum. -/
theorem iIndepFun.hasLaw_inf' {Ω ι α : Type*} {_ : MeasurableSpace Ω} [Fintype ι] [Nonempty ι]
    [MeasurableSpace α] [SemilatticeInf α] [MeasurableInf₂ α]
    {P : Measure Ω} {μ : ι → Measure α} {X : ι → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ X i ω)
      ((Measure.pi μ).map fun x ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ x i) P :=
  (hasLaw_map (Finset.measurable_inf'' Finset.univ_nonempty fun i _ ↦
    measurable_pi_apply i).aemeasurable).comp (hindep.hasLaw_pi hX)

/-- The supremum of a nonempty finite independent family of random variables in a measurable
sup-semilattice has the pushforward of the product law along the coordinatewise supremum. -/
theorem iIndepFun.hasLaw_sup' {Ω ι α : Type*} {_ : MeasurableSpace Ω} [Fintype ι] [Nonempty ι]
    [MeasurableSpace α] [SemilatticeSup α] [MeasurableSup₂ α]
    {P : Measure Ω} {μ : ι → Measure α} {X : ι → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ X i ω)
      ((Measure.pi μ).map fun x ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ x i) P :=
  (hasLaw_map (Finset.measurable_sup'' Finset.univ_nonempty fun i _ ↦
    measurable_pi_apply i).aemeasurable).comp (hindep.hasLaw_pi hX)

/-- The infimum over a nonempty `Finset` of independent random variables in a measurable
inf-semilattice has the pushforward of the subtype product law along the coordinatewise infimum. -/
theorem iIndepFun.hasLaw_finset_inf' {Ω ι α : Type*} {_ : MeasurableSpace Ω}
    [MeasurableSpace α] [SemilatticeInf α] [MeasurableInf₂ α]
    {P : Measure Ω} {μ : ι → Measure α} {X : ι → Ω → α}
    (hindep : iIndepFun X P) {s : Finset ι} (hs : s.Nonempty)
    (hX : ∀ i ∈ s, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω ↦ s.inf' hs fun i ↦ X i ω)
      ((Measure.pi fun i : s ↦ μ i).map fun x ↦ s.attach.inf' hs.attach fun i ↦ x i) P := by
  have : Nonempty s := hs.to_subtype
  have hlaw := (hindep.precomp Subtype.val_injective).hasLaw_inf' fun i : s ↦ hX i.1 i.2
  have hdom : (fun ω ↦ Finset.univ.inf' Finset.univ_nonempty fun i : s ↦ X i.1 ω) =
      fun ω ↦ s.inf' hs fun i ↦ X i ω :=
    funext fun ω ↦ eq_of_forall_le_iff fun _ ↦ by simp
  have hcod : (fun x : s → α ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ x i) =
      fun x ↦ s.attach.inf' hs.attach fun i ↦ x i :=
    funext fun x ↦ eq_of_forall_le_iff fun _ ↦ by simp
  rwa [hdom, hcod] at hlaw

/-- The supremum over a nonempty `Finset` of independent random variables in a measurable
sup-semilattice has the pushforward of the subtype product law along the coordinatewise supremum. -/
theorem iIndepFun.hasLaw_finset_sup' {Ω ι α : Type*} {_ : MeasurableSpace Ω}
    [MeasurableSpace α] [SemilatticeSup α] [MeasurableSup₂ α]
    {P : Measure Ω} {μ : ι → Measure α} {X : ι → Ω → α}
    (hindep : iIndepFun X P) {s : Finset ι} (hs : s.Nonempty)
    (hX : ∀ i ∈ s, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω ↦ s.sup' hs fun i ↦ X i ω)
      ((Measure.pi fun i : s ↦ μ i).map fun x ↦ s.attach.sup' hs.attach fun i ↦ x i) P := by
  have : Nonempty s := hs.to_subtype
  have hlaw := (hindep.precomp Subtype.val_injective).hasLaw_sup' fun i : s ↦ hX i.1 i.2
  have hdom : (fun ω ↦ Finset.univ.sup' Finset.univ_nonempty fun i : s ↦ X i.1 ω) =
      fun ω ↦ s.sup' hs fun i ↦ X i ω :=
    funext fun ω ↦ eq_of_forall_ge_iff fun _ ↦ by simp
  have hcod : (fun x : s → α ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ x i) =
      fun x ↦ s.attach.sup' hs.attach fun i ↦ x i :=
    funext fun x ↦ eq_of_forall_ge_iff fun _ ↦ by simp
  rwa [hdom, hcod] at hlaw

end ProbabilityTheory
