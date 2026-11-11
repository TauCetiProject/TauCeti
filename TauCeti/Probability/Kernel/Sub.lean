/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import TauCeti.MeasureTheory.Measure.Sub

/-!
# Measurability of one-occurrence erasure

For an s-finite kernel and a measurably selected location, removing one Dirac occurrence is
measurable. This permits recursive occurrence selection without losing measurability and
allows reduced Palm kernels to be obtained by erasing their conditioning occurrence.

The target space only needs measurable equality (in particular, a standard Borel space
suffices). The s-finite-kernel hypothesis supplies measurability of moving-set evaluations;
no topological or local-finiteness assumption is used.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, 2018, Chapters 2 and 9.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

variable {α X : Type*} [MeasurableSpace α] [MeasurableSpace X] [MeasurableEq X]

/-- The mass at a measurably selected location is measurable for an s-finite kernel. -/
@[fun_prop]
theorem measurable_apply_singleton (κ : Kernel α X) [IsSFiniteKernel κ]
    {f : α → X} (hf : Measurable f) : Measurable fun a ↦ κ a {f a} := by
  simpa using κ.measurable_kernel_prodMk_left
    (measurableSet_eq_fun measurable_snd (hf.comp measurable_fst))

/-- Removing one occurrence at a measurable location from an s-finite kernel is measurable.
At a multiple point only one copy is removed; at an absent point the measure is unchanged. -/
@[fun_prop]
theorem measurable_sub_dirac (κ : Kernel α X) [IsSFiniteKernel κ]
    {f : α → X} (hf : Measurable f) : Measurable fun a ↦ κ a - Measure.dirac (f a) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hrest : Measurable fun a ↦ κ a (A ∩ {f a}ᶜ) := by
    exact κ.measurable_kernel_prodMk_left (t := {p | p.2 ∈ A ∧ p.2 ≠ f p.1})
      ((hA.preimage measurable_snd).inter
        (measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)).compl)
  simp_rw [Measure.sub_dirac_eq_restrict_add_smul, add_apply,
    Measure.restrict_apply hA, smul_apply, smul_eq_mul]
  exact hrest.add ((κ.measurable_apply_singleton hf).sub measurable_const |>.mul
    ((Measure.measurable_coe hA).comp (Measure.measurable_dirac.comp hf)))

end ProbabilityTheory.Kernel
