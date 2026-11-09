/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Invariance
public import TauCeti.Probability.Kernel.Composition.Power

/-!
# Powers and invariant measures of parallel kernels

Parallel composition evolves two coordinates independently. Its powers are the parallel
compositions of the coordinate powers, and pushing a product measure through it gives the
product of the pushed-forward measures. In particular, products of invariant measures are
invariant. These identities supply the transition and stationary laws of independent product
chains without introducing a second product-kernel construction.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Independent coordinate evolution commutes with taking transition powers. -/
@[simp]
theorem parallelComp_pow (κ : Kernel α α) (η : Kernel β β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (n : ℕ) :
    (κ ∥ₖ η) ^ n = (κ ^ n) ∥ₖ (η ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, one_def] using (id_parallelComp_id (α := α) (β := β)).symm
  | succ n ih =>
    simpa only [Kernel.pow_add, pow_one, ih] using
      parallelComp_comp_parallelComp (κ := κ) (κ' := η) (η := κ ^ n) (η' := η ^ n)

/-- At any time, a product chain has the product of the two coordinate transition laws. -/
theorem parallelComp_pow_apply (κ : Kernel α α) (η : Kernel β β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (n : ℕ) (x : α × β) :
    ((κ ∥ₖ η) ^ n) x = ((κ ^ n) x.1).prod ((η ^ n) x.2) := by
  rw [parallelComp_pow, parallelComp_apply]

/-- Singleton transition masses of a product chain factor at each common time. -/
theorem parallelComp_pow_apply_singleton (κ : Kernel α α) (η : Kernel β β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (n : ℕ) (x y : α × β) :
    ((κ ∥ₖ η) ^ n) x {y} = (κ ^ n) x.1 {y.1} * (η ^ n) x.2 {y.2} := by
  rw [parallelComp_pow_apply, ← Set.singleton_prod_singleton, Measure.prod_prod]

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

/-- Pushing independent coordinates through separate kernels preserves their product law. -/
theorem parallelComp_comp_prod (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (κ : Kernel α γ) (η : Kernel β δ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (κ ∥ₖ η) ∘ₘ (μ.prod ν) = (κ ∘ₘ μ).prod (η ∘ₘ ν) := by
  rw [prod_comp_left, prod_comp_right, comp_assoc,
    Kernel.parallelComp_comp_parallelComp, Kernel.comp_id, Kernel.id_comp]

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {κ : Kernel α α} {η : Kernel β β} [IsSFiniteKernel κ] [IsSFiniteKernel η]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

/-- The product of invariant measures is invariant for independent coordinate evolution. -/
theorem Invariant.parallelComp (hκ : κ.Invariant μ) (hη : η.Invariant ν) :
    (κ ∥ₖ η).Invariant (μ.prod ν) := by
  rw [Invariant, Measure.parallelComp_comp_prod, hκ.def, hη.def]

end ProbabilityTheory.Kernel
