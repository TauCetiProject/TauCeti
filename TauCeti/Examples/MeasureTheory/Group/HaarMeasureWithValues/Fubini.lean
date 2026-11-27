/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Fubini

/-!
# Examples of Fubini's theorem for Haar measures with values in a ring

* On a product of finite discrete groups with counting volumes, the product integral is the
  iterated sum `∑ x, ∑ y, f (x, y)`, in either order.
-/

open TopologicalSpace LocallyConstant

namespace TauCeti.HaarMeasureWithValues

variable {A G H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [Fintype G]
  [Group H] [TopologicalSpace H] [DiscreteTopology H] [Fintype H] [CommRing A]
  (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)
  (hμ : μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ = 1)
  (hν : ν ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ = 1)

include hμ hν

/-- With counting volumes on finite discrete groups, the product integral is `∑ x, ∑ y, f (x, y)`.
-/
example (f : compactlySupported A (G × H) A) :
    (μ.prod ν).integral f = ∑ x, ∑ y, (f : LocallyConstant (G × H) A) (x, y) := by
  rw [← integral_integralRight, integral_eq_smul_sum_of_discrete, hμ, one_smul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [integralRight_apply, integral_eq_smul_sum_of_discrete, hν, one_smul]
  simp only [compactlySupported.sliceRight_apply]

/-- In the other order, the product integral is `∑ y, ∑ x, f (x, y)`. -/
example (f : compactlySupported A (G × H) A) :
    (μ.prod ν).integral f = ∑ y, ∑ x, (f : LocallyConstant (G × H) A) (x, y) := by
  rw [← integral_integralLeft, integral_eq_smul_sum_of_discrete, hν, one_smul]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [integralLeft_apply, integral_eq_smul_sum_of_discrete, hμ, one_smul]
  simp only [compactlySupported.sliceLeft_apply]

end TauCeti.HaarMeasureWithValues
