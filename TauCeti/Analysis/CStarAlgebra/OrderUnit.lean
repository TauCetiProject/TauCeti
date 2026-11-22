/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.SelfAdjointSpectrumInterval
public import TauCeti.Analysis.Normed.Order.OrderUnit.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The self-adjoint part of a unital C⋆-algebra as an order-unit space

For a nontrivial unital C⋆-algebra `A`, the self-adjoint part `selfAdjoint A`, with the order
inherited from `A` and the C⋆-norm, is an order-unit space with unit `1`: for `r ≥ 0` a
self-adjoint `a` satisfies `‖a‖ ≤ r` exactly when `-r • 1 ≤ a ≤ r • 1`, since both conditions
say that the real spectrum of `a` lies in `[-r, r]`. This identifies the C⋆-norm on self-adjoint
elements with the order-unit norm of `1`, so that the theory of order-unit spaces, their states
and their Lipschitz seminorms applies to `selfAdjoint A`.

## Main results

* `TauCeti.isOrderUnitNorm_selfAdjoint_one`: the C⋆-norm on `selfAdjoint A` is the order-unit
  norm of `1`.

## References

* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, §1.
-/

public section

namespace TauCeti

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

/-- For a nontrivial unital C⋆-algebra `A`, the C⋆-norm on `selfAdjoint A` is the order-unit
norm of `1`: `‖a‖ ≤ r ↔ -r • 1 ≤ a ≤ r • 1` for `r ≥ 0`. -/
theorem isOrderUnitNorm_selfAdjoint_one : IsOrderUnitNorm (1 : selfAdjoint A) where
  norm_eq_one := by simp
  norm_le_iff {a} {r} hr := by
    have ha : IsSelfAdjoint (a : A) := a.property
    have h₁ : ((-(r • 1) : selfAdjoint A) : A) = algebraMap ℝ A (-r) := by
      simp [Algebra.algebraMap_eq_smul_one]
    have h₂ : ((r • 1 : selfAdjoint A) : A) = algebraMap ℝ A r := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe, h₁, h₂, algebraMap_le_iff_le_spectrum ha,
      le_algebraMap_iff_spectrum_le ha, AddSubgroup.coe_norm,
      ha.norm_le_iff_spectrum_subset_Icc hr]
    simp only [Set.subset_def, Set.mem_Icc, forall₂_and]

end TauCeti
