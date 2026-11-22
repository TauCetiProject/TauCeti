/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import TauCeti.Analysis.Normed.Order.OrderUnit.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.CStarAlgebra.SelfAdjointSpectrumInterval

/-!
# Order-unit structure on the self-adjoint part of a C⋆-algebra

For a nontrivial unital C⋆-algebra `A`, the self-adjoint part `selfAdjoint A` with unit `1`
carries an order-unit norm coinciding with the inherited C⋆-norm
(`TauCeti.OrderUnit.isOrderUnitNorm_one_selfAdjoint`).
-/

public section

namespace TauCeti.OrderUnit

/-- The self-adjoint part `selfAdjoint A` of a nontrivial unital C⋆-algebra `A`, with `e = 1`,
is an order-unit space whose order-unit norm is the inherited C⋆-norm. -/
theorem isOrderUnitNorm_one_selfAdjoint {A : Type*} [CStarAlgebra A] [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A] : IsOrderUnitNorm (1 : selfAdjoint A) where
  norm_e := by
    -- Expose the norm on the subtype `selfAdjoint A` as the ambient C⋆-norm of `1`.
    change ‖(1 : A)‖ = 1
    exact norm_one
  norm_le_iff a r hr := by
    -- Expose the subtype norm and order on `selfAdjoint A` in terms of `A`.
    change ‖(a : A)‖ ≤ r ↔ ((-r • (1 : selfAdjoint A) : selfAdjoint A) : A) ≤ (a : A) ∧
      (a : A) ≤ ((r • (1 : selfAdjoint A) : selfAdjoint A) : A)
    rw [a.2.norm_le_iff_spectrum_subset_Icc hr]
    have hlo : ((-r • (1 : selfAdjoint A) : selfAdjoint A) : A) = algebraMap ℝ A (-r) := by
      simp [Algebra.algebraMap_eq_smul_one]
    have hhi : ((r • (1 : selfAdjoint A) : selfAdjoint A) : A) = algebraMap ℝ A r := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [hlo, hhi, algebraMap_le_iff_le_spectrum a.2, le_algebraMap_iff_spectrum_le a.2]
    simp [Set.subset_def, Set.mem_Icc, forall_and]

end TauCeti.OrderUnit
