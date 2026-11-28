/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.SelfAdjointSpectrumInterval
public import TauCeti.Analysis.Normed.Order.OrderUnit
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
* `IsSelfAdjoint.algebraMap_sub_le_algebraMap_add_smul` and
  `IsSelfAdjoint.algebraMap_add_smul_le_algebraMap_add`: C⋆-order perturbation bounds for adding
  a real multiple of a self-adjoint element to a real scalar.

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

section Perturbation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Adding a real multiple of a self-adjoint element to a real scalar shifts it below by at most
`b`: if `z` is self-adjoint and `|r| * ‖z‖ ≤ b`, then `a - b ≤ a + r • z` in the C⋆-order. -/
theorem _root_.IsSelfAdjoint.algebraMap_sub_le_algebraMap_add_smul {z : A} (hz : IsSelfAdjoint z)
    (a : ℝ) {r b : ℝ} (hrb : |r| * ‖z‖ ≤ b) :
    algebraMap ℝ A (a - b) ≤ algebraMap ℝ A a + r • z := by
  have hrz : IsSelfAdjoint (r • z) := by
    rw [IsSelfAdjoint, star_smul, star_trivial, hz.star_eq]
  have hnorm : ‖r • z‖ ≤ b := by simpa [norm_smul, Real.norm_eq_abs] using hrb
  have h1 : (0 : A) ≤ 1 := zero_le_one
  have hneg : algebraMap ℝ A (-b) ≤ r • z := by
    calc algebraMap ℝ A (-b)
        = (-b) • (1 : A) := Algebra.algebraMap_eq_smul_one (-b)
      _ ≤ (-‖r • z‖) • (1 : A) := smul_le_smul_of_nonneg_right (neg_le_neg hnorm) h1
      _ = -algebraMap ℝ A ‖r • z‖ := by rw [Algebra.algebraMap_eq_smul_one, neg_smul]
      _ ≤ r • z := hrz.neg_algebraMap_norm_le_self
  calc algebraMap ℝ A (a - b)
      = algebraMap ℝ A a + algebraMap ℝ A (-b) := by rw [sub_eq_add_neg, map_add]
    _ ≤ algebraMap ℝ A a + r • z := add_le_add_right hneg _

/-- Adding a real multiple of a self-adjoint element to a real scalar shifts it above by at most
`b`: if `z` is self-adjoint and `|r| * ‖z‖ ≤ b`, then `a + r • z ≤ a + b` in the C⋆-order. -/
theorem _root_.IsSelfAdjoint.algebraMap_add_smul_le_algebraMap_add {z : A} (hz : IsSelfAdjoint z)
    (a : ℝ) {r b : ℝ} (hrb : |r| * ‖z‖ ≤ b) :
    algebraMap ℝ A a + r • z ≤ algebraMap ℝ A (a + b) := by
  have hrz : IsSelfAdjoint (r • z) := by
    rw [IsSelfAdjoint, star_smul, star_trivial, hz.star_eq]
  have hnorm : ‖r • z‖ ≤ b := by simpa [norm_smul, Real.norm_eq_abs] using hrb
  have h1 : (0 : A) ≤ 1 := zero_le_one
  have hpos : r • z ≤ algebraMap ℝ A b := by
    calc r • z
        ≤ algebraMap ℝ A ‖r • z‖ := hrz.le_algebraMap_norm_self
      _ = ‖r • z‖ • (1 : A) := Algebra.algebraMap_eq_smul_one _
      _ ≤ b • (1 : A) := smul_le_smul_of_nonneg_right hnorm h1
      _ = algebraMap ℝ A b := (Algebra.algebraMap_eq_smul_one b).symm
  calc algebraMap ℝ A a + r • z
      ≤ algebraMap ℝ A a + algebraMap ℝ A b := add_le_add_right hpos _
    _ = algebraMap ℝ A (a + b) := (map_add _ a b).symm

end Perturbation

end TauCeti
