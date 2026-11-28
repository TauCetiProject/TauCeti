/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Completely positive maps into finite products

A family of completely positive maps `φ_i : A → B_i` into finitely many C⋆-algebras assembles to
a completely positive map `a ↦ (φ_i(a))_i` into the product (`CompletelyPositiveMap.pi`): a matrix
over the product is positive exactly when each of its components is
(`CStarMatrix.piStarAlgEquiv`).
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace CompletelyPositiveMap

section Pi

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {ι : Type*} [Fintype ι] {B : ι → Type*} [∀ i, NonUnitalCStarAlgebra (B i)]
  [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)]

/-- The completely positive map `a ↦ (φ_i(a))_i` into a finite product. -/
def pi (φ : ∀ i, A →CP B i) : A →CP ∀ i, B i where
  toLinearMap := LinearMap.pi fun i ↦ (φ i).toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    let e := CStarMatrix.piStarAlgEquiv ℂ (Fin k) B
    rw [← map_le_map_iff e, map_zero]
    exact fun i ↦ ((φ i).map_cstarMatrix_nonneg' k M hM).trans_eq (by ext; simp [e])

@[simp]
theorem pi_apply (φ : ∀ i, A →CP B i) (a : A) (i : ι) : pi φ a i = φ i a :=
  (rfl)

/-- `a ↦ (φ_i(a))_i` is contractive when each `φ_i` is. -/
theorem norm_pi_apply_le {φ : ∀ i, A →CP B i} (hφ : ∀ i a, ‖φ i a‖ ≤ ‖a‖) (a : A) :
    ‖pi φ a‖ ≤ ‖a‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2 fun i ↦ hφ i a

end Pi

end CompletelyPositiveMap
