/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Division
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Torsion.Basic

/-!
# The Picard group after division of common factors

Removing a common factor from the multiplicities, or from the weights and intersection
numbers together, does not change the weighted relations defining the numerical Picard group.
This gives a canonical identification of the Picard groups before and after division.

The weighted Picard group is the cokernel in the Stacks Project, Tag 0C7H.
-/

public section

namespace TauCeti.NumericalType

universe u

variable (T : NumericalType.{u}) (m w : ℕ+)
  (hm : ∀ i, (m : ℕ) ∣ T.multiplicity i) (hw : ∀ i, (w : ℕ) ∣ T.weight i)

/-- Dividing common factors does not change the weighted intersection matrix. -/
@[simp]
theorem weightedIntersection_divide : (T.divide m w hm hw).weightedIntersection =
    T.weightedIntersection := by
  ext i j
  simp only [weightedIntersection_apply]
  rw [Int.ediv_ediv_of_nonneg (Int.natCast_nonneg _), T.mul_divide_weight m w hm hw j]

/-- Dividing common factors leaves the submodule of principal multidegrees unchanged. -/
@[simp]
theorem principalDivisors_divide : (T.divide m w hm hw).principalDivisors =
    T.principalDivisors := by
  ext d
  simp only [mem_principalDivisors_iff, weightedIntersection_divide]

/-- The canonical Picard-group identification after division of common factors. -/
noncomputable def picDivideEquiv : (T.divide m w hm hw).Pic ≃ₗ[ℤ] T.Pic :=
  Submodule.quotEquivOfEq _ _ (T.principalDivisors_divide m w hm hw)

/-- The Picard identification preserves multidegree representatives. -/
@[simp]
theorem picDivideEquiv_mk (d : T.Component → ℤ) :
    T.picDivideEquiv m w hm hw (Submodule.Quotient.mk d) = Submodule.Quotient.mk d := (rfl)

/-- The inverse Picard identification also preserves multidegree representatives. -/
@[simp]
theorem picDivideEquiv_symm_mk (d : T.Component → ℤ) :
    (T.picDivideEquiv m w hm hw).symm (Submodule.Quotient.mk d) =
      Submodule.Quotient.mk d := (rfl)

/-- Prime-torsion dimension is unchanged by division of common factors. -/
theorem finrank_torsion_divide (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank (ZMod ℓ) ((T.divide m w hm hw).torsion ℓ) =
      Module.finrank (ZMod ℓ) (T.torsion ℓ) := by
  have hcard : Nat.card ((T.divide m w hm hw).torsion ℓ) = Nat.card (T.torsion ℓ) :=
    congrArg (fun P : Submodule ℤ (T.Component → ℤ) ↦
      Nat.card (AddSubgroup.torsionBy ((T.Component → ℤ) ⧸ P) (ℓ : ℤ)))
        (T.principalDivisors_divide m w hm hw)
  rw [natCard_torsion, natCard_torsion] at hcard
  exact Nat.pow_right_injective (Fact.out : ℓ.Prime).two_le hcard

end TauCeti.NumericalType
