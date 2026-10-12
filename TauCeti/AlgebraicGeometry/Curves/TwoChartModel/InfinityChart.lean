/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.FiniteChart
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.FieldTheory.IntermediateField.Adjoin.Inv
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# The chart at infinity of the rational function field

For the rational function field `k(X)`, the functions regular wherever `X⁻¹` is regular
are exactly the polynomials in `X⁻¹`. This identifies the second affine chart of the
two-chart model with an affine line, with its coordinate sent to `X⁻¹`. Together with
the finite chart, it gives the two standard affine pieces used to identify the model
with the projective line.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section I.2.
-/

public section

open _root_.AlgebraicGeometry
open scoped _root_.IntermediateField

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable (k : Type u) [Field k]

/-- The chart at infinity of `k(X)` is `k[X⁻¹]`, with its polynomial coordinate
identified with `X⁻¹`. -/
noncomputable def ratFuncInfinityChartAlgEquiv : Polynomial k ≃ₐ[k]
    holomorphyRing {P : Place k (RatFunc k) | (RatFunc.X : RatFunc k)⁻¹ ∈ P.integers} := by
  let y : RatFunc k := (RatFunc.X : RatFunc k)⁻¹
  have hy : Transcendental k y := by
    intro h
    exact RatFunc.transcendental_X ((IsAlgebraic.inv_iff).mp h)
  have htop : (IntermediateField.adjoin k {y} : IntermediateField k (RatFunc k)) = ⊤ := by
    simp only [y, IntermediateField.adjoin_simple_inv, RatFunc.adjoin_X]
  let A := Algebra.adjoin k {y}
  have hfrac : IsFractionRing A (RatFunc k) :=
    IntermediateField.isFractionRing_algebra_adjoin_of_adjoin_eq_top htop
  letI : IsFractionRing A (RatFunc k) := hfrac
  have hclosed : IsIntegrallyClosed A :=
    IsIntegrallyClosed.of_equiv (Polynomial.algEquivOfTranscendental k y hy).toRingEquiv
  letI : IsIntegrallyClosed A := hclosed
  have hclosure : (integralClosure A (RatFunc k)).restrictScalars k = A := by
    rw [IsIntegrallyClosed.integralClosure_eq_bot]
    ext z
    simp only [Subalgebra.mem_restrictScalars, Algebra.mem_bot, Set.mem_range]
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.property, fun hz ↦ ⟨⟨z, hz⟩, rfl⟩⟩
  have hchart : A = holomorphyRing {P : Place k (RatFunc k) | y ∈ P.integers} := by
    rw [← restrictScalars_integralClosure_adjoin_eq_holomorphyRing
      (IsFunctionField.ratFunc k) y]
    exact hclosure.symm
  exact (Polynomial.algEquivOfTranscendental k y hy).trans (Subalgebra.equivOfEq _ _ hchart)

/-- Evaluation of a polynomial in the affine coordinate at infinity agrees with the
existing polynomial chart map. -/
@[simp]
theorem ratFuncInfinityChartAlgEquiv_apply (p : Polynomial k) :
    ratFuncInfinityChartAlgEquiv k p =
      polynomialChartMap (k := k) (RatFunc.X : RatFunc k)⁻¹ p := by
  apply Subtype.ext
  simp [ratFuncInfinityChartAlgEquiv, Polynomial.algEquivOfTranscendental]

/-- Every function on the chart at infinity of `k(X)` is a polynomial in `X⁻¹`. -/
theorem polynomialChartMap_inv_X_surjective :
    Function.Surjective (polynomialChartMap (k := k) (RatFunc.X : RatFunc k)⁻¹) := by
  simpa only [Function.Surjective, ratFuncInfinityChartAlgEquiv_apply] using
    (ratFuncInfinityChartAlgEquiv k).surjective

/-- The coordinate of the chart at infinity is the inverse of the rational variable. -/
theorem coe_ratFuncInfinityChartAlgEquiv_X :
    ((ratFuncInfinityChartAlgEquiv k Polynomial.X :
      holomorphyRing {P : Place k (RatFunc k) | (RatFunc.X : RatFunc k)⁻¹ ∈ P.integers}) :
      RatFunc k) = (RatFunc.X : RatFunc k)⁻¹ := by
  rw [ratFuncInfinityChartAlgEquiv_apply, coe_polynomialChartMap]
  simp

end TauCeti.AlgebraicGeometry.twoChartModel
