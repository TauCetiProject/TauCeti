/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.FiniteChart
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order

/-!
# The finite chart of the rational function field model

The functions in `k(X)` regular at every place where `X` is regular are exactly the
polynomials in `X`. Thus the finite chart of the two-chart model of `k(X)` is the usual
affine line. This identification is the base chart for the finite normalization map
from the two-chart model of a function field to the rational model.

The mathematical input is the classification of the places of `k(X)` and the criterion
that a rational function regular at all finite places is a polynomial (Stichtenoth,
*Algebraic Function Fields and Codes*, second edition, Section I.2).
-/

public section

namespace TauCeti.AlgebraicGeometry.twoChartModel

variable (k : Type*) [Field k]

/-- Evaluation at `X` identifies the polynomial ring with the finite holomorphy chart
of the rational function field. -/
noncomputable def polynomialChartEquivRatFunc :
    Polynomial k ≃ₐ[k] (holomorphyRing
      {P : Place k (RatFunc k) | (RatFunc.X : RatFunc k) ∈ P.integers}) :=
  AlgEquiv.ofBijective (polynomialChartMap (k := k) RatFunc.X)
    ⟨polynomialChartMap_injective RatFunc.transcendental_X, by
      intro z
      have hz : ∀ (q : Polynomial k) (hq : Irreducible q),
          0 ≤ (Place.adicOfIrreducible hq).ord (z : RatFunc k) := by
        intro q hq
        have hX : (RatFunc.X : RatFunc k) ∈ (Place.adicOfIrreducible hq).integers := by
          rw [← RatFunc.algebraMap_X, Place.adicOfIrreducible_def]
          exact Place.algebraMap_mem_integers_ofPrime k (RatFunc k) _ Polynomial.X
        exact (Place.adicOfIrreducible hq).mem_integers_iff_ord_nonneg.mp
          ((mem_holomorphyRing_iff.mp z.property) _ hX)
      obtain ⟨p, hp⟩ := Place.forall_ord_adicOfIrreducible_nonneg_iff.mp hz
      refine ⟨p, Subtype.ext ?_⟩
      simpa only [coe_polynomialChartMap, RatFunc.aeval_X_left_eq_algebraMap] using hp⟩

/-- On a polynomial, the finite-chart equivalence is evaluation in `k(X)`. -/
@[simp] theorem coe_polynomialChartEquivRatFunc_apply (p : Polynomial k) :
    ((polynomialChartEquivRatFunc k p :
      holomorphyRing {P : Place k (RatFunc k) | (RatFunc.X : RatFunc k) ∈ P.integers}) :
      RatFunc k) = algebraMap (Polynomial k) (RatFunc k) p := by
  -- `AlgEquiv.ofBijective` retains the original evaluation map as its forward function.
  change ((polynomialChartMap (k := k) RatFunc.X p :
    holomorphyRing {P : Place k (RatFunc k) | (RatFunc.X : RatFunc k) ∈ P.integers}) :
      RatFunc k) = _
  rw [coe_polynomialChartMap, RatFunc.aeval_X_left_eq_algebraMap]

/-- A function on the finite chart is recovered by evaluating its corresponding polynomial. -/
@[simp] theorem algebraMap_polynomialChartEquivRatFunc_symm_apply
    (z : holomorphyRing
      {P : Place k (RatFunc k) | (RatFunc.X : RatFunc k) ∈ P.integers}) :
    algebraMap (Polynomial k) (RatFunc k) ((polynomialChartEquivRatFunc k).symm z) =
      (z : RatFunc k) := by
  rw [← coe_polynomialChartEquivRatFunc_apply,
    (polynomialChartEquivRatFunc k).apply_symm_apply]

end TauCeti.AlgebraicGeometry.twoChartModel
