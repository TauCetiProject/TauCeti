/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Chart.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval

/-!
# The affine Weierstrass equation as the third projective chart

Setting the last homogeneous coordinate to one identifies the chart ring of a projective
Weierstrass curve with the coordinate ring of its affine equation. The comparison is over any
commutative base ring and sends the universal chart point to the affine coordinates `[x : y : 1]`.

## Main definitions

* `WeierstrassCurve.Projective.chartRingTwoEquivCoordinateRing`: the algebra equivalence between
  the third projective chart ring and the affine coordinate ring.

## Provenance

Extracted from the chart identification in
`TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/FunctionField.lean`, adapted from AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `c3415f32a313e19ace43e05479aeaa0d56ca287a`,
file `projects/ModularCurves/ModularCurves/EllipticCurve/ModelVariableChange.lean`, declaration
`coordRingToZSection`. The comparison here uses `ChartRing` and requires only a commutative ring.
-/

public section

open MvPolynomial

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W' : Projective R)

private theorem aeval_polynomial_eq_zero :
    aeval ![Affine.CoordinateRing.mk W'.toAffine (Polynomial.C Polynomial.X),
      Affine.CoordinateRing.mk W'.toAffine Polynomial.X, 1] W'.polynomial = 0 := by
  rw [aeval_def, ← eval_map, ← map_polynomial]
  exact (equation_some _ _).mpr (Affine.CoordinateRing.equation_X_root W'.toAffine)

private noncomputable def chartRingToCoordinateRing :
    W'.ChartRing 2 →ₐ[R] W'.toAffine.CoordinateRing :=
  Ideal.Quotient.liftₐ _ (aeval ![Affine.CoordinateRing.mk W'.toAffine (Polynomial.C Polynomial.X),
      Affine.CoordinateRing.mk W'.toAffine Polynomial.X, 1]) fun _ hp ↦
    RingHom.mem_ker.mp <| Ideal.span_le.mpr (Set.range_subset_iff.mpr <| Fin.forall_fin_two.mpr
      ⟨by rw [chartRelation_zero]; exact W'.aeval_polynomial_eq_zero,
        by simp⟩) hp

private theorem chartRingToCoordinateRing_mk (p : MvPolynomial (Fin 3) R) :
    W'.chartRingToCoordinateRing (Ideal.Quotient.mk _ p) =
      aeval ![Affine.CoordinateRing.mk W'.toAffine (Polynomial.C Polynomial.X),
        Affine.CoordinateRing.mk W'.toAffine Polynomial.X, 1] p :=
  rfl

private noncomputable def coordinateRingToChartRing :
    W'.toAffine.CoordinateRing →ₐ[R] W'.ChartRing 2 :=
  Affine.CoordinateRing.evalAlgHom <|
    (equation_some (W'.chartPoint 2 0) (W'.chartPoint 2 1)).mp <| by
      -- The universal chart point has last coordinate one.
      convert W'.equation_chartPoint 2 using 1
      ext j
      fin_cases j <;> simp

/-- Setting the last homogeneous coordinate to one identifies the third projective chart ring
with the coordinate ring of the affine Weierstrass equation. -/
noncomputable def chartRingTwoEquivCoordinateRing :
    W'.ChartRing 2 ≃ₐ[R] W'.toAffine.CoordinateRing :=
  AlgEquiv.ofAlgHom W'.chartRingToCoordinateRing W'.coordinateRingToChartRing
    (by ext <;> simp [coordinateRingToChartRing, chartRingToCoordinateRing_mk])
    (Ideal.Quotient.algHom_ext R <| algHom_ext fun j ↦ by
      fin_cases j <;> simp [chartRingToCoordinateRing_mk, coordinateRingToChartRing])

/-- The chart comparison evaluates a polynomial at the two affine coordinates and one. -/
@[simp]
theorem chartRingTwoEquivCoordinateRing_mk (p : MvPolynomial (Fin 3) R) :
    W'.chartRingTwoEquivCoordinateRing (Ideal.Quotient.mk _ p) =
      aeval ![Affine.CoordinateRing.mk W'.toAffine (Polynomial.C Polynomial.X),
        Affine.CoordinateRing.mk W'.toAffine Polynomial.X, 1] p :=
  W'.chartRingToCoordinateRing_mk p

/-- The chart comparison sends the universal chart point to the affine coordinates `[x : y : 1]`.
-/
theorem chartRingTwoEquivCoordinateRing_chartPoint :
    W'.chartRingTwoEquivCoordinateRing ∘ W'.chartPoint 2 =
      ![Affine.CoordinateRing.mk W'.toAffine (Polynomial.C Polynomial.X),
        Affine.CoordinateRing.mk W'.toAffine Polynomial.X, 1] := by
  funext j
  simp [Function.comp_apply, chartRingTwoEquivCoordinateRing_mk]

/-- The inverse chart comparison sends the affine coordinate `x` to the first chart coordinate. -/
@[simp]
theorem chartRingTwoEquivCoordinateRing_symm_of_X :
    W'.chartRingTwoEquivCoordinateRing.symm
        (AdjoinRoot.of W'.toAffine.polynomial Polynomial.X) = W'.chartPoint 2 0 :=
  Affine.CoordinateRing.evalAlgHom_of_X _

/-- The inverse chart comparison sends the affine coordinate `y` to the second chart coordinate.
-/
@[simp]
theorem chartRingTwoEquivCoordinateRing_symm_root :
    W'.chartRingTwoEquivCoordinateRing.symm (AdjoinRoot.root W'.toAffine.polynomial) =
      W'.chartPoint 2 1 :=
  Affine.CoordinateRing.evalAlgHom_root _

end WeierstrassCurve.Projective
