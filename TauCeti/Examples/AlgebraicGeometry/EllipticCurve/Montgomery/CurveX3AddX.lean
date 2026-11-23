/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Basic
public import Mathlib.Data.ZMod.Defs

/-!
# Shared concrete points on the running Montgomery curve `y² = x³ + x`

The monic Montgomery model `TauCeti.Montgomery.model 0 1`, given by `y² = x³ + x`, is the running
example across the worked Montgomery examples over `𝔽₅` (`ZMod 5`) and `𝔽₇` (`ZMod 7`). This
module collects the concrete nonsingular affine points and nonsingularity witnesses that are reused
across multiple example modules, keeping single-module points private to their own files and
retaining each worked derivation in its respective example module.

Since `WeierstrassCurve.Affine.Nonsingular` and `WeierstrassCurve.Affine.Point` only require a
`CommRing` instance, none of these declarations introduce or require a `Fact (Nat.Prime _)`
instance, so they can be reused in both parametric and concrete example sections.

## Main definitions

* `TauCeti.Examples.Montgomery.CurveX3AddX.pointTwoZeroFive`: the non-distinguished point `(2, 0)`
  of `y² = x³ + x` over `ZMod 5`.
* `TauCeti.Examples.Montgomery.CurveX3AddX.pointOneThreeSeven`: the point `(1, 3)` of
  `y² = x³ + x` over `ZMod 7`.
* `TauCeti.Examples.Montgomery.CurveX3AddX.pointOneFourSeven`: the point `(1, 4)` of
  `y² = x³ + x` over `ZMod 7`.
* `TauCeti.Examples.Montgomery.CurveX3AddX.pointThreeThreeSeven`: the point `(3, 3)` of
  `y² = x³ + x` over `ZMod 7`.

## Main results

* `TauCeti.Examples.Montgomery.CurveX3AddX.nonsingular_two_zero_five`: `(2, 0)` is a nonsingular
  point of `model (0 : ZMod 5) 1`.
* `TauCeti.Examples.Montgomery.CurveX3AddX.nonsingular_one_three_seven`: `(1, 3)` is a nonsingular
  point of `model (0 : ZMod 7) 1`.
* `TauCeti.Examples.Montgomery.CurveX3AddX.nonsingular_one_four_seven`: `(1, 4)` is a nonsingular
  point of `model (0 : ZMod 7) 1`.
* `TauCeti.Examples.Montgomery.CurveX3AddX.nonsingular_three_three_seven`: `(3, 3)` is a
  nonsingular point of `model (0 : ZMod 7) 1`.

## References

* P. L. Montgomery, *Speeding the Pollard and elliptic curve methods of factorization*,
  Math. Comp. 48 (1987), 243–264, §10.3.1: the curve `B y² = x³ + A x² + x`.
-/

public section

open WeierstrassCurve TauCeti.Montgomery

namespace TauCeti.Examples.Montgomery.CurveX3AddX

/-! ### Points over `ZMod 5` -/

/-- `(2, 0)` is a nonsingular affine point of `y² = x³ + x` over `ZMod 5`. -/
theorem nonsingular_two_zero_five : (model (0 : ZMod 5) 1).toAffine.Nonsingular 2 0 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

/-- The affine point `(2, 0)` of `y² = x³ + x` over `ZMod 5`. -/
@[expose] def pointTwoZeroFive : (model (0 : ZMod 5) 1).toAffine.Point :=
  .some 2 0 nonsingular_two_zero_five

/-! ### Points over `ZMod 7` -/

/-- `(1, 3)` is a nonsingular affine point of `y² = x³ + x` over `ZMod 7`. -/
theorem nonsingular_one_three_seven : (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

/-- The affine point `(1, 3)` of `y² = x³ + x` over `ZMod 7`. -/
@[expose] def pointOneThreeSeven : (model (0 : ZMod 7) 1).toAffine.Point :=
  .some 1 3 nonsingular_one_three_seven

/-- `(1, 4)` is a nonsingular affine point of `y² = x³ + x` over `ZMod 7`. -/
theorem nonsingular_one_four_seven : (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 4 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

/-- The affine point `(1, 4)` of `y² = x³ + x` over `ZMod 7`. -/
@[expose] def pointOneFourSeven : (model (0 : ZMod 7) 1).toAffine.Point :=
  .some 1 4 nonsingular_one_four_seven

/-- `(3, 3)` is a nonsingular affine point of `y² = x³ + x` over `ZMod 7`. -/
theorem nonsingular_three_three_seven : (model (0 : ZMod 7) 1).toAffine.Nonsingular 3 3 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

/-- The affine point `(3, 3)` of `y² = x³ + x` over `ZMod 7`. -/
@[expose] def pointThreeThreeSeven : (model (0 : ZMod 7) 1).toAffine.Point :=
  .some 3 3 nonsingular_three_three_seven

end TauCeti.Examples.Montgomery.CurveX3AddX
