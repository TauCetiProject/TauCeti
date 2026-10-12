/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Unimodular
import Mathlib.LinearAlgebra.Projectivization.Constructions
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular

/-!
# The second Bosma–Lenstra addition law on a projective Weierstrass curve

Bosma and Lenstra attach to each line `aX + bY + cZ = 0` in `ℙ²` an addition law of bidegree
`(2, 2)` on a Weierstrass curve: a triple of polynomials in two point representatives `P` and `Q`
that represents `P + Q` unless `P - Q` lies on the line, in which case all three vanish. The laws
attached to two lines meeting off the curve therefore form a complete system.

Mathlib's `WeierstrassCurve.Projective.addXYZ` is, up to a constant factor, the law attached to the
line `Z = 0`, which meets the curve only at the point at infinity; it vanishes on the diagonal
(`WeierstrassCurve.Projective.addXYZ_self`). This file defines the law attached to the line `Y = 0`,
which meets the line `Z = 0` at `(1 : 0 : 0)`, a point not on the curve. Its coordinates are given
as explicit polynomials in the coefficients of the curve and the coordinates of `P` and `Q`. On the
curve its diagonal is the doubling formula, so its coordinates are named `dblAddX`, `dblAddY` and
`dblAddZ`.

## Main definitions

* `WeierstrassCurve.Projective.dblAddX`, `dblAddY`, `dblAddZ`: the coordinates of the addition law
  attached to the line `Y = 0`.
* `WeierstrassCurve.Projective.dblAddXYZ`: the triple of these coordinates.

## Main results

* `WeierstrassCurve.Projective.dblAddXYZ_smul`: the law is bihomogeneous of bidegree `(2, 2)`.
* `WeierstrassCurve.Projective.dblAddXYZ_self`: on the curve, the diagonal of the law is Mathlib's
  doubling formula `dblXYZ`.
* `WeierstrassCurve.Projective.addX_mul_dblAddY`, `addX_mul_dblAddZ`, `addY_mul_dblAddZ` and
  `addXYZ_cross_dblAddXYZ`: for two point representatives on the curve, the `2 × 2` minors of the
  matrix with rows `addXYZ P Q` and `dblAddXYZ P Q` vanish, that is, the cross product of the two
  rows is zero.
* `WeierstrassCurve.Projective.equation_dblAddXYZ_of_nonsingular`: over a field, the law takes two
  nonsingular point representatives to a solution of the Weierstrass equation.
* `WeierstrassCurve.Projective.addXYZ_ne_zero_or_dblAddXYZ_ne_zero`: over a field, the laws
  `addXYZ` and `dblAddXYZ` do not vanish simultaneously at two nonsingular point representatives,
  which is the non-vanishing condition for the two laws to form a complete system.
* `WeierstrassCurve.Projective.add_of_addXYZ_ne_zero` and
  `WeierstrassCurve.Projective.dblAddXYZ_equiv_add`: a nonzero value of either law represents the
  sum `add P Q`, the second over a field and at nonsingular point representatives.
* `WeierstrassCurve.Projective.map_dblAddXYZ`: the law commutes with ring homomorphisms.
* `WeierstrassCurve.Projective.span_range_addXYZ_union_range_dblAddXYZ_eq_top`: over a
  commutative ring, at two unimodular solutions of the equation of an elliptic curve, the six
  coordinates of `addXYZ` and `dblAddXYZ` generate the unit ideal.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240: Theorem 2, the remark following it, and §5.

## Provenance

Ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, directory
`projects/ModularCurves/ModularCurves/EllipticCurve/`:
* from `AdditionLaw.lean`: `dblAddX`, `dblAddY`, `dblAddZ`, `dblAddXYZ`, their `_smul` and `_self`
  lemmas, `addX_mul_dblAddY`, `addX_mul_dblAddZ` and `addY_mul_dblAddZ`. Statements and
  polynomials are those of the source; each polynomial is regrouped by the monomials in the
  coordinates of one of the two points. The `XZ` certificate is the source's. The `XY` and `YZ`
  minors are instead reduced to minors involving `negY (dblAddXYZ P Q)`, whose certificates are
  linear combinations of the source's.
* from `AdditionLawField.lean`: `equation_dblAddXYZ` (as `equation_dblAddXYZ_of_nonsingular`) and
  `addXYZ_ne_zero_or_dblAddXYZ_ne_zero`. The source's proportionality lemma for vectors with
  vanishing `2 × 2` minors is replaced by Mathlib's
  `Projectivization.mk_eq_mk_iff_crossProduct_eq_zero`, through `addXYZ_cross_dblAddXYZ`.
* from `AdditionLawOnCurve.lean`: `map_dblAddX`, `map_dblAddY`, `map_dblAddZ` and `map_dblAddXYZ`,
  and `map_addXYZ_ne_zero_or_map_dblAddXYZ_ne_zero`, within
  `span_range_addXYZ_union_range_dblAddXYZ_eq_top`.
* from `AdditionChartDomain.lean`: `span_lawOneTriple_union_lawTwoTriple_eq_top`, as
  `span_range_addXYZ_union_range_dblAddXYZ_eq_top`. The source states it at the universal points of
  a product of two charts; here the points are arbitrary solutions whose coordinates generate the
  unit ideal.
* from `AdditionSpecPoints.lean`: `descended_lawOne_eq_add` and `descended_lawTwo_smul_add`, as
  `add_of_addXYZ_ne_zero` and `dblAddXYZ_equiv_add`. The source states them at the images in a
  field of the universal points of a product of two charts, the second as an equality up to a
  nonzero scalar; here the points are arbitrary representatives (nonsingular, for the second), and
  the first holds over any commutative ring.
-/

public section

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

/- The definitions and certificates below contain about a thousand numeric exponents. This rule
elaborates each one directly as a natural number. Without it, the type of each exponent is left to
default-instance resolution, and elaborating the statements of the three certificate lemmas exceeds
the default `maxHeartbeats`. -/
local macro_rules | `($a ^ $n:num) => `(rightact% HPow.hPow $a ($n : ℕ))

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] {W' : Projective R}

/-! ### The addition law attached to the line `Y = 0` -/

-- The `a₃a₄` term printed in Bosma–Lenstra, p. 237 is easily misread as `a₃a₄(X₁Z₂ - 2X₂Z₁)X₂Z₁`;
-- with the misread term, `dblAddX_self`, `addX_mul_dblAddY` and `addX_mul_dblAddZ` would be false.
variable (W') in
/-- The `X`-coordinate of the addition law attached to the line `Y = 0`, evaluated at two
projective point representatives `P` and `Q` on a Weierstrass curve. On the curve, its diagonal is
`dblX` (`dblAddX_self`).

With `P = (X₁ : Y₁ : Z₁)` and `Q = (X₂ : Y₂ : Z₂)`, the `a₃a₄` term of this polynomial, viewed as a
polynomial in the curve coefficients, is `-a₃a₄(2X₁Z₂ + X₂Z₁)X₂Z₁`, as printed in Bosma–Lenstra,
p. 237. -/
@[expose] def dblAddX (P Q : Fin 3 → R) : R :=
  P x ^ 2 * (-W'.a₁ * W'.a₂ * Q x ^ 2 - W'.a₂ * Q x * Q y - W'.a₁ ^ 2 * W'.a₃ * Q x * Q z
      - 2 * W'.a₁ * W'.a₄ * Q x * Q z - W'.a₁ * W'.a₃ * Q y * Q z - W'.a₄ * Q y * Q z
      - W'.a₁ * W'.a₃ ^ 2 * Q z ^ 2 - 3 * W'.a₁ * W'.a₆ * Q z ^ 2)
    + P x * P y * (W'.a₁ ^ 2 * Q x ^ 2 - W'.a₂ * Q x ^ 2 + 2 * W'.a₁ * Q x * Q y
      - 2 * W'.a₄ * Q x * Q z + Q y ^ 2 - W'.a₃ ^ 2 * Q z ^ 2 - 3 * W'.a₆ * Q z ^ 2)
    + P x * P z * (-W'.a₁ * W'.a₄ * Q x ^ 2 - W'.a₂ * W'.a₃ * Q x ^ 2 - 2 * W'.a₄ * Q x * Q y
      - 2 * W'.a₁ * W'.a₃ ^ 2 * Q x * Q z - 6 * W'.a₁ * W'.a₆ * Q x * Q z
      - 2 * W'.a₃ * W'.a₄ * Q x * Q z - 2 * W'.a₃ ^ 2 * Q y * Q z - 6 * W'.a₆ * Q y * Q z
      - W'.a₁ ^ 3 * W'.a₆ * Q z ^ 2 + W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * Q z ^ 2
      - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * Q z ^ 2 - 4 * W'.a₁ * W'.a₂ * W'.a₆ * Q z ^ 2
      + W'.a₁ * W'.a₄ ^ 2 * Q z ^ 2 - W'.a₃ ^ 3 * Q z ^ 2 - 3 * W'.a₃ * W'.a₆ * Q z ^ 2)
    + P y ^ 2 * (W'.a₁ * Q x ^ 2 + Q x * Q y + W'.a₃ * Q x * Q z)
    + P y * P z * (W'.a₁ * W'.a₃ * Q x ^ 2 - W'.a₄ * Q x ^ 2 + 2 * W'.a₃ * Q x * Q y
      - 6 * W'.a₆ * Q x * Q z - W'.a₁ ^ 2 * W'.a₆ * Q z ^ 2 + W'.a₁ * W'.a₃ * W'.a₄ * Q z ^ 2
      - W'.a₂ * W'.a₃ ^ 2 * Q z ^ 2 - 4 * W'.a₂ * W'.a₆ * Q z ^ 2 + W'.a₄ ^ 2 * Q z ^ 2)
    + P z ^ 2 * (-W'.a₃ * W'.a₄ * Q x ^ 2 - 3 * W'.a₆ * Q x * Q y - W'.a₃ ^ 3 * Q x * Q z
      - 6 * W'.a₃ * W'.a₆ * Q x * Q z - W'.a₁ ^ 2 * W'.a₆ * Q y * Q z
      + W'.a₁ * W'.a₃ * W'.a₄ * Q y * Q z - W'.a₂ * W'.a₃ ^ 2 * Q y * Q z
      - 4 * W'.a₂ * W'.a₆ * Q y * Q z + W'.a₄ ^ 2 * Q y * Q z - W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * Q z ^ 2
      + W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * Q z ^ 2 - W'.a₂ * W'.a₃ ^ 3 * Q z ^ 2
      - 4 * W'.a₂ * W'.a₃ * W'.a₆ * Q z ^ 2 + W'.a₃ * W'.a₄ ^ 2 * Q z ^ 2)

variable (W') in
/-- The `Y`-coordinate of the addition law attached to the line `Y = 0`, evaluated at two
projective point representatives `P` and `Q` on a Weierstrass curve. On the curve, its diagonal is
`dblY` (`dblAddY_self`). -/
@[expose] def dblAddY (P Q : Fin 3 → R) : R :=
  P x ^ 2 * (-W'.a₂ ^ 2 * Q x ^ 2 + 3 * W'.a₄ * Q x ^ 2 + W'.a₁ ^ 2 * W'.a₄ * Q x * Q z
      - 2 * W'.a₁ * W'.a₂ * W'.a₃ * Q x * Q z - W'.a₂ * W'.a₄ * Q x * Q z
      + 3 * W'.a₃ ^ 2 * Q x * Q z + 9 * W'.a₆ * Q x * Q z + 3 * W'.a₁ ^ 2 * W'.a₆ * Q z ^ 2
      - 2 * W'.a₁ * W'.a₃ * W'.a₄ * Q z ^ 2 + W'.a₂ * W'.a₃ ^ 2 * Q z ^ 2
      + 3 * W'.a₂ * W'.a₆ * Q z ^ 2 - W'.a₄ ^ 2 * Q z ^ 2)
    + P x * P y * (W'.a₁ * W'.a₂ * Q x ^ 2 - 3 * W'.a₃ * Q x ^ 2 + 2 * W'.a₁ * W'.a₄ * Q x * Q z
      - 2 * W'.a₂ * W'.a₃ * Q x * Q z + 3 * W'.a₁ * W'.a₆ * Q z ^ 2 - W'.a₃ * W'.a₄ * Q z ^ 2)
    + P x * P z * (-W'.a₂ * W'.a₄ * Q x ^ 2 + 9 * W'.a₆ * Q x ^ 2
      + 6 * W'.a₁ ^ 2 * W'.a₆ * Q x * Q z - 4 * W'.a₁ * W'.a₃ * W'.a₄ * Q x * Q z
      + 2 * W'.a₂ * W'.a₃ ^ 2 * Q x * Q z + 12 * W'.a₂ * W'.a₆ * Q x * Q z
      - 4 * W'.a₄ ^ 2 * Q x * Q z + W'.a₁ ^ 4 * W'.a₆ * Q z ^ 2
      - W'.a₁ ^ 3 * W'.a₃ * W'.a₄ * Q z ^ 2 + W'.a₁ ^ 2 * W'.a₂ * W'.a₃ ^ 2 * Q z ^ 2
      + 5 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * Q z ^ 2 - W'.a₁ ^ 2 * W'.a₄ ^ 2 * Q z ^ 2
      - W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * Q z ^ 2 - W'.a₁ * W'.a₃ ^ 3 * Q z ^ 2
      - 3 * W'.a₁ * W'.a₃ * W'.a₆ * Q z ^ 2 + W'.a₂ ^ 2 * W'.a₃ ^ 2 * Q z ^ 2
      + 4 * W'.a₂ ^ 2 * W'.a₆ * Q z ^ 2 - W'.a₂ * W'.a₄ ^ 2 * Q z ^ 2 - W'.a₃ ^ 2 * W'.a₄ * Q z ^ 2
      - 3 * W'.a₄ * W'.a₆ * Q z ^ 2)
    + P y ^ 2 * (W'.a₁ * Q x * Q y + Q y ^ 2 + W'.a₃ * Q y * Q z)
    + P y * P z * (W'.a₁ * W'.a₄ * Q x ^ 2 - W'.a₂ * W'.a₃ * Q x ^ 2 + 6 * W'.a₁ * W'.a₆ * Q x * Q z
      - 2 * W'.a₃ * W'.a₄ * Q x * Q z + W'.a₁ ^ 3 * W'.a₆ * Q z ^ 2
      - W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * Q z ^ 2 + W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * Q z ^ 2
      + 4 * W'.a₁ * W'.a₂ * W'.a₆ * Q z ^ 2 - W'.a₁ * W'.a₄ ^ 2 * Q z ^ 2 - W'.a₃ ^ 3 * Q z ^ 2
      - 3 * W'.a₃ * W'.a₆ * Q z ^ 2)
    + P z ^ 2 * (3 * W'.a₂ * W'.a₆ * Q x ^ 2 - W'.a₄ ^ 2 * Q x ^ 2
      + W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * Q x * Q z - W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * Q x * Q z
      + 3 * W'.a₁ * W'.a₃ * W'.a₆ * Q x * Q z + W'.a₂ ^ 2 * W'.a₃ ^ 2 * Q x * Q z
      + 4 * W'.a₂ ^ 2 * W'.a₆ * Q x * Q z - W'.a₂ * W'.a₄ ^ 2 * Q x * Q z
      - 2 * W'.a₃ ^ 2 * W'.a₄ * Q x * Q z - 3 * W'.a₄ * W'.a₆ * Q x * Q z
      + W'.a₁ ^ 3 * W'.a₃ * W'.a₆ * Q z ^ 2 - W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ * Q z ^ 2
      + W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * Q z ^ 2 + W'.a₁ * W'.a₂ * W'.a₃ ^ 3 * Q z ^ 2
      + 4 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ * Q z ^ 2 - 2 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * Q z ^ 2
      + W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * Q z ^ 2 + 4 * W'.a₂ * W'.a₄ * W'.a₆ * Q z ^ 2
      - W'.a₃ ^ 4 * Q z ^ 2 - 6 * W'.a₃ ^ 2 * W'.a₆ * Q z ^ 2 - W'.a₄ ^ 3 * Q z ^ 2
      - 9 * W'.a₆ ^ 2 * Q z ^ 2)

variable (W') in
/-- The `Z`-coordinate of the addition law attached to the line `Y = 0`, evaluated at two
projective point representatives `P` and `Q` on a Weierstrass curve. On the curve, its diagonal is
`dblZ` (`dblAddZ_self`). -/
@[expose] def dblAddZ (P Q : Fin 3 → R) : R :=
  P x ^ 2 * (3 * W'.a₁ * Q x ^ 2 + 3 * Q x * Q y + W'.a₁ ^ 3 * Q x * Q z
      + 2 * W'.a₁ * W'.a₂ * Q x * Q z + W'.a₁ ^ 2 * Q y * Q z + W'.a₂ * Q y * Q z
      + W'.a₁ ^ 2 * W'.a₃ * Q z ^ 2 + W'.a₁ * W'.a₄ * Q z ^ 2)
    + P x * P y * (3 * Q x ^ 2 + 2 * W'.a₁ ^ 2 * Q x * Q z + 2 * W'.a₂ * Q x * Q z
      + 2 * W'.a₁ * Q y * Q z + 2 * W'.a₁ * W'.a₃ * Q z ^ 2 + W'.a₄ * Q z ^ 2)
    + P x * P z * (W'.a₁ * W'.a₂ * Q x ^ 2 + 3 * W'.a₃ * Q x ^ 2 + 2 * W'.a₂ * Q x * Q y
      + 2 * W'.a₁ ^ 2 * W'.a₃ * Q x * Q z + 2 * W'.a₁ * W'.a₄ * Q x * Q z
      + 2 * W'.a₂ * W'.a₃ * Q x * Q z + 2 * W'.a₁ * W'.a₃ * Q y * Q z + 2 * W'.a₄ * Q y * Q z
      + 2 * W'.a₁ * W'.a₃ ^ 2 * Q z ^ 2 + 3 * W'.a₁ * W'.a₆ * Q z ^ 2 + W'.a₃ * W'.a₄ * Q z ^ 2)
    + P y ^ 2 * (W'.a₁ * Q x * Q z + Q y * Q z + W'.a₃ * Q z ^ 2)
    + P y * P z * (W'.a₂ * Q x ^ 2 + 2 * W'.a₁ * W'.a₃ * Q x * Q z + 2 * W'.a₄ * Q x * Q z + Q y ^ 2
      + 2 * W'.a₃ * Q y * Q z + 2 * W'.a₃ ^ 2 * Q z ^ 2 + 3 * W'.a₆ * Q z ^ 2)
    + P z ^ 2 * (W'.a₂ * W'.a₃ * Q x ^ 2 + W'.a₄ * Q x * Q y + W'.a₁ * W'.a₃ ^ 2 * Q x * Q z
      + 2 * W'.a₃ * W'.a₄ * Q x * Q z + W'.a₃ ^ 2 * Q y * Q z + 3 * W'.a₆ * Q y * Q z
      + W'.a₃ ^ 3 * Q z ^ 2 + 3 * W'.a₃ * W'.a₆ * Q z ^ 2)

variable (W') in
/-- The coordinates of the addition law attached to the line `Y = 0`, evaluated at two projective
point representatives `P` and `Q` on a Weierstrass curve. On the curve, its diagonal is `dblXYZ`
(`dblAddXYZ_self`). -/
def dblAddXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblAddX P Q, W'.dblAddY P Q, W'.dblAddZ P Q]

/-- The `X`-coordinate of `dblAddXYZ P Q` is `dblAddX P Q`. -/
@[simp]
theorem dblAddXYZ_X (P Q : Fin 3 → R) : W'.dblAddXYZ P Q x = W'.dblAddX P Q :=
  (rfl)

/-- The `Y`-coordinate of `dblAddXYZ P Q` is `dblAddY P Q`. -/
@[simp]
theorem dblAddXYZ_Y (P Q : Fin 3 → R) : W'.dblAddXYZ P Q y = W'.dblAddY P Q :=
  (rfl)

/-- The `Z`-coordinate of `dblAddXYZ P Q` is `dblAddZ P Q`. -/
@[simp]
theorem dblAddXYZ_Z (P Q : Fin 3 → R) : W'.dblAddXYZ P Q z = W'.dblAddZ P Q :=
  (rfl)

/-! ### Bihomogeneity -/

/-- The `X`-coordinate of the addition law attached to the line `Y = 0` is bihomogeneous of
bidegree `(2, 2)`. -/
theorem dblAddX_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddX (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddX P Q := by
  simp only [dblAddX, smul_fin3_ext]
  ring1

/-- The `Y`-coordinate of the addition law attached to the line `Y = 0` is bihomogeneous of
bidegree `(2, 2)`. -/
theorem dblAddY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddY (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddY P Q := by
  simp only [dblAddY, smul_fin3_ext]
  ring1

/-- The `Z`-coordinate of the addition law attached to the line `Y = 0` is bihomogeneous of
bidegree `(2, 2)`. -/
theorem dblAddZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddZ (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddZ P Q := by
  simp only [dblAddZ, smul_fin3_ext]
  ring1

/-- The addition law attached to the line `Y = 0` is bihomogeneous of bidegree `(2, 2)`: rescaling
the representatives `P` and `Q` by `u` and `v` rescales its value by `(u * v) ^ 2`. -/
theorem dblAddXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.dblAddXYZ P Q := by
  simp [dblAddXYZ, dblAddX_smul, dblAddY_smul, dblAddZ_smul]

/-! ### The diagonal is the doubling formula -/

/-- On the curve, the `X`-coordinate of the addition law attached to the line `Y = 0` agrees on the
diagonal with the `X`-coordinate `dblX` of Mathlib's doubling formula. -/
theorem dblAddX_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddX P P = W'.dblX P := by
  linear_combination (norm := (rw [dblAddX, dblX]; ring1))
    (W'.a₁ ^ 3 * P x + 4 * W'.a₁ * W'.a₂ * P x + 9 * W'.a₃ * P x + 2 * W'.a₁ ^ 2 * P y
      + 8 * W'.a₂ * P y + W'.a₁ ^ 2 * W'.a₃ * P z + 4 * W'.a₂ * W'.a₃ * P z)
      * (equation_iff _).mp hP

/-- On the curve, the `Y`-coordinate of the addition law attached to the line `Y = 0` agrees on the
diagonal with the `Y`-coordinate `dblY` of Mathlib's doubling formula. -/
theorem dblAddY_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddY P P = W'.dblY P := by
  linear_combination (norm := (rw [dblAddY, dblY, negY_eq, negDblY, dblX, dblZ, negY]; ring1))
    (-W'.a₁ ^ 4 * P x - 6 * W'.a₁ ^ 2 * W'.a₂ * P x - 8 * W'.a₂ ^ 2 * P x - 3 * W'.a₄ * P x
      - W'.a₁ ^ 3 * P y - 4 * W'.a₁ * W'.a₂ * P y + 12 * W'.a₃ * P y - W'.a₁ ^ 3 * W'.a₃ * P z
      - W'.a₁ ^ 2 * W'.a₄ * P z - 4 * W'.a₁ * W'.a₂ * W'.a₃ * P z - 4 * W'.a₂ * W'.a₄ * P z
      + 6 * W'.a₃ ^ 2 * P z + 9 * W'.a₆ * P z) * (equation_iff _).mp hP

/-- On the curve, the `Z`-coordinate of the addition law attached to the line `Y = 0` agrees on the
diagonal with the `Z`-coordinate `dblZ` of Mathlib's doubling formula. -/
theorem dblAddZ_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddZ P P = W'.dblZ P := by
  linear_combination (norm := (rw [dblAddZ, dblZ, negY]; ring1))
    (-3 * W'.a₁ * P x - 6 * P y - 3 * W'.a₃ * P z) * (equation_iff _).mp hP

/-- On the curve, the diagonal of the addition law attached to the line `Y = 0` is Mathlib's
doubling formula `dblXYZ`. -/
theorem dblAddXYZ_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddXYZ P P = W'.dblXYZ P := by
  rw [dblAddXYZ, dblAddX_self hP, dblAddY_self hP, dblAddZ_self hP, dblXYZ]

/-! ### The two laws are proportional on the curve -/

-- The `XZ` minor of the matrix with rows `addXYZ P Q` and `dblAddXYZ P Q`, as a combination
-- of the Weierstrass polynomial evaluated at `P` and at `Q`.
private theorem addX_mul_dblAddZ_sub_addZ_mul_dblAddX (P Q : Fin 3 → R) :
    W'.addX P Q * W'.dblAddZ P Q - W'.addZ P Q * W'.dblAddX P Q =
      MvPolynomial.eval P W'.polynomial * (P x * (3 * Q x ^ 3 * Q y + W'.a₁ ^ 3 * Q x ^ 3 * Q z
          + W'.a₁ * W'.a₂ * Q x ^ 3 * Q z + 6 * W'.a₃ * Q x ^ 3 * Q z
          + 3 * W'.a₁ ^ 2 * Q x ^ 2 * Q y * Q z + 3 * W'.a₂ * Q x ^ 2 * Q y * Q z
          + 3 * W'.a₁ ^ 2 * W'.a₃ * Q x ^ 2 * Q z ^ 2 + 3 * W'.a₁ * W'.a₄ * Q x ^ 2 * Q z ^ 2
          + 6 * W'.a₂ * W'.a₃ * Q x ^ 2 * Q z ^ 2 - 3 * W'.a₁ * W'.a₃ * Q x * Q y * Q z ^ 2
          + 3 * W'.a₄ * Q x * Q y * Q z ^ 2 + 3 * W'.a₁ * W'.a₃ ^ 2 * Q x * Q z ^ 3
          + 9 * W'.a₁ * W'.a₆ * Q x * Q z ^ 3 + 6 * W'.a₃ * W'.a₄ * Q x * Q z ^ 3
          - 3 * Q y ^ 3 * Q z - 9 * W'.a₃ * Q y ^ 2 * Q z ^ 2 - 6 * W'.a₃ ^ 2 * Q y * Q z ^ 3
          + 3 * W'.a₆ * Q y * Q z ^ 3 + W'.a₁ ^ 3 * W'.a₆ * Q z ^ 4
          - W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * Q z ^ 4 + W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * Q z ^ 4
          + 4 * W'.a₁ * W'.a₂ * W'.a₆ * Q z ^ 4 - W'.a₁ * W'.a₄ ^ 2 * Q z ^ 4
          + 6 * W'.a₃ * W'.a₆ * Q z ^ 4)
        + P y * (W'.a₁ ^ 2 * Q x ^ 3 * Q z + W'.a₂ * Q x ^ 3 * Q z + 3 * W'.a₁ * Q x ^ 2 * Q y * Q z
          + 3 * W'.a₁ * W'.a₃ * Q x ^ 2 * Q z ^ 2 + 3 * W'.a₄ * Q x ^ 2 * Q z ^ 2
          + 3 * Q x * Q y ^ 2 * Q z + 3 * W'.a₃ * Q x * Q y * Q z ^ 2
          + 3 * W'.a₃ ^ 2 * Q x * Q z ^ 3 + 9 * W'.a₆ * Q x * Q z ^ 3 + W'.a₁ ^ 2 * W'.a₆ * Q z ^ 4
          - W'.a₁ * W'.a₃ * W'.a₄ * Q z ^ 4 + W'.a₂ * W'.a₃ ^ 2 * Q z ^ 4
          + 4 * W'.a₂ * W'.a₆ * Q z ^ 4 - W'.a₄ ^ 2 * Q z ^ 4)
        + P z * (W'.a₁ ^ 2 * Q x ^ 3 * Q y + W'.a₂ * Q x ^ 3 * Q y
          + W'.a₁ ^ 2 * W'.a₃ * Q x ^ 3 * Q z + W'.a₂ * W'.a₃ * Q x ^ 3 * Q z
          + 3 * W'.a₁ * Q x ^ 2 * Q y ^ 2 + 6 * W'.a₁ * W'.a₃ * Q x ^ 2 * Q y * Q z
          + 3 * W'.a₄ * Q x ^ 2 * Q y * Q z + 3 * W'.a₁ * W'.a₃ ^ 2 * Q x ^ 2 * Q z ^ 2
          + 3 * W'.a₃ * W'.a₄ * Q x ^ 2 * Q z ^ 2 + 3 * Q x * Q y ^ 3
          + 6 * W'.a₃ * Q x * Q y ^ 2 * Q z + 6 * W'.a₃ ^ 2 * Q x * Q y * Q z ^ 2
          + 9 * W'.a₆ * Q x * Q y * Q z ^ 2 + 3 * W'.a₃ ^ 3 * Q x * Q z ^ 3
          + 9 * W'.a₃ * W'.a₆ * Q x * Q z ^ 3 + W'.a₁ ^ 2 * W'.a₆ * Q y * Q z ^ 3
          - W'.a₁ * W'.a₃ * W'.a₄ * Q y * Q z ^ 3 + W'.a₂ * W'.a₃ ^ 2 * Q y * Q z ^ 3
          + 4 * W'.a₂ * W'.a₆ * Q y * Q z ^ 3 - W'.a₄ ^ 2 * Q y * Q z ^ 3
          + W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * Q z ^ 4 - W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * Q z ^ 4
          + W'.a₂ * W'.a₃ ^ 3 * Q z ^ 4 + 4 * W'.a₂ * W'.a₃ * W'.a₆ * Q z ^ 4
          - W'.a₃ * W'.a₄ ^ 2 * Q z ^ 4))
      + MvPolynomial.eval Q W'.polynomial * (Q y * (-3 * P x ^ 4 - W'.a₁ ^ 2 * P x ^ 3 * P z
          - 4 * W'.a₂ * P x ^ 3 * P z - 3 * W'.a₁ * W'.a₃ * P x ^ 2 * P z ^ 2
          - 6 * W'.a₄ * P x ^ 2 * P z ^ 2 - 3 * W'.a₃ ^ 2 * P x * P z ^ 3
          - 12 * W'.a₆ * P x * P z ^ 3 - W'.a₁ ^ 2 * W'.a₆ * P z ^ 4
          + W'.a₁ * W'.a₃ * W'.a₄ * P z ^ 4 - W'.a₂ * W'.a₃ ^ 2 * P z ^ 4
          - 4 * W'.a₂ * W'.a₆ * P z ^ 4 + W'.a₄ ^ 2 * P z ^ 4)
        + Q z * (-W'.a₁ ^ 3 * P x ^ 4 - W'.a₁ * W'.a₂ * P x ^ 4 - 6 * W'.a₃ * P x ^ 4
          - 4 * W'.a₁ ^ 2 * P x ^ 3 * P y - W'.a₂ * P x ^ 3 * P y
          - 4 * W'.a₁ ^ 2 * W'.a₃ * P x ^ 3 * P z - 3 * W'.a₁ * W'.a₄ * P x ^ 3 * P z
          - 7 * W'.a₂ * W'.a₃ * P x ^ 3 * P z - 6 * W'.a₁ * P x ^ 2 * P y ^ 2
          - 3 * W'.a₁ * W'.a₃ * P x ^ 2 * P y * P z - 3 * W'.a₄ * P x ^ 2 * P y * P z
          - 6 * W'.a₁ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 - 9 * W'.a₁ * W'.a₆ * P x ^ 2 * P z ^ 2
          - 9 * W'.a₃ * W'.a₄ * P x ^ 2 * P z ^ 2 - 3 * P x * P y ^ 3
          - 9 * W'.a₆ * P x * P y * P z ^ 2 - W'.a₁ ^ 3 * W'.a₆ * P x * P z ^ 3
          + W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P x * P z ^ 3 - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P x * P z ^ 3
          - 4 * W'.a₁ * W'.a₂ * W'.a₆ * P x * P z ^ 3 + W'.a₁ * W'.a₄ ^ 2 * P x * P z ^ 3
          - 3 * W'.a₃ ^ 3 * P x * P z ^ 3 - 15 * W'.a₃ * W'.a₆ * P x * P z ^ 3
          - W'.a₁ ^ 2 * W'.a₆ * P y * P z ^ 3 + W'.a₁ * W'.a₃ * W'.a₄ * P y * P z ^ 3
          - W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3 - 4 * W'.a₂ * W'.a₆ * P y * P z ^ 3
          + W'.a₄ ^ 2 * P y * P z ^ 3 - W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * P z ^ 4
          + W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4 - W'.a₂ * W'.a₃ ^ 3 * P z ^ 4
          - 4 * W'.a₂ * W'.a₃ * W'.a₆ * P z ^ 4 + W'.a₃ * W'.a₄ ^ 2 * P z ^ 4)) := by
  rw [eval_polynomial, eval_polynomial]
  simp only [addX, addZ, dblAddX, dblAddZ]
  ring1

/-- For two point representatives on the curve, the `XZ` minor of the matrix with rows
`addXYZ P Q` and `dblAddXYZ P Q` vanishes. -/
theorem addX_mul_dblAddZ {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * W'.dblAddZ P Q = W'.addZ P Q * W'.dblAddX P Q := by
  rw [← sub_eq_zero, addX_mul_dblAddZ_sub_addZ_mul_dblAddX, hP, hQ, zero_mul, zero_mul, add_zero]

-- With `N = negY (dblAddXYZ P Q)`, the minor `addX P Q * N - negAddY P Q * dblAddX P Q`, as a
-- combination of the Weierstrass polynomial evaluated at `P` and at `Q`.
private theorem addX_mul_negY_dblAddXYZ_sub_negAddY_mul_dblAddX (P Q : Fin 3 → R) :
    W'.addX P Q * W'.negY (W'.dblAddXYZ P Q) - W'.negAddY P Q * W'.dblAddX P Q =
      MvPolynomial.eval P W'.polynomial * (P x * (W'.a₁ ^ 2 * W'.a₂ * Q x ^ 4
          - 3 * W'.a₁ * W'.a₃ * Q x ^ 4 + W'.a₂ ^ 2 * Q x ^ 4 + 3 * W'.a₄ * Q x ^ 4
          + 3 * W'.a₁ * W'.a₂ * Q x ^ 3 * Q y - 6 * W'.a₃ * Q x ^ 3 * Q y
          + W'.a₁ ^ 2 * W'.a₄ * Q x ^ 3 * Q z + 7 * W'.a₂ * W'.a₄ * Q x ^ 3 * Q z
          - 3 * W'.a₃ ^ 2 * Q x ^ 3 * Q z + 9 * W'.a₆ * Q x ^ 3 * Q z
          + 3 * W'.a₂ * Q x ^ 2 * Q y ^ 2 + 3 * W'.a₁ ^ 2 * W'.a₃ * Q x ^ 2 * Q y * Q z
          - 3 * W'.a₂ * W'.a₃ * Q x ^ 2 * Q y * Q z + 18 * W'.a₂ * W'.a₆ * Q x ^ 2 * Q z ^ 2
          + 6 * W'.a₄ ^ 2 * Q x ^ 2 * Q z ^ 2 + 9 * W'.a₁ * W'.a₃ * Q x * Q y ^ 2 * Q z
          + 6 * W'.a₁ * W'.a₃ ^ 2 * Q x * Q y * Q z ^ 2 - 9 * W'.a₁ * W'.a₆ * Q x * Q y * Q z ^ 2
          - 6 * W'.a₃ * W'.a₄ * Q x * Q y * Q z ^ 2 + W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * Q x * Q z ^ 3
          - W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * Q x * Q z ^ 3
          - 3 * W'.a₁ * W'.a₃ * W'.a₆ * Q x * Q z ^ 3 + W'.a₂ ^ 2 * W'.a₃ ^ 2 * Q x * Q z ^ 3
          + 4 * W'.a₂ ^ 2 * W'.a₆ * Q x * Q z ^ 3 - W'.a₂ * W'.a₄ ^ 2 * Q x * Q z ^ 3
          + 21 * W'.a₄ * W'.a₆ * Q x * Q z ^ 3 + 6 * W'.a₃ * Q y ^ 3 * Q z
          + 9 * W'.a₃ ^ 2 * Q y ^ 2 * Q z ^ 2 - 9 * W'.a₆ * Q y ^ 2 * Q z ^ 2
          + 3 * W'.a₃ ^ 3 * Q y * Q z ^ 3 - 15 * W'.a₃ * W'.a₆ * Q y * Q z ^ 3
          + W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * Q z ^ 4 - W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * Q z ^ 4
          + W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * Q z ^ 4 + 4 * W'.a₂ * W'.a₄ * W'.a₆ * Q z ^ 4
          - 3 * W'.a₃ ^ 2 * W'.a₆ * Q z ^ 4 - W'.a₄ ^ 3 * Q z ^ 4 + 9 * W'.a₆ ^ 2 * Q z ^ 4)
          + P y * (-W'.a₁ ^ 3 * Q x ^ 4 - W'.a₁ * W'.a₂ * Q x ^ 4 - 4 * W'.a₁ ^ 2 * Q x ^ 3 * Q y
          - W'.a₂ * Q x ^ 3 * Q y - 4 * W'.a₁ ^ 2 * W'.a₃ * Q x ^ 3 * Q z
          - 3 * W'.a₁ * W'.a₄ * Q x ^ 3 * Q z - W'.a₂ * W'.a₃ * Q x ^ 3 * Q z
          - 6 * W'.a₁ * Q x ^ 2 * Q y ^ 2 - 9 * W'.a₁ * W'.a₃ * Q x ^ 2 * Q y * Q z
          - 3 * W'.a₄ * Q x ^ 2 * Q y * Q z - 6 * W'.a₁ * W'.a₃ ^ 2 * Q x ^ 2 * Q z ^ 2
          - 9 * W'.a₁ * W'.a₆ * Q x ^ 2 * Q z ^ 2 - 3 * W'.a₃ * W'.a₄ * Q x ^ 2 * Q z ^ 2
          - 3 * Q x * Q y ^ 3 - 6 * W'.a₃ * Q x * Q y ^ 2 * Q z
          - 6 * W'.a₃ ^ 2 * Q x * Q y * Q z ^ 2 - 9 * W'.a₆ * Q x * Q y * Q z ^ 2
          - W'.a₁ ^ 3 * W'.a₆ * Q x * Q z ^ 3 + W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * Q x * Q z ^ 3
          - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * Q x * Q z ^ 3 - 4 * W'.a₁ * W'.a₂ * W'.a₆ * Q x * Q z ^ 3
          + W'.a₁ * W'.a₄ ^ 2 * Q x * Q z ^ 3 - 3 * W'.a₃ ^ 3 * Q x * Q z ^ 3
          - 9 * W'.a₃ * W'.a₆ * Q x * Q z ^ 3 - W'.a₁ ^ 2 * W'.a₆ * Q y * Q z ^ 3
          + W'.a₁ * W'.a₃ * W'.a₄ * Q y * Q z ^ 3 - W'.a₂ * W'.a₃ ^ 2 * Q y * Q z ^ 3
          - 4 * W'.a₂ * W'.a₆ * Q y * Q z ^ 3 + W'.a₄ ^ 2 * Q y * Q z ^ 3
          - W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * Q z ^ 4 + W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * Q z ^ 4
          - W'.a₂ * W'.a₃ ^ 3 * Q z ^ 4 - 4 * W'.a₂ * W'.a₃ * W'.a₆ * Q z ^ 4
          + W'.a₃ * W'.a₄ ^ 2 * Q z ^ 4) + P z * (W'.a₁ ^ 2 * W'.a₄ * Q x ^ 4
          + W'.a₂ * W'.a₄ * Q x ^ 4 - W'.a₁ ^ 2 * W'.a₃ * Q x ^ 3 * Q y
          + 3 * W'.a₁ * W'.a₄ * Q x ^ 3 * Q y - W'.a₂ * W'.a₃ * Q x ^ 3 * Q y
          + 3 * W'.a₁ ^ 2 * W'.a₆ * Q x ^ 3 * Q z + 3 * W'.a₁ * W'.a₃ * W'.a₄ * Q x ^ 3 * Q z
          + 3 * W'.a₂ * W'.a₆ * Q x ^ 3 * Q z + 3 * W'.a₄ ^ 2 * Q x ^ 3 * Q z
          - 3 * W'.a₁ * W'.a₃ * Q x ^ 2 * Q y ^ 2 + 3 * W'.a₄ * Q x ^ 2 * Q y ^ 2
          - 3 * W'.a₁ * W'.a₃ ^ 2 * Q x ^ 2 * Q y * Q z + 9 * W'.a₁ * W'.a₆ * Q x ^ 2 * Q y * Q z
          + 9 * W'.a₁ * W'.a₃ * W'.a₆ * Q x ^ 2 * Q z ^ 2
          + 3 * W'.a₃ ^ 2 * W'.a₄ * Q x ^ 2 * Q z ^ 2 + 18 * W'.a₄ * W'.a₆ * Q x ^ 2 * Q z ^ 2
          - 3 * W'.a₃ * Q x * Q y ^ 3 - 3 * W'.a₃ ^ 2 * Q x * Q y ^ 2 * Q z
          + 9 * W'.a₆ * Q x * Q y ^ 2 * Q z - 3 * W'.a₃ ^ 3 * Q x * Q y * Q z ^ 2
          + W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * Q x * Q z ^ 3 - W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * Q x * Q z ^ 3
          + W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * Q x * Q z ^ 3 + 4 * W'.a₂ * W'.a₄ * W'.a₆ * Q x * Q z ^ 3
          + 9 * W'.a₃ ^ 2 * W'.a₆ * Q x * Q z ^ 3 - W'.a₄ ^ 3 * Q x * Q z ^ 3
          + 27 * W'.a₆ ^ 2 * Q x * Q z ^ 3 - W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * Q y * Q z ^ 3
          + W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * Q y * Q z ^ 3 - W'.a₂ * W'.a₃ ^ 3 * Q y * Q z ^ 3
          - 4 * W'.a₂ * W'.a₃ * W'.a₆ * Q y * Q z ^ 3 + W'.a₃ * W'.a₄ ^ 2 * Q y * Q z ^ 3
          + 3 * W'.a₁ ^ 2 * W'.a₆ ^ 2 * Q z ^ 4 - 3 * W'.a₁ * W'.a₃ * W'.a₄ * W'.a₆ * Q z ^ 4
          + 3 * W'.a₂ * W'.a₃ ^ 2 * W'.a₆ * Q z ^ 4 + 12 * W'.a₂ * W'.a₆ ^ 2 * Q z ^ 4
          - 3 * W'.a₄ ^ 2 * W'.a₆ * Q z ^ 4))
      + MvPolynomial.eval Q W'.polynomial * (Q x * (-W'.a₁ ^ 2 * W'.a₂ * P x ^ 4
          + 3 * W'.a₁ * W'.a₃ * P x ^ 4 - W'.a₂ ^ 2 * P x ^ 4 - 3 * W'.a₄ * P x ^ 4
          + W'.a₁ ^ 3 * P x ^ 3 * P y - 2 * W'.a₁ * W'.a₂ * P x ^ 3 * P y
          - W'.a₁ ^ 2 * W'.a₄ * P x ^ 3 * P z - 7 * W'.a₂ * W'.a₄ * P x ^ 3 * P z
          + 3 * W'.a₁ ^ 2 * P x ^ 2 * P y ^ 2 - 3 * W'.a₂ * P x ^ 2 * P y ^ 2
          + 3 * W'.a₁ * W'.a₄ * P x ^ 2 * P y * P z - 3 * W'.a₂ * W'.a₃ * P x ^ 2 * P y * P z
          - 3 * W'.a₂ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 - 9 * W'.a₂ * W'.a₆ * P x ^ 2 * P z ^ 2
          - 6 * W'.a₄ ^ 2 * P x ^ 2 * P z ^ 2 + 3 * W'.a₁ * P x * P y ^ 3
          + 9 * W'.a₁ * W'.a₆ * P x * P y * P z ^ 2 - W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P x * P z ^ 3
          + W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P x * P z ^ 3
          + 3 * W'.a₁ * W'.a₃ * W'.a₆ * P x * P z ^ 3 - W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * P z ^ 3
          - 4 * W'.a₂ ^ 2 * W'.a₆ * P x * P z ^ 3 + W'.a₂ * W'.a₄ ^ 2 * P x * P z ^ 3
          - 3 * W'.a₃ ^ 2 * W'.a₄ * P x * P z ^ 3 - 12 * W'.a₄ * W'.a₆ * P x * P z ^ 3
          + W'.a₁ ^ 3 * W'.a₆ * P y * P z ^ 3 - W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P y * P z ^ 3
          + W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3 + 4 * W'.a₁ * W'.a₂ * W'.a₆ * P y * P z ^ 3
          - W'.a₁ * W'.a₄ ^ 2 * P y * P z ^ 3 - W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P z ^ 4
          + W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P z ^ 4 - W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4
          - 4 * W'.a₂ * W'.a₄ * W'.a₆ * P z ^ 4 + W'.a₄ ^ 3 * P z ^ 4) + Q y * (6 * W'.a₃ * P x ^ 4
          + W'.a₁ ^ 2 * P x ^ 3 * P y + W'.a₂ * P x ^ 3 * P y + W'.a₁ ^ 2 * W'.a₃ * P x ^ 3 * P z
          + 7 * W'.a₂ * W'.a₃ * P x ^ 3 * P z + 3 * W'.a₁ * P x ^ 2 * P y ^ 2
          + 3 * W'.a₄ * P x ^ 2 * P y * P z + 3 * W'.a₁ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2
          + 9 * W'.a₃ * W'.a₄ * P x ^ 2 * P z ^ 2 + 3 * P x * P y ^ 3
          + 9 * W'.a₆ * P x * P y * P z ^ 2 + 3 * W'.a₃ ^ 3 * P x * P z ^ 3
          + 15 * W'.a₃ * W'.a₆ * P x * P z ^ 3 + W'.a₁ ^ 2 * W'.a₆ * P y * P z ^ 3
          - W'.a₁ * W'.a₃ * W'.a₄ * P y * P z ^ 3 + W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3
          + 4 * W'.a₂ * W'.a₆ * P y * P z ^ 3 - W'.a₄ ^ 2 * P y * P z ^ 3
          + W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * P z ^ 4 - W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4
          + W'.a₂ * W'.a₃ ^ 3 * P z ^ 4 + 4 * W'.a₂ * W'.a₃ * W'.a₆ * P z ^ 4
          - W'.a₃ * W'.a₄ ^ 2 * P z ^ 4) + Q z * (-W'.a₁ ^ 2 * W'.a₄ * P x ^ 4
          - W'.a₂ * W'.a₄ * P x ^ 4 + 3 * W'.a₃ ^ 2 * P x ^ 4 - 9 * W'.a₆ * P x ^ 4
          + W'.a₁ ^ 2 * W'.a₃ * P x ^ 3 * P y - 3 * W'.a₁ * W'.a₄ * P x ^ 3 * P y
          + W'.a₂ * W'.a₃ * P x ^ 3 * P y - 3 * W'.a₁ ^ 2 * W'.a₆ * P x ^ 3 * P z
          - 3 * W'.a₁ * W'.a₃ * W'.a₄ * P x ^ 3 * P z + 3 * W'.a₂ * W'.a₃ ^ 2 * P x ^ 3 * P z
          - 12 * W'.a₂ * W'.a₆ * P x ^ 3 * P z - 3 * W'.a₄ ^ 2 * P x ^ 3 * P z
          + 3 * W'.a₁ * W'.a₃ * P x ^ 2 * P y ^ 2 - 3 * W'.a₄ * P x ^ 2 * P y ^ 2
          - 9 * W'.a₁ * W'.a₃ * W'.a₆ * P x ^ 2 * P z ^ 2 - 27 * W'.a₄ * W'.a₆ * P x ^ 2 * P z ^ 2
          + 3 * W'.a₃ * P x * P y ^ 3 + 9 * W'.a₃ * W'.a₆ * P x * P y * P z ^ 2
          - W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P x * P z ^ 3 + W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P x * P z ^ 3
          - W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P x * P z ^ 3 - 4 * W'.a₂ * W'.a₄ * W'.a₆ * P x * P z ^ 3
          - 6 * W'.a₃ ^ 2 * W'.a₆ * P x * P z ^ 3 + W'.a₄ ^ 3 * P x * P z ^ 3
          - 36 * W'.a₆ ^ 2 * P x * P z ^ 3 + W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * P y * P z ^ 3
          - W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P y * P z ^ 3 + W'.a₂ * W'.a₃ ^ 3 * P y * P z ^ 3
          + 4 * W'.a₂ * W'.a₃ * W'.a₆ * P y * P z ^ 3 - W'.a₃ * W'.a₄ ^ 2 * P y * P z ^ 3
          - 3 * W'.a₁ ^ 2 * W'.a₆ ^ 2 * P z ^ 4 + 3 * W'.a₁ * W'.a₃ * W'.a₄ * W'.a₆ * P z ^ 4
          - 3 * W'.a₂ * W'.a₃ ^ 2 * W'.a₆ * P z ^ 4 - 12 * W'.a₂ * W'.a₆ ^ 2 * P z ^ 4
          + 3 * W'.a₄ ^ 2 * W'.a₆ * P z ^ 4)) := by
  rw [dblAddXYZ, negY_eq, eval_polynomial, eval_polynomial]
  simp only [addX, negAddY, dblAddX, dblAddY, dblAddZ]
  ring1

/-- For two point representatives on the curve, the `XY` minor of the matrix with rows
`addXYZ P Q` and `dblAddXYZ P Q` vanishes. -/
theorem addX_mul_dblAddY {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * W'.dblAddY P Q = W'.addY P Q * W'.dblAddX P Q := by
  have h := addX_mul_negY_dblAddXYZ_sub_negAddY_mul_dblAddX (W' := W') P Q
  rw [hP, hQ, zero_mul, zero_mul, add_zero, dblAddXYZ, negY_eq] at h
  rw [addY, negY_eq]
  linear_combination -h - W'.a₃ * addX_mul_dblAddZ hP hQ

-- With `N = negY (dblAddXYZ P Q)`, the minor `negAddY P Q * dblAddZ P Q - addZ P Q * N`, as a
-- combination of the Weierstrass polynomial evaluated at `P` and at `Q`.
private theorem negAddY_mul_dblAddZ_sub_addZ_mul_negY_dblAddXYZ (P Q : Fin 3 → R) :
    W'.negAddY P Q * W'.dblAddZ P Q - W'.addZ P Q * W'.negY (W'.dblAddXYZ P Q) =
      MvPolynomial.eval P W'.polynomial * (P x * (3 * W'.a₁ ^ 2 * Q x ^ 4 + 6 * W'.a₂ * Q x ^ 4
          + 6 * W'.a₁ * Q x ^ 3 * Q y + W'.a₁ ^ 2 * W'.a₂ * Q x ^ 3 * Q z
          + 9 * W'.a₁ * W'.a₃ * Q x ^ 3 * Q z + 4 * W'.a₂ ^ 2 * Q x ^ 3 * Q z
          + 12 * W'.a₄ * Q x ^ 3 * Q z + 9 * Q x ^ 2 * Q y ^ 2
          - 3 * W'.a₁ * W'.a₂ * Q x ^ 2 * Q y * Q z + 9 * W'.a₃ * Q x ^ 2 * Q y * Q z
          + 3 * W'.a₁ * W'.a₂ * W'.a₃ * Q x ^ 2 * Q z ^ 2 + 9 * W'.a₂ * W'.a₄ * Q x ^ 2 * Q z ^ 2
          + 9 * W'.a₃ ^ 2 * Q x ^ 2 * Q z ^ 2 + 27 * W'.a₆ * Q x ^ 2 * Q z ^ 2
          + 3 * W'.a₁ ^ 2 * Q x * Q y ^ 2 * Q z - 6 * W'.a₁ * W'.a₄ * Q x * Q y * Q z ^ 2
          + 3 * W'.a₁ ^ 2 * W'.a₆ * Q x * Q z ^ 3 - 3 * W'.a₁ * W'.a₃ * W'.a₄ * Q x * Q z ^ 3
          + 6 * W'.a₂ * W'.a₃ ^ 2 * Q x * Q z ^ 3 + 24 * W'.a₂ * W'.a₆ * Q x * Q z ^ 3
          + 3 * W'.a₁ * Q y ^ 3 * Q z + 3 * W'.a₁ * W'.a₃ * Q y ^ 2 * Q z ^ 2
          - 3 * W'.a₄ * Q y ^ 2 * Q z ^ 2 - 3 * W'.a₁ * W'.a₆ * Q y * Q z ^ 3
          - 3 * W'.a₃ * W'.a₄ * Q y * Q z ^ 3 + W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * Q z ^ 4
          - W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * Q z ^ 4 + W'.a₂ ^ 2 * W'.a₃ ^ 2 * Q z ^ 4
          + 4 * W'.a₂ ^ 2 * W'.a₆ * Q z ^ 4 - W'.a₂ * W'.a₄ ^ 2 * Q z ^ 4
          + 3 * W'.a₄ * W'.a₆ * Q z ^ 4) + P z * (W'.a₁ ^ 2 * W'.a₂ * Q x ^ 4 + W'.a₂ ^ 2 * Q x ^ 4
          - W'.a₁ ^ 3 * Q x ^ 3 * Q y + 2 * W'.a₁ * W'.a₂ * Q x ^ 3 * Q y
          + W'.a₁ ^ 2 * W'.a₄ * Q x ^ 3 * Q z + 3 * W'.a₁ * W'.a₂ * W'.a₃ * Q x ^ 3 * Q z
          + 4 * W'.a₂ * W'.a₄ * Q x ^ 3 * Q z - 3 * W'.a₁ ^ 2 * Q x ^ 2 * Q y ^ 2
          + 3 * W'.a₂ * Q x ^ 2 * Q y ^ 2 - 3 * W'.a₁ ^ 2 * W'.a₃ * Q x ^ 2 * Q y * Q z
          + 3 * W'.a₂ * W'.a₃ * Q x ^ 2 * Q y * Q z + 3 * W'.a₁ * W'.a₃ * W'.a₄ * Q x ^ 2 * Q z ^ 2
          + 3 * W'.a₂ * W'.a₃ ^ 2 * Q x ^ 2 * Q z ^ 2 + 9 * W'.a₂ * W'.a₆ * Q x ^ 2 * Q z ^ 2
          + 3 * W'.a₄ ^ 2 * Q x ^ 2 * Q z ^ 2 - 3 * W'.a₁ * Q x * Q y ^ 3
          - 3 * W'.a₁ * W'.a₃ * Q x * Q y ^ 2 * Q z + 3 * W'.a₄ * Q x * Q y ^ 2 * Q z
          - 3 * W'.a₁ * W'.a₃ ^ 2 * Q x * Q y * Q z ^ 2 - 9 * W'.a₁ * W'.a₆ * Q x * Q y * Q z ^ 2
          + 3 * W'.a₃ * W'.a₄ * Q x * Q y * Q z ^ 2 + W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * Q x * Q z ^ 3
          - W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * Q x * Q z ^ 3 + W'.a₂ ^ 2 * W'.a₃ ^ 2 * Q x * Q z ^ 3
          + 4 * W'.a₂ ^ 2 * W'.a₆ * Q x * Q z ^ 3 - W'.a₂ * W'.a₄ ^ 2 * Q x * Q z ^ 3
          + 3 * W'.a₃ ^ 2 * W'.a₄ * Q x * Q z ^ 3 + 9 * W'.a₄ * W'.a₆ * Q x * Q z ^ 3
          - W'.a₁ ^ 3 * W'.a₆ * Q y * Q z ^ 3 + W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * Q y * Q z ^ 3
          - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * Q y * Q z ^ 3 - 4 * W'.a₁ * W'.a₂ * W'.a₆ * Q y * Q z ^ 3
          + W'.a₁ * W'.a₄ ^ 2 * Q y * Q z ^ 3 + W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * Q z ^ 4
          - W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * Q z ^ 4 + W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * Q z ^ 4
          + 4 * W'.a₂ * W'.a₄ * W'.a₆ * Q z ^ 4 - W'.a₄ ^ 3 * Q z ^ 4))
      + MvPolynomial.eval Q W'.polynomial * (Q x * (-3 * W'.a₁ ^ 2 * P x ^ 4 - 6 * W'.a₂ * P x ^ 4
          - 9 * W'.a₁ * P x ^ 3 * P y - W'.a₁ ^ 2 * W'.a₂ * P x ^ 3 * P z
          - 9 * W'.a₁ * W'.a₃ * P x ^ 3 * P z - 4 * W'.a₂ ^ 2 * P x ^ 3 * P z
          - 9 * W'.a₄ * P x ^ 3 * P z - 9 * P x ^ 2 * P y ^ 2 - 9 * W'.a₃ * P x ^ 2 * P y * P z
          - 3 * W'.a₁ * W'.a₂ * W'.a₃ * P x ^ 2 * P z ^ 2 - 6 * W'.a₂ * W'.a₄ * P x ^ 2 * P z ^ 2
          - 9 * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 - 27 * W'.a₆ * P x ^ 2 * P z ^ 2
          - 3 * W'.a₁ ^ 2 * W'.a₆ * P x * P z ^ 3 + 3 * W'.a₁ * W'.a₃ * W'.a₄ * P x * P z ^ 3
          - 6 * W'.a₂ * W'.a₃ ^ 2 * P x * P z ^ 3 - 24 * W'.a₂ * W'.a₆ * P x * P z ^ 3
          + 3 * W'.a₄ ^ 2 * P x * P z ^ 3 - W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P z ^ 4
          + W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P z ^ 4 - W'.a₂ ^ 2 * W'.a₃ ^ 2 * P z ^ 4
          - 4 * W'.a₂ ^ 2 * W'.a₆ * P z ^ 4 + W'.a₂ * W'.a₄ ^ 2 * P z ^ 4)
          + Q y * (3 * W'.a₁ * P x ^ 4 + W'.a₁ ^ 3 * P x ^ 3 * P z
          + 4 * W'.a₁ * W'.a₂ * P x ^ 3 * P z + 3 * W'.a₁ ^ 2 * W'.a₃ * P x ^ 2 * P z ^ 2
          + 6 * W'.a₁ * W'.a₄ * P x ^ 2 * P z ^ 2 + 3 * W'.a₁ * W'.a₃ ^ 2 * P x * P z ^ 3
          + 12 * W'.a₁ * W'.a₆ * P x * P z ^ 3 + W'.a₁ ^ 3 * W'.a₆ * P z ^ 4
          - W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P z ^ 4 + W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P z ^ 4
          + 4 * W'.a₁ * W'.a₂ * W'.a₆ * P z ^ 4 - W'.a₁ * W'.a₄ ^ 2 * P z ^ 4)
          + Q z * (-W'.a₁ ^ 2 * W'.a₂ * P x ^ 4 - W'.a₂ ^ 2 * P x ^ 4 - 3 * W'.a₄ * P x ^ 4
          - 3 * W'.a₁ * W'.a₂ * P x ^ 3 * P y - W'.a₁ ^ 2 * W'.a₄ * P x ^ 3 * P z
          - 3 * W'.a₁ * W'.a₂ * W'.a₃ * P x ^ 3 * P z - 7 * W'.a₂ * W'.a₄ * P x ^ 3 * P z
          - 3 * W'.a₂ * P x ^ 2 * P y ^ 2 - 3 * W'.a₂ * W'.a₃ * P x ^ 2 * P y * P z
          - 3 * W'.a₁ * W'.a₃ * W'.a₄ * P x ^ 2 * P z ^ 2
          - 3 * W'.a₂ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 - 9 * W'.a₂ * W'.a₆ * P x ^ 2 * P z ^ 2
          - 6 * W'.a₄ ^ 2 * P x ^ 2 * P z ^ 2 - W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P x * P z ^ 3
          + W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P x * P z ^ 3 - W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * P z ^ 3
          - 4 * W'.a₂ ^ 2 * W'.a₆ * P x * P z ^ 3 + W'.a₂ * W'.a₄ ^ 2 * P x * P z ^ 3
          - 3 * W'.a₃ ^ 2 * W'.a₄ * P x * P z ^ 3 - 12 * W'.a₄ * W'.a₆ * P x * P z ^ 3
          - W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P z ^ 4 + W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P z ^ 4
          - W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4 - 4 * W'.a₂ * W'.a₄ * W'.a₆ * P z ^ 4
          + W'.a₄ ^ 3 * P z ^ 4)) := by
  rw [dblAddXYZ, negY_eq, eval_polynomial, eval_polynomial]
  simp only [negAddY, addZ, dblAddX, dblAddY, dblAddZ]
  ring1

/-- For two point representatives on the curve, the `YZ` minor of the matrix with rows
`addXYZ P Q` and `dblAddXYZ P Q` vanishes. -/
theorem addY_mul_dblAddZ {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addY P Q * W'.dblAddZ P Q = W'.addZ P Q * W'.dblAddY P Q := by
  have h := negAddY_mul_dblAddZ_sub_addZ_mul_negY_dblAddXYZ (W' := W') P Q
  rw [hP, hQ, zero_mul, zero_mul, add_zero, dblAddXYZ, negY_eq] at h
  rw [addY, negY_eq]
  linear_combination -h - W'.a₁ * addX_mul_dblAddZ hP hQ

open Matrix in
/-- For two point representatives on the curve, the cross product of `addXYZ P Q` and
`dblAddXYZ P Q` vanishes; equivalently, the three `2 × 2` minors of the matrix with these rows
vanish (`addX_mul_dblAddY`, `addX_mul_dblAddZ`, `addY_mul_dblAddZ`). Over a field, when both
vectors are nonzero, this means that they represent the same point of `ℙ²`
(`Projectivization.mk_eq_mk_iff_crossProduct_eq_zero`). -/
theorem addXYZ_cross_dblAddXYZ {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addXYZ P Q ⨯₃ W'.dblAddXYZ P Q = 0 := by
  rw [cross_apply, addXYZ, dblAddXYZ]
  simp [addY_mul_dblAddZ hP hQ, addX_mul_dblAddZ hP hQ, addX_mul_dblAddY hP hQ]

private theorem dblAddXYZ_units_smul_self {P : Fin 3 → R} (hP : W'.Equation P) (u : Rˣ) :
    W'.dblAddXYZ (u • P) P = (u : R) ^ 2 • W'.dblXYZ P := by
  simpa [Units.smul_def, dblAddXYZ_self hP] using W'.dblAddXYZ_smul P P u 1

/-- If the addition law `addXYZ` attached to the line `Z = 0` does not vanish at two point
representatives `P` and `Q`, then its value `addXYZ P Q` is their sum `add P Q`. Unlike
`dblAddXYZ_equiv_add` for the law attached to `Y = 0`, this is an equality rather than an
equivalence, and it holds over any commutative ring, for representatives not necessarily on the
curve. -/
theorem add_of_addXYZ_ne_zero {P Q : Fin 3 → R} (h : W'.addXYZ P Q ≠ 0) :
    W'.add P Q = W'.addXYZ P Q := by
  -- if `P = u • Q`, then `addXYZ P Q` is `u ^ 2` times `addXYZ Q Q = 0`
  refine add_of_not_equiv fun ⟨u, hu⟩ ↦ h ?_
  simpa [← hu, Units.smul_def, addXYZ_self, funext_iff, Fin.forall_fin_succ] using
    W'.addXYZ_smul Q Q u 1

/-! ### Over a field -/

section Field

variable {F : Type*} [Field F] {W : Projective F}

/-- Over a field, a nonzero value of the addition law `dblAddXYZ P Q` attached to the line
`Y = 0`, at two nonsingular point representatives `P` and `Q`, represents their sum `add P Q`.
For the law `addXYZ` attached to the line `Z = 0`, a nonzero value is equal to `add P Q`, over any
commutative ring and at any point representatives (`add_of_addXYZ_ne_zero`). -/
theorem dblAddXYZ_equiv_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hd : W.dblAddXYZ P Q ≠ 0) : W.dblAddXYZ P Q ≈ W.add P Q := by
  by_cases hPQ : P ≈ Q
  · -- `P = u • Q`, and both `dblAddXYZ P Q` and `add P Q` are unit multiples of `dblXYZ Q`
    obtain ⟨u, rfl⟩ : ∃ u : Fˣ, u • Q = P := hPQ
    rw [dblAddXYZ_units_smul_self hQ.left, Units.smul_def, add_of_equiv (smul_equiv Q u.isUnit),
      dblXYZ_smul, smul_equiv_smul _ _ (u.isUnit.pow 2) (u.isUnit.pow 4)]
  -- otherwise `add P Q = addXYZ P Q`, which is nonzero; nonzero vectors with vanishing cross
  -- product represent the same projective point
  rw [add_of_not_equiv hPQ]
  exact Setoid.symm <| (Projectivization.mk_eq_mk_iff F _ _
      (ne_zero_of_nonsingular <| add_of_not_equiv hPQ ▸ nonsingular_add hP hQ) hd).mp <|
    (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero _ _).mpr <|
      addXYZ_cross_dblAddXYZ hP.left hQ.left

/-- Over a field, the value of the addition law attached to the line `Y = 0` at two nonsingular
point representatives satisfies the Weierstrass equation. For solutions over an arbitrary
commutative ring, see `WeierstrassCurve.Projective.Equation.dblAddXYZ`. -/
theorem equation_dblAddXYZ_of_nonsingular {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : W.Equation (W.dblAddXYZ P Q) := by
  by_cases hd : W.dblAddXYZ P Q = 0
  · simp [hd, equation_iff]
  exact (equation_of_equiv (dblAddXYZ_equiv_add hP hQ hd)).mpr (nonsingular_add hP hQ).left

/-- Over a field, the addition laws `addXYZ` and `dblAddXYZ`, attached to the lines `Z = 0` and
`Y = 0`, do not vanish simultaneously at two nonsingular point representatives. This is the
non-vanishing condition in the definition of a complete system of addition laws; that the two
values are linearly dependent is `addXYZ_cross_dblAddXYZ`. -/
theorem addXYZ_ne_zero_or_dblAddXYZ_ne_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : W.addXYZ P Q ≠ 0 ∨ W.dblAddXYZ P Q ≠ 0 := by
  by_cases hPQ : P ≈ Q
  · -- `P = u • Q`, and `dblAddXYZ P Q` is a nonzero multiple of `dblXYZ Q = add Q Q`.
    obtain ⟨u, rfl⟩ := hPQ
    rw [dblAddXYZ_units_smul_self hQ.left]
    exact .inr <| smul_ne_zero (pow_ne_zero 2 u.ne_zero) <|
      ne_zero_of_nonsingular <| add_self Q ▸ nonsingular_add hQ hQ
  -- Otherwise `addXYZ P Q = add P Q`, which is nonsingular and hence nonzero.
  exact .inl <| ne_zero_of_nonsingular <| add_of_not_equiv hPQ ▸ nonsingular_add hP hQ

end Field

/-! ### Maps -/

section Map

variable {S : Type*} [CommRing S] (f : R →+* S) (P Q : Fin 3 → R)

/-- The `X`-coordinate of the addition law attached to the line `Y = 0` commutes with a ring
homomorphism applied to the coefficients of the curve and to the point representatives. -/
@[simp]
theorem map_dblAddX : (W'.map f).dblAddX (f ∘ P) (f ∘ Q) = f (W'.dblAddX P Q) := by
  simp only [dblAddX, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, WeierstrassCurve.map,
    Function.comp_apply]

/-- The `Y`-coordinate of the addition law attached to the line `Y = 0` commutes with a ring
homomorphism applied to the coefficients of the curve and to the point representatives. -/
@[simp]
theorem map_dblAddY : (W'.map f).dblAddY (f ∘ P) (f ∘ Q) = f (W'.dblAddY P Q) := by
  simp only [dblAddY, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, WeierstrassCurve.map,
    Function.comp_apply]

/-- The `Z`-coordinate of the addition law attached to the line `Y = 0` commutes with a ring
homomorphism applied to the coefficients of the curve and to the point representatives. -/
@[simp]
theorem map_dblAddZ : (W'.map f).dblAddZ (f ∘ P) (f ∘ Q) = f (W'.dblAddZ P Q) := by
  simp only [dblAddZ, map_ofNat, map_add, map_mul, map_pow, WeierstrassCurve.map,
    Function.comp_apply]

/-- The addition law attached to the line `Y = 0` commutes with a ring homomorphism applied to the
coefficients of the curve and to the point representatives. -/
@[simp]
theorem map_dblAddXYZ : (W'.map f).dblAddXYZ (f ∘ P) (f ∘ Q) = f ∘ W'.dblAddXYZ P Q := by
  simp only [dblAddXYZ, map_dblAddX, map_dblAddY, map_dblAddZ, comp_fin3]

end Map

/-! ### Non-vanishing over a ring -/

/-- Let `P` and `Q` be unimodular solutions of the Weierstrass equation of an elliptic curve over a
commutative ring. Then the six coordinates of the two addition laws `addXYZ P Q` and
`dblAddXYZ P Q` generate the unit ideal; equivalently, at every prime ideal, some coordinate of one
of the two laws does not vanish. The analogue over a field, for nonsingular point representatives,
is `addXYZ_ne_zero_or_dblAddXYZ_ne_zero`. -/
theorem span_range_addXYZ_union_range_dblAddXYZ_eq_top [W'.IsElliptic] {P Q : Fin 3 → R}
    (hP : W'.Equation P) (hQ : W'.Equation Q) (hP₁ : Module.IsUnimodular R P)
    (hQ₁ : Module.IsUnimodular R Q) :
    Ideal.span (Set.range (W'.addXYZ P Q) ∪ Set.range (W'.dblAddXYZ P Q)) = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  -- the reduction of a triple modulo `m` vanishes exactly when its coordinates lie in `m`
  have hφ {T : Fin 3 → R} : algebraMap R m.ResidueField ∘ T = 0 ↔ Ideal.span (Set.range T) ≤ m := by
    simp [funext_iff, Ideal.span_le, Set.range_subset_iff]
  -- the reductions of `P` and `Q` are nonzero, hence nonsingular, points of the reduced curve
  have hns {T : Fin 3 → R} (hT : W'.Equation T) (hT₁ : Module.IsUnimodular R T) := by
    refine (equation_iff_nonsingular_of_ne_zero (W := W'.map (algebraMap R m.ResidueField))
      fun h0 ↦ hm.ne_top ?_).mp (hT.map _)
    -- a linear functional taking the value `1` at `T` would take a value in `m`
    obtain ⟨f, hf⟩ := Module.isUnimodular_iff.mp hT₁
    rw [Ideal.eq_top_iff_one, ← hf, LinearMap.pi_apply_eq_sum_univ]
    exact Ideal.sum_mem _ fun i _ ↦ by
      rw [smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hφ.mp h0 (Ideal.subset_span ⟨i, rfl⟩))
  -- `hle` says both laws vanish at the reductions of `P` and `Q`, which the field case excludes
  rw [Ideal.span_union, sup_le_iff, ← hφ, ← hφ, ← map_addXYZ, ← map_dblAddXYZ] at hle
  exact not_and_or.mpr (addXYZ_ne_zero_or_dblAddXYZ_ne_zero (hns hP hP₁) (hns hQ hQ₁)) hle

end WeierstrassCurve.Projective
