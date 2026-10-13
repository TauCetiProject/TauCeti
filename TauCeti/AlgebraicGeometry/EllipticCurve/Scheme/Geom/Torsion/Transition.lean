/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank

/-!
# Transition maps between elliptic torsion schemes

Multiplication by `m` restricts to a homomorphism `E[mn] ⟶ E[n]`. This map is the base change
of `[m] : E ⟶ E` along `E[n] ⟶ E`, so for `m ≠ 0` it is finite locally free and surjective,
of rank `m²`. Its scheme-theoretic kernel is `E[m]`, included in `E[mn]` by the usual inclusion.
These statements hold over arbitrary bases, including in characteristics dividing `m` or `n`.

The case `m = p`, `n = p^r` supplies the faithfully flat transitions in the elliptic
`p`-divisible group. Both the inclusions and the transition maps commute with arbitrary base
change of the elliptic curve. The maps and their identity and composition laws specialize the
commutative group-scheme API in `TauCeti.GroupScheme`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1 and Chapter 5.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) (m n : ℤ)

/-- For `m ≠ 0`, the torsion transition is finite. -/
theorem isFinite_torsionMulBy_left (hm : m ≠ 0) :
    IsFinite (E.torsionMulBy m n).left :=
  MorphismProperty.of_isPullback (E.isPullback_torsionMulBy m n) (E.isFinite_mulBy_left hm)

/-- For `m ≠ 0`, the torsion transition is flat. -/
theorem flat_torsionMulBy_left (hm : m ≠ 0) : Flat (E.torsionMulBy m n).left :=
  MorphismProperty.of_isPullback (E.isPullback_torsionMulBy m n) (E.flat_mulBy_left hm)

/-- For `m ≠ 0`, the torsion transition is surjective, without a characteristic restriction. -/
theorem surjective_torsionMulBy_left (hm : m ≠ 0) :
    Surjective (E.torsionMulBy m n).left :=
  MorphismProperty.of_isPullback (E.isPullback_torsionMulBy m n) (E.surjective_mulBy_left hm)

/-- Every fibre of the transition `E[mn] ⟶ E[n]` has length `m²`, for `m ≠ 0`. -/
@[simp]
theorem finrank_torsionMulBy_left (hm : m ≠ 0) (x : (E.torsion n).X.left) :
    (E.torsionMulBy m n).left.finrank x = m.natAbs ^ 2 := by
  have := E.isFinite_mulBy_left hm
  have := E.flat_mulBy_left hm
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (E.isPullback_torsionMulBy m n),
    E.finrank_mulBy_left hm]

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
