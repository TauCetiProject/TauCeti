/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Tower
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
import all TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion
import all TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Basic

/-!
# Finite locally free levels of the elliptic torsion tower

For an elliptic curve `E/S` and a nonzero natural number `p`, the functor
`E.toCommGrp.torsionTower p` has finite locally free levels of rank `p^(2n)` and closed
immersion transition arrows. The construction includes level zero, namely `E[1]`.
Together with the natural base-change comparison for torsion towers, this gives a
base-change-compatible tower of finite locally free commutative group schemes over
arbitrary bases, without any restriction on residue characteristics.

These are the finite levels of the elliptic `p`-divisible group when `p` is prime.
Multiplication transitions and their scheme-theoretic kernels are developed separately
in `Geom.Torsion.Transition` and `GroupScheme.Torsion.Iterated`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1 and Chapter 5.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) (p : ℕ) [NeZero p]

/-- Each level of the elliptic torsion tower is finite over the base. -/
instance isFinite_torsionTower_obj_hom (n : ℕ) :
    IsFinite ((E.toCommGrp.torsionTower p).obj n).X.hom := by
  simpa only [CommGrp.torsionTower, torsion] using
    E.isFinite_torsion_hom (pow_ne_zero n (Int.natCast_ne_zero.mpr (NeZero.ne p)))

/-- Each level of the elliptic torsion tower is flat over the base. -/
instance flat_torsionTower_obj_hom (n : ℕ) :
    Flat ((E.toCommGrp.torsionTower p).obj n).X.hom := by
  simpa only [CommGrp.torsionTower, torsion] using
    E.flat_torsion_hom (pow_ne_zero n (Int.natCast_ne_zero.mpr (NeZero.ne p)))

omit [NeZero p] in
/-- Each level of the elliptic torsion tower is locally of finite presentation, including
over nonnoetherian bases. -/
instance locallyOfFinitePresentation_torsionTower_obj_hom (n : ℕ) :
    LocallyOfFinitePresentation ((E.toCommGrp.torsionTower p).obj n).X.hom := by
  simpa only [CommGrp.torsionTower, torsion] using
    E.locallyOfFinitePresentation_torsion_hom ((p : ℤ) ^ n)

/-- The level `E[pⁿ]` has constant finite-flat rank `p^(2n)`. -/
@[simp]
theorem finrank_torsionTower_obj_hom (n : ℕ) (s : S) :
    ((E.toCommGrp.torsionTower p).obj n).X.hom.finrank s = p ^ (2 * n) := by
  simpa only [CommGrp.torsionTower, torsion, Int.natAbs_pow, Int.natAbs_natCast,
    ← pow_mul, Nat.mul_comm n 2] using
    E.finrank_torsion_hom (pow_ne_zero n (Int.natCast_ne_zero.mpr (NeZero.ne p))) s

variable {p}

omit [NeZero p] in
/-- All inclusion arrows in the elliptic torsion tower are closed immersions. -/
instance isClosedImmersion_torsionTower_map_left {m n : ℕ} (f : m ⟶ n) :
    IsClosedImmersion (((E.toCommGrp.torsionTower p).map f).hom.hom.left) := by
  have h := congrArg Over.Hom.left (E.toCommGrp.torsionTower_map_ι p f)
  have := E.isClosedImmersion_torsionι_left ((p : ℤ) ^ n)
  have hsep : IsSeparated (E.torsionι ((p : ℤ) ^ n)).left := .of_isAffineHom _
  have : IsClosedImmersion
      ((((E.toCommGrp.torsionTower p).map f).hom.hom.left) ≫
        (E.torsionι ((p : ℤ) ^ n)).left) := by
    exact (congrArg (fun k ↦ IsClosedImmersion k) h).mpr (by
      simpa only [CommGrp.torsionTower, torsionι, torsion] using
        E.isClosedImmersion_torsionι_left ((p : ℤ) ^ m))
  exact @IsClosedImmersion.of_comp _ _ _ _ _ this hsep

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
