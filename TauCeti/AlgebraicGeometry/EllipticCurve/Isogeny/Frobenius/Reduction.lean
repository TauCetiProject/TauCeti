/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.TautologicalPoint
-- Proof-only: the tautological point is the generic point pushed along the pullback.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint
-- Proof-only: the `q`-power map is additive.
import TauCeti.FieldTheory.Finite.Frobenius

/-!
# The Frobenius acts on points as the `q`-power map

Let `W` be an elliptic curve over a finite field `F` with `q` elements, and `K` an extension of
`F`. The `q`-power Frobenius isogeny of `W` base-changes to an isogeny `π` of `W⁄K`, whose
pullback raises the functions defined over `F` to the `q`-th power. Every point `P` of `W` over
`K` has a place of degree one of the function field of `W⁄K`
(`WeierstrassCurve.Affine.pointEquivDegreeOnePlace`). The tautological point of `π` is `π`
evaluated at the generic point, and its reduction at the place of `P`
(`WeierstrassCurve.Affine.reductionOfDegreeEqOne`) is `π` evaluated at `P`. This file computes
that reduction: it is

    π (x, y) = (x ^ q, y ^ q),

the image of `P` under the point map induced by the `q`-power Frobenius of `K` over `F`. So the
points of `W` over `K` fixed by `π` are those with coordinates in `F`, and `π` commutes with every
point map induced by a field map over `F`. On the torsion of `W` over a separable closure of `F`,
`π` is therefore the Galois Frobenius of `F`, which is the form in which it enters the count of
the points of `W` over `F` and the Hasse bound. The comparison with the class-group point map
`TauCeti.Isogeny.toPointHom` is not made here.

## Main results

* `TauCeti.Isogeny.reductionOfDegreeEqOne_tautologicalPoint_baseChangeFrobenius`: at the place of
  `P`, the tautological point of the base-changed Frobenius
  `TauCeti.Isogeny.baseChangeFrobenius` reduces to the image of `P` under
  `Point.map (FiniteField.frobeniusAlgHom F K)`, the `q`-power map on coordinates.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11, V.1.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K] [DecidableEq K]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **The Frobenius acts on points as the `q`-power map on coordinates**: at the place of a point
`P` of `W` over `K`, the tautological point of the base-changed Frobenius `π` reduces to
`π (x, y) = (x ^ q, y ^ q)`, the image of `P` under the `q`-power Frobenius of `K` over `F`. -/
-- Not `@[simp]`: its left-hand side is not simp-normal, since
-- `tautologicalPoint_eq_map_genericPoint` rewrites the tautological point.
theorem reductionOfDegreeEqOne_tautologicalPoint_baseChangeFrobenius
    (P : (W⁄K).toAffine.Point) :
    reductionOfDegreeEqOne (W⁄K).toAffine ((W⁄K).toAffine.pointEquivDegreeOnePlace P).2
        (baseChangeFrobenius K W).pullback.tautologicalPoint =
      Point.equivBaseChangeSelf _ (Point.map (FiniteField.frobeniusAlgHom F K) P) := by
  have hq : Nat.card F ≠ 0 := Nat.card_pos.ne'
  rw [reductionOfDegreeEqOne_eq_iff, tautologicalPoint_eq_map_genericPoint, genericPoint_eq_some,
    Point.map_some]
  rcases P with _ | ⟨a, b, h⟩
  · rw [coe_pointEquivDegreeOnePlace_zero, ← Point.zero_def, map_zero, map_zero, map_zero,
      sub_zero, mem_polePoints_iff, Point.xCoord_some]
    refine Or.inr ?_
    rw [fieldPullback_baseChangeFrobenius_genericX, map_pow, Place.valuation_infinity,
      genericX_eq_algebraMap]
    exact one_lt_pow₀ (one_lt_infinityPlace_X _) hq
  · have hQ : (W⁄K).toAffine.Nonsingular (FiniteField.frobeniusAlgHom F K a)
        (FiniteField.frobeniusAlgHom F K b) :=
      (W.baseChange_nonsingular (FiniteField.frobeniusAlgHom F K).injective a b).mpr h
    -- a constant of `F(W⁄K)` raised to the `q`-th power is the image of its `q`-power Frobenius
    have hc (c : K) :
        algebraMap K (W⁄K).toAffine.FunctionField (FiniteField.frobeniusAlgHom F K c) =
          algebraMap K _ c ^ Nat.card F := by
      rw [FiniteField.coe_frobeniusAlgHom, map_pow, Nat.card_eq_fintype_card]
    let _ : Algebra F (W⁄K).toAffine.FunctionField :=
      ((algebraMap K (W⁄K).toAffine.FunctionField).comp (algebraMap F K)).toAlgebra
    have hsub := TauCeti.FiniteField.sub_pow_natCard F (W⁄K).toAffine.FunctionField
    rw [Point.map_some, Point.equivBaseChangeSelf_some _ hQ,
      some_sub_baseChange_mem_polePoints_iff, coe_pointEquivDegreeOnePlace_some,
      fieldPullback_baseChangeFrobenius_genericX, fieldPullback_baseChangeFrobenius_genericY, hc,
      hc, ← hsub, ← hsub, map_pow, map_pow]
    exact ⟨pow_lt_one₀ zero_le (valuation_pointPlace_genericX_sub_lt_one _ h.1) hq,
      pow_lt_one₀ zero_le (valuation_pointPlace_genericY_sub_lt_one _ h.1) hq⟩

end TauCeti.Isogeny

end
