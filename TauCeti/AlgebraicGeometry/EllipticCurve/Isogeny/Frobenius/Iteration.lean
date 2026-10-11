/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Torsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber

/-!
# Iterated Frobenius and its fixed points

For an elliptic curve over a finite field with `q` elements, the `n`th power of its Frobenius
endomorphism acts on geometric points by raising both coordinates to `q ^ n`. For positive `n`,
`1 - π ^ n` is a nonzero separable isogeny: it pulls the invariant differential back to itself.
Over a separably closed extension, its degree therefore counts exactly the points fixed by
`π ^ n`. The fixed locus is finite, so this count can supply the coefficients of the elliptic
curve's zeta function without choosing a model of the field with `q ^ n` elements.

The iteration and coordinate formulas hold over any extension of the finite field. Separably
closed constants enter only in the degree count. The positive-iterate restriction is essential:
at `n = 0` the fixed locus is the whole geometric point group and `1 - π ^ n = 0`.

## Main results

* `TauCeti.Isogeny.Hom.pow_ofIsogeny_baseChangeFrobenius_pointMap`: the action is the iterated
  coordinate Frobenius, with coordinate formulas below.
* `TauCeti.Isogeny.Hom.one_sub_pow_ofIsogeny_baseChangeFrobenius_ne_zero` and
  `isSeparable_toIsogeny_one_sub_pow_ofIsogeny_baseChangeFrobenius`: positive iterates give
  nonzero separable difference isogenies.
* `TauCeti.Isogeny.Hom.ncard_fixedPoints_pow_ofIsogeny_baseChangeFrobenius`: the fixed-point
  count is `deg (1 - π ^ n)`.
* `TauCeti.Isogeny.Hom.finite_fixedPoints_pow_ofIsogeny_baseChangeFrobenius`: the fixed locus
  is finite even without a closure hypothesis.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.2.3.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
  (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- Every positive power of Frobenius kills the invariant differential. -/
@[simp↓]
theorem pullbackDifferential_pow_ofIsogeny_baseChangeFrobenius (n : ℕ) (hn : 0 < n) :
    ((ofIsogeny (baseChangeFrobenius K W)) ^ n).pullbackDifferential
      (invariantDifferential (W⁄K).toAffine) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [pullbackDifferential_pow, pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply,
    pullbackDifferential_ofIsogeny, pullbackDifferential_baseChangeFrobenius_invariantDifferential,
    map_zero]

/-- The difference between the identity and a positive Frobenius iterate is nonzero. -/
theorem one_sub_pow_ofIsogeny_baseChangeFrobenius_ne_zero (n : ℕ) (hn : 0 < n) :
    1 - (ofIsogeny (baseChangeFrobenius K W)) ^ n ≠ 0 := by
  intro h
  have hω : (1 - (ofIsogeny (baseChangeFrobenius K W)) ^ n).pullbackDifferential
      (invariantDifferential (W⁄K).toAffine) = invariantDifferential (W⁄K).toAffine := by
    simp [hn]
  rw [h, pullbackDifferential_zero, LinearMap.zero_apply] at hω
  exact invariantDifferential_ne_zero _ hω.symm

/-- The difference between the identity and a positive Frobenius iterate is separable. -/
theorem isSeparable_toIsogeny_one_sub_pow_ofIsogeny_baseChangeFrobenius (n : ℕ) (hn : 0 < n) :
    Algebra.IsSeparable
      (toIsogeny <|
        one_sub_pow_ofIsogeny_baseChangeFrobenius_ne_zero (K := K) W n hn).fieldPullback.fieldRange
      (W⁄K).toAffine.FunctionField := by
  rw [isSeparable_iff_pullbackDifferential_ne_zero, ← pullbackDifferential_ofIsogeny,
    ofIsogeny_toIsogeny]
  simp [hn]

section Points

variable [DecidableEq K]

/-- Iterated Frobenius on points agrees with mapping by the power of the coordinate Frobenius. -/
theorem pow_ofIsogeny_baseChangeFrobenius_pointMap [Fintype F] (n : ℕ)
    (P : (W⁄K).toAffine.Point) :
    ((ofIsogeny (baseChangeFrobenius K W)) ^ n).pointMap P =
      Point.map ((FiniteField.frobeniusAlgHom F K) ^ n) P := by
  rw [pow_pointMap]
  have hmap := funext (pointMap_ofIsogeny_baseChangeFrobenius (K := K) W)
  rw [hmap]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero]
    cases P <;> rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih,
      Point.map_map, pow_succ', AlgHom.End_toMul_mul]

/-- The `x`-coordinate of the `n`th Frobenius iterate is raised to `q ^ n`. -/
@[simp]
theorem xCoord_pow_ofIsogeny_baseChangeFrobenius_pointMap (n : ℕ)
    (P : (W⁄K).toAffine.Point) :
    Point.xCoord (((ofIsogeny (baseChangeFrobenius K W)) ^ n).pointMap P) =
      Point.xCoord P ^ (Nat.card F) ^ n := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [pow_ofIsogeny_baseChangeFrobenius_pointMap, Point.xCoord_map,
    TauCeti.FiniteField.frobeniusAlgHom_pow_apply]

/-- The `y`-coordinate of the `n`th Frobenius iterate is raised to `q ^ n`. -/
@[simp]
theorem yCoord_pow_ofIsogeny_baseChangeFrobenius_pointMap (n : ℕ)
    (P : (W⁄K).toAffine.Point) :
    Point.yCoord (((ofIsogeny (baseChangeFrobenius K W)) ^ n).pointMap P) =
      Point.yCoord P ^ (Nat.card F) ^ n := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [pow_ofIsogeny_baseChangeFrobenius_pointMap, Point.yCoord_map,
    TauCeti.FiniteField.frobeniusAlgHom_pow_apply]

/-- A point is fixed by the `n`th Frobenius iterate exactly when both its affine coordinates
are fixed by `q ^ n`-powering. This includes the point at infinity. -/
@[simp]
theorem pow_ofIsogeny_baseChangeFrobenius_pointMap_eq_self_iff (n : ℕ)
    (P : (W⁄K).toAffine.Point) :
    ((ofIsogeny (baseChangeFrobenius K W)) ^ n).pointMap P = P ↔
      Point.xCoord P ^ (Nat.card F) ^ n = Point.xCoord P ∧
      Point.yCoord P ^ (Nat.card F) ^ n = Point.yCoord P := by
  constructor
  · intro h
    exact ⟨(xCoord_pow_ofIsogeny_baseChangeFrobenius_pointMap W n P).symm.trans
        (congrArg Point.xCoord h),
      (yCoord_pow_ofIsogeny_baseChangeFrobenius_pointMap W n P).symm.trans
        (congrArg Point.yCoord h)⟩
  · rintro ⟨hx, hy⟩
    by_cases hP : P = 0
    · simp [hP]
    classical
    have : Fintype F := Fintype.ofFinite F
    have hne : ((ofIsogeny (baseChangeFrobenius K W)) ^ n).pointMap P ≠ 0 := by
      rw [pow_ofIsogeny_baseChangeFrobenius_pointMap, ← Point.map_zero (W' := W)
        ((FiniteField.frobeniusAlgHom F K) ^ n)]
      exact fun h ↦ hP (Point.map_injective _ h)
    exact Point.eq_of_coords hne hP
      ((xCoord_pow_ofIsogeny_baseChangeFrobenius_pointMap W n P).trans hx)
      ((yCoord_pow_ofIsogeny_baseChangeFrobenius_pointMap W n P).trans hy)

/-- The points fixed by a positive Frobenius iterate form a finite set over any extension. -/
theorem finite_fixedPoints_pow_ofIsogeny_baseChangeFrobenius (n : ℕ) (hn : 0 < n) :
    {P : (W⁄K).toAffine.Point |
      ((ofIsogeny (baseChangeFrobenius K W)) ^ n).pointMap P = P}.Finite := by
  have hset : {P : (W⁄K).toAffine.Point |
      ((ofIsogeny (baseChangeFrobenius K W)) ^ n).pointMap P = P} =
      {P | (1 - (ofIsogeny (baseChangeFrobenius K W)) ^ n).pointMap P = 0} := by
    ext P
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, sub_pointMap, one_def, id_pointMap, sub_eq_zero,
      eq_comm]
  rw [hset]
  exact finite_setOf_pointMap_eq (one_sub_pow_ofIsogeny_baseChangeFrobenius_ne_zero W n hn) 0

/-- Over a separably closed extension, `deg (1 - π ^ n)` counts the points fixed by `π ^ n`
for every positive `n` (Silverman V.2.3). -/
theorem ncard_fixedPoints_pow_ofIsogeny_baseChangeFrobenius [IsSepClosed K] (n : ℕ) (hn : 0 < n) :
    {P : (W⁄K).toAffine.Point |
      ((ofIsogeny (baseChangeFrobenius K W)) ^ n).pointMap P = P}.ncard =
      (1 - (ofIsogeny (baseChangeFrobenius K W)) ^ n).degree := by
  have h := one_sub_pow_ofIsogeny_baseChangeFrobenius_ne_zero (K := K) W n hn
  have := isSeparable_toIsogeny_one_sub_pow_ofIsogeny_baseChangeFrobenius (K := K) W n hn
  rw [← ofIsogeny_toIsogeny h, degree_ofIsogeny, ← ncard_fiber_toPointHom_eq_degree _ 0]
  congr 1
  ext P
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← pointMap_ofIsogeny_eq_toPointHom,
    ofIsogeny_toIsogeny, sub_pointMap, one_def, id_pointMap, sub_eq_zero, eq_comm]

end Points

end TauCeti.Isogeny.Hom

end
