/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Unique

/-!
# Functions on the affine curve with a pole of order at most three

Let `W` be a Weierstrass curve over a field `F`, with coordinate ring `R[W]` and coordinate
functions `x` and `y`. Every element of `R[W]` is `p(x) + q(x) y` for polynomials `p` and `q`, and
at the place at infinity the two summands have pole orders `2 deg p` and `2 deg q + 3`, of
different parities. So the pole orders of the elements of `R[W]` are `0, 2, 3, 4, …`, and the
elements of small pole order are explicit:

* an element with a pole at infinity has a pole of order at least two;
* an element with a pole of order less than three is `αx + β`;
* an element with a pole of order at most three is `γy + αx + β`.

These are the computations `L(2O) = ⟨1, x⟩` and `L(3O) = ⟨1, x, y⟩` behind the proof that an
isomorphism of elliptic curves fixing the point at infinity is a change of variables. They are
stated for any valuation `v` of the function field that is trivial on `F` and gives `x` a pole,
so that they apply to a valuation transported along a map of function fields before that map is
known to identify the places at infinity. For the place at infinity itself and an elliptic curve,
the spaces `L(n · O)` are computed in full in `Affine/FunctionField/Genus.lean`.

## Main results

* `WeierstrassCurve.Affine.val_mk_Y_lt_val_X_sq`: `v y < (v x) ^ 2`.
* `WeierstrassCurve.Affine.val_X_le_of_one_lt`: `1 < v z` implies `v x ≤ v z`.
* `WeierstrassCurve.Affine.exists_eq_of_val_lt_val_mk_Y`: `v z < v y` implies `z = αx + β`.
* `WeierstrassCurve.Affine.exists_eq_of_val_le_val_mk_Y`: `v z ≤ v y` implies
  `z = γy + αx + β`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], the proof of III.3.1.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}

/-- A polynomial of degree at most one in `x` is `αx + β` in the coordinate ring. -/
private theorem smul_one_eq_of_natDegree_le_one {p : F[X]} (hp : p.natDegree ≤ 1) :
    p • (1 : W.CoordinateRing) = algebraMap F W.CoordinateRing (p.coeff 1) *
      AdjoinRoot.of W.polynomial Polynomial.X + algebraMap F W.CoordinateRing (p.coeff 0) := by
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp]
  rw [Algebra.smul_def, mul_one, map_add, map_mul, ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, AdjoinRoot.algebraMap_eq]

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation W.FunctionField Γ) [v.IsTrivialOn F]
  (hx : 1 < v (algebraMap F[X] W.FunctionField Polynomial.X))

include hx

/-- The value of `p(x) + q(x) y`, for polynomials `p` and `q`: the larger of `(v x) ^ deg p` and
`(v x) ^ deg q · v y`, a summand being dropped when its polynomial vanishes. -/
private theorem val_smul_one_add_smul_mk_Y (p q : F[X]) :
    v (algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W Y)) =
      max (v (algebraMap F[X] W.FunctionField p))
        (v (algebraMap F[X] W.FunctionField q) *
          v (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))) := by
  have h := val_add_mul_mk_Y v hx (algebraMap F[X] (RatFunc F) p) (algebraMap F[X] (RatFunc F) q)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_mul] at h
  rw [← h, map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_mul,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]

/-- **`y` has a pole of order less than twice that of `x`**: `v y < (v x) ^ 2`, since
`(v y) ^ 2 = (v x) ^ 3`. -/
theorem val_mk_Y_lt_val_X_sq :
    v (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
      < v (algebraMap F[X] W.FunctionField Polynomial.X) ^ 2 := by
  refine lt_of_pow_lt_pow_left₀ 2 zero_le ?_
  rw [val_mk_Y_sq v hx, ← pow_mul]
  exact pow_lt_pow_right₀ hx (by norm_num)

/-- A nonzero polynomial in `x` whose value is less than `(v x) ^ 2` has degree at most one. -/
private theorem natDegree_le_one_of_val_lt {p : F[X]} (hp : p ≠ 0)
    (h : v (algebraMap F[X] W.FunctionField p)
      < v (algebraMap F[X] W.FunctionField Polynomial.X) ^ 2) : p.natDegree ≤ 1 := by
  rw [val_algebraMap_eq_pow_natDegree v hx hp, pow_lt_pow_iff_right₀ hx] at h
  omega

/-- The value of `q y`, for a nonzero polynomial `q`, is at least that of `y`. -/
private theorem val_mk_Y_le_mul {q : F[X]} (hq : q ≠ 0) :
    v (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
      ≤ v (algebraMap F[X] W.FunctionField q) *
        v (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
  rw [val_algebraMap_eq_pow_natDegree v hx hq]
  exact le_mul_of_one_le_left zero_le (one_le_pow₀ hx.le)

/-- **No function on the affine curve has a pole of order one at infinity**: if `z` has a pole,
its pole is at least that of `x`. -/
theorem val_X_le_of_one_lt {z : W.CoordinateRing}
    (hz : 1 < v (algebraMap W.CoordinateRing W.FunctionField z)) :
    v (algebraMap F[X] W.FunctionField Polynomial.X)
      ≤ v (algebraMap W.CoordinateRing W.FunctionField z) := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq z
  rw [val_smul_one_add_smul_mk_Y v hx] at hz ⊢
  rcases eq_or_ne q 0 with rfl | hq
  · rcases eq_or_ne p 0 with rfl | hp
    · simp at hz
    simp only [map_zero, zero_mul, zero_le, max_eq_left] at hz ⊢
    rw [val_algebraMap_eq_pow_natDegree v hx hp] at hz ⊢
    refine le_self_pow₀ hx.le fun h => ?_
    rw [h, pow_zero] at hz
    exact hz.false
  · exact (val_X_lt_val_mk_Y v hx).le.trans ((val_mk_Y_le_mul v hx hq).trans (le_max_right _ _))

/-- **A function on the affine curve with a pole of order less than three is `αx + β`**: if
`v z < v y`, then `z = αx + β` for constants `α` and `β`. -/
theorem exists_eq_of_val_lt_val_mk_Y {z : W.CoordinateRing}
    (hz : v (algebraMap W.CoordinateRing W.FunctionField z)
      < v (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))) :
    ∃ α β : F, z = algebraMap F W.CoordinateRing α * AdjoinRoot.of W.polynomial Polynomial.X
      + algebraMap F W.CoordinateRing β := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq z
  rw [val_smul_one_add_smul_mk_Y v hx] at hz
  -- a nonzero `q` would give a pole of order at least three
  obtain rfl : q = 0 := by
    by_contra hq
    exact (lt_of_le_of_lt ((val_mk_Y_le_mul v hx hq).trans (le_max_right _ _)) hz).false
  rw [zero_smul, add_zero]
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, 0, by simp⟩
  have hp' := natDegree_le_one_of_val_lt v hx hp
    (((le_max_left _ _).trans_lt hz).trans (val_mk_Y_lt_val_X_sq v hx))
  exact ⟨_, _, smul_one_eq_of_natDegree_le_one hp'⟩

/-- **A function on the affine curve with a pole of order at most three is `γy + αx + β`**: if
`v z ≤ v y`, then `z = γy + αx + β` for constants `α`, `β` and `γ`. -/
theorem exists_eq_of_val_le_val_mk_Y {z : W.CoordinateRing}
    (hz : v (algebraMap W.CoordinateRing W.FunctionField z)
      ≤ v (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))) :
    ∃ α β γ : F, z = algebraMap F W.CoordinateRing γ * AdjoinRoot.root W.polynomial
      + algebraMap F W.CoordinateRing α * AdjoinRoot.of W.polynomial Polynomial.X
      + algebraMap F W.CoordinateRing β := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq z
  rw [val_smul_one_add_smul_mk_Y v hx] at hz
  -- `q` is constant: a pole of `q` would add to the triple pole of `y`
  have hq : q.natDegree = 0 := by
    rcases eq_or_ne q 0 with rfl | hq
    · simp
    have h := (le_max_right _ _).trans hz
    rw [val_algebraMap_eq_pow_natDegree v hx hq] at h
    have h1 : v (algebraMap F[X] W.FunctionField Polynomial.X) ^ q.natDegree ≤ 1 :=
      (mul_le_iff_le_one_left (zero_lt_one.trans (hx.trans (val_X_lt_val_mk_Y v hx)))).mp h
    by_contra h0
    exact (one_lt_pow₀ hx h0).not_ge h1
  -- `p` has degree at most one: its value is below `v y < (v x) ^ 2`
  have hp : p.natDegree ≤ 1 := by
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    exact natDegree_le_one_of_val_lt v hx hp
      (((le_max_left _ _).trans hz).trans_lt (val_mk_Y_lt_val_X_sq v hx))
  obtain ⟨c, rfl⟩ : ∃ c, q = C c := ⟨_, eq_C_of_natDegree_eq_zero hq⟩
  refine ⟨p.coeff 1, p.coeff 0, c, ?_⟩
  rw [smul_one_eq_of_natDegree_le_one hp, Algebra.smul_def, ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply, CoordinateRing.mk, AdjoinRoot.mk_X]
  ring

end WeierstrassCurve.Affine
