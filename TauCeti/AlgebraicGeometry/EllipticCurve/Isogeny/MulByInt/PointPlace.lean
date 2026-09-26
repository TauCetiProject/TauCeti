/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Place
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
-- Proof-only: the non-vanishing of the division polynomials off the kernel.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality
-- Proof-only: the two coordinate identities relating `P` and `n • P`.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Descent
-- Proof-only: the adic valuation of a height one prime is trivial on the constants.
import TauCeti.FieldTheory.FunctionField.Place.Adic
-- Proof-only: triviality on the base survives restriction.
import TauCeti.RingTheory.Valuation.IsTrivialOn
-- Proof-only: a valuation with no pole at `x` is bounded on the coordinate ring.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.CoordinateRingIntegral
-- Proof-only: the centre of a bounded valuation on a Dedekind domain.
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic
-- Proof-only: the place at infinity is the only place at which `x` has a pole.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Unique
-- Proof-only: the place at infinity restricts to itself along `[n]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
-- Proof-only: a place has finitely many places above it.
import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre
-- Proof-only: `[n]` is separable when `n` is invertible, so it splits every place completely over a
-- separably closed field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified

/-!
# The place of a point restricts along `[n]` to the place of its multiple

An affine point `P` of `W` has a place of `F(W)`, and pulling that place back along the
function-field map of `[n]` gives a valuation of `F(W)` again. This file identifies it: it is
equivalent to the place of `n • P`, which is the place at infinity when `n • P = 0`. So among the
places attached to the `F`-rational points of `W`, those above the place of a point `T`, for the
covering `[n]`, are the places of the `[n]`-preimages of `T`. A fibre can also contain places of
higher degree, which are not attached to points and are not treated here; over an algebraically
closed field there are none. That is what turns the pullback of a divisor along `[n]` into a sum
over a fibre, which is the form in which the divisor construction of the Weil pairing uses it.

The restricted valuation need not be normalized, since `[n]` can multiply orders, which is why the
statements are equivalences rather than equalities.

## Main results

* `TauCeti.Isogeny.isEquiv_comap_pointPlace`: the place of `P` restricted along `[n]` is
  equivalent to the place of `n • P`, when `n • P` is affine.
* `TauCeti.Isogeny.isEquiv_comap_pointPlace_infinityPlace_iff`: the place of an affine point `P`
  restricts to the place at infinity exactly when `n • P = 0`, over any field.
* `TauCeti.Isogeny.isEquiv_comap_pointPlace_iff`: and conversely, the place of an affine point
  restricts to the place of `T` only if the point is an `[n]`-preimage of `T`, so the affine
  `F`-rational places over the place of `T` are exactly those of its `[n]`-preimages.
* `TauCeti.Isogeny.isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff`: the same for every pair
  of points, read through the point--place dictionary, the point at infinity included.
* `TauCeti.Isogeny.finite_setOf_zsmul_eq`: the fibre `{R | n • R = T}` is finite.
* `TauCeti.Isogeny.restrict_eq_pointEquivDegreeOnePlace_iff`: over a separably closed field, the
  places over the place of `T` are exactly the places of its `[n]`-preimages, since `[n]` splits
  every place completely.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], III.1.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.

The construction follows `TauCeti.Isogeny.isEquiv_comap_infinityPlace`
(`TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/InfinityPlace.lean`), the same statement for the
place at infinity; the ordering of the argument, and the choice to work at the `Valuation.comap`
level rather than through `Place.restrict`, are taken from there.

## Prior art

The same statement for `[ℓ]` is proved in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0),
`projects/HasseWeil/HasseWeil/Foundation/EC/MulByIntSamePlace.lean`, which also covers the case of
a point that `[ℓ]` sends to infinity. Nothing here is adapted from it: that proof identifies the
two valuation rings directly, via `Valuation.isEquiv_of_val_le_one` and the division-polynomial
group law, where this one takes the centre of the normalized restriction on the coordinate ring.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain
open scoped Polynomial.Bivariate WithZero

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- Ellipticity already makes the coordinate ring integrally closed, hence a Dedekind domain.
Deriving it here as a `local instance` — the pattern `Affine/FunctionField/PointPlace.lean` uses —
keeps the assumption out of the exported signatures instead of making every caller supply it. -/
local instance : IsDedekindDomain W.toAffine.CoordinateRing :=
  have := WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing W.toAffine
  W.toAffine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

omit [DecidableEq F] [W.IsElliptic] in
-- A constant `c` of the function field is the class of the constant polynomial `C (C c)`.
private theorem algebraMap_mk_C_C (c : F) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (CoordinateRing.mk W.toAffine (C (C c))) = algebraMap F W.toAffine.FunctionField c := by
  rw [CoordinateRing.mk_C_eq_algebraMap, ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply F F[X] W.toAffine.CoordinateRing,
    ← IsScalarTower.algebraMap_apply F W.toAffine.CoordinateRing W.toAffine.FunctionField]

omit [DecidableEq F] [W.IsElliptic] in
/-- **Clearing the denominator of a coordinate difference.** A pulled-back coordinate is a quotient
of coordinate-ring classes; subtracting a constant keeps the denominator and shifts the numerator by
that constant times it. Both coordinate valuations below are this one identity, read off at the
`x`- and the `y`-coordinate. -/
private theorem sub_algebraMap_eq_div {a : W.toAffine.FunctionField} {p q : F[X][Y]}
    (hq : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (CoordinateRing.mk W.toAffine q) ≠ 0)
    (ha : a = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (CoordinateRing.mk W.toAffine p) /
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (CoordinateRing.mk W.toAffine q))
    (c : F) :
    a - algebraMap F W.toAffine.FunctionField c =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (CoordinateRing.mk W.toAffine (p - C (C c) * q)) /
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (CoordinateRing.mk W.toAffine q) := by
  rw [ha, div_sub' hq, ← algebraMap_mk_C_C, map_sub, map_mul, map_sub, map_mul, mul_comm]

/-- `[n]*y − y'` vanishes at `P` when `n • P = (x', y')`. -/
private theorem valuation_pointPlace_mulByIntY_sub_lt_one {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : psiFunctionField W n ≠ 0) {x' y' : F} (h' : W.toAffine.Nonsingular x' y')
    (hnP : n • Affine.Point.some x y h = Affine.Point.some x' y' h') :
    (CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField
        (mulByIntY W n - algebraMap F W.toAffine.FunctionField y') < 1 := by
  have hψ := evalEval_ψ_ne_zero_of_zsmul_ne_zero W h (hnP.trans_ne (Affine.Point.some_ne_zero h'))
  have hpsi3 : psiFunctionField W n ^ 3 =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (CoordinateRing.mk W.toAffine ((W.ψ n) ^ 3)) := by
    rw [map_pow, map_pow, ← psiFunctionField_def]
  rw [sub_algebraMap_eq_div W (p := W.ω n) (hpsi3 ▸ pow_ne_zero 3 hn)
    (by rw [mulByIntY_def, omegaFunctionField_def, hpsi3]) y']
  refine CoordinateRing.valuation_pointPlace_div_lt_one _ h.left
    (by rw [evalEval_pow]; exact pow_ne_zero 3 hψ) ?_
  rw [evalEval_sub, evalEval_mul, evalEval_pow, evalEval_C, eval_C,
    ← W.mul_evalEval_ψ_cube_eq_evalEval_ω_of_zsmul h h' hnP, sub_self]

/-- `[n]*x` takes the value `x'` at `P` when `n • P = (x', y')`. -/
private theorem valuation_pointPlace_mulByIntX_sub_lt_one {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : psiFunctionField W n ≠ 0) {x' y' : F} (h' : W.toAffine.Nonsingular x' y')
    (hnP : n • Affine.Point.some x y h = Affine.Point.some x' y' h') :
    (CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField
        (mulByIntX W n - algebraMap F W.toAffine.FunctionField x') < 1 := by
  have hΨ := eval_ΨSq_ne_zero_of_zsmul_ne_zero W h (hnP.trans_ne (Affine.Point.some_ne_zero h'))
  rw [sub_algebraMap_eq_div W (p := C (W.Φ n)) (psiFunctionField_sq W n ▸ pow_ne_zero 2 hn)
    (by rw [mulByIntX_def, phiFunctionField_def, CoordinateRing.mk_φ, psiFunctionField_sq]) x']
  refine CoordinateRing.valuation_pointPlace_div_lt_one _ h.left (by rwa [evalEval_C]) ?_
  rw [evalEval_sub, evalEval_mul, evalEval_C, evalEval_C, evalEval_C, eval_C,
    ← mul_eval_ΨSq_eq_eval_Φ_of_zsmul W h h' hnP, sub_self]

/-- Step 2: the comap of the place of `P` is at most `1` on the whole coordinate ring. -/
private theorem comap_algebraMap_coordinateRing_le_one {x y : F}
    (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (hP : n • Affine.Point.some x y h ≠ 0)
    (r : W.toAffine.CoordinateRing) :
    (((CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField).comap
        (mulByIntIsogeny W hn).fieldPullback.toRingHom)
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r) ≤ 1 := by
  refine Valuation.algebraMap_coordinateRing_le_one _ ?_ r
  rw [Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    ← WeierstrassCurve.Affine.genericX_eq_algebraMap,
    fieldPullback_mulByIntIsogeny_genericX, mulByIntX_def, phiFunctionField_def,
    CoordinateRing.mk_φ, psiFunctionField_sq]
  exact CoordinateRing.valuation_pointPlace_div_le_one _ h.left
    (by rw [evalEval_C]; exact eval_ΨSq_ne_zero_of_zsmul_ne_zero W h hP)

/-- **The place of `P` restricts along `[n]` to the place of `n • P`**, for an affine `n • P`. The
case `n • P = 0` is `isEquiv_comap_pointPlace_infinityPlace_iff`. -/
-- Normalizing the restricted valuation and taking its centre on the coordinate ring names a height
-- one prime; the two division-polynomial coordinate identities put the ideal of `n • P` inside
-- that centre, and maximality of the point ideal forces the two to agree.
theorem isEquiv_comap_pointPlace {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    {x' y' : F} (h' : W.toAffine.Nonsingular x' y')
    (hnP : n • Affine.Point.some x y h = Affine.Point.some x' y' h') :
    (((CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField).comap
        (mulByIntIsogenyOfNeZero W
            (left_ne_zero_of_smul (hnP.trans_ne (Affine.Point.some_ne_zero h')))
          ).fieldPullback.toRingHom).IsEquiv
      ((CoordinateRing.pointPlace h'.left).valuation W.toAffine.FunctionField) := by
  have hP0 : n • Affine.Point.some x y h ≠ 0 := hnP.trans_ne (Affine.Point.some_ne_zero h')
  have hn : psiFunctionField W n ≠ 0 :=
    psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero (left_ne_zero_of_smul hP0)
  set v := (CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField with hvdef
  set u := v.comap (mulByIntIsogeny W hn).fieldPullback.toRingHom with hudef
  -- an explicit element of value strictly between `0` and `1`: `[n]*x - x'` vanishes at `P`
  -- (so its value is below `1`) but is not the zero function (so its value is not `0`)
  set z := algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
    (CoordinateRing.XClass W.toAffine x') with hzdef
  -- `XClass x'` is `x - x'`, so its pullback is `[n]*x - x'`
  have huz : u z = v (mulByIntX W n - algebraMap F W.toAffine.FunctionField x') := by
    rw [hzdef, hudef, Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    simp only [CoordinateRing.XClass, map_sub, ← genericX_def, algebraMap_mk_C_C,
      fieldPullback_mulByIntIsogeny_genericX, AlgHom.commutes]
  have hz1 : u z ≠ 1 := by
    rw [huz]; exact (valuation_pointPlace_mulByIntX_sub_lt_one W h hn h' hnP).ne
  have hz0 : u z ≠ 0 := by
    rw [huz]; exact (Valuation.ne_zero_iff v).mpr (mulByIntX_sub_algebraMap_ne_zero W hn x')
  have : u.IsNontrivial := ⟨z, hz0, hz1⟩
  obtain ⟨Q, hQu, hQmem⟩ := Valuation.exists_heightOneSpectrum_isEquiv_of_le_one
    W.toAffine.CoordinateRing u (comap_algebraMap_coordinateRing_le_one W h hn hP0)
  have hmemX : CoordinateRing.XClass W.toAffine x' ∈ Q.asIdeal := by
    rw [hQmem, ← hzdef, huz]
    exact valuation_pointPlace_mulByIntX_sub_lt_one W h hn h' hnP
  have hmemY : CoordinateRing.YClass W.toAffine (C y') ∈ Q.asIdeal := by
    -- `YClass (C y')` is `y - y'`, so its pullback is `[n]*y - y'`
    have hY : (mulByIntIsogeny W hn).fieldPullback (algebraMap W.toAffine.CoordinateRing
        W.toAffine.FunctionField (CoordinateRing.YClass W.toAffine (C y'))) =
        mulByIntY W n - algebraMap F W.toAffine.FunctionField y' := by
      simp only [CoordinateRing.YClass, map_sub, ← genericY_def, algebraMap_mk_C_C,
        fieldPullback_mulByIntIsogeny_genericY, AlgHom.commutes]
    rw [hQmem, Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hY]
    exact valuation_pointPlace_mulByIntY_sub_lt_one W h hn h' hnP
  rw [← CoordinateRing.eq_pointPlace_of_mem_asIdeal h'.left hmemX hmemY]
  exact hQu.symm

/-- **The place of an affine `n`-torsion point restricts along `[n]` to the place at infinity.**
For `P = (x, y)` with `n • P = 0`, the valuation `z ↦ v_P([n]^* z)` of `F(W)` is equivalent to the
place at infinity: `[n]*x = Φₙ/ΨSqₙ` has a pole at `P`. No closure hypothesis on `F` is needed. -/
-- `ΨSqₙ` vanishes at `x` because `P` is `n`-torsion, and `Φₙ`, having no root in common with it,
-- does not; the place at infinity is the only place at which `x` has a pole.
theorem isEquiv_comap_pointPlace_infinityPlace_of_zsmul_eq_zero {x y : F}
    (h : W.toAffine.Nonsingular x y) {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (hnP : n • Affine.Point.some x y h = 0) :
    (((CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField).comap
        (mulByIntIsogeny W hn).fieldPullback.toRingHom).IsEquiv (infinityPlace W.toAffine) := by
  refine isEquiv_infinityPlace_of_one_lt _ ?_
  have hΨ : (W.ΨSq n).eval x = 0 := (W.eval_ΨSq_eq_zero_iff_zsmul_eq_zero h n).mpr
    (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mpr hnP)
  have hΦ : (W.Φ n).eval x ≠ 0 := by
    simpa [hΨ] using aeval_ne_zero_of_isCoprime (W.isCoprime_Φ_ΨSq n W.isUnit_Δ.ne_zero) x
  rw [Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    ← WeierstrassCurve.Affine.genericX_eq_algebraMap,
    fieldPullback_mulByIntIsogeny_genericX, mulByIntX_def, phiFunctionField_def,
    CoordinateRing.mk_φ, psiFunctionField_sq]
  exact CoordinateRing.one_lt_valuation_pointPlace_div _ h.left (by rwa [evalEval_C])
    (by rwa [evalEval_C])
    fun h0 ↦ pow_ne_zero 2 hn (by rw [psiFunctionField_sq, h0, map_zero])

/-- **The affine points over the place at infinity are the `n`-torsion points.** For an
`F`-rational affine point `P`, the place of `P` restricts along `[n]` to the place at infinity
exactly when `n • P = 0`. -/
-- Stated with the coercion rather than `fieldPullback.toRingHom`, as for
-- `isEquiv_comap_pointPlace_iff`, so that the left-hand side is in `simp` normal form.
@[simp]
theorem isEquiv_comap_pointPlace_infinityPlace_iff {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    (((CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField).comap
        (mulByIntIsogeny W hn).fieldPullback).IsEquiv (infinityPlace W.toAffine) ↔
      n • Affine.Point.some x y h = 0 := by
  refine ⟨fun hinf ↦ ?_, isEquiv_comap_pointPlace_infinityPlace_of_zsmul_eq_zero W h hn⟩
  by_contra hP0
  -- otherwise `n • P` is affine, and the restriction is also the place of `n • P`, at which `x`
  -- has no pole
  obtain ⟨x', y', h', hnP⟩ := Affine.Point.exists_eq_some_of_ne_zero hP0
  exact Place.not_isEquiv_infinityPlace_valuation (CoordinateRing.pointPlace h'.left)
    ((isEquiv_comap_pointPlace W h h' hnP).symm.trans hinf).symm

/-- **The affine points over the place of `T` are its `[n]`-preimages.** For `F`-rational affine
points `P` and `T`, the place of `P` restricts along `[n]` to the place of `T` precisely when
`n • P = T`. -/
-- The left-hand side is stated with the coercion rather than `fieldPullback.toRingHom`, which is
-- what `AlgHom.toRingHom_eq_coe` normalises it to; in the `toRingHom` spelling `simpNF` rejects
-- the attribute, since simp would rewrite the term the lemma keys on.
@[simp]
theorem isEquiv_comap_pointPlace_iff {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) {x' y' : F} (h' : W.toAffine.Nonsingular x' y') :
    (((CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField).comap
        (mulByIntIsogeny W hn).fieldPullback).IsEquiv
      ((CoordinateRing.pointPlace h'.left).valuation W.toAffine.FunctionField) ↔
      n • Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  refine ⟨fun hab ↦ ?_, isEquiv_comap_pointPlace W h h'⟩
  -- a point that `[n]` kills restricts to the place at infinity, which is not the place of `T`
  by_cases hP0 : n • Affine.Point.some x y h = 0
  · exact absurd ((isEquiv_comap_pointPlace_infinityPlace_of_zsmul_eq_zero W h hn hP0).symm.trans
      hab) (Place.not_isEquiv_infinityPlace_valuation (CoordinateRing.pointPlace h'.left))
  -- otherwise `n • P` has affine coordinates, and both places restrict to the same one
  obtain ⟨x'', y'', h'', hnP⟩ := Affine.Point.exists_eq_some_of_ne_zero hP0
  have hb := isEquiv_comap_pointPlace W h h'' hnP
  have hpq : CoordinateRing.pointPlace h''.left = CoordinateRing.pointPlace h'.left :=
    HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (hb.symm.trans hab)
  obtain ⟨rfl, rfl⟩ := (CoordinateRing.pointPlace_eq_iff h''.left h'.left).mp hpq
  rw [hnP]

/-- **The places over the place of `T` along `[n]` are the places of the `[n]`-preimages of
`T`**, among the places of points. -/
theorem isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (R T : W.toAffine.Point) :
    (((pointEquivDegreeOnePlace W.toAffine R).1.valuation).comap
        (mulByIntIsogeny W hn).fieldPullback.toRingHom).IsEquiv
      (pointEquivDegreeOnePlace W.toAffine T).1.valuation ↔ n • R = T := by
  have hinf : ((infinityPlace W.toAffine).comap
      (mulByIntIsogeny W hn).fieldPullback.toRingHom).IsEquiv (infinityPlace W.toAffine) :=
    isEquiv_comap_infinityPlace _
  rcases R with _ | ⟨xR, yR, hR⟩ <;> rcases T with _ | ⟨xT, yT, hT⟩
  · rw [coe_pointEquivDegreeOnePlace_zero, Place.valuation_infinity, ← Affine.Point.zero_def,
      smul_zero]
    exact iff_of_true hinf rfl
  · rw [coe_pointEquivDegreeOnePlace_zero, Place.valuation_infinity,
      coe_pointEquivDegreeOnePlace_some, Place.valuation_ofPrime, ← Affine.Point.zero_def,
      smul_zero]
    exact iff_of_false
      (fun hE ↦ Place.not_isEquiv_infinityPlace_valuation (CoordinateRing.pointPlace hT.left)
        (hinf.symm.trans hE))
      (Affine.Point.some_ne_zero hT).symm
  · rw [coe_pointEquivDegreeOnePlace_some, Place.valuation_ofPrime,
      coe_pointEquivDegreeOnePlace_zero, Place.valuation_infinity, ← Affine.Point.zero_def]
    exact isEquiv_comap_pointPlace_infinityPlace_iff W hR hn
  · rw [coe_pointEquivDegreeOnePlace_some, coe_pointEquivDegreeOnePlace_some,
      Place.valuation_ofPrime, Place.valuation_ofPrime]
    exact isEquiv_comap_pointPlace_iff W hR hn hT

/-- **The `[n]`-fibre over a point is finite**: the places of its points lie over the place of
`T`, and a place has finitely many places above it in the finite extension `[n]`. -/
theorem finite_setOf_zsmul_eq {n : ℤ} (hn : psiFunctionField W n ≠ 0) (T : W.toAffine.Point) :
    {R : W.toAffine.Point | n • R = T}.Finite := by
  let _ := (mulByIntIsogeny W hn).fieldPullback.toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_fieldPullback (mulByIntIsogeny W hn) fun _ ↦ rfl
  have := (mulByIntIsogeny W hn).finiteDimensional_functionField fun _ ↦ rfl
  have hinj : Function.Injective fun R : W.toAffine.Point ↦
      (pointEquivDegreeOnePlace W.toAffine R).1 :=
    Subtype.val_injective.comp (pointEquivDegreeOnePlace W.toAffine).injective
  exact ((Place.finite_setOf_restrict_eq (k' := F) (F' := W.toAffine.FunctionField) F
    W.toAffine.FunctionField (pointEquivDegreeOnePlace W.toAffine T).1).preimage
      hinj.injOn).subset fun R hR ↦
    (Place.restrict_eq_iff_isEquiv_comap F _ _ _).mpr
      ((isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff W hn R T).mpr hR)

section SepClosed

variable [IsSepClosed F]

/-- **The places over the place of `T` along `[n]` are the places of its `[n]`-preimages**, over
a separably closed field in which `n` is invertible: a place above a point place has degree one,
since `[n]` splits every place completely. -/
theorem restrict_eq_pointEquivDegreeOnePlace_iff {n : ℤ} (hchar : (n : F) ≠ 0)
    (T : W.toAffine.Point) (P : Place F W.toAffine.FunctionField) :
    letI := (mulByIntIsogeny W
      (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
    haveI := isScalarTower_of_algebraMap_eq_fieldPullback
      (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)) (fun _ ↦ rfl)
    haveI := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).finiteDimensional_functionField
      (fun _ ↦ rfl)
    P.restrict F W.toAffine.FunctionField = (pointEquivDegreeOnePlace W.toAffine T).1 ↔
      ∃ R, n • R = T ∧ (pointEquivDegreeOnePlace W.toAffine R).1 = P := by
  let _ := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_fieldPullback
    (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)) (fun _ ↦ rfl)
  have := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).finiteDimensional_functionField
    (fun _ ↦ rfl)
  have := (isSeparable_mulByIntIsogeny_iff W (psiFunctionField_ne_zero W hchar)).2 hchar
  have hover (R : W.toAffine.Point) :
      (pointEquivDegreeOnePlace W.toAffine R).1.restrict F W.toAffine.FunctionField =
        (pointEquivDegreeOnePlace W.toAffine T).1 ↔ n • R = T :=
    (Place.restrict_eq_iff_isEquiv_comap F _ _ _).trans
      (isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff W _ R T)
  refine ⟨fun hP ↦ ?_, fun ⟨R, hR, hRP⟩ ↦ by rw [← hRP]; exact (hover R).mpr hR⟩
  -- a place over a place of degree one has degree one, the relative degree being one
  have hdeg : P.degree = 1 := by
    rw [Place.degree_eq_degree_restrict_mul_relativeDegree F W.toAffine.FunctionField P, hP,
      (pointEquivDegreeOnePlace W.toAffine T).2, one_mul]
    exact (isSplitCompletely _ (fun _ ↦ rfl) _).relativeDegree_eq_one hP
  obtain ⟨R, hR⟩ : ∃ R, (pointEquivDegreeOnePlace W.toAffine R).1 = P :=
    ⟨(pointEquivDegreeOnePlace W.toAffine).symm ⟨P, hdeg⟩, by simp⟩
  exact ⟨R, (hover R).mp (by rw [hR]; exact hP), hR⟩

end SepClosed

end TauCeti.Isogeny
end
