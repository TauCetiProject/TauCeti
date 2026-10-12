/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Basic
-- Proof-only, named in no statement here: the monic witness `Φₙ − C c * ΨSqₙ` with its root
-- equation.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Integral

/-!
# `[n]` maps infinity to infinity

`Isogeny/MulByInt/Basic.lean` builds the coordinate pullback of `[n]` and records that the
`MapsInfinity` condition — and so `[n]` as an `Isogeny W W` — is not proved there. This file
proves it, for every `n` with `ψₙ` nonvanishing at the generic point.

## The argument

`CoordinatePullback.mapsInfinity_iff_isIntegralElem_genericX` reduces pointedness to a single
integral witness, so all that is `[n]`-specific is the generic `x`-coordinate: `[n]*x · ΨSqₙ(x) =
Φₙ(x)` makes it a root of `Φₙ − C ([n]*x) * ΨSqₙ`, monic by `monic_Φ_sub_C_mul_ΨSq`, with `[n]*x`
the pullback of the class of `X`.

## Main results

* `TauCeti.Isogeny.mapsInfinity_mulByIntPullback`: the pullback of `[n]` maps infinity to
  infinity.
* `TauCeti.Isogeny.mulByIntIsogeny`: `[n]` as an `Isogeny W W`.
* `TauCeti.Isogeny.fieldPullback_mulByIntIsogeny_genericX` and
  `TauCeti.Isogeny.fieldPullback_mulByIntIsogeny_genericY`: the pullback of `[n]` sends the generic
  coordinates to `[n]*x` and `[n]*y`.
* `TauCeti.Isogeny.mulByIntX_sub_algebraMap_ne_zero`: `[n]*x` is not a constant — the
  transcendence of the generic coordinate, carried across the pullback.
* `TauCeti.Isogeny.map_mulByIntIsogeny_genericPoint`: the function-field map of `[n]` carries the
  generic point to `n • ` the generic point.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.

## Provenance

The integral witness is adapted from the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) pinned at
`513e83879e2f8cbc626eb9e04d660e92be16ccba`, `HasseWeil/MulByIntPullback.lean`, declaration
`mulByInt_x_transcendental`, which builds the same polynomial
`Φₙ.map (algebraMap F S) − C c * ΨSqₙ.map (algebraMap F S)` and the same root step, there to
contradict transcendence of the generic `x`-coordinate rather than to establish `MapsInfinity`.
Its monicity half is already in this repository as `monic_Φ_sub_C_mul_ΨSq`, itself ported from
that project's `NagellLutz`.

The `MapsInfinity` packaging is not from that source and has no counterpart in it: its `Isogeny`
carries a function-field `AlgHom` obtained by localizing an injective coordinate homomorphism,
with no pointedness field, so it never needs the `y`-coordinate step or the reduction to the two
coordinates.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

-- Private: `mapsInfinity_mulByIntPullback` below states the stronger fact for every element of
-- the coordinate ring, so a consumer wanting this one specialises `mapsInfinity_iff` instead.
private theorem isIntegralElem_genericX [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    RingHom.IsIntegralElem (mulByIntPullback W hn).toRingHom W.genericX := by
  let _ : Algebra W.CoordinateRing W.FunctionField :=
    (mulByIntPullback W hn).toRingHom.toAlgebra
  have hmap : (algebraMap W.CoordinateRing W.FunctionField).comp
      (algebraMap F W.CoordinateRing) = algebraMap F W.FunctionField := by
    ext x; rw [RingHom.algebraMap_toAlgebra]; exact (mulByIntPullback W hn).commutes x
  -- Monicity and the root equation are the two halves of the division-polynomial criterion, and
  -- both are already available: the witness is `Φₙ − C ([n]*x) * ΨSqₙ` over the coordinate ring.
  refine ⟨(W.map (algebraMap F W.CoordinateRing)).Φ n -
      C (AdjoinRoot.of W.polynomial X) * (W.map (algebraMap F W.CoordinateRing)).ΨSq n,
    WeierstrassCurve.monic_Φ_sub_C_mul_ΨSq _ n _, ?_⟩
  refine WeierstrassCurve.aeval_Φ_sub_C_mul_ΨSq_eq_zero _ ?_
  have hx : algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.of W.polynomial X) =
      mulByIntX W n := mulByIntPullback_X W hn
  simp only [hx, _root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_Φ,
    _root_.WeierstrassCurve.map_ΨSq, Polynomial.map_map, hmap, ← eval₂_eq_eval_map, ← aeval_def]
  exact mulByIntX_mul_aeval_ΨSq W n hn

/-- **The pullback of `[n]` maps infinity to infinity**, so `[n]` is an isogeny. -/
theorem mapsInfinity_mulByIntPullback [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    (mulByIntPullback W hn).MapsInfinity :=
  (CoordinatePullback.mapsInfinity_iff_isIntegralElem_genericX _).2
    (isIntegralElem_genericX W hn)

/-- **Multiplication by `n` as an isogeny**, for every `n` whose division polynomial does not
vanish at the generic point. -/
noncomputable def mulByIntIsogeny [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    _root_.TauCeti.Isogeny W W where
  pullback := mulByIntPullback W hn
  mapsInfinity := mapsInfinity_mulByIntPullback W hn

@[simp]
theorem mulByIntIsogeny_pullback [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).pullback = mulByIntPullback W hn :=
  (rfl)

/-- **The function-field map of `[n]` carries the generic point to its `n`-th multiple.** -/
@[simp]
theorem map_mulByIntIsogeny_genericPoint [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    Point.map (mulByIntIsogeny W hn).fieldPullback W.genericPoint = n • W.genericPoint := by
  rw [← tautologicalPoint_eq_map_genericPoint, mulByIntIsogeny_pullback,
    tautologicalPoint_mulByIntPullback]

/-- **Multiplication by `n` as an isogeny, for every `n ≠ 0`**, the non-vanishing hypothesis
discharged by `psiFunctionField_ne_zero_of_Δ_ne_zero` as in `mulByIntPullbackOfNeZero`. -/
noncomputable abbrev mulByIntIsogenyOfNeZero [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    _root_.TauCeti.Isogeny W W :=
  mulByIntIsogeny W (psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero hn)

/-- **The pullback of `[n]` sends the generic `x` to `[n]*x`.**

Not the same statement as `fieldPullback_mulByIntIsogeny_X`, which the degree tower needs and
which lands in `F(x)` as a quotient of `RatFunc F`; this is the `mulByIntX` form, which is what
a computation in `F(W)` wants, as in `mulByIntX_sub_algebraMap_ne_zero` below and in the place and
Wronskian computations downstream. -/
@[simp]
theorem fieldPullback_mulByIntIsogeny_genericX [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).fieldPullback W.genericX = mulByIntX W n := by
  rw [WeierstrassCurve.Affine.genericX_def, fieldPullback_algebraMap, mulByIntIsogeny_pullback]
  exact mulByIntPullback_X W hn

/-- **The pullback of `[n]` sends the generic `y` to `[n]*y`**, the companion of
`fieldPullback_mulByIntIsogeny_genericX` for the second coordinate. -/
@[simp]
theorem fieldPullback_mulByIntIsogeny_genericY [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).fieldPullback W.genericY = mulByIntY W n := by
  rw [WeierstrassCurve.Affine.genericY_def, fieldPullback_algebraMap, mulByIntIsogeny_pullback]
  exact mulByIntPullback_Y W hn

/-- **`[n]*x` is not a constant**: it is the image of the generic coordinate under an injective
map, and the generic coordinate is not a constant. -/
theorem mulByIntX_sub_algebraMap_ne_zero [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (x : F) :
    mulByIntX W n - algebraMap F W.FunctionField x ≠ 0 := by
  rw [sub_ne_zero]
  intro heq
  refine W.genericX_ne_algebraMap x ((mulByIntIsogeny W hn).fieldPullback.toRingHom.injective ?_)
  calc (mulByIntIsogeny W hn).fieldPullback.toRingHom W.genericX
      = mulByIntX W n := fieldPullback_mulByIntIsogeny_genericX W hn
    _ = algebraMap F W.FunctionField x := heq
    _ = (mulByIntIsogeny W hn).fieldPullback.toRingHom (algebraMap F W.FunctionField x) :=
        ((mulByIntIsogeny W hn).fieldPullback.commutes x).symm

end Isogeny

end TauCeti
