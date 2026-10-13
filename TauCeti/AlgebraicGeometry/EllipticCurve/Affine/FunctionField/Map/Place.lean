/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal
-- Proof-only: a valuation with no pole at `x` has no pole on the coordinate ring.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.CoordinateRingIntegral
-- Proof-only: the place of `f P` restricts to a valuation equivalent to the place of `P`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Reduction
-- Proof-only: a valuation bounded on a Dedekind domain is equivalent to an adic valuation, and a
-- generating set of a height one prime contains an element of order one.
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

/-!
# Places of points under change of the coefficient field

Let `W` be an elliptic curve over a field `F` and `f : F →+* K` a homomorphism of fields. A point
`P` of `W` is carried to the point `f P` of `W.map f`, and the function field `F(W)` embeds into
`K(W.map f)` (`WeierstrassCurve.Affine.FunctionField.map`). This file compares the places of the
two function fields at the points.

The place of `f P` restricts to the place of `P`, with ramification index one: the order at `f P`
of the image of a function is its order at `P`. At an affine point `P = (x₀, y₀)` the restriction
is centred at the ideal `(x - x₀, y - y₀)`, which identifies it with the place of `P` up to
equivalence. The ramification index is read off from a uniformizer at `f P` that is defined over
`F`: one of `x - f x₀` and `y - f y₀` has order one, since they generate the ideal of `f P`. At the
point at infinity the function `x / y` has order one on both sides.

Conversely, a place of `K(W.map f)` whose restriction to `F(W)` is equivalent to the place of `P`
is the place of `f P`, and a place at which some function of `F(W)` has a zero or a pole restricts
to a place of `F(W)`. So the divisor of a function whose zeros and poles lie at rational points is
carried to the corresponding divisor over `K`:

    div (f^* g) = ∑ D(P) (f P)   when   div g = ∑ D(P) (P).

No hypothesis on the extension `K / F` is needed: it may be transcendental or inseparable.

## Main results

* `WeierstrassCurve.Affine.FunctionField.comap_valuation_pointEquivDegreeOnePlace_map`: the place
  of `f P` restricts to the place of `P`.
* `WeierstrassCurve.Affine.FunctionField.ord_pointEquivDegreeOnePlace_map`: the order at `f P` of
  the image of a function is its order at `P`.
* `WeierstrassCurve.Affine.FunctionField.exists_isEquiv_comap_valuation_map`: a place at which
  the image of a function has a zero or a pole restricts to a place of `F(W)`.
* `WeierstrassCurve.Affine.FunctionField.eq_pointEquivDegreeOnePlace_mapAlong_of_isEquiv`: a
  place restricting to the place of `P` is the place of `f P`.
* `WeierstrassCurve.Affine.FunctionField.principal_map_eq_pushforward`: a principal divisor
  supported on rational points is carried to the corresponding divisor over `K`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.1–II.3.
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], III.1, III.6.
-/

public section

open Polynomial IsDedekindDomain TauCeti TauCeti.AlgebraicGeometry
open scoped WithZero

namespace WeierstrassCurve.Affine.FunctionField

variable {F K : Type*} [Field F] [Field K] (W : WeierstrassCurve.Affine F) (f : F →+* K)

/-- The coordinate ring of an elliptic curve is a Dedekind domain, over any field; this is used
for both `W` and `W.map f`. -/
local instance {L : Type*} [Field L] (V : WeierstrassCurve.Affine L) [V.IsElliptic] :
    IsDedekindDomain V.CoordinateRing :=
  have := isIntegrallyClosed_coordinateRing V
  V.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **The restriction of a place of `K(W.map f)` to `F(W)` is trivial on `F`**, since `f` carries
the constants of `F(W)` to constants of `K(W.map f)`. -/
theorem isTrivialOn_comap_valuation_map (w : Place K (W.map f).FunctionField) :
    (w.valuation.comap (map W f)).IsTrivialOn F where
  eq_one a ha := by
    rw [Valuation.comap_apply, map_algebraMap]
    exact Valuation.IsTrivialOn.eq_one (f a) ((map_ne_zero f).mpr ha)

/-- **The place at infinity of `W.map f` restricts to the place at infinity of `W`.** -/
-- The two are equivalent, and `x / y` has order one at both.
private theorem comap_valuation_infinity_map :
    (Place.infinity (W.map f)).valuation.comap (map W f) = (Place.infinity W).valuation := by
  have hxy (V : WeierstrassCurve.Affine K) : V.infinityPlace (V.genericX / V.genericY) =
      WithZero.exp (-1) := by
    rw [genericX_eq_algebraMap, IsScalarTower.algebraMap_apply K[X] V.CoordinateRing
      V.FunctionField, genericY_def, infinityPlace.X_div_mk_Y]
  refine Valuation.eq_of_isEquiv_of_surjective (Valuation.surjective_of_map_eq_exp_neg_one _
    (t := W.genericX / W.genericY) ?_) (Place.valuation_surjective _) ?_
  · rw [Valuation.comap_apply, map_div₀, map_genericX, map_genericY, Place.valuation_infinity,
      hxy]
  · rw [Place.valuation_infinity, Place.valuation_infinity]
    exact isEquiv_comap_infinityPlace_map W f

variable [W.IsElliptic]

/-- **The place of `f P` restricts to the place of `P`**, at an affine point `P`. -/
-- The restriction is equivalent to the place of `P`; it is normalized because one of `x - f x₀`
-- and `y - f y₀`, both images of functions on `W`, is a uniformizer at `f P`.
private theorem comap_valuation_ofPrime_pointPlace_map {x y : F} (h : W.Nonsingular x y) :
    (Place.ofPrime K (W.map f).FunctionField
        (CoordinateRing.pointPlace
          ((W.map_nonsingular f.injective x y).mpr h).left)).valuation.comap (map W f) =
      (Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h.left)).valuation := by
  have h' := (W.map_nonsingular f.injective x y).mpr h
  obtain ⟨r, hr, hr1⟩ := (CoordinateRing.pointPlace h'.left).exists_mem_intValuation_eq_exp_neg_one
    (s := {CoordinateRing.XClass (W.map f) (f x), CoordinateRing.YClass (W.map f) (C (f y))})
    (by rw [CoordinateRing.pointPlace_asIdeal, CoordinateRing.XYIdeal])
  obtain ⟨r₀, rfl⟩ : ∃ r₀, CoordinateRing.map W f r₀ = r := by
    rcases hr with rfl | rfl
    · exact ⟨_, CoordinateRing.map_XClass W f x⟩
    · exact ⟨CoordinateRing.YClass W (C y), by rw [CoordinateRing.map_YClass, Polynomial.map_C]⟩
  refine Valuation.eq_of_isEquiv_of_surjective (Valuation.surjective_of_map_eq_exp_neg_one _
    (t := algebraMap W.CoordinateRing W.FunctionField r₀) ?_) (Place.valuation_surjective _)
    (isEquiv_comap_pointPlace_map W f h.left)
  rw [Valuation.comap_apply, map_algebraMap_coordinateRing, Place.valuation_ofPrime_algebraMap, hr1]

/-- **The place of `f P` restricts to the place of `P`**: for every function `z` on `W`, the value
of `f^* z` at `f P` is the value of `z` at `P`. -/
theorem comap_valuation_pointEquivDegreeOnePlace_map (P : W.Point) :
    (pointEquivDegreeOnePlace (W.map f) (P.mapAlong f f.injective)).1.valuation.comap (map W f) =
      (pointEquivDegreeOnePlace W P).1.valuation := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, Point.mapAlong_zero, Point.zero_def, Point.zero_def,
      coe_pointEquivDegreeOnePlace_zero, coe_pointEquivDegreeOnePlace_zero]
    exact comap_valuation_infinity_map W f
  · rw [Point.mapAlong_some, coe_pointEquivDegreeOnePlace_some, coe_pointEquivDegreeOnePlace_some]
    exact comap_valuation_ofPrime_pointPlace_map W f h

/-- **The order at `f P` of `f^* z` is the order at `P` of `z`**: changing the coefficient field
does not ramify the places of points. -/
@[simp]
theorem ord_pointEquivDegreeOnePlace_map (P : W.Point) (z : W.FunctionField) :
    (pointEquivDegreeOnePlace (W.map f) (P.mapAlong f f.injective)).1.ord (map W f z) =
      (pointEquivDegreeOnePlace W P).1.ord z := by
  rw [Place.ord_def, Place.ord_def, ← comap_valuation_pointEquivDegreeOnePlace_map W f P,
    Valuation.comap_apply]

/-- **A place at which the image of a function has a zero or a pole restricts to a place**: if
`f^* z` is not a unit at the place `w` of `K(W.map f)` for some `z ≠ 0`, then the restriction of
`w` to `F(W)` is equivalent to a place of `F(W)`. -/
theorem exists_isEquiv_comap_valuation_map (w : Place K (W.map f).FunctionField)
    {z : W.FunctionField} (hz : z ≠ 0) (hwz : w.valuation (map W f z) ≠ 1) :
    ∃ P : Place F W.FunctionField, (w.valuation.comap (map W f)).IsEquiv P.valuation := by
  set u := w.valuation.comap (map W f)
  have := isTrivialOn_comap_valuation_map W f w
  -- either `x` has a pole, and the restriction is the place at infinity, or the restriction has
  -- no pole on the coordinate ring, and is centred at a height one prime
  by_cases hx : 1 < u (algebraMap F[X] W.FunctionField X)
  · exact ⟨Place.infinity W, by
      rw [Place.valuation_infinity]
      exact isEquiv_infinityPlace_of_one_lt _ hx⟩
  · have : u.IsNontrivial := ⟨⟨z, (Valuation.ne_zero_iff u).mpr hz, hwz⟩⟩
    obtain ⟨Q, hQu, -⟩ := Valuation.exists_heightOneSpectrum_isEquiv_of_le_one W.CoordinateRing u
      (Valuation.algebraMap_coordinateRing_le_one u (not_lt.mp hx))
    exact ⟨Place.ofPrime F W.FunctionField Q, by rw [Place.valuation_ofPrime]; exact hQu.symm⟩

/-- **A place restricting to the place of `P` is the place of `f P`**: if the restriction of a
place `w` of `K(W.map f)` to `F(W)` is equivalent to the place of a point `P` of `W`, then `w` is
the place of `f P`. -/
theorem eq_pointEquivDegreeOnePlace_mapAlong_of_isEquiv (w : Place K (W.map f).FunctionField)
    (P : W.Point)
    (h : (w.valuation.comap (map W f)).IsEquiv (pointEquivDegreeOnePlace W P).1.valuation) :
    w = (pointEquivDegreeOnePlace (W.map f) (P.mapAlong f f.injective)).1 := by
  have := isTrivialOn_comap_valuation_map W f w
  rcases P with _ | ⟨x, y, hP⟩
  · -- `x` has a pole at the restriction, hence at `w`
    rw [coe_pointEquivDegreeOnePlace_zero, Place.valuation_infinity] at h
    rw [← Point.zero_def, Point.mapAlong_zero, Point.zero_def, coe_pointEquivDegreeOnePlace_zero]
    have hx := h.one_lt_iff_one_lt.mpr (one_lt_infinityPlace_X W)
    rw [Valuation.comap_apply, map_algebraMap_X] at hx
    refine Place.eq_of_isEquiv ?_
    rw [Place.valuation_infinity]
    exact isEquiv_infinityPlace_of_one_lt _ hx
  · -- `x` has no pole at `w`, and `x - f x₀`, `y - f y₀` vanish there
    rw [coe_pointEquivDegreeOnePlace_some] at h
    rw [Point.mapAlong_some, coe_pointEquivDegreeOnePlace_some]
    have hx := h.le_one_iff_le_one.mpr
      ((Place.exists_eq_ofPrime_iff_valuation_X_le_one _).mp ⟨_, rfl⟩)
    rw [Valuation.comap_apply, map_algebraMap_X] at hx
    have hX := h.lt_one_iff_lt_one.mpr (valuation_pointPlace_genericX_sub_lt_one W hP.left)
    have hY := h.lt_one_iff_lt_one.mpr (valuation_pointPlace_genericY_sub_lt_one W hP.left)
    rw [Valuation.comap_apply, map_sub, map_genericX, map_algebraMap, ← algebraMap_XClass] at hX
    rw [Valuation.comap_apply, map_sub, map_genericY, map_algebraMap, ← algebraMap_YClass] at hY
    obtain ⟨Q, rfl⟩ := (Place.exists_eq_ofPrime_iff_valuation_X_le_one w).mpr hx
    rw [CoordinateRing.eq_pointPlace_of_mem_asIdeal _
      ((Place.valuation_ofPrime_algebraMap_lt_one_iff _ _ _).mp hX)
      ((Place.valuation_ofPrime_algebraMap_lt_one_iff _ _ _).mp hY)]

/-- **The divisor of a function supported on rational points, after changing the coefficient
field.** If the divisor of `g` is `∑ D(P) (P)` for a divisor `D` on the points of `W`, then the
divisor of `f^* g` is `∑ D(P) (f P)`. -/
theorem principal_map_eq_pushforward {g : W.FunctionFieldˣ} {D : WeilDivisor W.Point}
    (hg : Divisor.principal W.isFunctionField g =
      WeilDivisor.pushforward (fun P ↦ (pointEquivDegreeOnePlace W P).1) D) :
    Divisor.principal (W.map f).isFunctionField (Units.map (map W f).toMonoidHom g) =
      WeilDivisor.pushforward
        (fun P ↦ (pointEquivDegreeOnePlace (W.map f) (P.mapAlong f f.injective)).1) D := by
  classical
  have hρ : Function.Injective fun P ↦ (pointEquivDegreeOnePlace W P).1 :=
    Subtype.val_injective.comp (pointEquivDegreeOnePlace W).injective
  have hρ' : Function.Injective
      fun P : W.Point ↦ (pointEquivDegreeOnePlace (W.map f) (P.mapAlong f f.injective)).1 :=
    (Subtype.val_injective.comp (pointEquivDegreeOnePlace (W.map f)).injective).comp
      (Point.mapAlong_injective f f.injective)
  refine WeilDivisor.ext fun w ↦ ?_
  simp only [Divisor.coeff_principal, RingHom.toMonoidHom_eq_coe, Units.coe_map,
    MonoidHom.coe_ofClass]
  by_cases hw : w ∈ Set.range
      fun P : W.Point ↦ (pointEquivDegreeOnePlace (W.map f) (P.mapAlong f f.injective)).1
  · -- at the place of `f P`, both sides are the order of `g` at `P`
    obtain ⟨P, rfl⟩ := hw
    rw [ord_pointEquivDegreeOnePlace_map, ← WeilDivisor.coeff_pullback hρ',
      ← Divisor.coeff_principal W.isFunctionField,
      hg, ← WeilDivisor.coeff_pullback hρ, WeilDivisor.pullback_pushforward,
      WeilDivisor.pullback_pushforward]
  · -- elsewhere `f^* g` is a unit: a zero or a pole would lie over a zero or a pole of `g`, which
    -- is at a rational point, and the place over the place of `P` is that of `f P`
    rw [WeilDivisor.coeff_pushforward, Finset.sum_eq_zero fun P hP ↦
      (hw ⟨P, (Finset.mem_filter.mp hP).2⟩).elim]
    by_contra hne
    have hwg : w.valuation (map W f g) ≠ 1 := fun h1 ↦ hne (by rw [Place.ord_def, h1]; simp)
    obtain ⟨Q, hQ⟩ := exists_isEquiv_comap_valuation_map W f w g.ne_zero hwg
    have hQg : Q ∈ (Divisor.principal W.isFunctionField g).support := by
      rw [Divisor.mem_support_principal_iff]
      intro h0
      refine hwg ((hQ.eq_one_iff_eq_one (x := (g : W.FunctionField))).mpr ?_)
      rw [Place.valuation_eq_exp_neg_ord _ g.ne_zero, h0, neg_zero, WithZero.exp_zero]
    rw [hg, WeilDivisor.pushforward_apply] at hQg
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hQg)
    exact hw ⟨P, (eq_pointEquivDegreeOnePlace_mapAlong_of_isEquiv W f w P hQ).symm⟩

end WeierstrassCurve.Affine.FunctionField

end
