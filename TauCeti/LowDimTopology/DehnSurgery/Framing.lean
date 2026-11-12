/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Torus.FirstHomology
public import TauCeti.LowDimTopology.DehnSurgery.Slope
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Basic

/-!
# Framing a parametrized torus, and the boundary torus of a knot exterior

A parametrization `e : S¹ × S¹ ≃ₜ Y` of a torus `Y` frames it: the classes of the two coordinate
circles `t ↦ e (exp (2πit), 1)` and `t ↦ e (1, exp (2πit))` form an ordered basis of `H₁(Y; ℤ)`,
by the computation `TauCeti.circleProdFirstHomologyEquiv` of the first homology of a parametrized
torus. This file builds that framed boundary torus, `TauCeti.FramedBoundaryTorus.ofHomeomorph e`,
whose meridian is the first coordinate circle and whose longitude is the second, and computes its
coordinates: the class of the `(p, q)` curve `t ↦ e (exp (2πipt), exp (2πiqt))` has
`(μ, λ)`-coordinates `(p, q)`. So that class is primitive exactly when `p` and `q` are coprime, and
then its slope has value `p / q`. This is the convention of the Dehn-surgery slopes: the slope
`p / q` is the class of `p · μ + q · λ`, realized by an explicit curve on the torus.

Applied to a solid torus neighbourhood `Φ : D² × S¹ → X` of a knot in a Hausdorff space, with the
parametrization `TauCeti.IsSolidTorusNeighborhood.exteriorFrontierHomeomorph` of the frontier of
the knot exterior, this frames the boundary torus of the exterior by `Φ`
(`TauCeti.IsSolidTorusNeighborhood.framedBoundaryTorus`). Its meridian is the boundary
`t ↦ Φ (exp (2πit), 1)` of a disc fibre of the solid torus, and its longitude is the push-off
`t ↦ Φ (1, exp (2πit))` of the knot. This is the framed torus along which a Dehn filling of the
exterior is specified by a slope. The longitude determined by `Φ` is generally not the preferred
(Seifert) longitude. Under vanishing first and second integral homology of the ambient space,
`TauCeti.IsSolidTorusNeighborhood.preferredFramedBoundaryTorus` in
`TauCeti/LowDimTopology/DehnSurgery/SeifertFraming.lean` constructs the preferred framing
`(μ, λ - n · μ)`, where `n` is the framing number of `Φ`.

## Main definitions

* `TauCeti.FramedBoundaryTorus.ofHomeomorph e`: the torus `Y` framed by the parametrization `e`.
* `TauCeti.FramedBoundaryTorus.torusCurveClass e p q`: the class in `H₁(Y; ℤ)` of the `(p, q)`
  curve `t ↦ e (exp (2πipt), exp (2πiqt))`.
* `TauCeti.IsSolidTorusNeighborhood.framedBoundaryTorus`: the boundary torus of a knot exterior,
  framed by the solid torus neighbourhood.

## Main results

* `TauCeti.FramedBoundaryTorus.coord_torusCurveClass`: the class of the `(p, q)` curve has
  coordinates `(p, q)`.
* `TauCeti.FramedBoundaryTorus.ofHomeomorph_basis_zero`,
  `TauCeti.FramedBoundaryTorus.ofHomeomorph_basis_one`: the meridian and longitude classes are
  those of the two coordinate circles.
* `TauCeti.FramedBoundaryTorus.isPrimitive_torusCurveClass_iff`,
  `TauCeti.FramedBoundaryTorus.value_mk_torusCurveClass`: the `(p, q)` curve is primitive exactly
  when `p` and `q` are coprime, and then has slope value `p / q`.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Section 2E (meridians and longitudes
  of a framed solid torus) and Section 9F (slopes `p / q` on the boundary torus).
-/

public section

noncomputable section

open ContinuousMap (singularHomologyMap singularHomologyMap_torusClass)

open CategoryTheory unitInterval TauCeti.HurewiczOne

namespace TauCeti

namespace FramedBoundaryTorus

variable {Y : Type} [TopologicalSpace Y]

/-- The torus `Y` framed by a parametrization `e : S¹ × S¹ ≃ₜ Y`: its meridian and longitude are
the classes in `H₁(Y; ℤ)` of the two coordinate circles `t ↦ e (exp (2πit), 1)` and
`t ↦ e (1, exp (2πit))` (`TauCeti.FramedBoundaryTorus.ofHomeomorph_basis_zero`,
`TauCeti.FramedBoundaryTorus.ofHomeomorph_basis_one`).

The body is exposed so that the carrier of the torus is `Y` for consumers, and hence that homology
classes of loops in `Y` are elements of `(ofHomeomorph e).H`. -/
@[expose]
def ofHomeomorph (e : Circle × Circle ≃ₜ Y) : FramedBoundaryTorus where
  torus := ⟨Y, ⟨e.symm.trans circleProdHomeomorphUnitAddTorus⟩⟩
  basis := .ofEquivFun (circleProdFirstHomologyEquiv e)

variable (e : Circle × Circle ≃ₜ Y)

/-- The homology class of the `(p, q)` curve `t ↦ e (exp (2πipt), exp (2πiqt))` on the torus
framed by `e`: the image under `e` of the class `TauCeti.torusClass p q` of the `(p, q)` curve of
`S¹ × S¹`. -/
def torusCurveClass (p q : ℤ) : (ofHomeomorph e).H :=
  singularHomologyMap ℤ 1 (e : C(Circle × Circle, Y)) (torusClass p q)

/-- The class of the `(p, q)` curve on the torus framed by `e` is the image under `e` of the class
of the `(p, q)` curve of `S¹ × S¹`. -/
theorem torusCurveClass_eq_singularHomologyMap (p q : ℤ) :
    torusCurveClass e p q = singularHomologyMap ℤ 1 (e : C(Circle × Circle, Y)) (torusClass p q) :=
  (rfl)

/-- The class of the `(p, q)` curve is its Hurewicz class in `H₁(Y; ℤ)`. -/
theorem torusCurveClass_def (p q : ℤ) :
    torusCurveClass e p q =
      H₁AddEquivHomology (TopCat.of Y) (loopClass ((torusCurve p q).map e.continuous)) :=
  singularHomologyMap_torusClass (e : C(Circle × Circle, Y)) p q

/-- **The coordinates of the `(p, q)` curve.** For the torus framed by a parametrization `e`, the
homology class of the curve `t ↦ e (exp (2πipt), exp (2πiqt))` has `(μ, λ)`-coordinates
`(p, q)`. -/
@[simp]
theorem coord_torusCurveClass (p q : ℤ) :
    (ofHomeomorph e).coord (torusCurveClass e p q) = (p, q) := by
  have hE : (ofHomeomorph e).basis.equivFun (torusCurveClass e p q) = ![p, q] :=
    (congrArg (· (torusCurveClass e p q))
      (Module.Basis.equivFun_ofEquivFun (circleProdFirstHomologyEquiv e))).trans
      ((congrArg (circleProdFirstHomologyEquiv e) (torusCurveClass_def e p q)).trans
        (circleProdFirstHomologyEquiv_torusCurve e p q))
  rw [← LinearEquiv.eq_symm_apply, coord_symm_apply]
  apply (ofHomeomorph e).basis.equivFun.injective
  rw [hE]
  ext i
  fin_cases i <;> simp

/-- The meridian class of the torus framed by `e` is the class of the first coordinate circle
`t ↦ e (exp (2πit), 1)`. -/
theorem ofHomeomorph_basis_zero : (ofHomeomorph e).basis 0 = torusCurveClass e 1 0 := by
  apply (ofHomeomorph e).coord.injective
  rw [coord_basis_zero, coord_torusCurveClass]

/-- The longitude class of the torus framed by `e` is the class of the second coordinate circle
`t ↦ e (1, exp (2πit))`. -/
theorem ofHomeomorph_basis_one : (ofHomeomorph e).basis 1 = torusCurveClass e 0 1 := by
  apply (ofHomeomorph e).coord.injective
  rw [coord_basis_one, coord_torusCurveClass]

/-- The class of the `(p, q)` curve on the torus framed by `e` is primitive exactly when `p` and
`q` are coprime. -/
@[simp]
theorem isPrimitive_torusCurveClass_iff (p q : ℤ) :
    IsPrimitive (torusCurveClass e p q) ↔ IsCoprime p q := by
  rw [← (ofHomeomorph e).coord.isPrimitive_iff, coord_torusCurveClass, isPrimitive_prod_iff]

/-- **The `(p, q)` curve has slope `p / q`.** For coprime `p` and `q`, the slope of the class of
the curve `t ↦ e (exp (2πipt), exp (2πiqt))` on the torus framed by `e` has value `p / q`, read as
`∞` when `q = 0`. -/
theorem value_mk_torusCurveClass {p q : ℤ} (hpq : IsCoprime p q) :
    (ofHomeomorph e).value
        (Slope.mk _ ((isPrimitive_torusCurveClass_iff e p q).2 hpq)) = slopeValue (p, q) := by
  rw [value_mk, coord_torusCurveClass]

end FramedBoundaryTorus

namespace IsSolidTorusNeighborhood

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}

/-- The **boundary torus of a knot exterior, framed by a solid torus neighbourhood** `Φ` of the
knot: the frontier of the exterior, the complement of the image of the open solid torus, framed by
its parametrization `TauCeti.IsSolidTorusNeighborhood.exteriorFrontierHomeomorph`, which sends
`(w, z) ∈ S¹ × S¹` to `Φ (w, z)`. Its meridian is the class of the boundary
`t ↦ Φ (exp (2πit), 1)` of a disc fibre and its longitude the class of the push-off
`t ↦ Φ (1, exp (2πit))` of the knot; the class of the curve `t ↦ Φ (exp (2πipt), exp (2πiqt))`
has coordinates `(p, q)` (`TauCeti.FramedBoundaryTorus.coord_torusCurveClass`). -/
abbrev framedBoundaryTorus (h : IsSolidTorusNeighborhood f Φ) : FramedBoundaryTorus :=
  .ofHomeomorph h.exteriorFrontierHomeomorph

end IsSolidTorusNeighborhood

end TauCeti
