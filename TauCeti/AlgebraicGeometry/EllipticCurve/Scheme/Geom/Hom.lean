/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy
public import TauCeti.CategoryTheory.Monoidal.Cartesian.CommGrp

/-!
# Homomorphisms and endomorphisms of elliptic curves over a scheme

Let `E` and `E'` be elliptic curves over a scheme `S`, with their group laws. This file regards
`E` as a commutative group scheme over `S`, that is, a commutative group object
`E.toCommGrp` of `Over S`. A homomorphism `E ⟶ E'` of elliptic curves over `S` is then a morphism
`E.toCommGrp ⟶ E'.toCommGrp` of `CommGrp (Over S)`: a morphism of schemes over `S` together with
the property of being a homomorphism of group schemes. A bare morphism of schemes over `S`
carrying zero to zero is not a homomorphism by definition: that every such morphism is one is a
theorem (Katz–Mazur 2.5.1) which this type does not presuppose.

Since `CommGrp (Over S)` is preadditive (`CategoryTheory.CommGrp.instPreadditive`), the
homomorphisms `E.toCommGrp ⟶ E'.toCommGrp` form an abelian group `Hom_S(E, E')`, and the
endomorphisms `End E.toCommGrp` form a ring `End_S(E)` whose multiplication is composition,
`f * g = g ≫ f`. On underlying schemes, the sum of two homomorphisms is their sum under the
addition morphism of `E'`, the zero homomorphism is the composite of the structure morphism of `E`
and the zero section of `E'`, and the negative is the composite with the negation morphism.

In `End_S(E)`, the integer `n` is multiplication by `n` (`EllipticCurveGeom.mulBy`), so the
ring homomorphism `ℤ → End_S(E)` is multiplication by integers. Its image in the category of group
schemes over `S` is the homomorphism whose kernel is the `n`-torsion `E[n]`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.toCommGrp`: an elliptic curve over `S` as a
  commutative group object of `Over S`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.hom_ext_left`: a homomorphism of elliptic curves is
  determined by its morphism of schemes.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.add_hom_hom_hom_left`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.zero_hom_hom_hom_left` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.neg_hom_hom_hom_left`: the sum, zero and negative
  of homomorphisms on underlying schemes.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.homMk_mulBy`: multiplication by `n` is the integer
  `n` of the endomorphism ring.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3–2.5.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {E' : EllipticCurveGeom S}

/-- **An elliptic curve as a commutative group scheme.** The elliptic curve `E` over `S`, as the
object `Over.mk E.structureMap` of `Over S` with its commutative group law, is a commutative group
object of `Over S`. The morphisms `E.toCommGrp ⟶ E'.toCommGrp` are the homomorphisms of elliptic
curves over `S`, and they form an abelian group. -/
noncomputable abbrev toCommGrp : CommGrp (Over S) :=
  { X := Over.mk E.structureMap }

/-- **Homomorphisms of elliptic curves are determined by their morphisms of schemes.** -/
theorem hom_ext_left {f g : E.toCommGrp ⟶ E'.toCommGrp}
    (h : f.hom.hom.hom.left = g.hom.hom.hom.left) : f = g :=
  CommGrp.hom_ext _ _ (Over.OverMorphism.ext h)

/-- The sum of two homomorphisms of elliptic curves over `S` is, on underlying schemes, their sum
under the addition morphism of the target. -/
theorem add_hom_hom_hom_left (f g : E.toCommGrp ⟶ E'.toCommGrp) :
    (f + g).hom.hom.hom.left = pullback.lift f.hom.hom.hom.left g.hom.hom.hom.left
      ((Over.w f.hom.hom.hom).trans (Over.w g.hom.hom.hom).symm) ≫ E'.addition := by
  rw [CommGrp.add_hom_hom_hom, hom_mul_left]

/-- The zero homomorphism of elliptic curves over `S` is, on underlying schemes, the structure
morphism of the source followed by the zero section of the target. -/
theorem zero_hom_hom_hom_left :
    (0 : E.toCommGrp ⟶ E'.toCommGrp).hom.hom.hom.left = E.structureMap ≫ E'.zero := by
  simp

/-- The negative of a homomorphism of elliptic curves over `S` is, on underlying schemes, the
homomorphism followed by the negation morphism of the target. -/
theorem neg_hom_hom_hom_left (f : E.toCommGrp ⟶ E'.toCommGrp) :
    (-f).hom.hom.hom.left = f.hom.hom.hom.left ≫ E'.neg := by
  rw [CommGrp.neg_hom_hom_hom, hom_inv_left]

/-! ### Multiplication by an integer in the endomorphism ring -/

/-- **Multiplication by `n` is the integer `n` of the endomorphism ring.** The homomorphism of
elliptic curves given by `[n] : E ⟶ E` is the image of `n` under `ℤ → End_S(E)`. -/
theorem homMk_mulBy (n : ℤ) :
    CommGrp.homMk (A := E.toCommGrp) (B := E.toCommGrp) (E.mulBy n) = (n : End E.toCommGrp) :=
  CommGrp.hom_ext _ _ <| by
    rw [CommGrp.homMk_hom_hom_hom, CommGrp.intCast_hom_hom_hom, mulBy_eq_zpow]

/-- The integer `n` of the endomorphism ring of `E` is multiplication by `n`. This takes priority
over the general `CategoryTheory.CommGrp.intCast_hom_hom_hom`, so that `E.mulBy n` is the simp
normal form. -/
@[simp high]
theorem intCast_hom_hom_hom (n : ℤ) : (n : End E.toCommGrp).hom.hom.hom = E.mulBy n := by
  rw [← homMk_mulBy, CommGrp.homMk_hom_hom_hom]

/-- The natural number `n` of the endomorphism ring of `E` is multiplication by `n`. -/
@[simp high]
theorem natCast_hom_hom_hom (n : ℕ) : (n : End E.toCommGrp).hom.hom.hom = E.mulBy n := by
  rw [← Int.cast_natCast, intCast_hom_hom_hom]

/-- The image of the integer `n` of the endomorphism ring of `E` in the category of group schemes
over `S` is multiplication by `n`. -/
@[simp]
theorem forget₂Grp_map_intCast (n : ℤ) :
    (CommGrp.forget₂Grp (Over S)).map (n : End E.toCommGrp) = Grp.ofHom (E.mulBy n) :=
  Grp.hom_ext _ _ <| by
    rw [CommGrp.forget₂Grp_map_hom, Grp.ofHom_hom_hom, intCast_hom_hom_hom]

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
