/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.GroupLaw
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.GroupLaw

/-!
# Multiplication by an integer on an elliptic curve over a scheme

Let `E` be an elliptic curve over a scheme `S`, with its group law: the object `Over.mk π` of
`Over S`, for the structure morphism `π : E ⟶ S`, is a commutative group object
(`EllipticCurveGeom.grpObj`). For an integer `n`, multiplication by `n` is the endomorphism
`[n] : E ⟶ E` over `S` that sends a point `x` of `E`, with values in any `T` over `S`, to `n • x`,
written `x ^ n` for the multiplicative group law on points. It is defined as the `n`-th power of the
identity of `E` in the commutative group of points of `E` with values in `E` itself, and it is a
homomorphism of group schemes over `S`, so that `Grp.ofHom (E.mulBy n)` is the corresponding
morphism of `Grp (Over S)`, to which the kernel constructions for group schemes apply.

On underlying schemes, `[0]` is the composite of the structure morphism and the zero section,
`[-1]` is the negation morphism and `[m + n]` is the sum of `[m]` and `[n]` under the addition
morphism. Multiplication by an integer commutes with every homomorphism of group schemes, and with
arbitrary base change: a pointed morphism of elliptic curves forming a pullback square over a
morphism of bases carries `[n]` to `[n]`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy E n`: multiplication by `n : ℤ` on `E`, an
  endomorphism of `Over.mk E.structureMap` in `Over S`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isMonHom_mulBy`: multiplication by `n` is a
  homomorphism of group schemes over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.comp_mulBy`: it sends a point `x` to `x ^ n`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy_add`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy_neg` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy_mul`: `[m + n] = [m] * [n]`,
  `[-n] = [n]⁻¹` and `[m * n] = [n] ≫ [m]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy_comp`: every homomorphism of elliptic curves
  over `S` commutes with multiplication by `n`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy_zero_left`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy_neg_one_left` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy_add_left`: `[0]`, `[-1]` and `[m + n]` on
  underlying schemes.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy_left_comp_of_isPullback`: multiplication by
  `n` commutes with base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mulBy_left_baseChangeIso_hom_fst`: the projection
  from the base change `E.baseChange f` to `E` carries `[n]` to `[n]`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-! ### Multiplication by an integer -/

/-- **Multiplication by an integer** `[n] : E ⟶ E` on an elliptic curve `E` over a scheme `S`, as
an endomorphism of `E` in `Over S`. It is the `n`-th power of the identity of `E` for the group law
on points of `E`, and it sends every point `x` of `E` to `x ^ n` (`comp_mulBy`). -/
noncomputable def mulBy (n : ℤ) : Over.mk E.structureMap ⟶ Over.mk E.structureMap :=
  𝟙 _ ^ n

/-- Multiplication by `n` is the `n`-th power of the identity for the group law on points. -/
theorem mulBy_eq_zpow (n : ℤ) : E.mulBy n = 𝟙 _ ^ n :=
  (rfl)

/-- Multiplication by `n` sends a point `x` of `E`, with values in any `Z` over `S`, to
`x ^ n`. -/
@[reassoc (attr := simp)]
theorem comp_mulBy {Z : Over S} (x : Z ⟶ Over.mk E.structureMap) (n : ℤ) :
    x ≫ E.mulBy n = x ^ n := by
  rw [mulBy_eq_zpow, GrpObj.comp_zpow, Category.comp_id]

/-- **Multiplication by `n` is a homomorphism of group schemes.** -/
instance isMonHom_mulBy (n : ℤ) : IsMonHom (E.mulBy n) := by
  -- `𝟙 _ ^ n` is the underlying morphism of the `n`-th power of the identity of `E` in the
  -- category `Grp (Over S)` of group schemes over `S`
  have h := (𝟙 (Grp.mk (Over.mk E.structureMap)) ^ n).hom.isMonHom_hom
  rwa [Grp.Hom.hom_hom_zpow, Grp.id_hom_hom] at h

/-- `[0]` is the zero point of the group of points of `E` with values in `E`. -/
@[simp]
theorem mulBy_zero : E.mulBy 0 = 1 := by
  simp [mulBy_eq_zpow]

/-- `[1]` is the identity. -/
@[simp]
theorem mulBy_one : E.mulBy 1 = 𝟙 _ := by
  simp [mulBy_eq_zpow]

/-- `[m + n]` is the product of `[m]` and `[n]` for the group law on points. -/
@[simp]
theorem mulBy_add (m n : ℤ) : E.mulBy (m + n) = E.mulBy m * E.mulBy n := by
  simp [mulBy_eq_zpow, zpow_add]

/-- `[-n]` is the inverse of `[n]` for the group law on points. -/
@[simp]
theorem mulBy_neg (n : ℤ) : E.mulBy (-n) = (E.mulBy n)⁻¹ := by
  simp [mulBy_eq_zpow]

/-- `[m - n]` is the quotient of `[m]` by `[n]` for the group law on points. -/
@[simp]
theorem mulBy_sub (m n : ℤ) : E.mulBy (m - n) = E.mulBy m / E.mulBy n := by
  simp [sub_eq_add_neg, div_eq_mul_inv]

/-- `[m * n]` is `[n]` followed by `[m]`. -/
@[simp]
theorem mulBy_mul (m n : ℤ) : E.mulBy (m * n) = E.mulBy n ≫ E.mulBy m := by
  rw [comp_mulBy, mulBy_eq_zpow, mulBy_eq_zpow, zpow_mul']

/-- **Homomorphisms commute with multiplication by `n`.** A homomorphism of group schemes
`f : E ⟶ E'` between elliptic curves over `S` satisfies `[n] ≫ f = f ≫ [n]`. -/
@[reassoc]
theorem mulBy_comp {E' : EllipticCurveGeom S} (n : ℤ)
    (f : Over.mk E.structureMap ⟶ Over.mk E'.structureMap) [IsMonHom f] :
    E.mulBy n ≫ f = f ≫ E'.mulBy n := by
  rw [mulBy_eq_zpow, GrpObj.zpow_comp, comp_mulBy, Category.id_comp]

/-! ### Multiplication by an integer on the underlying scheme -/

/-- Multiplication by `n` lies over `S`. -/
@[reassoc (attr := simp)]
theorem mulBy_left_structureMap (n : ℤ) :
    (E.mulBy n).left ≫ E.structureMap = E.structureMap :=
  (E.mulBy n).w

/-- Multiplication by `n` fixes the zero section. -/
@[reassoc (attr := simp)]
theorem zero_mulBy_left (n : ℤ) : E.zero ≫ (E.mulBy n).left = E.zero := by
  simpa only [Over.comp_left, one_left] using
    congrArg CommaMorphism.left (IsMonHom.one_hom (f := E.mulBy n))

/-- On the underlying scheme, `[0]` is the composite of the structure morphism and the zero
section. -/
theorem mulBy_zero_left : (E.mulBy 0).left = E.structureMap ≫ E.zero := by
  simp

/-- On the underlying scheme, `[-1]` is the negation morphism. -/
theorem mulBy_neg_one_left : (E.mulBy (-1)).left = E.neg := by
  simp

/-- On the underlying scheme, `[m + n]` is the sum of `[m]` and `[n]` under the addition
morphism. -/
theorem mulBy_add_left (m n : ℤ) :
    (E.mulBy (m + n)).left =
      pullback.lift (E.mulBy m).left (E.mulBy n).left (by simp) ≫ E.addition := by
  simp

/-! ### Multiplication by an integer and base change -/

section BaseChange

variable {S' : Scheme.{u}} {E} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

include hg h0 in
/-- **Multiplication by `n` commutes with base change.** Let `g : E' ⟶ E` be a morphism of
elliptic curves lying over `f : S' ⟶ S`, such that the square formed by `g`, `f` and the structure
morphisms is a pullback square, and carrying the zero section of `E'` to that of `E`. Then `g`
carries multiplication by `n` on `E'` to multiplication by `n` on `E`. -/
@[reassoc]
theorem mulBy_left_comp_of_isPullback (n : ℤ) :
    (E'.mulBy n).left ≫ g = g ≫ (E.mulBy n).left := by
  -- `g` carries the sum of two points of `E'` to the sum of their images
  have add (a b : E'.carrier ⟶ E'.carrier) (ha : a ≫ E'.structureMap = E'.structureMap)
      (hb : b ≫ E'.structureMap = E'.structureMap) :
      (pullback.lift a b (ha.trans hb.symm) ≫ E'.addition) ≫ g =
        pullback.lift (a ≫ g) (b ≫ g) (by simp [hg.w, reassoc_of% ha, reassoc_of% hb]) ≫
          E.addition := by
    rw [Category.assoc, addition_comp_of_isPullback hg h0, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp
  induction n using Int.induction_on with
  | zero => rw [mulBy_zero_left, mulBy_zero_left, Category.assoc, h0, ← hg.w_assoc]
  | succ n ih =>
    rw [mulBy_add_left, add _ _ (by simp) (by simp), mulBy_add_left, ← Category.assoc g]
    congr 1
    apply pullback.hom_ext <;> simp [ih]
  | pred n ih =>
    rw [sub_eq_add_neg, mulBy_add_left, add _ _ (by simp) (by simp), mulBy_add_left,
      ← Category.assoc g]
    congr 1
    apply pullback.hom_ext
    · simpa [neg_comp_of_isPullback_assoc hg h0] using ih
    · simp [neg_comp_of_isPullback hg h0]

end BaseChange

variable {S' : Scheme.{u}} (f : S' ⟶ S)

/-- **Multiplication by `n` on a base change.** The projection from the base change
`E.baseChange f` to `E` carries multiplication by `n` on `E.baseChange f` to multiplication by `n`
on `E`. -/
@[reassoc (attr := simp)]
theorem mulBy_left_baseChangeIso_hom_fst (n : ℤ) :
    ((E.baseChange f).mulBy n).left ≫ (E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f =
      (E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f ≫ (E.mulBy n).left := by
  rw [mulBy_left_comp_of_isPullback (E.isPullback_baseChange f) (by simp), Category.assoc]

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
