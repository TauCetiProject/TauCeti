/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.OfWeierstrass
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Finite
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection
import TauCeti.AlgebraicGeometry.Morphisms.Finite.FlatDegree
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Dominant
import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Smooth

/-!
# Multiplication by an integer on the projective Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R` and `E = projModel W` its
projective model, a commutative group scheme over `Spec R` (`WeierstrassCurve.grpObjProjModel`).
This file studies the morphism `[n] : E ⟶ E` of schemes underlying multiplication by an integer
`n`, which is multiplication by `n` on the elliptic curve `toEllipticCurveGeom W` read on `E`
(`WeierstrassCurve.projModelMulBy_eq`).

A point of `W` with coordinates in a field `L` over `R` is a point of `E` with values in `L`, and
`[n]` sends the point of `P` to the point of `n • P`. Over a field, applied to the generic point of
`W`, whose coordinates are the affine coordinates in the function field, this computes the action
of `[n]` on the generic point of the scheme `E`: the equation-level pullback of rational functions
along `[n]` (`TauCeti.Isogeny.mulByIntIsogenyOfNeZero`, given by the division polynomials)
describes where `[n]` sends the generic point. Hence for `n ≠ 0` the morphism `[n]`
is dominant, and its pullback of rational functions `[n]^* : K(E) ⟶ K(E)`
(`AlgebraicGeometry.Scheme.Hom.functionFieldMap`) is the equation-level pullback, read through the
identification `projModelFunctionFieldEquiv` of `K(E)` with `W.toAffine.FunctionField`. This
identifies the extension of function fields induced by the scheme `[n]` with the one whose degree
`n²` is computed from the equations (`TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero`), so
`[K(E) : [n]^* K(E)] = n²`. Over a field `[n]` is also flat, being a dominant morphism to a curve
smooth over the field. For a finite flat dominant morphism of integral schemes the rank at every
point is the degree of the function-field extension
(`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_fieldRange_functionFieldMap`), so together with
the finiteness of `[n]` these compute the rank of `[n]` over a field as `n²`: the fibre of `[n]`
over every point is the spectrum of an algebra of dimension `n²` over its residue field.

## Main definitions

* `WeierstrassCurve.projModelMulBy W n`: the morphism `[n] : projModel W ⟶ projModel W`.
* `WeierstrassCurve.mulByFunctionFieldPullback W n`: over a field, for `n ≠ 0`, the pullback
  `[n]^* : K(E) →+* K(E)` of rational functions along `[n]`.

## Main results

* `WeierstrassCurve.projModelMulBy_eq`: it is multiplication by `n` on `toEllipticCurveGeom W`.
* `WeierstrassCurve.projModelMulBy_comp_of_isPullback` and
  `WeierstrassCurve.comp_projModelMulBy_of_isPullback`: `[n]` commutes with pointed base changes
  from and to the projective model.
* `WeierstrassCurve.isFinite_projModelMulBy`: for `n ≠ 0`, `[n]` is finite.
* `WeierstrassCurve.comp_projModelMulBy_eq_homMk_zpow_left`: for a section `P` of the projective
  model, `nP` is the `n`-th power of `P` bundled as a morphism of `Over (Spec R)`.
* `WeierstrassCurve.comp_projModelMulBy_add`, `WeierstrassCurve.comp_projModelMulBy_two` and
  `WeierstrassCurve.comp_projModelMulBy_add_one_eq_projModelZero_iff`: for a section `P` of the
  projective model, `(m + n)P` is `mP + nP` through the addition morphism, `2P` is `P + P`, and
  `(n + 1)P = 0` exactly when `nP = -P`.
* `WeierstrassCurve.projModelPointsEquiv_symm_projModelBaseChange_projModelMulBy`: `[n]` sends the
  point with values in a field `L` of a point `P` of `W` over `L` to that of `n • P`;
  `WeierstrassCurve.projModelPoint_projModelMulBy_of_zsmul_some` and
  `WeierstrassCurve.projModelPoint_projModelMulBy_of_zsmul_eq_zero` state this on the point with
  homogeneous coordinates `[x : y : 1]`, according as `n • (x, y)` is affine or zero.
* `WeierstrassCurve.projModelAffinePoint_projModelMulBy_ne_projModelZero_iff` and
  `WeierstrassCurve.isUnit_evalEval_ψ_iff`: over a commutative ring, the `n`-th multiple of the
  point `[x : y : 1]` misses the zero section over a point `s` of the base exactly when `ψₙ(x, y)`
  does not lie in `s`, and over every point exactly when `ψₙ(x, y)` is a unit.
* `WeierstrassCurve.isDominant_projModelMulBy`: over a field, for `n ≠ 0`, `[n]` is dominant.
* `WeierstrassCurve.projModelFunctionFieldEquiv_mulByFunctionFieldPullback`: over a field, for
  `n ≠ 0`, the pullback of rational functions along `[n]` is the equation-level pullback
  `(TauCeti.Isogeny.mulByIntIsogenyOfNeZero W hn).fieldPullback`.
* `WeierstrassCurve.flat_projModelMulBy`: over a field, for `n ≠ 0`, `[n]` is flat.
* `WeierstrassCurve.finrank_fieldRange_mulByFunctionFieldPullback`: over a field, for `n ≠ 0`,
  `[K(E) : [n]^* K(E)] = n²`.
* `WeierstrassCurve.finrank_projModelMulBy`: over a field, for `n ≠ 0`, `[n]` has rank `n²` at
  every point.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.2 and III.6.4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

section CommRing

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- **Multiplication by an integer on the projective Weierstrass model**: the morphism of schemes
`[n] : projModel W ⟶ projModel W` underlying the `n`-th power of the identity of the commutative
group scheme `projModel W` over `Spec R` (`grpObjProjModel`). It sends every point `x` of the
projective model to `x ^ n` (`comp_projModelMulBy`), and it is multiplication by `n` on the
elliptic curve `toEllipticCurveGeom W` (`projModelMulBy_eq`). -/
noncomputable def projModelMulBy (n : ℤ) : W.projModel ⟶ W.projModel :=
  (𝟙 (Over.mk W.projModelOver) ^ n).left

/-- Multiplication by `n` sends a point `x` of the projective model, with values in any `Z` over
`Spec R`, to `x ^ n`. -/
@[reassoc (attr := simp)]
theorem comp_projModelMulBy {Z : Over (Spec (.of R))} (x : Z ⟶ Over.mk W.projModelOver)
    (n : ℤ) : x.left ≫ W.projModelMulBy n = (x ^ n).left := by
  rw [projModelMulBy, ← Over.comp_left, GrpObj.comp_zpow, Category.comp_id]

/-- Multiplication by `n` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem projModelMulBy_projModelOver (n : ℤ) :
    W.projModelMulBy n ≫ W.projModelOver = W.projModelOver :=
  Over.w (𝟙 (Over.mk W.projModelOver) ^ n)

/-- **Multiplication by `n` on the projective model is multiplication by `n` on the elliptic
curve `toEllipticCurveGeom W`**, read on the projective model through `toEllipticCurveGeomIso`. -/
theorem projModelMulBy_eq (n : ℤ) :
    W.projModelMulBy n = (toEllipticCurveGeomIso W).inv ≫
      ((toEllipticCurveGeom W).mulBy n).left ≫ (toEllipticCurveGeomIso W).hom := by
  -- the identification of `toEllipticCurveGeom W` with the projective model is a homomorphism of
  -- group schemes, so it commutes with taking `n`-th powers
  have h : (toEllipticCurveGeom W).mulBy n ≫ (toEllipticCurveGeomOverIso W).hom =
      (toEllipticCurveGeomOverIso W).hom ≫ 𝟙 (Over.mk W.projModelOver) ^ n := by
    rw [EllipticCurveGeom.mulBy_eq_zpow, GrpObj.zpow_comp, GrpObj.comp_zpow, Category.id_comp,
      Category.comp_id]
  rw [← toEllipticCurveGeomOverIso_hom_left, ← Over.comp_left, h, Over.comp_left,
    toEllipticCurveGeomOverIso_hom_left, Iso.inv_hom_id_assoc, projModelMulBy]

/-- **Multiplication by `n` commutes with a pointed base change from the projective model.** Let
`a : projModel W ⟶ E` be a morphism to an elliptic curve `E` over a scheme `S`, forming a pullback
square over a morphism `b : Spec R ⟶ S` and carrying the zero section to the zero section. Then `a`
carries multiplication by `n` on the projective model to multiplication by `n` on `E`. -/
@[reassoc]
theorem projModelMulBy_comp_of_isPullback {S : Scheme.{u}} {E : EllipticCurveGeom S}
    {a : W.projModel ⟶ E.carrier} {b : Spec (.of R) ⟶ S}
    (hab : IsPullback a W.projModelOver E.structureMap b) (h₀ : W.projModelZero ≫ a = b ≫ E.zero)
    (n : ℤ) : W.projModelMulBy n ≫ a = a ≫ (E.mulBy n).left := by
  have hab' : IsPullback ((toEllipticCurveGeomIso W).hom ≫ a)
      (toEllipticCurveGeom W).structureMap E.structureMap b := by
    simpa using (IsPullback.of_horiz_isIso (fst := (toEllipticCurveGeomIso W).hom)
      (snd := (toEllipticCurveGeom W).structureMap) (f := W.projModelOver) (g := 𝟙 _)
      ⟨by simp⟩).paste_horiz hab
  have := EllipticCurveGeom.mulBy_left_comp_of_isPullback hab' (by simp [h₀]) n
  simp only [Category.assoc] at this
  rw [projModelMulBy_eq, Category.assoc, Category.assoc, this, Iso.inv_hom_id_assoc]

/-- **Multiplication by `n` commutes with a pointed base change to the projective model.** Let
`g : E ⟶ projModel W` be a morphism from an elliptic curve `E` over a scheme `S`, forming a pullback
square over a morphism `f : S ⟶ Spec R` and carrying the zero section to the zero section. Then `g`
carries multiplication by `n` on `E` to multiplication by `n` on the projective model. -/
@[reassoc]
theorem comp_projModelMulBy_of_isPullback {S : Scheme.{u}} {E : EllipticCurveGeom S}
    {g : E.carrier ⟶ W.projModel} {f : S ⟶ Spec (.of R)}
    (hg : IsPullback g E.structureMap W.projModelOver f) (h₀ : E.zero ≫ g = f ≫ W.projModelZero)
    (n : ℤ) : g ≫ W.projModelMulBy n = (E.mulBy n).left ≫ g := by
  have hg' : IsPullback (g ≫ (toEllipticCurveGeomIso W).inv) E.structureMap
      (toEllipticCurveGeom W).structureMap f := by
    simpa using hg.paste_horiz (IsPullback.of_horiz_isIso (fst := (toEllipticCurveGeomIso W).inv)
      (snd := W.projModelOver) (f := (toEllipticCurveGeom W).structureMap) (g := 𝟙 _)
      ⟨by simp [← toEllipticCurveGeomIso_hom_projModelOver]⟩)
  have := EllipticCurveGeom.mulBy_left_comp_of_isPullback hg'
    (by simp [reassoc_of% h₀, ← zero_toEllipticCurveGeomIso_hom]) n
  rw [projModelMulBy_eq]
  simpa using (this =≫ (toEllipticCurveGeomIso W).hom).symm

/-- Multiplication by a nonzero integer on the projective Weierstrass model is finite, being
multiplication by `n` on the elliptic curve `toEllipticCurveGeom W`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFinite_mulBy_left`). -/
instance isFinite_projModelMulBy (n : ℤ) [NeZero n] : IsFinite (W.projModelMulBy n) := by
  have := (toEllipticCurveGeom W).isFinite_mulBy_left (NeZero.ne n)
  rw [projModelMulBy_eq]
  infer_instance

end CommRing

section Sections

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} [W.IsElliptic]
  {P : Spec (.of R) ⟶ W.projModel}

/-- **Multiplication by `n` on a section.** A section `P` of the projective model, bundled as a
morphism of `Over (Spec R)` from the terminal object, has `n`-th multiple the `n`-th power of that
morphism. -/
theorem comp_projModelMulBy_eq_homMk_zpow_left (hP : P ≫ W.projModelOver = 𝟙 _) (n : ℤ) :
    P ≫ W.projModelMulBy n = ((Over.homMk P (by simpa using hP) :
      𝟙_ (Over (Spec (.of R))) ⟶ Over.mk W.projModelOver) ^ n).left := by
  rw [← comp_projModelMulBy]
  -- the underlying morphism of `Over.homMk P _` is `P` by definition
  rfl

/-- **Multiplication by a sum on a section.** For a section `P` of the projective model, the
`(m + n)`-th multiple of `P` is the sum of its `m`-th and `n`-th multiples, computed by the
addition morphism. -/
theorem comp_projModelMulBy_add (hP : P ≫ W.projModelOver = 𝟙 _) (m n : ℤ) :
    P ≫ W.projModelMulBy (m + n) =
      pullback.lift (P ≫ W.projModelMulBy m) (P ≫ W.projModelMulBy n) (by simp) ≫
        W.additionMorphism := by
  simp only [comp_projModelMulBy_eq_homMk_zpow_left hP, zpow_add, Hom.mul_def, Over.comp_left,
    Over.lift_left, mul_projModelOver_left]
  -- the two sides differ only in the proof of the condition of `pullback.lift`
  rfl

/-- **Doubling a section.** For a section `P` of the projective model, `2P` is the addition
morphism at the pair `(P, P)`. -/
theorem comp_projModelMulBy_two (hP : P ≫ W.projModelOver = 𝟙 _) :
    P ≫ W.projModelMulBy 2 = pullback.lift P P rfl ≫ W.additionMorphism := by
  rw [show (2 : ℤ) = 1 + 1 by norm_num, comp_projModelMulBy_add hP]
  simp only [comp_projModelMulBy_eq_homMk_zpow_left hP, zpow_one, Over.homMk_left]

/-- For a section `P` of the projective model, `(n + 1)P = 0` exactly when `nP = -P`. -/
theorem comp_projModelMulBy_add_one_eq_projModelZero_iff (hP : P ≫ W.projModelOver = 𝟙 _)
    (n : ℤ) :
    P ≫ W.projModelMulBy (n + 1) = W.projModelZero ↔
      P ≫ W.projModelMulBy n = P ≫ W.projModelNeg := by
  have h₁ : (1 : 𝟙_ (Over (Spec (.of R))) ⟶ Over.mk W.projModelOver).left = W.projModelZero := by
    simp [Hom.one_def]
  have hneg : P ≫ W.projModelNeg = P ≫ W.projModelMulBy (-1) := by
    simp [comp_projModelMulBy_eq_homMk_zpow_left hP, Hom.inv_def]
  simp only [hneg, comp_projModelMulBy_eq_homMk_zpow_left hP, ← h₁, zpow_add_one, zpow_neg_one]
  exact ⟨fun h ↦ congrArg Over.Hom.left
      (mul_eq_one_iff_eq_inv.mp (Over.OverMorphism.ext h)),
    fun h ↦ congrArg Over.Hom.left (mul_eq_one_iff_eq_inv.mpr (Over.OverMorphism.ext h))⟩

end Sections

section FieldPoints

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
  {L : Type u} [Field L] (g : R →+* L)

-- A point of the projective model of `W.map g` over `Spec L`, followed by the base change morphism
-- to the projective model of `W`, is a point of the projective model of `W` with values in `L`,
-- lying over `Spec g`; this is a homomorphism of groups of points.
private noncomputable def baseChangePointsHom :
    (𝟙_ (Over (Spec (.of L))) ⟶ Over.mk (W.map g).projModelOver) →*
      (Over.mk (Spec.map (CommRingCat.ofHom g)) ⟶ Over.mk W.projModelOver) where
  toFun x := Over.homMk (x.left ≫ W.projModelBaseChange g) (by
    simpa [projModelBaseChange_projModelOver] using x.w =≫ Spec.map (CommRingCat.ofHom g))
  map_one' := by
    ext1
    simp [Hom.one_def]
  map_mul' x y := by
    ext1
    simp only [Hom.mul_def, Over.comp_left, Over.lift_left, mul_projModelOver_left, Category.assoc,
      additionMorphism_projModelBaseChange, Over.homMk_left]
    -- the base change morphism carries the pair `(x, y)` to the pair of the base changed points
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp

private theorem baseChangePointsHom_left (x : 𝟙_ (Over (Spec (.of L))) ⟶
    Over.mk (W.map g).projModelOver) :
    (W.baseChangePointsHom g x).left = x.left ≫ W.projModelBaseChange g :=
  rfl

/-- **Multiplication by `n` on points with values in a field.** Let `g : R →+* L` be a ring
homomorphism to a field. A point `P` of `W` over `L` gives the point
`(projModelPointsEquiv (W.map g)).symm P` of the projective model of `W.map g` over `Spec L`, hence,
through the base change morphism `projModelBaseChange`, a point of `projModel W` with values in
`L`. Multiplication by `n` sends the point of `P` to the point of `n • P`. -/
theorem projModelPointsEquiv_symm_projModelBaseChange_projModelMulBy [DecidableEq L]
    (P : (W.map g).toAffine.Point) (n : ℤ) :
    ((W.map g).projModelPointsEquiv.symm P).1 ≫ W.projModelBaseChange g ≫ W.projModelMulBy n =
      ((W.map g).projModelPointsEquiv.symm (n • P)).1 ≫ W.projModelBaseChange g := by
  have h := congrArg Over.Hom.left
    (map_zpow (W.baseChangePointsHom g) ((W.map g).projModelPointsMulEquiv.symm (.ofAdd P)) n)
  rw [← comp_projModelMulBy, baseChangePointsHom_left, baseChangePointsHom_left,
    ← map_zpow, ← ofAdd_zsmul, projModelPointsMulEquiv_symm_apply_left,
    projModelPointsMulEquiv_symm_apply_left, toAdd_ofAdd, toAdd_ofAdd] at h
  simpa using h.symm

/-- The point with values in a field `L` of an affine point `(x, y)` of `W` over `L`, through the
base change morphism `projModelBaseChange`, is the point with homogeneous coordinates
`[x : y : 1]` along `g`. -/
theorem projModelPointsEquiv_symm_some_projModelBaseChange {x y : L}
    (h : (W.map g).toAffine.Nonsingular x y) :
    ((W.map g).projModelPointsEquiv.symm (.some x y h)).1 ≫ W.projModelBaseChange g =
      W.projModelPoint g (P := ![x, y, 1]) ((Projective.equation_some _ _).mpr h.1) (i := 2)
        (by simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using
          isUnit_one) := by
  have hP : (W.map g).toProjective.Nonsingular ![x, y, 1] := (Projective.nonsingular_some _ _).mpr h
  have hE : ((W.map g).toProjective.map (RingHom.id L)).Equation ![x, y, 1] := by
    simpa only [WeierstrassCurve.map_id] using hP.1
  have hi : IsUnit (![x, y, 1] 2) := by
    simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using isUnit_one
  -- the section of the affine point `(x, y)` has homogeneous coordinates `[x : y : 1]`
  have hsymm : ((W.map g).projModelPointsEquiv.symm (.some x y h)).1 =
      (W.map g).projModelPoint (RingHom.id L) hE hi :=
    congrArg Subtype.val <| (Equiv.symm_apply_eq _).mpr <|
      ((projModelPointsEquiv_projModelPoint _ hE hi).trans
        (Projective.Point.toAffine_some hP)).symm
  rw [hsymm]
  exact (projModelPoint_projModelBaseChange _ _ hi).trans
    (projModelPoint_eq_projModelPoint_iff.mpr ⟨RingHom.id_comp g, 1, by simp⟩)

/-- If multiplication by `n` sends the affine point `(x, y)` of `W` over a field `L` to `(x', y')`,
then `[n]` sends the point with homogeneous coordinates `[x : y : 1]` along `g` to the one with
homogeneous coordinates `[x' : y' : 1]`. -/
theorem projModelPoint_projModelMulBy_of_zsmul_some [DecidableEq L] {x y x' y' : L}
    {h : (W.map g).toAffine.Nonsingular x y} {h' : (W.map g).toAffine.Nonsingular x' y'} {n : ℤ}
    (hn : n • Affine.Point.some x y h = .some x' y' h') :
    W.projModelPoint g (P := ![x, y, 1]) ((Projective.equation_some _ _).mpr h.1) (i := 2)
        (by simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using
          isUnit_one) ≫ W.projModelMulBy n =
      W.projModelPoint g (P := ![x', y', 1]) ((Projective.equation_some _ _).mpr h'.1) (i := 2)
        (by simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using
          isUnit_one) := by
  rw [← projModelPointsEquiv_symm_some_projModelBaseChange W g h,
    ← projModelPointsEquiv_symm_some_projModelBaseChange W g h', Category.assoc,
    projModelPointsEquiv_symm_projModelBaseChange_projModelMulBy, hn]

/-- If multiplication by `n` kills the affine point `(x, y)` of `W` over a field `L`, then `[n]`
sends the point with homogeneous coordinates `[x : y : 1]` along `g` to the zero section, along
`g`. -/
theorem projModelPoint_projModelMulBy_of_zsmul_eq_zero [DecidableEq L] {x y : L}
    {h : (W.map g).toAffine.Nonsingular x y} {n : ℤ} (hn : n • Affine.Point.some x y h = 0) :
    W.projModelPoint g (P := ![x, y, 1]) ((Projective.equation_some _ _).mpr h.1) (i := 2)
        (by simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using
          isUnit_one) ≫ W.projModelMulBy n =
      Spec.map (CommRingCat.ofHom g) ≫ W.projModelZero := by
  rw [← projModelPointsEquiv_symm_some_projModelBaseChange W g h, Category.assoc,
    projModelPointsEquiv_symm_projModelBaseChange_projModelMulBy, hn,
    ← projModelZero_projModelBaseChange]
  congr 2
  exact congrArg Subtype.val
    ((Equiv.symm_apply_eq _).mpr (projModelPointsEquiv_projModelZero _).symm)

end FieldPoints

section Multiples

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} [W.IsElliptic] {x y : R}
  (h : W.toAffine.Equation x y)

/-- **The `n`-th multiple of `[x : y : 1]` over a point of the base.** Over a point `s` of
`Spec R`, the `n`-th multiple of the point `[x : y : 1]` misses the zero section exactly when the
value `ψₙ(x, y)` of the `n`-th division polynomial does not lie in `s`. -/
theorem projModelAffinePoint_projModelMulBy_ne_projModelZero_iff (n : ℤ) (s : Spec (.of R)) :
    (W.projModelAffinePoint h ≫ W.projModelMulBy n) s ≠ W.projModelZero s ↔
      (W.ψ n).evalEval x y ∉ s.asIdeal := by
  classical
  have := s.isPrime
  let g := algebraMap R s.asIdeal.ResidueField
  -- the closed point of `Spec κ(s)` lies over `s`
  let t : Spec (.of s.asIdeal.ResidueField) := ⟨⊥, Ideal.isPrime_bot⟩
  have ht : Spec.map (CommRingCat.ofHom g) t = s := by
    refine PrimeSpectrum.ext ?_
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  have hns : (W.map g).toAffine.Nonsingular (g x) (g y) :=
    Affine.equation_iff_nonsingular.mp (h.map g)
  -- the point `[x : y : 1]` with values in `κ(s)`
  have hpt : Spec.map (CommRingCat.ofHom g) ≫ W.projModelAffinePoint h =
      W.projModelPoint g (P := ![g x, g y, 1]) ((Projective.equation_some _ _).mpr hns.1) (i := 2)
        (by simp) := by
    rw [← projModelAffinePoint_projModelBaseChange, projModelAffinePoint_def,
      projModelPoint_projModelBaseChange]
    exact (projModelPoint_eq_projModelPoint_iff_of_apply_eq rfl).mpr ⟨RingHom.id_comp g, rfl⟩
  have hψ : g ((W.ψ n).evalEval x y) = ((W.map g).ψ n).evalEval (g x) (g y) := by
    rw [map_ψ, Polynomial.map_mapRingHom_evalEval]
  have hs : (W.projModelAffinePoint h ≫ W.projModelMulBy n) s =
      (W.projModelPoint g (P := ![g x, g y, 1]) ((Projective.equation_some _ _).mpr hns.1) (i := 2)
        (by simp) ≫ W.projModelMulBy n) t := by
    rw [← hpt, Category.assoc, Scheme.Hom.comp_apply (Spec.map _) _ t, ht]
  rw [ne_projModelZero_iff_mem_basicOpen (by simp) s, hs,
    ← Ideal.algebraMap_residueField_eq_zero.not, hψ]
  by_cases hn : n • Affine.Point.some _ _ hns = 0
  · rw [projModelPoint_projModelMulBy_of_zsmul_eq_zero W g hn, Scheme.Hom.comp_apply,
      projModelZero_mem_basicOpen_iff]
    simpa using evalEval_ψ_eq_zero_of_zsmul_eq_zero (W.map g) hns n
      (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mpr hn)
  · obtain ⟨x', y', h', hn'⟩ : ∃ x' y' h', n • Affine.Point.some _ _ hns = .some x' y' h' := by
      cases hP : n • Affine.Point.some _ _ hns with
      | zero => exact absurd hP hn
      | @some x' y' h' => exact ⟨x', y', h', rfl⟩
    rw [projModelPoint_projModelMulBy_of_zsmul_some W g hn', projModelPoint_mem_basicOpen_iff]
    refine iff_of_true (by simpa using t.isPrime.one_notMem) fun hψ0 ↦ hn ?_
    exact zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mp
      (zsmul_eq_zero_of_evalEval_ψ_eq_zero (W.map g) hns n hψ0)

/-- **The `n`-th multiple of `[x : y : 1]` misses the zero section exactly when `ψₙ(x, y)` is a
unit.** The `n`-th multiple of the point `[x : y : 1]` of the projective model over `Spec R`
meets the zero section over no point of `Spec R` exactly when the value `ψₙ(x, y)` of the `n`-th
division polynomial is a unit of `R`. -/
theorem isUnit_evalEval_ψ_iff (n : ℤ) :
    IsUnit ((W.ψ n).evalEval x y) ↔
      ∀ s, (W.projModelAffinePoint h ≫ W.projModelMulBy n) s ≠ W.projModelZero s := by
  simp_rw [projModelAffinePoint_projModelMulBy_ne_projModelZero_iff]
  refine ⟨fun hu s hs ↦ s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs hu), fun H ↦ ?_⟩
  by_contra hu
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hu)
  exact H ⟨m, hm.isPrime⟩ hmem

end Multiples

section GenericPoint

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

-- Through `projModelFunctionFieldEquiv`, `[n]` acts on the generic point `Spec K(E) ⟶ E` of the
-- projective model through the equation-level pullback of rational functions along `[n]`.
private theorem SpecMap_fromSpecStalk_genericPoint_projModelMulBy {n : ℤ} (hn : n ≠ 0) :
    Spec.map (CommRingCat.ofHom (W.projModelFunctionFieldEquiv : W.projModel.functionField →+*
        W.toAffine.FunctionField)) ≫ W.projModel.fromSpecStalk (genericPoint W.projModel) ≫
          W.projModelMulBy n =
      Spec.map (CommRingCat.ofHom ((TauCeti.Isogeny.mulByIntIsogenyOfNeZero W hn).fieldPullback :
        W.toAffine.FunctionField →+* W.toAffine.FunctionField)) ≫
          Spec.map (CommRingCat.ofHom (W.projModelFunctionFieldEquiv :
            W.projModel.functionField →+* W.toAffine.FunctionField)) ≫
              W.projModel.fromSpecStalk (genericPoint W.projModel) := by
  rw [← Category.assoc, SpecMap_projModelFunctionFieldEquiv_fromSpecStalk, SpecMap_projModelPoint]
  -- the generic point is the point of the equation-level generic point `(x, y)`, which `[n]` sends
  -- to its `n`-th multiple, the point with coordinates the pullbacks of `x` and `y` along `[n]`
  have hgen := (TauCeti.Isogeny.map_mulByIntIsogeny_genericPoint W.toAffine
    (TauCeti.Isogeny.psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero hn)).symm
  rw [Affine.genericPoint_eq_some, Affine.Point.map_some] at hgen
  exact (W.projModelPoint_projModelMulBy_of_zsmul_some _ hgen).trans
    (projModelPoint_eq_projModelPoint_iff.mpr ⟨(AlgHom.comp_algebraMap _).symm, 1,
      funext fun k ↦ by fin_cases k <;> simp⟩)

-- `[n]` acts on the generic point `Spec K(E) ⟶ E` of the projective model through the
-- equation-level pullback of rational functions along `[n]`, conjugated by
-- `projModelFunctionFieldEquiv`.
private theorem SpecMap_comp_fromSpecStalk_genericPoint {n : ℤ} (hn : n ≠ 0) :
    Spec.map (CommRingCat.ofHom (W.projModelFunctionFieldEquiv :
      W.projModel.functionField →+* W.toAffine.FunctionField) ≫
        CommRingCat.ofHom ((TauCeti.Isogeny.mulByIntIsogenyOfNeZero W hn).fieldPullback :
          W.toAffine.FunctionField →+* W.toAffine.FunctionField) ≫
        CommRingCat.ofHom (W.projModelFunctionFieldEquiv.symm :
          W.toAffine.FunctionField →+* W.projModel.functionField)) ≫
        W.projModel.fromSpecStalk (genericPoint W.projModel) =
      W.projModel.fromSpecStalk (genericPoint W.projModel) ≫ W.projModelMulBy n := by
  rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    ← SpecMap_fromSpecStalk_genericPoint_projModelMulBy, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp]
  simp

/-- Over a field, multiplication by a nonzero integer on the projective Weierstrass model is
dominant. -/
instance isDominant_projModelMulBy (n : ℤ) [NeZero n] : IsDominant (W.projModelMulBy n) :=
  (W.projModelMulBy n).isDominant_of_SpecMap_fromSpecStalk _
    (W.SpecMap_comp_fromSpecStalk_genericPoint (NeZero.ne n))

/-- **The pullback of rational functions along multiplication by `n`.** Over a field, for
`n ≠ 0`, the pullback `[n]^* : K(E) →+* K(E)` of rational functions along the dominant morphism
`[n]` of the projective Weierstrass model `E` (`AlgebraicGeometry.Scheme.Hom.functionFieldMap`).
Through `projModelFunctionFieldEquiv` it is the equation-level pullback
(`projModelFunctionFieldEquiv_mulByFunctionFieldPullback`). -/
noncomputable def mulByFunctionFieldPullback (n : ℤ) [NeZero n] :
    W.projModel.functionField →+* W.projModel.functionField :=
  (W.projModelMulBy n).functionFieldMap.hom

/-- **The pullback of rational functions along `[n]` is the equation-level one.** Over a field,
for `n ≠ 0`, the pullback `[n]^* : K(E) →+* K(E)` of rational functions along multiplication by `n`
on the projective Weierstrass model `E`, read through the identification
`projModelFunctionFieldEquiv` of `K(E)` with the function field of the affine equation, is the
pullback of rational functions along the equation-level multiplication by `n`,
`(TauCeti.Isogeny.mulByIntIsogenyOfNeZero W hn).fieldPullback`. -/
@[simp]
theorem projModelFunctionFieldEquiv_mulByFunctionFieldPullback (n : ℤ) [NeZero n]
    (f : W.projModel.functionField) :
    W.projModelFunctionFieldEquiv (W.mulByFunctionFieldPullback n f) =
      (TauCeti.Isogeny.mulByIntIsogenyOfNeZero W (NeZero.ne n)).fieldPullback
        (W.projModelFunctionFieldEquiv f) := by
  rw [mulByFunctionFieldPullback, ← ((W.projModelMulBy n).eq_functionFieldMap_iff _).mpr
    (W.SpecMap_comp_fromSpecStalk_genericPoint (NeZero.ne n))]
  simp

/-- Over a field, multiplication by a nonzero integer on the projective Weierstrass model is
flat, as is every dominant morphism to a curve smooth over a field. -/
instance flat_projModelMulBy (n : ℤ) [NeZero n] : Flat (W.projModelMulBy n) :=
  (W.projModelMulBy n).flat_of_isDominant_of_smooth W.projModelOver

/-- **The degree of the function-field extension of `[n]` is `n²`.** Over a field, for `n ≠ 0`,
the function field `K(E)` of the projective Weierstrass model `E` has degree `n²` over its
image `[n]^* K(E)` under the pullback of rational functions along multiplication by `n`. Through
`projModelFunctionFieldEquiv`, this is the degree of the equation-level multiplication by `n`
(`TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero`). -/
@[simp]
theorem finrank_fieldRange_mulByFunctionFieldPullback (n : ℤ) [NeZero n] :
    Module.finrank (W.mulByFunctionFieldPullback n).fieldRange W.projModel.functionField =
      n.natAbs ^ 2 := by
  set φ := TauCeti.Isogeny.mulByIntIsogenyOfNeZero W (NeZero.ne n)
  rw [← TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero W (NeZero.ne n),
    TauCeti.Isogeny.degree_def]
  -- `projModelFunctionFieldEquiv` carries `[n]^* K(E)` onto the image of the equation-level
  -- pullback.
  refine Algebra.finrank_eq_of_equiv_equiv
    (((W.mulByFunctionFieldPullback n).rangeRestrictFieldEquiv.symm.trans
      W.projModelFunctionFieldEquiv).trans φ.fieldPullback.equivFieldRange.toRingEquiv)
    W.projModelFunctionFieldEquiv ?_
  -- both sides send `[n]^* f` to the image of `[n]^* f` under `projModelFunctionFieldEquiv`
  ext x
  simp [φ, ← projModelFunctionFieldEquiv_mulByFunctionFieldPullback, Subfield.algebraMap_ofSubfield]

/-- **Multiplication by `n` has rank `n²`** (Katz–Mazur 2.3.1). Over a field, for `n ≠ 0`, the
finite flat morphism `[n]` of the projective Weierstrass model has rank `n²` at every point `y`:
the fibre of `[n]` over `y` is the spectrum of an algebra of dimension `n²` over the residue field
of `y`. The rank of a finite flat dominant morphism of integral schemes is the degree of its
function-field extension, here `n²` (`finrank_fieldRange_mulByFunctionFieldPullback`). -/
@[simp]
theorem finrank_projModelMulBy (n : ℤ) [NeZero n] (y : W.projModel) :
    (W.projModelMulBy n).finrank y = n.natAbs ^ 2 := by
  rw [(W.projModelMulBy n).finrank_eq_finrank_fieldRange_functionFieldMap y,
    ← finrank_fieldRange_mulByFunctionFieldPullback W n, mulByFunctionFieldPullback]

end GenericPoint

end WeierstrassCurve
