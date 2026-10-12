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
* `WeierstrassCurve.isFinite_projModelMulBy`: for `n ≠ 0`, `[n]` is finite.
* `WeierstrassCurve.projModelPointsEquiv_symm_projModelBaseChange_projModelMulBy`: `[n]` sends the
  point with values in a field `L` of a point `P` of `W` over `L` to that of `n • P`.
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

/-- Multiplication by a nonzero integer on the projective Weierstrass model is finite, being
multiplication by `n` on the elliptic curve `toEllipticCurveGeom W`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFinite_mulBy_left`). -/
instance isFinite_projModelMulBy (n : ℤ) [NeZero n] : IsFinite (W.projModelMulBy n) := by
  have := (toEllipticCurveGeom W).isFinite_mulBy_left (NeZero.ne n)
  rw [projModelMulBy_eq]
  infer_instance

end CommRing

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

-- The point with values in `L` of an affine point `(x, y)` of `W` over `L` is the point with
-- homogeneous coordinates `[x : y : 1]`.
private theorem projModelPointsEquiv_symm_some_projModelBaseChange {x y : L}
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

-- If multiplication by `n` sends the affine point `(x, y)` of `W` over `L` to `(x', y')`, then
-- `[n]` sends the point with homogeneous coordinates `[x : y : 1]` to the one with `[x' : y' : 1]`.
private theorem projModelPoint_projModelMulBy_of_zsmul_some [DecidableEq L] {x y x' y' : L}
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

end FieldPoints

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
