/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Addition
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Neg
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.GroupLaw

/-!
# The group law of an elliptic curve over a scheme

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S`, and regard `E`
as the object `Over.mk π` of the cartesian monoidal category `Over S`, whose tensor product is the
fibre product over `S`. This file makes `E` a commutative group object of `Over S`: a commutative
group scheme over `S`. The unit is the zero section, the multiplication is the addition morphism
`E ×_S E ⟶ E` (`EllipticCurveGeom.addition`) and the inverse is the negation morphism `E ⟶ E`
(`EllipticCurveGeom.neg`), both glued from the Bosma–Lenstra formulae of the local Weierstrass
equations of `E`.

The group axioms are local on `S`, and over the base `U` of a pointed Weierstrass chart they are
the group axioms of the projective model of the equation of the chart
(`WeierstrassCurve.grpObjProjModel`). The argument is carried out on points. For `T` over `S`, the
morphisms `T ⟶ E` over `S` form a commutative group, with the sum of `x` and `y` the composite of
`(x, y) : T ⟶ E ×_S E` with the addition morphism. Restricting `T` to the base of a chart and
reading points of `E` there as points of the projective model of the equation of the chart is
injective jointly over all charts and carries the sum, the zero and the negation of points to those
of the projective model, so the group axioms for points of `E` follow from those for points of the
projective model. These groups are natural in `T`, so `E` represents a presheaf of commutative
groups on `Over S`, and is therefore a commutative group object
(`CategoryTheory.CommGrpObj.ofRepresentableBy`).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.grpObj`: the group-object structure on
  `Over.mk E.structureMap`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isCommMonObj`: the group law is commutative.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.one_left`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mul_left` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.inv_left`: the unit, multiplication and inverse are
  the zero section, the addition morphism and the negation morphism.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1–2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

open PointedWeierstrassChart

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-! ### The zero section, addition and negation in `Over S` -/

-- The zero section as a morphism of `Over S`.
private noncomputable abbrev zeroHom : 𝟙_ (Over S) ⟶ Over.mk E.structureMap :=
  Over.homMk E.zero (by simp)

-- The addition morphism as a morphism of `Over S`.
private noncomputable abbrev addHom :
    Over.mk E.structureMap ⊗ Over.mk E.structureMap ⟶ Over.mk E.structureMap :=
  Over.homMk E.addition (by simp)

-- The negation morphism as a morphism of `Over S`.
private noncomputable abbrev negHom : Over.mk E.structureMap ⟶ Over.mk E.structureMap :=
  Over.homMk E.neg (by simp)

/-! ### Points of `E` read on a chart -/

section Points

variable {Z : Over S}

-- The sum, the zero and the negation of points of `E` with values in `Z`. They are instances only
-- in this section, which shows that they form a commutative group (`pointsCommGroup`); outside it,
-- the group structure of points is the one of the group object `Over.mk E.structureMap`.
private noncomputable abbrev pointsMul : Mul (Z ⟶ Over.mk E.structureMap) :=
  ⟨fun f g ↦ lift f g ≫ E.addHom⟩

private noncomputable abbrev pointsOne : One (Z ⟶ Over.mk E.structureMap) :=
  ⟨toUnit Z ≫ E.zeroHom⟩

private noncomputable abbrev pointsInv : Inv (Z ⟶ Over.mk E.structureMap) :=
  ⟨fun f ↦ f ≫ E.negHom⟩

attribute [local instance] pointsMul pointsOne pointsInv

private theorem points_mul_def (f g : Z ⟶ Over.mk E.structureMap) : f * g = lift f g ≫ E.addHom :=
  (rfl)

private theorem points_one_def : (1 : Z ⟶ Over.mk E.structureMap) = toUnit Z ≫ E.zeroHom :=
  (rfl)

private theorem points_inv_def (f : Z ⟶ Over.mk E.structureMap) : f⁻¹ = f ≫ E.negHom :=
  (rfl)

section Chart

variable {E} (c : PointedWeierstrassChart E.structureMap E.zero)

-- The restriction of `T` to the base of the chart `c`, over `Spec c.ring`.
private noncomputable abbrev chartObj (T : Over S) : Over (Spec (.of c.ring)) :=
  Over.mk (pullback.snd T.hom c.baseMap ≫ c.baseIso.hom)

-- A point of `E` with values in `Z`, restricted to the base of `c`, lies over the base of `c`.
private theorem fst_comp_left_structureMap (f : Z ⟶ Over.mk E.structureMap) :
    (pullback.fst Z.hom c.baseMap ≫ f.left) ≫ E.structureMap =
      pullback.snd Z.hom c.baseMap ≫ c.baseMap := by
  rw [← pullback.condition, Category.assoc]
  exact pullback.fst _ _ ≫= Over.w f

-- A point of `E` with values in `Z`, restricted to the base of `c`, as a point of the projective
-- model of the equation of `c`.
private noncomputable def chartHom (f : Z ⟶ Over.mk E.structureMap) :
    chartObj c Z ⟶ Over.mk c.equation.projModelOver :=
  Over.homMk (c.isPullback.lift (pullback.fst Z.hom c.baseMap ≫ f.left)
    (pullback.snd Z.hom c.baseMap) (fst_comp_left_structureMap c f) ≫ c.modelIso.hom) (by simp)

private theorem chartHom_left (f : Z ⟶ Over.mk E.structureMap) :
    (chartHom c f).left = c.isPullback.lift (pullback.fst Z.hom c.baseMap ≫ f.left)
      (pullback.snd Z.hom c.baseMap) (fst_comp_left_structureMap c f) ≫ c.modelIso.hom :=
  (rfl)

-- The restriction to the base of `c` of a point `f` of `E` is recovered from its reading in the
-- projective model.
private theorem fst_comp_left (f : Z ⟶ Over.mk E.structureMap) :
    pullback.fst Z.hom c.baseMap ≫ f.left = ((chartHom c f).left ≫ c.modelIso.inv) ≫ c.toTotal := by
  simp [chartHom]

-- Points of `E` are determined by their readings on all charts.
private theorem ext_of_chartHom {f g : Z ⟶ Over.mk E.structureMap}
    (h : ∀ c : PointedWeierstrassChart E.structureMap E.zero, chartHom c f = chartHom c g) :
    f = g := by
  obtain ⟨A⟩ := E.localModel
  ext1
  exact A.hom_ext Z.hom _ _ fun i ↦ by rw [fst_comp_left, fst_comp_left, h]

-- On the base of `c`, the sum of two points reads as the sum of their readings.
private theorem chartHom_add (f g : Z ⟶ Over.mk E.structureMap) :
    chartHom c (f * g) = chartHom c f * chartHom c g := by
  rw [points_mul_def]
  ext1
  -- the pair of the readings of `f` and `g`, as points of the restriction of `E`
  set P := pullback.lift (f := c.toBase) (g := c.toBase) ((chartHom c f).left ≫ c.modelIso.inv)
    ((chartHom c g).left ≫ c.modelIso.inv) (by simp [chartHom]) with hP
  have key : c.isPullback.lift (pullback.fst Z.hom c.baseMap ≫ (lift f g ≫ E.addHom).left)
      (pullback.snd Z.hom c.baseMap) (fst_comp_left_structureMap c _) = P ≫ c.addition := by
    refine c.isPullback.hom_ext ?_ ?_
    · have : pullback.fst Z.hom c.baseMap ≫ pullback.lift f.left g.left (f.w.trans g.w.symm) =
          P ≫ pullback.map _ _ _ _ c.toTotal c.toTotal c.baseMap c.isPullback.w.symm
            c.isPullback.w.symm := by
        apply pullback.hom_ext <;> simp [hP, fst_comp_left]
      simp only [addHom, Over.comp_left, Over.homMk_left, Over.lift_left, IsPullback.lift_fst,
        Category.assoc]
      rw [reassoc_of% this, pullbackMap_addition]
    · simp [hP, chartHom]
  rw [chartHom_left, key, Category.assoc, addition_modelIso_hom, ← Category.assoc]
  simp only [Hom.mul_def, Over.comp_left, Over.lift_left, WeierstrassCurve.mul_projModel_left]
  congr 1
  apply pullback.hom_ext <;> simp [hP, chartHom]

-- On the base of `c`, the zero point reads as the zero point.
private theorem chartHom_one : chartHom c (1 : Z ⟶ Over.mk E.structureMap) = 1 := by
  rw [points_one_def]
  ext1
  have key : c.isPullback.lift (pullback.fst Z.hom c.baseMap ≫ (toUnit Z ≫ E.zeroHom).left)
      (pullback.snd Z.hom c.baseMap) (fst_comp_left_structureMap c _) =
        pullback.snd Z.hom c.baseMap ≫ c.pulledZero :=
    c.isPullback.hom_ext (by simp [zeroHom, pullback.condition_assoc]) (by simp)
  rw [chartHom_left, key]
  simp [Hom.one_def]

-- On the base of `c`, the negation of a point reads as the negation of its reading.
private theorem chartHom_neg (f : Z ⟶ Over.mk E.structureMap) :
    chartHom c f⁻¹ = (chartHom c f)⁻¹ := by
  rw [points_inv_def]
  ext1
  have key : c.isPullback.lift (pullback.fst Z.hom c.baseMap ≫ (f ≫ E.negHom).left)
      (pullback.snd Z.hom c.baseMap) (fst_comp_left_structureMap c _) =
        c.isPullback.lift (pullback.fst Z.hom c.baseMap ≫ f.left)
          (pullback.snd Z.hom c.baseMap) (fst_comp_left_structureMap c f) ≫ c.neg :=
    c.isPullback.hom_ext
      (by rw [Category.assoc, ← toTotal_neg, IsPullback.lift_fst_assoc]; simp [negHom]) (by simp)
  rw [chartHom_left, key, Category.assoc, neg_modelIso_hom]
  simp [Hom.inv_def, chartHom_left]

end Chart

-- The morphisms `Z ⟶ E` over `S` form a commutative group, with the sum of `f` and `g` the
-- composite of `(f, g) : Z ⟶ E ×_S E` with the addition morphism.
private noncomputable abbrev pointsCommGroup : CommGroup (Z ⟶ Over.mk E.structureMap) where
  toMul := E.pointsMul
  toOne := E.pointsOne
  toInv := E.pointsInv
  mul_assoc f g h := E.ext_of_chartHom fun c ↦ by
    rw [chartHom_add, chartHom_add, chartHom_add, chartHom_add, _root_.mul_assoc]
  one_mul f := E.ext_of_chartHom fun c ↦ by rw [chartHom_add, chartHom_one, _root_.one_mul]
  mul_one f := E.ext_of_chartHom fun c ↦ by rw [chartHom_add, chartHom_one, _root_.mul_one]
  inv_mul_cancel f := E.ext_of_chartHom fun c ↦ by
    rw [chartHom_add, chartHom_neg, chartHom_one, _root_.inv_mul_cancel]
  mul_comm f g := E.ext_of_chartHom fun c ↦ by rw [chartHom_add, chartHom_add, _root_.mul_comm]

-- The presheaf of commutative groups of points of `E` on `Over S`: precomposition with a morphism
-- of `Over S` is a homomorphism of groups of points.
private noncomputable def pointsFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj Z := letI := E.pointsCommGroup (Z := Z.unop); .of (Z.unop ⟶ Over.mk E.structureMap)
  map {Z Z'} h := letI := E.pointsCommGroup (Z := Z.unop); letI := E.pointsCommGroup (Z := Z'.unop)
    CommGrpCat.ofHom
      { toFun := (h.unop ≫ ·)
        map_one' := by simp [points_one_def]
        map_mul' f g := by simp [points_mul_def, comp_lift_assoc] }

-- `E` represents its presheaf of points.
private noncomputable def pointsRepresentableBy :
    (E.pointsFunctor ⋙ forget _).RepresentableBy (Over.mk E.structureMap) where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

-- The commutative group-object structure on `Over.mk E.structureMap` given by the presheaf of
-- commutative groups it represents.
private noncomputable abbrev commGrpObj : CommGrpObj (Over.mk E.structureMap) :=
  .ofRepresentableBy _ E.pointsFunctor E.pointsRepresentableBy

-- In the represented structure, the unit is the zero section.
private theorem commGrpObj_one : E.commGrpObj.toMonObj.one = E.zeroHom := by
  -- by construction, the unit is the zero point `toUnit _ ≫ zeroHom` of `𝟙_ (Over S)`
  rw [← Category.id_comp E.zeroHom, ← toUnit_unit]
  rfl

-- In the represented structure, the multiplication is the addition morphism.
private theorem commGrpObj_mul : E.commGrpObj.toMonObj.mul = E.addHom := by
  -- by construction, the multiplication is the sum `lift (fst _ _) (snd _ _) ≫ addHom` of the
  -- two projections
  rw [← Category.id_comp E.addHom, ← lift_fst_snd]
  rfl

-- In the represented structure, the inverse is the negation morphism.
private theorem commGrpObj_inv : E.commGrpObj.toGrpObj.inv = E.negHom := by
  -- by construction, the inverse is the negation `𝟙 _ ≫ negHom` of the identity point
  rw [← Category.id_comp E.negHom]
  rfl

end Points

/-! ### The group law -/

/-- **The group law of an elliptic curve over a scheme.** An elliptic curve `E` over a scheme `S`,
as the object `Over.mk E.structureMap` of the cartesian monoidal category `Over S`, is a group
object: its unit is the zero section, its multiplication is the addition morphism
`E ×_S E ⟶ E` and its inverse is the negation morphism. -/
noncomputable instance grpObj : GrpObj (Over.mk E.structureMap) where
  one := Over.homMk E.zero (by simp)
  mul := Over.homMk E.addition (by simp)
  inv := Over.homMk E.neg (by simp)
  -- each axiom is the corresponding axiom of the structure represented by the points of `E`
  one_mul := by simpa only [commGrpObj_one, commGrpObj_mul] using E.commGrpObj.toMonObj.one_mul
  mul_one := by simpa only [commGrpObj_one, commGrpObj_mul] using E.commGrpObj.toMonObj.mul_one
  mul_assoc := by simpa only [commGrpObj_mul] using E.commGrpObj.toMonObj.mul_assoc
  left_inv := by
    simpa only [commGrpObj_one, commGrpObj_mul, commGrpObj_inv] using E.commGrpObj.toGrpObj.left_inv
  right_inv := by
    simpa only [commGrpObj_one, commGrpObj_mul, commGrpObj_inv] using
      E.commGrpObj.toGrpObj.right_inv

/-- **The group law of an elliptic curve over a scheme is commutative.** -/
instance isCommMonObj : IsCommMonObj (Over.mk E.structureMap) where
  mul_comm := by
    -- the multiplication of `grpObj` is `addHom`, the multiplication of the represented structure
    have h := E.commGrpObj.toIsCommMonObj.mul_comm
    rw [commGrpObj_mul] at h
    exact h

/-- The unit of the group law of an elliptic curve is the zero section. -/
@[simp]
theorem one_left : η[Over.mk E.structureMap].left = E.zero :=
  (rfl)

/-- The multiplication of the group law of an elliptic curve is the addition morphism. -/
@[simp]
theorem mul_left : μ[Over.mk E.structureMap].left = E.addition :=
  (rfl)

/-- The inverse of the group law of an elliptic curve is the negation morphism. -/
@[simp]
theorem inv_left : ι[Over.mk E.structureMap].left = E.neg :=
  (rfl)

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
