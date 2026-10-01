/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Reduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
-- Proof-only: the class-group point map sends a point to the point under its place.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Place
-- Proof-only: a restricted rational place is rational.
import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
-- Proof-only: a place has finitely many extensions.
import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre
-- Proof-only: an elliptic curve has infinitely many points over a separably closed field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed

/-!
# The action of a morphism on points

A morphism `f : Hom W₁ W₂` of elliptic curves is recorded by its tautological point, a point of
`W₂` over the function field of `W₁`. Its value at a point `P` of `W₁` is the reduction of that
point at the place of `P` (`WeierstrassCurve.Affine.reductionOfDegreeEqOne`). This file defines
that map, `Hom.pointMap`, and proves the facts that make it the action of `f` on points:

* it is additive **in the morphism**;
* for an isogeny `φ`, the place of `φ P` is the restriction of the place of `P` along `φ^*`,
  and composites act by composition;
* the zero morphism sends every point to `O` and the identity fixes every point;
* for a separable isogeny over a separably closed field it agrees with the additive class-group
  point map `TauCeti.Isogeny.toPointHom`.

**Rigidity.** A nonzero morphism has finite fibres on points. Thus two morphisms agreeing on
infinitely many points are equal. Over a separably closed field the points are infinitely many,
and a morphism is determined by its action on them.

Rigidity yields **additivity of composition in the inner variable** wherever the outer morphism
acts additively on points. For a separable isogeny `φ` over a separably closed field this gives
`φ ∘ (f + g) = φ ∘ f + φ ∘ g`.

## Main definitions

* `TauCeti.Isogeny.Hom.pointMap`: the action of a morphism on points.

## Main results

* `TauCeti.Isogeny.Hom.add_pointMap`: the action is additive in the morphism.
* `TauCeti.Isogeny.Hom.pointMap_ofIsogeny_eq_iff`: an isogeny sends `P` to `Q` exactly when the
  place of `P` restricts along its pullback to the place of `Q`.
* `TauCeti.Isogeny.Hom.pointMap_ofIsogeny_eq_iff_restrict`: the criterion as equality of places.
* `TauCeti.Isogeny.Hom.comp_pointMap`: a composite acts by composition.
* `TauCeti.Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom`: for a separable isogeny over a
  separably closed field the action is the class-group point map.
* `TauCeti.Isogeny.Hom.pointMap_add`: the point map of a separable isogeny is additive.
* `TauCeti.Isogeny.Hom.finite_setOf_pointMap_eq`: a nonzero morphism has finite fibres.
* `TauCeti.Isogeny.Hom.eq_of_infinite_setOf_pointMap_eq` and `TauCeti.Isogeny.Hom.ext_pointMap`:
  rigidity.
* `TauCeti.Isogeny.Hom.comp_add_of_pointMap_add`: composition is additive in the inner morphism
  when the outer point map is additive and the source has infinitely many points.
* `TauCeti.Isogeny.Hom.ofIsogeny_comp_add`: composition with a separable isogeny over a separably
  closed field is additive in the inner morphism.
* `TauCeti.Isogeny.Hom.ofIsogeny_comp_zsmul`: and, consequently, `ℤ`-linear in it.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 (the map on points of a
  map of curves, read off the restriction of places), III.4.8 and III.4.10.
-/

public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The action of a morphism on points**: `f` sends `P` to the reduction of its tautological
point at the place of `P`. For an isogeny this is the point under `P`
(`pointMap_ofIsogeny_eq_iff`), and the zero morphism sends every point to `O`. -/
noncomputable def pointMap (f : Hom W₁ W₂) (P : W₁.Point) : W₂.Point :=
  (Point.equivBaseChangeSelf W₂).symm
    (reductionOfDegreeEqOne W₂ (W₁.pointEquivDegreeOnePlace P).2 f.tautologicalPoint)

/-- **The image of `P` is the point congruent to the tautological point** at the place of `P`. -/
theorem pointMap_eq_iff {f : Hom W₁ W₂} {P : W₁.Point} {Q : W₂.Point} :
    f.pointMap P = Q ↔
      f.tautologicalPoint - Point.baseChange (W' := W₂) F W₁.FunctionField
          (Point.equivBaseChangeSelf W₂ Q) ∈
        polePoints W₂ (W₁.pointEquivDegreeOnePlace P).1 := by
  rw [pointMap, AddEquiv.symm_apply_eq, reductionOfDegreeEqOne_eq_iff]

/-- **The zero morphism sends every point to `O`.** -/
@[simp]
theorem zero_pointMap (P : W₁.Point) : (0 : Hom W₁ W₂).pointMap P = 0 := by
  rw [pointMap, tautologicalPoint_zero, map_zero, map_zero]

/-- **The action on points is additive in the morphism.** -/
@[simp]
theorem add_pointMap (f g : Hom W₁ W₂) (P : W₁.Point) :
    (f + g).pointMap P = f.pointMap P + g.pointMap P := by
  rw [pointMap, tautologicalPoint_add, map_add, map_add, pointMap, pointMap]

@[simp]
theorem neg_pointMap (f : Hom W₁ W₂) (P : W₁.Point) : (-f).pointMap P = -f.pointMap P := by
  rw [pointMap, tautologicalPoint_neg, map_neg, map_neg, pointMap]

@[simp]
theorem sub_pointMap (f g : Hom W₁ W₂) (P : W₁.Point) :
    (f - g).pointMap P = f.pointMap P - g.pointMap P := by
  rw [sub_eq_add_neg, add_pointMap, neg_pointMap, sub_eq_add_neg]

@[simp]
theorem zsmul_pointMap (n : ℤ) (f : Hom W₁ W₂) (P : W₁.Point) :
    (n • f).pointMap P = n • f.pointMap P := by
  rw [pointMap, tautologicalPoint_zsmul, map_zsmul, map_zsmul, pointMap]

@[simp]
theorem nsmul_pointMap (n : ℕ) (f : Hom W₁ W₂) (P : W₁.Point) :
    (n • f).pointMap P = n • f.pointMap P := by
  rw [pointMap, tautologicalPoint_nsmul, map_nsmul, map_nsmul, pointMap]

/-- **Every morphism sends `O` to `O`.** -/
@[simp]
theorem pointMap_zero (f : Hom W₁ W₂) : f.pointMap 0 = 0 := by
  have h0 : (W₁.pointEquivDegreeOnePlace 0).1 = Place.infinity W₁ :=
    coe_pointEquivDegreeOnePlace_zero W₁
  rw [pointMap_eq_iff, h0, (Point.equivBaseChangeSelf W₂).map_zero, map_zero, sub_zero]
  exact tautologicalPoint_mem_polePoints f

/-- **The identity morphism fixes every point.** -/
@[simp]
theorem id_pointMap (P : W₁.Point) : (id W₁).pointMap P = P := by
  rw [pointMap, id_def, tautologicalPoint_ofIsogeny, Isogeny.id_pullback,
    CoordinatePullback.tautologicalPoint_id, reductionOfDegreeEqOne_genericPoint,
    AddEquiv.symm_apply_apply]

section Isogeny

variable (φ : Isogeny W₁ W₂)

/-- **An isogeny sends a point to the point under it.** If the place of `P` restricts along `φ^*`
to the place of `Q`, then `φ` sends `P` to `Q`. -/
theorem pointMap_ofIsogeny_of_isEquiv {P : W₁.Point} {Q : W₂.Point}
    (h : (((W₁.pointEquivDegreeOnePlace P).1.valuation).comap
      (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField)).IsEquiv
        (W₂.pointEquivDegreeOnePlace Q).1.valuation) :
    (ofIsogeny φ).pointMap P = Q := by
  rw [pointMap_eq_iff, tautologicalPoint_ofIsogeny, Isogeny.tautologicalPoint_eq_map_genericPoint,
    genericPoint_eq_some, Point.map_some]
  rcases Q with _ | ⟨a, b, hQ⟩
  · rw [← Point.zero_def, map_zero, map_zero, sub_zero, mem_polePoints_iff, Point.xCoord_some]
    refine Or.inr ?_
    rw [coe_pointEquivDegreeOnePlace_zero] at h
    have hx : 1 < (Place.infinity W₂).valuation (genericX W₂) := by
      rw [Place.valuation_infinity, genericX_eq_algebraMap]
      exact one_lt_infinityPlace_X W₂
    rwa [← not_le, ← Valuation.isEquiv_iff_val_le_one.mp h, not_le] at hx
  · rw [Point.equivBaseChangeSelf_some, some_sub_baseChange_mem_polePoints_iff]
    rw [coe_pointEquivDegreeOnePlace_some] at h
    have hx := valuation_pointPlace_genericX_sub_lt_one W₂ hQ.1
    have hy := valuation_pointPlace_genericY_sub_lt_one W₂ hQ.1
    rw [← Valuation.isEquiv_iff_val_lt_one.mp h, Valuation.comap_apply] at hx hy
    rw [RingHom.coe_coe, map_sub, AlgHom.commutes] at hx hy
    exact ⟨hx, hy⟩

/-- **The place of the image of `P` is the restriction of the place of `P`** along the pullback of
the isogeny, expressed as equivalence of valuations. -/
theorem isEquiv_comap_pointMap_ofIsogeny (P : W₁.Point) :
    (((W₁.pointEquivDegreeOnePlace P).1.valuation).comap
      (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField)).IsEquiv
        (W₂.pointEquivDegreeOnePlace ((ofIsogeny φ).pointMap P)).1.valuation := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback fun _ ↦ rfl
  have := φ.finiteDimensional_functionField fun _ ↦ rfl
  let v := (W₁.pointEquivDegreeOnePlace P).1
  -- the restriction of a rational place is rational
  have hv : (v.restrict F W₂.FunctionField).degree = 1 := by
    have hle := Place.degree_restrict_le F W₂.FunctionField v
    have hpos := (v.restrict F W₂.FunctionField).one_le_degree_of_isFunctionField
      W₂.isFunctionField
    have hdeg : v.degree = 1 := (W₁.pointEquivDegreeOnePlace P).2
    omega
  let Q := (W₂.pointEquivDegreeOnePlace).symm ⟨v.restrict F W₂.FunctionField, hv⟩
  have hQ : (W₂.pointEquivDegreeOnePlace Q).1 = v.restrict F W₂.FunctionField := by simp [Q]
  have he : (v.valuation.comap (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField)).IsEquiv
      (W₂.pointEquivDegreeOnePlace Q).1.valuation :=
    (Place.restrict_eq_iff_isEquiv_comap F W₂.FunctionField v _).mp hQ.symm
  rwa [pointMap_ofIsogeny_of_isEquiv φ he]

/-- **An isogeny sends `P` to `Q` exactly when the place of `P` restricts to the place of `Q`**
along its pullback. -/
theorem pointMap_ofIsogeny_eq_iff {P : W₁.Point} {Q : W₂.Point} :
    (ofIsogeny φ).pointMap P = Q ↔
      (((W₁.pointEquivDegreeOnePlace P).1.valuation).comap
        (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField)).IsEquiv
          (W₂.pointEquivDegreeOnePlace Q).1.valuation :=
  ⟨fun h ↦ h ▸ isEquiv_comap_pointMap_ofIsogeny φ P, pointMap_ofIsogeny_of_isEquiv φ⟩

/-- **An isogeny sends `P` to `Q` exactly when the place of `P` restricts to the place of `Q`.** -/
theorem pointMap_ofIsogeny_eq_iff_restrict {P : W₁.Point} {Q : W₂.Point} :
    letI := φ.fieldPullback.toRingHom.toAlgebra
    letI := φ.finiteDimensional_functionField fun _ ↦ rfl
    (ofIsogeny φ).pointMap P = Q ↔
      (W₁.pointEquivDegreeOnePlace P).1.restrict F W₂.FunctionField =
        (W₂.pointEquivDegreeOnePlace Q).1 := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := φ.finiteDimensional_functionField fun _ ↦ rfl
  exact (pointMap_ofIsogeny_eq_iff φ).trans
    (Place.restrict_eq_iff_isEquiv_comap F W₂.FunctionField _ _).symm

/-- **For a separable isogeny over a separably closed field the action on points is the
class-group point map**, both sending `P` to the point under it. In particular it is additive
in the point there. -/
theorem pointMap_ofIsogeny_eq_toPointHom [IsSepClosed F]
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] (P : W₁.Point) :
    haveI := W₂.isIntegrallyClosed_coordinateRing
    (ofIsogeny φ).pointMap P = φ.toPointHom P := by
  have := W₁.isIntegrallyClosed_coordinateRing
  have := W₂.isIntegrallyClosed_coordinateRing
  have := W₂.isDedekindDomain_coordinateRing_of_isIntegrallyClosed
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback fun _ ↦ rfl
  have := φ.finiteDimensional_functionField fun _ ↦ rfl
  exact pointMap_ofIsogeny_of_isEquiv φ <|
    (Place.restrict_eq_iff_isEquiv_comap F W₂.FunctionField _ _).mp
      (φ.coe_pointEquivDegreeOnePlace_toPointHom (fun _ ↦ rfl) P).symm

/-- **A separable isogeny over a separably closed field acts additively on points.** -/
@[simp]
theorem pointMap_add [IsSepClosed F]
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField] (P Q : W₁.Point) :
    (ofIsogeny φ).pointMap (P + Q) =
      (ofIsogeny φ).pointMap P + (ofIsogeny φ).pointMap Q := by
  have := W₂.isIntegrallyClosed_coordinateRing
  rw [pointMap_ofIsogeny_eq_toPointHom, map_add,
    ← pointMap_ofIsogeny_eq_toPointHom, ← pointMap_ofIsogeny_eq_toPointHom]

end Isogeny

/-- **A composite acts on points by composition.** -/
@[simp]
theorem comp_pointMap [W₃.IsElliptic] (g : Hom W₂ W₃) (f : Hom W₁ W₂) (P : W₁.Point) :
    (g.comp f).pointMap P = g.pointMap (f.pointMap P) := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [comp_zero, zero_pointMap, zero_pointMap, pointMap_zero]
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · rw [zero_comp, zero_pointMap, zero_pointMap]
  rw [ofIsogeny_comp_ofIsogeny, pointMap_ofIsogeny_eq_iff, Isogeny.comp_fieldPullback,
    AlgHom.comp_toRingHom, Valuation.comap_comp]
  exact ((isEquiv_comap_pointMap_ofIsogeny φ P).comap
    (ψ.fieldPullback : W₃.FunctionField →+* W₂.FunctionField)).trans
      (isEquiv_comap_pointMap_ofIsogeny ψ _)

/-- **A nonzero morphism has finite fibres on points.** -/
theorem finite_setOf_pointMap_eq {f : Hom W₁ W₂} (hf : f ≠ 0) (Q : W₂.Point) :
    {P | f.pointMap P = Q}.Finite := by
  obtain ⟨φ, rfl⟩ := (eq_zero_or_exists_ofIsogeny f).resolve_left hf
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback fun _ ↦ rfl
  have := φ.finiteDimensional_functionField fun _ ↦ rfl
  let place : W₁.Point → Place F W₁.FunctionField := fun P ↦ (W₁.pointEquivDegreeOnePlace P).1
  have hplace : Set.InjOn place {P | (ofIsogeny φ).pointMap P = Q} := fun _ _ _ _ h ↦
    (W₁.pointEquivDegreeOnePlace).injective (Subtype.ext h)
  refine Set.Finite.of_finite_image (Set.Finite.subset
    (Place.finite_setOf_restrict_eq F W₂.FunctionField (W₂.pointEquivDegreeOnePlace Q).1) ?_)
    hplace
  rintro _ ⟨P, hP, rfl⟩
  exact (Place.restrict_eq_iff_isEquiv_comap F W₂.FunctionField _ _).mpr
    ((pointMap_ofIsogeny_eq_iff φ).mp hP)

/-- **Rigidity: two morphisms agreeing on infinitely many points are equal.** -/
theorem eq_of_infinite_setOf_pointMap_eq {f g : Hom W₁ W₂}
    (h : {P | f.pointMap P = g.pointMap P}.Infinite) : f = g := by
  by_contra hfg
  refine h (Set.Finite.subset (finite_setOf_pointMap_eq (sub_ne_zero.mpr hfg) 0) fun P hP ↦ ?_)
  rw [Set.mem_ofPred_eq, sub_pointMap, hP, sub_self]

/-- **Rigidity: when `W₁` has infinitely many points, a morphism is determined by its action on
them.** Over a separably closed field this is always the case. -/
theorem ext_pointMap [Infinite W₁.Point] {f g : Hom W₁ W₂}
    (h : ∀ P, f.pointMap P = g.pointMap P) : f = g :=
  eq_of_infinite_setOf_pointMap_eq (by simpa [h] using Set.infinite_univ)

/-- **Composition is additive in the inner morphism** when the source has infinitely many points
and the outer morphism acts additively on points. -/
theorem comp_add_of_pointMap_add [W₃.IsElliptic] [Infinite W₁.Point]
    (h : Hom W₂ W₃) (hadd : ∀ P Q, h.pointMap (P + Q) = h.pointMap P + h.pointMap Q)
    (f g : Hom W₁ W₂) : h.comp (f + g) = h.comp f + h.comp g := by
  refine ext_pointMap fun P ↦ ?_
  simp only [comp_pointMap, add_pointMap, hadd]

omit [DecidableEq F] in
/-- **Composition with a separable isogeny over a separably closed field is additive in the inner
morphism.** -/
@[simp]
theorem ofIsogeny_comp_add [IsSepClosed F] [W₃.IsElliptic] (φ : Isogeny W₂ W₃)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₂.FunctionField] (f g : Hom W₁ W₂) :
    (ofIsogeny φ).comp (f + g) = (ofIsogeny φ).comp f + (ofIsogeny φ).comp g := by
  classical
  have := WeierstrassCurve.Affine.infinite_point W₁
  exact comp_add_of_pointMap_add (ofIsogeny φ) (pointMap_add φ) f g

omit [DecidableEq F] in
/-- **Composition with a separable isogeny over a separably closed field is `ℤ`-linear in the
inner morphism.** -/
@[simp]
theorem ofIsogeny_comp_zsmul [IsSepClosed F] [W₃.IsElliptic] (φ : Isogeny W₂ W₃)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₂.FunctionField] (n : ℤ) (f : Hom W₁ W₂) :
    (ofIsogeny φ).comp (n • f) = n • (ofIsogeny φ).comp f :=
  map_zsmul (AddMonoidHom.mk' (fun f : Hom W₁ W₂ ↦ (ofIsogeny φ).comp f)
    (ofIsogeny_comp_add φ)) n f

end TauCeti.Isogeny.Hom

end
