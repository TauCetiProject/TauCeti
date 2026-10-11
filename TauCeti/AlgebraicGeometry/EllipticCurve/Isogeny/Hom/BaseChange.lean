/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
-- Proof-only: base change preserves the degree of an isogeny.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree

/-!
# Faithful additive base change of morphisms of elliptic curves

Base change of isogenies extends to `Isogeny.Hom`, sending the zero morphism to zero.
It preserves identity and composition and is injective along every homomorphism of fields.
For an elliptic target it also preserves addition: the tautological point of a transported
morphism is the transported tautological point, and field embeddings preserve the point-group
law. Thus identities between sums and composites can be checked after extending the ground
field, for example to a separable closure. Base change also commutes with the action on points,
the place of a transported point restricting to the place of the point; so statements about the
action on points, too, can be checked after extending the ground field.

The construction reuses `Isogeny.map`, Mathlib's additive map on points `Affine.Point.map`,
and the identification of morphisms with their tautological points in `Isogeny.Hom.Add`.

## Main definitions and results

* `TauCeti.Isogeny.Hom.map`: transport along a homomorphism of fields.
* `TauCeti.Isogeny.Hom.map_injective`: transport reflects equality.
* `TauCeti.Isogeny.Hom.tautologicalPoint_map`: compatibility with tautological points.
* `TauCeti.Isogeny.Hom.mapAddHom`: additive base change.
* `TauCeti.Isogeny.Hom.comp_map` and `TauCeti.Isogeny.Hom.map_add`: preservation of
  composition and addition.
* `TauCeti.Isogeny.Hom.degree_map`: preservation of the degree.
* `TauCeti.Isogeny.Hom.pointMap_map`: compatibility with the action on points.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.4.
-/

public section

open Polynomial WeierstrassCurve.Affine

namespace TauCeti.Isogeny.Hom

variable {F K L : Type*} [Field F] [Field K] [Field L]
  {W₁ W₂ W₃ : WeierstrassCurve.Affine F}

open scoped Classical in
/-- Transport a morphism along a homomorphism of its ground field, with zero sent to zero. -/
noncomputable def map (h : Hom W₁ W₂) (f : F →+* K) : Hom (W₁.map f) (W₂.map f) :=
  if hh : h = 0 then 0 else ofIsogeny ((toIsogeny hh).map f)

/-- Base change sends the zero morphism to zero. -/
@[simp]
theorem zero_map (f : F →+* K) : (0 : Hom W₁ W₂).map f = 0 := by
  classical
  simp [map]

/-- Base change on nonzero morphisms is the existing base change of isogenies. -/
@[simp]
theorem ofIsogeny_map (φ : Isogeny W₁ W₂) (f : F →+* K) :
    (ofIsogeny φ).map f = ofIsogeny (φ.map f) := by
  classical
  simp [map]

/-- The coordinate-ring square for the underlying multiplicative maps commutes,
including at the zero morphism. -/
@[simp]
theorem map_coordinateRingMap (h : Hom W₁ W₂) (f : F →+* K) (z : W₂.CoordinateRing) :
    (h.map f).toNonUnitalAlgHom (CoordinateRing.map W₂ f z) =
      FunctionField.map W₁ f (h.toNonUnitalAlgHom z) := by
  rcases eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩ <;> simp

/-- Extending the ground field reflects equality of morphisms. -/
theorem map_injective (f : F →+* K) :
    Function.Injective (fun h : Hom W₁ W₂ ↦ h.map f) := by
  intro h h' hh
  apply Hom.ext
  apply NonUnitalAlgHom.ext
  intro z
  apply (FunctionField.map W₁ f).injective
  simpa using congrArg
    (fun g : Hom (W₁.map f) (W₂.map f) ↦
      g.toNonUnitalAlgHom (CoordinateRing.map W₂ f z)) hh

@[simp]
theorem map_inj (f : F →+* K) {h h' : Hom W₁ W₂} : h.map f = h'.map f ↔ h = h' :=
  (map_injective f).eq_iff

@[simp]
theorem map_eq_zero_iff (h : Hom W₁ W₂) (f : F →+* K) : h.map f = 0 ↔ h = 0 := by
  rw [← zero_map f, map_inj]

/-- Base change preserves composition, including composites with zero. -/
@[simp]
theorem comp_map (g : Hom W₂ W₃) (h : Hom W₁ W₂) (f : F →+* K) :
    (g.comp h).map f = (g.map f).comp (h.map f) := by
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp
  rcases eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩ <;> simp

/-- **Base change preserves the degree**, the zero morphism included. -/
@[simp]
theorem degree_map (h : Hom W₁ W₂) (f : F →+* K) : (h.map f).degree = h.degree := by
  rcases eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩ <;> simp

/-- Base change preserves identity morphisms. -/
@[simp]
theorem id_map (W : WeierstrassCurve.Affine F) (f : F →+* K) :
    (id W).map f = id (W.map f) := by
  simp [id_def]

/-- Transport along the identity homomorphism fixes every morphism. -/
@[simp]
theorem map_id (h : Hom W₁ W₂) : h.map (RingHom.id F) = h := by
  -- The curve types agree definitionally, as in `WeierstrassCurve.map_id`.
  rcases eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩
  · exact zero_map _
  · rw [ofIsogeny_map]
    exact congrArg ofIsogeny (Isogeny.map_id φ)

/-- Transport is functorial in the ground-field homomorphism. -/
@[simp]
theorem map_map (h : Hom W₁ W₂) (f : F →+* K) (g : K →+* L) :
    (h.map f).map g = h.map (g.comp f) := by
  -- The curve types agree definitionally, as in `WeierstrassCurve.map_map`.
  rcases eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩
  · rw [zero_map]
    exact (zero_map g).trans (zero_map (g.comp f)).symm
  · simp only [ofIsogeny_map]
    exact congrArg ofIsogeny (Isogeny.map_map φ f g)

section Additive

variable [W₂.IsElliptic]

open scoped Classical in
/-- The tautological point of a transported morphism is its transported tautological point.
The cast identifies the two coefficient maps using the function-field commuting square. -/
@[simp]
theorem tautologicalPoint_map (h : Hom W₁ W₂) (f : F →+* K) :
    (h.map f).tautologicalPoint =
      AddEquiv.cast (M := fun V : WeierstrassCurve (W₁.map f).FunctionField ↦ V.toAffine.Point)
        (i := (W₂⁄W₁.FunctionField).map (FunctionField.map W₁ f))
        (j := (W₂.map f)⁄(W₁.map f).FunctionField)
        (FunctionField.map_map_algebraMap W₁ f W₂)
        (Point.mapAlong (W := W₂⁄W₁.FunctionField)
          (FunctionField.map W₁ f) (FunctionField.map W₁ f).injective
          h.tautologicalPoint) := by
  classical
  rcases eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩
  · rw [zero_map, tautologicalPoint_zero, tautologicalPoint_zero, Point.mapAlong_zero,
      map_zero]
  -- `erw` unfolds the base-change spelling in the endpoints of the explicit curve cast.
  erw [ofIsogeny_map, tautologicalPoint_ofIsogeny, tautologicalPoint_ofIsogeny,
    ← Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero φ.pullback),
    Point.mapAlong_some, AddEquiv.cast_apply,
    Point.cast_some (FunctionField.map_map_algebraMap W₁ f W₂),
    ← Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero (φ.map f).pullback)]
  simp only [CoordinatePullback.xCoord_tautologicalPoint,
    CoordinatePullback.yCoord_tautologicalPoint, Isogeny.map_pullback,
    CoordinatePullback.map_of_X, CoordinatePullback.map_root]
  rfl

/-- Base change preserves the group-law sum of morphisms. -/
@[simp]
theorem map_add (h h' : Hom W₁ W₂) (f : F →+* K) :
    (h + h').map f = h.map f + h'.map f := by
  classical
  let := (FunctionField.map W₁ f).toAlgebra
  apply tautologicalPoint_injective
  simp only [tautologicalPoint_map, tautologicalPoint_add]
  -- `erw` also identifies the ring homomorphism with the algebra map of `toAlgebra`.
  erw [Point.mapAlong_eq_map (F := W₁.FunctionField) (K := (W₁.map f).FunctionField),
    Point.mapAlong_eq_map (F := W₁.FunctionField) (K := (W₁.map f).FunctionField),
    Point.mapAlong_eq_map (F := W₁.FunctionField) (K := (W₁.map f).FunctionField),
    _root_.map_add, _root_.map_add]

/-- Additive base change of morphisms along a homomorphism of ground fields. -/
noncomputable def mapAddHom (f : F →+* K) : Hom W₁ W₂ →+ Hom (W₁.map f) (W₂.map f) where
  toFun h := h.map f
  map_zero' := zero_map f
  map_add' h h' := map_add h h' f

@[simp]
theorem mapAddHom_apply (f : F →+* K) (h : Hom W₁ W₂) : mapAddHom f h = h.map f := (rfl)

/-- Base change preserves negatives of morphisms. -/
@[simp]
theorem map_neg (h : Hom W₁ W₂) (f : F →+* K) : (-h).map f = -(h.map f) :=
  (mapAddHom f).map_neg h

/-- Base change preserves differences of morphisms. -/
@[simp]
theorem map_sub (h h' : Hom W₁ W₂) (f : F →+* K) :
    (h - h').map f = h.map f - h'.map f :=
  (mapAddHom f).map_sub h h'

/-- Base change commutes with integer multiples of morphisms. -/
@[simp]
theorem map_zsmul (n : ℤ) (h : Hom W₁ W₂) (f : F →+* K) :
    (n • h).map f = n • h.map f :=
  (mapAddHom f).map_zsmul n h

/-- Base change commutes with natural multiples of morphisms. -/
@[simp]
theorem map_nsmul (n : ℕ) (h : Hom W₁ W₂) (f : F →+* K) :
    (n • h).map f = n • h.map f :=
  (mapAddHom f).map_nsmul n h

end Additive

section PointMap

variable [DecidableEq F] [DecidableEq K] [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Base change commutes with the action on points**: the transported morphism sends the
transported point `P` to the transport of the image of `P`. -/
@[simp]
theorem pointMap_map (h : Hom W₁ W₂) (f : F →+* K) (P : W₁.Point) :
    (h.map f).pointMap (P.mapAlong f f.injective) = (h.pointMap P).mapAlong f f.injective := by
  rcases P with _ | ⟨a, b, hP⟩
  · rw [← Point.zero_def, Point.mapAlong_zero, pointMap_zero, pointMap_zero, Point.mapAlong_zero]
  rcases eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩
  · rw [zero_map, zero_pointMap, zero_pointMap, Point.mapAlong_zero]
  -- the place of the transported point restricts to the place of `P`, so the congruence between
  -- the tautological point and the image of `P` there persists after transport
  have he := W₁.isEquiv_comap_pointPlace_map f hP.1
  have hQ := (pointMap_eq_iff (f := ofIsogeny φ) (P := .some a b hP)).mp rfl
  generalize (ofIsogeny φ).pointMap (.some a b hP) = Q at hQ ⊢
  rw [ofIsogeny_map, pointMap_eq_iff, Point.mapAlong_some, tautologicalPoint_ofIsogeny,
    ← Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero _),
    coe_pointEquivDegreeOnePlace_some]
  rw [tautologicalPoint_ofIsogeny,
    ← Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero _),
    coe_pointEquivDegreeOnePlace_some] at hQ
  rcases Q with _ | ⟨c, d, hc⟩
  · rw [← Point.zero_def, Point.mapAlong_zero, map_zero, map_zero, sub_zero, mem_polePoints_iff,
      Point.xCoord_some]
    rw [← Point.zero_def, map_zero, map_zero, sub_zero, mem_polePoints_iff,
      Point.xCoord_some] at hQ
    simp only [CoordinatePullback.xCoord_tautologicalPoint, Isogeny.map_pullback,
      CoordinatePullback.map_of_X] at hQ ⊢
    exact Or.inr (he.one_lt_iff_one_lt.mpr (hQ.resolve_left (Point.some_ne_zero _)))
  · rw [Point.mapAlong_some, Point.equivBaseChangeSelf_some,
      some_sub_baseChange_mem_polePoints_iff]
    rw [Point.equivBaseChangeSelf_some, some_sub_baseChange_mem_polePoints_iff] at hQ
    simp only [CoordinatePullback.xCoord_tautologicalPoint,
      CoordinatePullback.yCoord_tautologicalPoint, Isogeny.map_pullback,
      CoordinatePullback.map_of_X, CoordinatePullback.map_root] at hQ ⊢
    have h₁ := he.lt_one_iff_lt_one.mpr hQ.1
    have h₂ := he.lt_one_iff_lt_one.mpr hQ.2
    rw [Valuation.comap_apply, _root_.map_sub, FunctionField.map_algebraMap] at h₁ h₂
    exact ⟨h₁, h₂⟩

end PointMap

end TauCeti.Isogeny.Hom

end
