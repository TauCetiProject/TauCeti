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
* `TauCeti.Isogeny.Hom.pointMap_map_algebraMap_map`: compatibility of the action on points of the
  base changes `W⁄L` and `W⁄M` with Mathlib's point map along an algebra homomorphism `L →ₐ[F] M`;
  for an automorphism of `L` over `F` this is Galois equivariance.
* `TauCeti.Isogeny.Hom.pointMap_map_algebraMap_genericPoint` and
  `TauCeti.Isogeny.Hom.pointMap_map_algebraMap_map_genericPoint`: evaluating the base-changed
  action on the generic point (or its image under an `F`-algebra homomorphism) recovers the
  tautological point (or its image).

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

/-- A morphism transported along equalities of its source and target curves acts on the transported
points by transport. -/
theorem pointMap_cast {V₁ V₁' V₂ V₂' : WeierstrassCurve K} [V₁.IsElliptic]
    [V₂.IsElliptic] [V₁'.IsElliptic] [V₂'.IsElliptic] (e₁ : V₁ = V₁') (e₂ : V₂ = V₂')
    {h : Hom V₁.toAffine V₂.toAffine} {h' : Hom V₁'.toAffine V₂'.toAffine} (hh : HEq h h')
    (P : V₁.toAffine.Point) :
    h'.pointMap (cast (congrArg (fun V : WeierstrassCurve K ↦ V.toAffine.Point) e₁) P) =
      cast (congrArg (fun V : WeierstrassCurve K ↦ V.toAffine.Point) e₂) (h.pointMap P) := by
  subst e₁ e₂
  cases eq_of_heq hh
  rfl

omit [DecidableEq F] in
/-- **Base change commutes with the point maps along algebra homomorphisms**: for an
`F`-algebra homomorphism `σ : L →ₐ[F] M` of fields, the base change of `h` to `M` sends the image
under `σ` of a point `P` of `W₁⁄L` to the image under `σ` of the image of `P` under the base change
of `h` to `L`. For an automorphism `σ` of `L` over `F` this says that the action of `h` on the
points over `L` is equivariant for the Galois action. -/
theorem pointMap_map_algebraMap_map {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F M]
    [DecidableEq L] [DecidableEq M] (h : Hom W₁ W₂) (σ : L →ₐ[F] M)
    (P : (W₁⁄L).toAffine.Point) :
    (h.map (algebraMap F M)).pointMap (Point.map σ P) =
      Point.map σ ((h.map (algebraMap F L)).pointMap P) := by
  classical
  -- transport `Point.map σ` to the transport `mapAlong σ`, along `(W⁄L).map σ = W⁄M` on both sides
  refine (congrArg _ (Point.map_eq_cast_mapAlong σ P)).trans ?_
  refine (pointMap_cast (W₁.map_baseChange σ) (W₂.map_baseChange σ)
    (h := (h.map (algebraMap F L)).map (σ : L →+* M)) ?_ _).trans ?_
  · rw [map_map]
    exact congr_arg_heq (fun g ↦ h.map g) σ.comp_algebraMap
  · exact (congrArg _ (pointMap_map _ _ P)).trans (Point.map_eq_cast_mapAlong σ _).symm

omit [DecidableEq F] [DecidableEq K] [W₂.IsElliptic] in
/-- At the place of the generic point on `W₁⁄F(W₁)`, the base-change embedding `F(W₁) → F(W₁)(W₁)`
from the curve factor agrees modulo the maximal ideal with `algebraMap` from the constant field. -/
private theorem valuation_pointPlace_generic_map_sub_lt_one
    (hP : (W₁.map (algebraMap F W₁.FunctionField)).Equation W₁.genericX W₁.genericY)
    (z : W₁.FunctionField) :
    (Place.ofPrime W₁.FunctionField (W₁.map (algebraMap F W₁.FunctionField)).FunctionField
      (CoordinateRing.pointPlace hP)).valuation
      (FunctionField.map W₁ (algebraMap F W₁.FunctionField) z -
        algebraMap W₁.FunctionField _ z) < 1 := by
  let L := W₁.FunctionField
  let ι := algebraMap F L
  let v := (Place.ofPrime L (W₁.map ι).FunctionField (CoordinateRing.pointPlace hP)).valuation
  have hval_le {w : L} (hw : v (FunctionField.map W₁ ι w - algebraMap L _ w) < 1) :
      v (FunctionField.map W₁ ι w) ≤ 1 := by
    rw [show FunctionField.map W₁ ι w = (FunctionField.map W₁ ι w - algebraMap L _ w) +
      algebraMap L _ w from (sub_add_cancel _ _).symm]
    exact (v.map_add _ _).trans
      (max_le hw.le (Valuation.IsTrivialOn.valuation_algebraMap_le_one v w))
  have hadj {w : L} (hw : w ∈ Algebra.adjoin F ({W₁.genericX, W₁.genericY} : Set L)) :
      v (FunctionField.map W₁ ι w - algebraMap L _ w) < 1 := by
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [FunctionField.map_genericX]
        exact valuation_pointPlace_genericX_sub_lt_one (W₁.map ι) hP
      · rw [FunctionField.map_genericY]
        exact valuation_pointPlace_genericY_sub_lt_one (W₁.map ι) hP
    | algebraMap c =>
      rw [FunctionField.map_algebraMap, sub_self, map_zero]
      exact zero_lt_one
    | add x y _ _ hx hy =>
      rw [_root_.map_add, _root_.map_add, add_sub_add_comm]
      exact (v.map_add _ _).trans_lt (max_lt hx hy)
    | mul x y _ _ hx hy =>
      rw [_root_.map_mul, _root_.map_mul,
        show FunctionField.map W₁ ι x * FunctionField.map W₁ ι y -
            algebraMap L _ x * algebraMap L _ y =
          (FunctionField.map W₁ ι x - algebraMap L _ x) * FunctionField.map W₁ ι y +
            algebraMap L _ x * (FunctionField.map W₁ ι y - algebraMap L _ y) by ring]
      exact (v.map_add _ _).trans_lt (max_lt
        ((v.map_mul _ _).trans_lt ((mul_le_of_le_one_right' (hval_le hy)).trans_lt hx))
        ((v.map_mul _ _).trans_lt ((mul_le_of_le_one_left'
          (Valuation.IsTrivialOn.valuation_algebraMap_le_one v x)).trans_lt hy)))
  obtain ⟨r, s, hs_mem, rfl⟩ := IsFractionRing.div_surjective (A := W₁.CoordinateRing) z
  let r' := algebraMap W₁.CoordinateRing L r
  let s' := algebraMap W₁.CoordinateRing L s
  have hr := hadj (algebraMap_mem_adjoin_genericX_genericY W₁ r)
  have hs := hadj (algebraMap_mem_adjoin_genericX_genericY W₁ s)
  have hs0 : s' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs_mem
  have hvs₂ : v (algebraMap L _ s') = 1 := Valuation.IsTrivialOn.eq_one s' hs0
  have hvs₁ : v (FunctionField.map W₁ ι s') = 1 := by
    rw [show FunctionField.map W₁ ι s' = (FunctionField.map W₁ ι s' - algebraMap L _ s') +
      algebraMap L _ s' from (sub_add_cancel _ _).symm,
      v.map_add_eq_of_lt_right (hs.trans_eq hvs₂.symm), hvs₂]
  have hs₁0 : FunctionField.map W₁ ι s' ≠ 0 :=
    (map_ne_zero_iff _ (FunctionField.map W₁ ι).injective).mpr hs0
  have hs₂0 : algebraMap L (W₁.map ι).FunctionField s' ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap L _).injective).mpr hs0
  change v (FunctionField.map W₁ ι (r' / s') - algebraMap L _ (r' / s')) < 1
  rw [map_div₀, map_div₀, div_sub_div _ _ hs₁0 hs₂0, map_div₀, v.map_mul, hvs₁, hvs₂,
    mul_one, div_one,
    show FunctionField.map W₁ ι r' * algebraMap L _ s' -
        FunctionField.map W₁ ι s' * algebraMap L _ r' =
      (FunctionField.map W₁ ι r' - algebraMap L _ r') * algebraMap L _ s' -
        algebraMap L _ r' * (FunctionField.map W₁ ι s' - algebraMap L _ s') by ring]
  exact (v.map_sub _ _).trans_lt (max_lt (by rwa [v.map_mul, hvs₂, mul_one])
    ((v.map_mul _ _).trans_lt ((mul_le_of_le_one_left'
      (Valuation.IsTrivialOn.valuation_algebraMap_le_one v r')).trans_lt hs)))

omit [DecidableEq F] [DecidableEq K] in
/-- **Evaluating a base-changed morphism at the generic point recovers its tautological point**:
at the diagonal place `(x - genericX, y - genericY)` of `F(W₁)(W₁)`, every function `z ∈ F(W₁)`
transported from the first factor agrees modulo the maximal ideal with the constant `z` from the
base field, so the tautological point of `h.map (algebraMap F F(W₁))` reduces to
`h.tautologicalPoint`. -/
@[simp]
theorem pointMap_map_algebraMap_genericPoint [DecidableEq W₁.FunctionField] (h : Hom W₁ W₂) :
    (h.map (algebraMap F W₁.FunctionField)).pointMap (genericPoint W₁) = h.tautologicalPoint := by
  -- `genericPoint W₁` and `h.tautologicalPoint` are typed on `W⁄F(W₁)`, which is definitionally
  -- `W.map (algebraMap F F(W₁))` but semireducible; `erw` aligns the curve types for `rw`.
  rcases eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩
  · erw [zero_map, zero_pointMap, tautologicalPoint_zero]
    rfl
  have hns : (W₁.map (algebraMap F W₁.FunctionField)).Nonsingular W₁.genericX W₁.genericY :=
    nonsingular_genericX_genericY W₁
  have hgen : (genericPoint W₁ : (W₁.map (algebraMap F W₁.FunctionField)).Point) =
      Point.some _ _ hns := genericPoint_eq_some W₁
  have hQ := (Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero φ.pullback)).symm
  erw [ofIsogeny_map, hgen, pointMap_eq_iff, tautologicalPoint_ofIsogeny,
    tautologicalPoint_ofIsogeny,
    ← Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero
      (φ.map (algebraMap F W₁.FunctionField)).pullback),
    hQ, Point.equivBaseChangeSelf_some, some_sub_baseChange_mem_polePoints_iff,
    coe_pointEquivDegreeOnePlace_some]
  simp only [CoordinatePullback.xCoord_tautologicalPoint,
    CoordinatePullback.yCoord_tautologicalPoint, Isogeny.map_pullback,
    CoordinatePullback.map_of_X, CoordinatePullback.map_root]
  exact ⟨valuation_pointPlace_generic_map_sub_lt_one hns.1 _,
    valuation_pointPlace_generic_map_sub_lt_one hns.1 _⟩

omit [DecidableEq F] [DecidableEq K] in
/-- **Evaluating a base-changed morphism at a specialized generic point recovers the specialized
tautological point**: for any `F`-algebra homomorphism `σ : F(W₁) →ₐ[F] M` into a field `M`, the
base-changed morphism sends `Point.map σ (genericPoint W₁)` to `Point.map σ h.tautologicalPoint`. -/
theorem pointMap_map_algebraMap_map_genericPoint {M : Type*} [Field M] [Algebra F M]
    [DecidableEq M] (h : Hom W₁ W₂) (σ : W₁.FunctionField →ₐ[F] M) :
    (h.map (algebraMap F M)).pointMap (Point.map σ (genericPoint W₁)) =
      Point.map σ h.tautologicalPoint := by
  classical
  rw [pointMap_map_algebraMap_map, pointMap_map_algebraMap_genericPoint]

end PointMap

end TauCeti.Isogeny.Hom

end
