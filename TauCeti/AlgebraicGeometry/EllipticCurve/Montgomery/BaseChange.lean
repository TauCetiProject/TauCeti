/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Coordinates
-- Proof-only: transport of points along an equality of curves keeps their coordinates.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# Base change of Montgomery points and their coordinate pairs

An injective ring homomorphism `f : R →+* S`, such as a field embedding, carries the native
points of the monic Montgomery model `TauCeti.Montgomery.model A B` over `R` to native points of
`model (f A) (f B)` over `S` by applying `f` to both coordinates. This is
`WeierstrassCurve.Affine.Point.mapAlong`, read through the identification
`(model A B).map f = model (f A) (f B)` of `TauCeti.Montgomery.map_model`.

The coordinate pair of the image of a point is the image under `TauCeti.Montgomery.Pair.map f` of
its coordinate pair, so Montgomery's `x`-only arithmetic over `R` may be carried out after base
change. Over fields the map is additive, and the projective `x`-coordinate commutes with the
coordinatewise change of field `RingHom.mapProjective`. Thus both the coordinate pairs and their
projective classes commute with base change.

## Main definitions

* `TauCeti.Montgomery.mapPoint f hf`: the native point of `model (f A) (f B)` induced by a native
  point of `model A B`, for an injective ring homomorphism `f`.

## Main results

* `TauCeti.Montgomery.coordinates_mapPoint`: the coordinate pair of `mapPoint f hf P` is the
  image of the coordinate pair of `P` under `f`.
* `TauCeti.Montgomery.mapPoint_neg`, `TauCeti.Montgomery.mapPoint_injective` and, over fields,
  `TauCeti.Montgomery.mapPoint_add` and `TauCeti.Montgomery.mapPoint_zsmul`: the map commutes
  with negation, addition and integer multiples and is injective.
* `TauCeti.Montgomery.projectiveX_mapPoint`: the projective `x`-coordinate of the image of a
  point is the coordinatewise image of its projective `x`-coordinate.
* `TauCeti.Montgomery.projectiveX_mapPoint_eq_projectiveX_mapPoint_iff`: along a field
  embedding, two native points have the same projective `x`-coordinate after base change exactly
  when they do before.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S] {A B : R} (f : R →+* S)
  (hf : Function.Injective f)

/-- The native point of `model (f A) (f B)` induced by a native point of `model A B` along an
injective ring homomorphism `f`: infinity goes to infinity and `(x', y')` to `(f x', f y')`. -/
noncomputable def mapPoint (P : (model A B).toAffine.Point) :
    (model (f A) (f B)).toAffine.Point :=
  cast (congrArg (fun V : WeierstrassCurve S ↦ V.toAffine.Point) (map_model A B f))
    (P.mapAlong f hf)

/-- Base change sends the point at infinity to the point at infinity. -/
@[simp]
theorem mapPoint_zero : mapPoint f hf (0 : (model A B).toAffine.Point) = 0 := by
  rw [mapPoint, Affine.Point.mapAlong_zero]
  exact Affine.Point.cast_zero (map_model A B f)

/-- Base change applies `f` to both coordinates of an affine point. -/
@[simp]
theorem mapPoint_some {x y : R} (h : (model A B).toAffine.Nonsingular x y) :
    mapPoint f hf (.some x y h) =
      .some (f x) (f y) (map_model A B f ▸ (Affine.map_nonsingular _ hf x y).mpr h) := by
  rw [mapPoint, Affine.Point.mapAlong_some]
  exact Affine.Point.cast_some (map_model A B f) _

/-- Base change commutes with negation. -/
@[simp]
theorem mapPoint_neg (P : (model A B).toAffine.Point) :
    mapPoint f hf (-P) = -mapPoint f hf P := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Affine.Point.zero_def]
  · simp [Affine.Point.neg_some, Affine.negY]

/-- Base change along an injective ring homomorphism is injective on native points. -/
theorem mapPoint_injective : Function.Injective (mapPoint f hf (A := A) (B := B)) :=
  fun _ _ h ↦ Affine.Point.mapAlong_injective f hf ((cast_inj _).mp h)

/-- **The coordinate pair commutes with base change**: the coordinate pair of the image of `P`
is the image under `f` of the coordinate pair of `P`. -/
@[simp]
theorem coordinates_mapPoint (P : (model A B).toAffine.Point) :
    coordinates (f A) (f B) (mapPoint f hf P) = (coordinates A B P).map f := by
  rcases P with _ | ⟨x, y, h⟩
  · ext <;> simp [← Affine.Point.zero_def]
  · ext <;> simp

end CommRing

section Field

variable {K L : Type*} [Field K] [Field L] {A B : K} (f : K →+* L)

variable [DecidableEq K] [DecidableEq L] in
/-- Over fields, base change is additive. -/
@[simp]
theorem mapPoint_add (P Q : (model A B).toAffine.Point) :
    mapPoint f f.injective (P + Q) = mapPoint f f.injective P + mapPoint f f.injective Q := by
  rw [mapPoint, mapPoint, mapPoint, Affine.Point.mapAlong_add]
  exact map_add (AddEquiv.cast (M := fun V : WeierstrassCurve L ↦ V.toAffine.Point)
    (map_model A B f)) _ _

variable [DecidableEq K] [DecidableEq L] in
/-- Over fields, base change commutes with integer multiples. -/
@[simp]
theorem mapPoint_zsmul (n : ℤ) (P : (model A B).toAffine.Point) :
    mapPoint f f.injective (n • P) = n • mapPoint f f.injective P :=
  map_zsmul (AddMonoidHom.mk' _ (mapPoint_add f)) n P

/-- The projective `x`-coordinate commutes with a field embedding, including at infinity.
This is equality of projective points, not just preservation of their fibres. -/
theorem projectiveX_mapPoint (hB : B ≠ 0) (P : (model A B).toAffine.Point) :
    projectiveX (f A) ((map_ne_zero f).mpr hB) (mapPoint f f.injective P) =
      f.mapProjective (projectiveX A hB P) := by
  simp only [projectiveX_def, coordinates_mapPoint, Pair.mapProjective_toProj]

/-- **The projective `x`-coordinate is compatible with field embeddings**: two native points
have the same projective `x`-coordinate after base change exactly when they do before. -/
theorem projectiveX_mapPoint_eq_projectiveX_mapPoint_iff (hB : B ≠ 0)
    {P Q : (model A B).toAffine.Point} :
    projectiveX (f A) ((map_ne_zero f).mpr hB) (mapPoint f f.injective P) =
        projectiveX (f A) ((map_ne_zero f).mpr hB) (mapPoint f f.injective Q) ↔
      projectiveX A hB P = projectiveX A hB Q := by
  simp only [projectiveX_mapPoint f hB, (f.mapProjective_injective).eq_iff]

end Field

end TauCeti.Montgomery
