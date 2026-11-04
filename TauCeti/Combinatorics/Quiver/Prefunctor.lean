/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Combinatorics.Quiver.Subquiver

/-!
# Prefunctors on paths, on vertices and on total arrows

Elementary facts about a prefunctor `φ : Q ⥤q R` which `Prefunctor.mapPath` and `Prefunctor.comp`
leave unrecorded: pushing a path along `φ` preserves its length and maps its vertices along
`φ.obj`, a prefunctor with a two-sided inverse is bijective on vertices, a pair of composable
one-sided inverse pairs composes to a one-sided inverse pair, and a prefunctor that undoes another
on vertices and arrows also undoes it on paths. It also records the map `Prefunctor.mapTotal` that
a prefunctor induces on the total spaces of arrows `Quiver.Total`, used to state that a functor
between categories with topologies on their arrows is continuous.

## Main results

* `Prefunctor.length_mapPath`: pushing a path along a prefunctor preserves its length.
* `Prefunctor.vertices_mapPath`: the vertices of the pushed path are the images of the vertices of
  the original path.
* `Prefunctor.obj_bijective_of_comp_eq_id`: mutually inverse prefunctors are bijective on vertices.
* `Prefunctor.comp_comp_comp_eq_id`: composing two one-sided inverse pairs of prefunctors gives a
  one-sided inverse pair.
* `Prefunctor.cast_mapPath_eq_of_eq`: equal prefunctors have equal path maps after casting the
  endpoints.
* `Prefunctor.cast_mapPath_mapPath`: a prefunctor that undoes another on vertices and arrows
  undoes it on paths.
* `Prefunctor.mapTotal`: the map induced by a prefunctor on total spaces of arrows, with its
  identity and composition laws `Prefunctor.mapTotal_id` and `Prefunctor.mapTotal_comp`.

## References

The first three feed `TauCeti.PathAlgebra.mapAlgHom` in
`TauCeti/RepresentationTheory/Quiver/PathAlgebra/Map.lean`, whose uniform hypothesis is
bijectivity on vertices, and the transport of the zigzag relations in
`TauCeti/RepresentationTheory/Quiver/Zigzag/Isomorphism.lean`, which is stated in terms of path
lengths.
`Prefunctor.cast_mapPath_mapPath` gives the inverse laws for path transport along isomorphisms of
bounded networks in `TauCeti/Combinatorics/Network/Isomorphism.lean`.
-/

public section

namespace TauCeti

universe u u' u'' v v' v''

variable {Q : Type u} {R : Type u'} {S : Type u''} [Quiver.{v} Q] [Quiver.{v'} R] [Quiver.{v''} S]

/-- **Pushing a path along a prefunctor preserves its length**: the image path traverses the image
of each arrow of the original, in order. -/
@[simp]
theorem _root_.Prefunctor.length_mapPath (φ : Q ⥤q R) {a b : Q} (p : Quiver.Path a b) :
    (φ.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => rw [Prefunctor.mapPath_cons, Quiver.Path.length_cons, ih,
      Quiver.Path.length_cons]

/-- The vertices of a path pushed along a prefunctor are the images of its vertices, in order. -/
@[simp]
theorem _root_.Prefunctor.vertices_mapPath (φ : Q ⥤q R) {a b : Q} (p : Quiver.Path a b) :
    (φ.mapPath p).vertices = p.vertices.map φ.obj := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

/-- **Mutually inverse prefunctors are bijective on vertices.** -/
theorem _root_.Prefunctor.obj_bijective_of_comp_eq_id (φ : Q ⥤q R) (ψ : R ⥤q Q)
    (hφψ : φ.comp ψ = Prefunctor.id Q) (hψφ : ψ.comp φ = Prefunctor.id R) :
    Function.Bijective φ.obj :=
  Function.bijective_iff_has_inverse.mpr
    ⟨ψ.obj, fun a ↦ congrArg (fun F : Q ⥤q Q ↦ F.obj a) hφψ,
      fun b ↦ congrArg (fun F : R ⥤q R ↦ F.obj b) hψφ⟩

/-- **One-sided inverse pairs of prefunctors compose**: if `ψ` is a right inverse of `φ` and `ψ'`
one of `φ'`, then `ψ' ⋙q ψ` is a right inverse of `φ ⋙q φ'`. Applying this to a mutually inverse
pair in each order gives both inverse laws for the composite pair. -/
theorem _root_.Prefunctor.comp_comp_comp_eq_id (φ : Q ⥤q R) (ψ : R ⥤q Q) (φ' : R ⥤q S)
    (ψ' : S ⥤q R) (hφψ : φ.comp ψ = Prefunctor.id Q) (hφψ' : φ'.comp ψ' = Prefunctor.id R) :
    (φ.comp φ').comp (ψ'.comp ψ) = Prefunctor.id Q := by
  rw [Prefunctor.comp_assoc, ← Prefunctor.comp_assoc φ' ψ' ψ, hφψ', Prefunctor.id_comp, hφψ]

/-- Equal prefunctors map a path equally after casting along the induced endpoint equalities. -/
theorem _root_.Prefunctor.cast_mapPath_eq_of_eq {φ ψ : Q ⥤q R} (h : φ = ψ)
    {a b : Q} (p : Quiver.Path a b) :
    (φ.mapPath p).cast
      (congrArg (fun ξ : Q ⥤q R ↦ ξ.obj a) h)
      (congrArg (fun ξ : Q ⥤q R ↦ ξ.obj b) h) = ψ.mapPath p := by
  subst ψ
  rfl

/-- **A prefunctor that undoes another on vertices and arrows undoes it on paths**: pushing a path
along `φ` and then `ψ` returns the original path once its endpoints are transported back. -/
theorem _root_.Prefunctor.cast_mapPath_mapPath (φ : Q ⥤q R) (ψ : R ⥤q Q)
    (hobj : ∀ a, ψ.obj (φ.obj a) = a)
    (hmap : ∀ {a b} (e : a ⟶ b), (ψ.map (φ.map e)).cast (hobj a) (hobj b) = e)
    {a b : Q} (p : Quiver.Path a b) :
    (ψ.mapPath (φ.mapPath p)).cast (hobj a) (hobj b) = p := by
  induction p with
  | nil => exact Quiver.Path.cast_nil (hobj a)
  | @cons b c p e ih =>
      -- `Quiver.Path.cast_cons` keeps the middle vertex fixed; here it moves along `hobj b`.
      have cast_cons {a' b' c' : Q} (q : Quiver.Path a' b') (f : b' ⟶ c') (ha : a' = a)
          (hb : b' = b) (hc : c' = c) :
          (q.cons f).cast ha hc = (q.cast ha hb).cons (f.cast hb hc) := by
        subst ha hb hc
        rfl
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons, cast_cons _ _ _ (hobj b), ih, hmap]

/-- The map on total spaces of arrows induced by a prefunctor, sending `f : a ⟶ b` to
`φ.map f : φ.obj a ⟶ φ.obj b`. -/
@[expose] def _root_.Prefunctor.mapTotal (φ : Q ⥤q R) (f : Quiver.Total Q) : Quiver.Total R :=
  ⟨φ.obj f.left, φ.obj f.right, φ.map f.hom⟩

/-- The image of a total arrow given by its components is given by their images. -/
@[simp]
theorem _root_.Prefunctor.mapTotal_mk (φ : Q ⥤q R) {a b : Q} (f : a ⟶ b) :
    φ.mapTotal ⟨a, b, f⟩ = ⟨φ.obj a, φ.obj b, φ.map f⟩ := (rfl)

/-- The source of the image of a total arrow is the image of its source. -/
@[simp]
theorem _root_.Prefunctor.mapTotal_left (φ : Q ⥤q R) (f : Quiver.Total Q) :
    (φ.mapTotal f).left = φ.obj f.left := (rfl)

/-- The target of the image of a total arrow is the image of its target. -/
@[simp]
theorem _root_.Prefunctor.mapTotal_right (φ : Q ⥤q R) (f : Quiver.Total Q) :
    (φ.mapTotal f).right = φ.obj f.right := (rfl)

/-- The arrow underlying the image of a total arrow is the image of its arrow. -/
@[simp]
theorem _root_.Prefunctor.mapTotal_hom (φ : Q ⥤q R) (f : Quiver.Total Q) :
    (φ.mapTotal f).hom = φ.map f.hom := (rfl)

/-- The identity prefunctor induces the identity on total arrows. -/
@[simp]
theorem _root_.Prefunctor.mapTotal_id : (𝟭q Q).mapTotal = id := (rfl)

/-- A composite of prefunctors induces the composite of the maps on total arrows. -/
@[simp]
theorem _root_.Prefunctor.mapTotal_comp (φ : Q ⥤q R) (ψ : R ⥤q S) :
    (φ ⋙q ψ).mapTotal = ψ.mapTotal ∘ φ.mapTotal := (rfl)

end TauCeti
