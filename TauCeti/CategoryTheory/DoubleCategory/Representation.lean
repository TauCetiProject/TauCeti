/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import TauCeti.CategoryTheory.DoubleCategory.Globular

/-!
# Implicit double categories and their representations

An *implicit double category* on objects `O`, with horizontal generating quiver `H` and vertical
generating quiver `V`, is a strict double category whose horizontal and vertical edge categories
are the free path categories on `H` and on `V`. The boundaries of its cells are paths of
generators, which concatenate strictly.

A *representation* of the horizontal direction chooses, for all composable generators `f` and
`g`, a generator `f ⋆ g` with an invertible globular cell `[f, g] ≅ [f ⋆ g]`, and, for every
object `a`, an identity generator `1ₐ` with an invertible globular cell `[] ≅ [1ₐ]`. These are
data. The empty path `[]` and the singleton path `[1ₐ]` remain distinct; their comparison is part
of the representation. Applying the choices recursively from the left gives, for every path `p`,
a generator `rep p` with an invertible globular cell `p ≅ [rep p]`: the empty path is represented
by the identity generator, a singleton path by its generator through the identity cell, and a
longer path `p ++ [f]` by `rep p ⋆ f`. Hence a representation makes the horizontal direction
*representable*: every path is isomorphic to a singleton in the category of horizontally globular
cells.

The horizontal notions are stated for a strict double category whose horizontal edge category is
a path category and whose vertical edge category is arbitrary, so that they also apply to
one-directional presentations. The vertical notions are the horizontal ones applied to the
transpose. A representation of an implicit double category consists of one in each direction.

## Main declarations

* `TauCeti.Quiver.pathCategory` and `TauCeti.Quiver.Hom.toPathOf`: the path category of an
  explicitly supplied quiver and its paths of length one.
* `TauCeti.ImplicitDoubleCategory`: strict double categories on two free path categories.
* `TauCeti.StrictDoubleCategory.HorizontalRepresentation`: chosen binary and nullary horizontal
  composites with their comparison cells.
* `TauCeti.StrictDoubleCategory.HorizontalRepresentation.rep` and
  `TauCeti.StrictDoubleCategory.HorizontalRepresentation.repIso`: the recursive representation
  of an arbitrary path.
* `TauCeti.ImplicitDoubleCategory.Representation`, `TauCeti.ImplicitDoubleCategory.Representable`
  and `TauCeti.ImplicitDoubleCategory.representable_of_representation`.
* `TauCeti.ImplicitDoubleCategory.not_representable_of_isEmpty`: if some object has no horizontal
  generating loop, the empty path at that object has no representation.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651, Definitions 3.1–3.3 and Remark 3.5.
-/

@[expose] public section

universe s u h v

namespace TauCeti

open CategoryTheory DoubleCategoryStruct

/-- The category of paths of an explicitly supplied quiver `Q` on `O`. Its morphisms are the
paths `Quiver.Path`, its composition is concatenation and its identities are the empty paths. -/
abbrev Quiver.pathCategory (O : Type u) (Q : Quiver.{h} O) : Category.{max u h} O :=
  @Paths.categoryPaths O Q

/-- The path of length one on a generator `f` of an explicitly supplied quiver `Q`: this is
`Quiver.Hom.toPath` with the quiver given explicitly. -/
abbrev Quiver.Hom.toPathOf {O : Type u} (Q : Quiver.{h} O) {a b : O} (f : @Quiver.Hom O Q a b) :
    StrictDoubleCategory.Edge (Quiver.pathCategory O Q) a b :=
  @Quiver.Hom.toPath O Q a b f

namespace StrictDoubleCategory

variable {O : Type u} {H : Quiver.{h} O} {V : Category.{v} O}

variable (D : StrictDoubleCategory.{s} O (Quiver.pathCategory O H) V)

/-- A representation of the horizontal direction of a strict double category whose horizontal
edges are the paths of a quiver `H`: a chosen identity generator `unit a` at every object with an
invertible globular cell from the empty path to `[unit a]`, and a chosen composite generator
`mul f g` of all composable generators with an invertible globular cell from `[f, g]` to
`[mul f g]`. -/
@[ext]
structure HorizontalRepresentation where
  /-- The chosen identity generator at an object. -/
  unit (a : O) : @Quiver.Hom O H a a
  /-- The chosen composite of two composable generators. -/
  mul {a b c : O} : @Quiver.Hom O H a b → @Quiver.Hom O H b c → @Quiver.Hom O H a c
  /-- The comparison of the empty path with the chosen identity generator. -/
  unitIso (a : O) :
    D.HorizontalIso (edgeId (Quiver.pathCategory O H) a) (Quiver.Hom.toPathOf H (unit a))
  /-- The comparison of a path of length two with the chosen composite generator. -/
  mulIso {a b c : O} (f : @Quiver.Hom O H a b) (g : @Quiver.Hom O H b c) :
    D.HorizontalIso
      (edgeComp (Quiver.pathCategory O H) (Quiver.Hom.toPathOf H f) (Quiver.Hom.toPathOf H g))
      (Quiver.Hom.toPathOf H (mul f g))

/-- The horizontal direction is representable when every path of horizontal generators is
isomorphic, by an invertible horizontally globular cell, to a path of length one. -/
def HorizontallyRepresentable : Prop :=
  ∀ {a b : O} (p : Edge (Quiver.pathCategory O H) a b),
    ∃ f : @Quiver.Hom O H a b, Nonempty (D.HorizontalIso p (Quiver.Hom.toPathOf H f))

namespace HorizontalRepresentation

variable {D} (R : D.HorizontalRepresentation)

/-- The generator representing a path: the identity generator for the empty path, the generator
itself for a path of length one, and `rep p ⋆ f` for a path `p ++ [f]` with `p` nonempty. -/
def rep {a : O} : {b : O} → @Quiver.Path O H a b → @Quiver.Hom O H a b
  | _, .nil => R.unit a
  | _, .cons .nil f => f
  | _, .cons (.cons p g) f => R.mul (rep (.cons p g)) f

/-- The invertible globular cell comparing a path with the generator representing it. For the
empty path it is the chosen nullary comparison, for a path of length one it is the identity,
and for a path `p ++ [f]` with `p` nonempty it is the comparison of `p` pasted horizontally with
the identity cell of `[f]`, followed by the chosen binary comparison for `rep p` and `f`. -/
def repIso {a : O} :
    {b : O} → (p : @Quiver.Path O H a b) → D.HorizontalIso p (Quiver.Hom.toPathOf H (R.rep p))
  | _, .nil => R.unitIso a
  | _, .cons .nil _ => Iso.refl _
  | _, .cons (.cons p g) f =>
    (D.hCompFunctor _ _ _).mapIso
        ((repIso (.cons p g)).prod (Iso.refl ⟨Quiver.Hom.toPathOf H f⟩)) ≪≫
      R.mulIso (R.rep (.cons p g)) f

variable {a b c d : O}

/-- The empty path is represented by the chosen identity generator. -/
@[simp]
theorem rep_id (a : O) : R.rep (edgeId (Quiver.pathCategory O H) a) = R.unit a :=
  rfl

/-- A path of length one is represented by its generator. -/
@[simp]
theorem rep_toPathOf (f : @Quiver.Hom O H a b) : R.rep (Quiver.Hom.toPathOf H f) = f :=
  rfl

theorem rep_cons_cons (p : @Quiver.Path O H a b) (g : @Quiver.Hom O H b c)
    (f : @Quiver.Hom O H c d) : R.rep ((p.cons g).cons f) = R.mul (R.rep (p.cons g)) f :=
  rfl

/-- A nonempty path followed by one generator is represented by the chosen composite of the
representing generator of the path with that generator. -/
theorem rep_cons {p : @Quiver.Path O H a b} (hp : p.length ≠ 0) (f : @Quiver.Hom O H b c) :
    R.rep (p.cons f) = R.mul (R.rep p) f := by
  cases p with
  | nil => exact absurd rfl hp
  | cons p g => rfl

/-- A path of length two is represented by the chosen composite of its two generators. -/
@[simp]
theorem rep_toPathOf_comp_toPathOf (f : @Quiver.Hom O H a b) (g : @Quiver.Hom O H b c) :
    R.rep (edgeComp (Quiver.pathCategory O H) (Quiver.Hom.toPathOf H f)
      (Quiver.Hom.toPathOf H g)) = R.mul f g :=
  rfl

/-- The comparison for the empty path is the chosen nullary comparison. -/
@[simp]
theorem repIso_id (a : O) : R.repIso (edgeId (Quiver.pathCategory O H) a) = R.unitIso a :=
  rfl

/-- The comparison for a path of length one is the identity. -/
@[simp]
theorem repIso_toPathOf (f : @Quiver.Hom O H a b) :
    R.repIso (Quiver.Hom.toPathOf H f) = Iso.refl _ :=
  rfl

theorem repIso_cons_cons (p : @Quiver.Path O H a b) (g : @Quiver.Hom O H b c)
    (f : @Quiver.Hom O H c d) :
    R.repIso ((p.cons g).cons f) =
      (D.hCompFunctor _ _ _).mapIso
          ((R.repIso (p.cons g)).prod (Iso.refl ⟨Quiver.Hom.toPathOf H f⟩)) ≪≫
        R.mulIso (R.rep (p.cons g)) f :=
  rfl

/-- The comparison for a path of length two is the chosen binary comparison. -/
@[simp]
theorem repIso_toPathOf_comp_toPathOf (f : @Quiver.Hom O H a b) (g : @Quiver.Hom O H b c) :
    R.repIso (edgeComp (Quiver.pathCategory O H) (Quiver.Hom.toPathOf H f)
      (Quiver.Hom.toPathOf H g)) = R.mulIso f g := by
  refine (R.repIso_cons_cons .nil f g).trans (Iso.ext ?_)
  -- The comparison for `[f]` is the identity, so the first factor is the image of an identity.
  exact (congrArg (· ≫ (R.mulIso f g).hom) ((D.hCompFunctor a b c).map_id
    (⟨Quiver.Hom.toPathOf H f⟩, ⟨Quiver.Hom.toPathOf H g⟩))).trans (Category.id_comp _)

include R in
/-- A representation supplies representability: every path is isomorphic to the path of length
one on its representing generator. -/
theorem horizontallyRepresentable : D.HorizontallyRepresentable :=
  fun p ↦ ⟨R.rep p, ⟨R.repIso p⟩⟩

end HorizontalRepresentation

/-- If there is no horizontal generator from an object to itself, the empty path at that object
is isomorphic to no path of length one, so the horizontal direction is not representable. -/
theorem not_horizontallyRepresentable_of_isEmpty (a : O) [IsEmpty (@Quiver.Hom O H a a)] :
    ¬ D.HorizontallyRepresentable :=
  fun hD ↦ (hD (edgeId (Quiver.pathCategory O H) a)).elim fun f _ ↦ isEmptyElim f

/-- If there is no horizontal generator from an object to itself, there is no horizontal
representation, since it would choose an identity generator at that object. -/
theorem isEmpty_horizontalRepresentation (a : O) [IsEmpty (@Quiver.Hom O H a a)] :
    IsEmpty D.HorizontalRepresentation :=
  ⟨fun R ↦ isEmptyElim (R.unit a)⟩

end StrictDoubleCategory

open StrictDoubleCategory

/-- An implicit double category on objects `O` with horizontal generating quiver `H` and vertical
generating quiver `V`: a strict double category whose horizontal and vertical edge categories are
the free path categories on `H` and `V`. -/
abbrev ImplicitDoubleCategory (O : Type u) (H : Quiver.{h} O) (V : Quiver.{v} O) :=
  StrictDoubleCategory.{s} O (Quiver.pathCategory O H) (Quiver.pathCategory O V)

namespace ImplicitDoubleCategory

variable {O : Type u} {H : Quiver.{h} O} {V : Quiver.{v} O}
  (D : ImplicitDoubleCategory.{s} O H V)

/-- A representation of an implicit double category: chosen binary and nullary composites of
generators, with their comparison cells, in both directions. The vertical representation is a
horizontal representation of the transpose, so its comparison cells are invertible vertically
globular cells. -/
@[ext]
structure Representation where
  /-- The representation of the horizontal direction. -/
  horizontal : D.HorizontalRepresentation
  /-- The representation of the vertical direction. -/
  vertical : D.transpose.HorizontalRepresentation

/-- An implicit double category is representable when every path of horizontal generators is
isomorphic to a path of length one by an invertible horizontally globular cell, and every path of
vertical generators is isomorphic to a path of length one by an invertible vertically globular
cell. -/
structure Representable : Prop where
  /-- Every horizontal path is isomorphic to a path of length one. -/
  horizontal : D.HorizontallyRepresentable
  /-- Every vertical path is isomorphic to a path of length one. -/
  vertical : D.transpose.HorizontallyRepresentable

/-- A representation of an implicit double category, given by binary and nullary choices,
supplies representations of all paths, so the implicit double category is representable. -/
theorem representable_of_representation (R : D.Representation) : D.Representable :=
  ⟨R.horizontal.horizontallyRepresentable, R.vertical.horizontallyRepresentable⟩

/-- If some object has no horizontal generator to itself, for instance when there are no
horizontal generators at all, then the implicit double category is not representable: the empty
path at that object exists, but there is no path of length one to compare it with. -/
theorem not_representable_of_isEmpty (a : O) [IsEmpty (@Quiver.Hom O H a a)] :
    ¬ D.Representable :=
  fun hD ↦ D.not_horizontallyRepresentable_of_isEmpty a hD.horizontal

/-- If some object has no horizontal generator to itself, the implicit double category has no
representation. -/
theorem isEmpty_representation (a : O) [IsEmpty (@Quiver.Hom O H a a)] :
    IsEmpty D.Representation :=
  ⟨fun R ↦ (D.isEmpty_horizontalRepresentation a).false R.horizontal⟩

end ImplicitDoubleCategory

end TauCeti
