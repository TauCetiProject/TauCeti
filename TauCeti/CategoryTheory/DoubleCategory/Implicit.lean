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

An implicit double category, in the sense of Fairbanks and Shulman, is a strict double category
whose horizontal and vertical edge categories are the free path categories on two generating
quivers `H` and `V` on the same objects. Its edges are paths of generating arrows, and they
concatenate strictly, so the cells form a strict double category even when the generating
arrows are only meant to compose weakly.

Weak composition of generators is expressed by a representation: chosen composites `f ⋆ g` and
identity generators `1ₐ`, with invertible globular cells `[f, g] ≅ [f ⋆ g]` and `[] ≅ [1ₐ]`
comparing a path of length two or zero with a path `[·]` of length one. These comparisons are
part of the data. In particular the empty path `[]` and the path `[1ₐ]` remain distinct
(`Quiver.Path.cons_ne_nil`), and only the chosen comparison cell relates them.

From the binary and nullary choices, every path `p` is compared with a single generator
`HorizontalRepresentation.rep p`, the left-associated chosen composite of its arrows, by the
invertible globular cell `HorizontalRepresentation.repIso p`. Hence a represented implicit
double category is representable: every path is isomorphic to a path of length one. Conversely,
representability gives a representation by choice. If some object has no generating loop, its
empty path is not isomorphic to any path of length one, so no representation exists.

The horizontal part of this theory only uses that the horizontal edges are paths, so it is
stated for every strict double category whose horizontal edge category is a path category. The
vertical direction is handled through the transpose: a representation of the vertical paths of
`D` is a horizontal representation of `D.transpose`.

## Main declarations

* `TauCeti.StrictDoubleCategory.pathCategory`: the free category on an explicit quiver.
* `TauCeti.StrictDoubleCategory.HorizontalRepresentation`: chosen binary and nullary
  composites of horizontal generators with their comparison cells, for any strict double
  category whose horizontal edges are paths.
* `TauCeti.StrictDoubleCategory.HorizontalRepresentation.repIso`: the comparison of an
  arbitrary horizontal path with its chosen composite.
* `TauCeti.ImplicitDoubleCategory`: strict double categories on two free path categories.
* `TauCeti.ImplicitDoubleCategory.Representation`: representations in both directions.
* `TauCeti.ImplicitDoubleCategory.Representable`: every horizontal and every vertical path is
  isomorphic to a path of length one.
* `TauCeti.ImplicitDoubleCategory.representable_of_representation` and
  `TauCeti.ImplicitDoubleCategory.representable_iff_nonempty_representation`.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651. Definitions 3.1–3.3 and Remark 3.5.
-/

public section

universe s u h v

namespace TauCeti

open CategoryTheory

namespace StrictDoubleCategory

/-- The free category on an explicitly supplied quiver `Q` on `O`: its morphisms are the paths
of `Q`, composed by concatenation. It is Mathlib's path category `Paths.categoryPaths`, read as a
category structure on `O` itself, and it is not installed as an instance. -/
abbrev pathCategory (O : Type u) (Q : Quiver.{h} O) : Category.{max u h} O :=
  @Paths.categoryPaths O Q

/-- The identity edge of the path category is the empty path. -/
theorem edgeId_pathCategory {O : Type u} (Q : Quiver.{h} O) (a : O) :
    edgeId (pathCategory O Q) a = @Quiver.Path.nil O Q a :=
  rfl

/-- Composing an edge of the path category with the path `[f]` of length one appends `f`. -/
theorem edgeComp_pathCategory_toPath {O : Type u} (Q : Quiver.{h} O) {a b c : O}
    (p : Edge (pathCategory O Q) a b) (f : @Quiver.Hom O Q b c) :
    edgeComp (pathCategory O Q) p (@Quiver.Hom.toPath O Q b c f) =
      @Quiver.Path.cons O Q a b c p f :=
  rfl

variable {O : Type u} {H : Quiver.{h} O} {V : Category.{v} O}
  (D : StrictDoubleCategory.{s} O (pathCategory O H) V)

/-- Every horizontal path of `D` is isomorphic, by an invertible horizontal globular cell, to a
path of length one. -/
def HorizontallyRepresentable : Prop :=
  ∀ {a b : O} (p : Edge (pathCategory O H) a b),
    ∃ f : @Quiver.Hom O H a b, Nonempty (D.HorizontalIso p (@Quiver.Hom.toPath O H a b f))

/-- Unfolding horizontal representability: every horizontal path is isomorphic to a path of
length one. -/
theorem horizontallyRepresentable_iff :
    D.HorizontallyRepresentable ↔ ∀ {a b : O} (p : Edge (pathCategory O H) a b),
      ∃ f : @Quiver.Hom O H a b, Nonempty (D.HorizontalIso p (@Quiver.Hom.toPath O H a b f)) :=
  Iff.rfl

variable {D} in
/-- In horizontally representable `D`, a horizontal path is isomorphic to a path of length
one. -/
theorem HorizontallyRepresentable.exists_iso (hD : D.HorizontallyRepresentable) {a b : O}
    (p : Edge (pathCategory O H) a b) :
    ∃ f : @Quiver.Hom O H a b, Nonempty (D.HorizontalIso p (@Quiver.Hom.toPath O H a b f)) :=
  hD p

/-- A horizontal representation of a strict double category whose horizontal edges are paths: a
chosen identity generator `1ₐ` on every object and a chosen composite `f ⋆ g` of every
composable pair of horizontal generators, with invertible horizontal globular cells
`[] ≅ [1ₐ]` and `[f, g] ≅ [f ⋆ g]`. -/
structure HorizontalRepresentation where
  /-- The chosen identity generator `1ₐ` on `a`. -/
  unit (a : O) : @Quiver.Hom O H a a
  /-- The chosen composite `f ⋆ g` of composable generators. -/
  mul {a b c : O} : @Quiver.Hom O H a b → @Quiver.Hom O H b c → @Quiver.Hom O H a c
  /-- The nullary comparison `[] ≅ [1ₐ]`. -/
  unitIso (a : O) :
    D.HorizontalIso (edgeId (pathCategory O H) a) (@Quiver.Hom.toPath O H a a (unit a))
  /-- The binary comparison `[f, g] ≅ [f ⋆ g]`. -/
  mulIso {a b c : O} (f : @Quiver.Hom O H a b) (g : @Quiver.Hom O H b c) :
    D.HorizontalIso
      (edgeComp (pathCategory O H) (@Quiver.Hom.toPath O H a b f) (@Quiver.Hom.toPath O H b c g))
      (@Quiver.Hom.toPath O H a c (mul f g))

namespace HorizontalRepresentation

variable {D} (R : D.HorizontalRepresentation)

/-- The generator representing a horizontal path: the chosen identity generator for the empty
path, `f` for the path `[f]`, and the left-associated chosen composite
`(⋯((f₁ ⋆ f₂) ⋆ f₃) ⋯) ⋆ fₙ` for a path `[f₁, …, fₙ]` with `n ≥ 2`. Its body is exposed
because the type of `repIso` computes with it. -/
@[expose]
def rep {a : O} : {b : O} → Edge (pathCategory O H) a b → @Quiver.Hom O H a b
  | _, @Quiver.Path.nil _ .(H) _ => R.unit a
  | _, @Quiver.Path.cons _ .(H) _ _ _ (@Quiver.Path.nil _ .(H) _) f => f
  | _, @Quiver.Path.cons _ .(H) _ _ _ (@Quiver.Path.cons _ .(H) _ _ _ p g) f =>
    R.mul (rep (@Quiver.Path.cons _ H _ _ _ p g)) f

/-- The comparison of a horizontal path with its chosen composite: the nullary comparison for
the empty path, the identity for a path of length one, and for a longer path `p ++ [f]` the
comparison for `p`, whiskered by `[f]`, followed by the binary comparison
`[rep p, f] ≅ [rep p ⋆ f]`. -/
def repIso {a : O} : {b : O} → (p : Edge (pathCategory O H) a b) →
    D.HorizontalIso p (@Quiver.Hom.toPath O H a b (R.rep p))
  | _, @Quiver.Path.nil _ .(H) _ => R.unitIso a
  | _, @Quiver.Path.cons _ .(H) _ _ _ (@Quiver.Path.nil _ .(H) _) _ => Iso.refl _
  | _, @Quiver.Path.cons _ .(H) _ _ _ (@Quiver.Path.cons _ .(H) _ _ _ p g) f =>
    (D.hWhiskerRight (@Quiver.Hom.toPath O H _ _ f)).mapIso
        (repIso (@Quiver.Path.cons _ H _ _ _ p g)) ≪≫
      R.mulIso (R.rep (@Quiver.Path.cons _ H _ _ _ p g)) f

@[simp]
theorem rep_nil (a : O) : R.rep (edgeId (pathCategory O H) a) = R.unit a :=
  rfl

@[simp]
theorem rep_singleton {a b : O} (f : @Quiver.Hom O H a b) :
    R.rep (@Quiver.Hom.toPath O H a b f) = f :=
  rfl

/-- Appending a generator `f` to a nonempty path `p ++ [g]` composes its representing generator
with `f`. -/
@[simp]
theorem rep_cons_cons {a b c d : O} (p : Edge (pathCategory O H) a b)
    (g : @Quiver.Hom O H b c) (f : @Quiver.Hom O H c d) :
    R.rep (@Quiver.Path.cons O H a c d (@Quiver.Path.cons O H a b c p g) f) =
      R.mul (R.rep (@Quiver.Path.cons O H a b c p g)) f :=
  rfl

@[simp]
theorem rep_pair {a b c : O} (f : @Quiver.Hom O H a b) (g : @Quiver.Hom O H b c) :
    R.rep (edgeComp (pathCategory O H) (@Quiver.Hom.toPath O H a b f)
      (@Quiver.Hom.toPath O H b c g)) = R.mul f g :=
  rfl

/-- The recursive comparison of the empty path is the chosen nullary comparison. -/
@[simp]
theorem repIso_nil (a : O) : R.repIso (edgeId (pathCategory O H) a) = R.unitIso a :=
  (rfl)

/-- The recursive comparison of a path of length one is its identity. -/
@[simp]
theorem repIso_singleton {a b : O} (f : @Quiver.Hom O H a b) :
    R.repIso (@Quiver.Hom.toPath O H a b f) = Iso.refl _ :=
  (rfl)

/-- The recursive comparison of a nonempty path `p ++ [g]` followed by a generator `f` is the
comparison of `p ++ [g]`, whiskered by `[f]`, followed by the binary comparison. -/
@[simp]
theorem repIso_cons_cons {a b c d : O} (p : Edge (pathCategory O H) a b)
    (g : @Quiver.Hom O H b c) (f : @Quiver.Hom O H c d) :
    R.repIso (@Quiver.Path.cons O H a c d (@Quiver.Path.cons O H a b c p g) f) =
      (D.hWhiskerRight (@Quiver.Hom.toPath O H c d f)).mapIso
          (R.repIso (@Quiver.Path.cons O H a b c p g)) ≪≫
        R.mulIso (R.rep (@Quiver.Path.cons O H a b c p g)) f :=
  (rfl)

/-- The recursive comparison of a path `[f, g]` of length two is the chosen binary
comparison. -/
@[simp]
theorem repIso_pair {a b c : O} (f : @Quiver.Hom O H a b) (g : @Quiver.Hom O H b c) :
    R.repIso (edgeComp (pathCategory O H) (@Quiver.Hom.toPath O H a b f)
      (@Quiver.Hom.toPath O H b c g)) = R.mulIso f g :=
  -- By definition, the comparison of `[f, g]` is the identity of `[f]` whiskered by `[g]`,
  -- followed by the binary comparison.
  (congrArg (· ≪≫ R.mulIso f g)
    ((D.hWhiskerRight (@Quiver.Hom.toPath O H b c g)).mapIso_refl _)).trans (Iso.refl_trans _)

end HorizontalRepresentation

/-- A horizontal representation makes every horizontal path isomorphic to a path of length
one. -/
theorem HorizontalRepresentation.horizontallyRepresentable
    {D : StrictDoubleCategory.{s} O (pathCategory O H) V} (R : D.HorizontalRepresentation) :
    D.HorizontallyRepresentable :=
  fun p ↦ ⟨R.rep p, ⟨R.repIso p⟩⟩

variable {D} in
/-- A horizontal representation chosen from horizontal representability: the identity generator
represents the empty path and the composite of `f` and `g` represents the path `[f, g]`. -/
noncomputable def HorizontallyRepresentable.representation (hD : D.HorizontallyRepresentable) :
    D.HorizontalRepresentation where
  unit a := (hD.exists_iso (edgeId (pathCategory O H) a)).choose
  mul f g := (hD.exists_iso (edgeComp (pathCategory O H) (@Quiver.Hom.toPath O H _ _ f)
    (@Quiver.Hom.toPath O H _ _ g))).choose
  unitIso a := (hD.exists_iso (edgeId (pathCategory O H) a)).choose_spec.some
  mulIso f g := (hD.exists_iso (edgeComp (pathCategory O H) (@Quiver.Hom.toPath O H _ _ f)
    (@Quiver.Hom.toPath O H _ _ g))).choose_spec.some

/-- The horizontal paths of `D` are representable if and only if `D` admits a horizontal
representation. -/
theorem horizontallyRepresentable_iff_nonempty_horizontalRepresentation :
    D.HorizontallyRepresentable ↔ Nonempty D.HorizontalRepresentation :=
  ⟨fun hD ↦ ⟨hD.representation⟩, fun ⟨R⟩ ↦ R.horizontallyRepresentable⟩

/-- If an object `a` has no horizontal generating loop, the empty path at `a` is isomorphic to
no path of length one, so the horizontal paths of `D` are not representable. -/
theorem not_horizontallyRepresentable_of_isEmpty (a : O) [IsEmpty (@Quiver.Hom O H a a)] :
    ¬ D.HorizontallyRepresentable :=
  fun hD ↦ isEmptyElim (hD.exists_iso (edgeId (pathCategory O H) a)).choose

end StrictDoubleCategory

open StrictDoubleCategory

/-- An implicit double category on objects `O` with horizontal generating quiver `H` and
vertical generating quiver `V`: a strict double category whose horizontal and vertical edges are
the paths of `H` and of `V`. -/
abbrev ImplicitDoubleCategory (O : Type u) (H : Quiver.{h} O) (V : Quiver.{v} O) :=
  StrictDoubleCategory.{s} O (pathCategory O H) (pathCategory O V)

namespace ImplicitDoubleCategory

variable {O : Type u} {H : Quiver.{h} O} {V : Quiver.{v} O}
  (D : ImplicitDoubleCategory.{s} O H V)

/-- An implicit double category is representable when every horizontal path and every vertical
path is isomorphic, by an invertible globular cell, to a path of length one. The vertical
condition is the horizontal condition for the transpose. -/
def Representable : Prop :=
  D.HorizontallyRepresentable ∧ D.transpose.HorizontallyRepresentable

/-- An implicit double category is representable if and only if its horizontal paths and its
vertical paths, the horizontal paths of its transpose, are representable. -/
theorem representable_iff :
    D.Representable ↔ D.HorizontallyRepresentable ∧ D.transpose.HorizontallyRepresentable :=
  Iff.rfl

variable {D} in
/-- The horizontal paths of a representable implicit double category are representable. -/
theorem Representable.horizontallyRepresentable (hD : D.Representable) :
    D.HorizontallyRepresentable :=
  hD.1

variable {D} in
/-- The vertical paths of a representable implicit double category are representable. -/
theorem Representable.verticallyRepresentable (hD : D.Representable) :
    D.transpose.HorizontallyRepresentable :=
  hD.2

/-- A representation of an implicit double category: horizontal and vertical chosen binary and
nullary composites with their comparison cells. The vertical part is a horizontal
representation of the transpose. -/
structure Representation where
  /-- The representation of horizontal paths. -/
  horizontal : D.HorizontalRepresentation
  /-- The representation of vertical paths, as horizontal paths of the transpose. -/
  vertical : D.transpose.HorizontalRepresentation

/-- A representation, given by chosen binary and nullary composites, makes an implicit double
category representable. -/
theorem representable_of_representation (R : D.Representation) : D.Representable :=
  ⟨R.horizontal.horizontallyRepresentable, R.vertical.horizontallyRepresentable⟩

/-- An implicit double category is representable if and only if it admits a representation. -/
theorem representable_iff_nonempty_representation :
    D.Representable ↔ Nonempty D.Representation :=
  ⟨fun hD ↦ ⟨⟨HorizontallyRepresentable.representation hD.horizontallyRepresentable,
      HorizontallyRepresentable.representation hD.verticallyRepresentable⟩⟩,
    fun ⟨R⟩ ↦ D.representable_of_representation R⟩

/-- If an object `a` has no horizontal generating loop, then `D` is not representable. -/
theorem not_representable_of_isEmpty (a : O) [IsEmpty (@Quiver.Hom O H a a)] :
    ¬ D.Representable :=
  fun hD ↦ D.not_horizontallyRepresentable_of_isEmpty a hD.horizontallyRepresentable

/-- If an object `a` has no horizontal generating loop, then `D` has no representation: there
is no identity generator to represent the empty path at `a`. -/
theorem isEmpty_representation_of_isEmpty (a : O) [IsEmpty (@Quiver.Hom O H a a)] :
    IsEmpty D.Representation :=
  ⟨fun R ↦ isEmptyElim (R.horizontal.unit a)⟩

end ImplicitDoubleCategory

end TauCeti
