/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Globular
public import TauCeti.CategoryTheory.PathCategory.Basic

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
(`Quiver.Path.cons_ne_nil`), and the representation supplies a chosen globular isomorphism
between them.

From the binary and nullary choices, every path `p` is compared with a single generator
`HorizontalRepresentation.rep p`, the left-associated chosen composite of its arrows, by the
invertible globular cell `HorizontalRepresentation.repIso p`. Hence a represented implicit
double category is representable: every path is isomorphic to a path of length one. Conversely,
representability gives a representation by choice. If there is a path from `a` to `b` but no
generator from `a` to `b`, for instance the empty path at an object without a generating loop,
that path is not isomorphic to any path of length one, so no representation exists.

The horizontal part of this theory only uses that the horizontal edges are paths, so it is
stated for every strict double category whose horizontal edge category is a path category. The
vertical direction is handled through the transpose: a representation of the vertical paths of
`D` is a horizontal representation of `D.transpose`.

## Main declarations

* `TauCeti.StrictDoubleCategory.HorizontalRepresentation`: chosen binary and nullary
  composites of horizontal generators with their comparison cells, for any strict double
  category whose horizontal edges are paths.
* `TauCeti.StrictDoubleCategory.HorizontalRepresentation.repIso`: the comparison of an
  arbitrary horizontal path with its chosen composite.
* `TauCeti.StrictDoubleCategory.HorizontalRepresentation.rep_cons_comp` and
  `TauCeti.StrictDoubleCategory.HorizontalRepresentation.repIso_cons_comp`: the concatenation
  formulas, folding a suffix with `foldRep` and `foldIso`.
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

/-- Fold a horizontal path `q = [f₁, …, fₙ]` into a generator, starting from the generator `x`:
the left-associated chosen composite `(⋯((x ⋆ f₁) ⋆ f₂) ⋯) ⋆ fₙ`. Its body is exposed because
the type of `foldIso` computes with it. -/
@[expose]
def foldRep {a b : O} (x : @Quiver.Hom O H a b) :
    {c : O} → Edge (pathCategory O H) b c → @Quiver.Hom O H a c
  | _, .nil => x
  | _, .cons q f => R.mul (foldRep x q) f

@[simp]
theorem foldRep_nil {a b : O} (x : @Quiver.Hom O H a b) :
    R.foldRep x (@Quiver.Path.nil O H b) = x :=
  rfl

@[simp]
theorem foldRep_cons {a b c d : O} (x : @Quiver.Hom O H a b) (q : Edge (pathCategory O H) b c)
    (f : @Quiver.Hom O H c d) :
    R.foldRep x (@Quiver.Path.cons O H b c d q f) = R.mul (R.foldRep x q) f :=
  rfl

/-- Fold a comparison `e : p ≅ [x]` along a horizontal path `q = [f₁, …, fₙ]`: the comparison of
`p ++ q` with `[R.foldRep x q]` that whiskers `e` by `q` and then applies the binary comparison
once for each arrow of `q`. -/
def foldIso {a b : O} {p : Edge (pathCategory O H) a b} {x : @Quiver.Hom O H a b}
    (e : D.HorizontalIso p (@Quiver.Hom.toPath O H a b x)) :
    {c : O} → (q : Edge (pathCategory O H) b c) →
      D.HorizontalIso (edgeComp (pathCategory O H) p q)
        (@Quiver.Hom.toPath O H a c (R.foldRep x q))
  | _, .nil => e
  | _, .cons q f =>
    (D.hWhiskerRight (@Quiver.Hom.toPath O H _ _ f)).mapIso (foldIso e q) ≪≫
      R.mulIso (R.foldRep x q) f

@[simp]
theorem foldIso_nil {a b : O} {p : Edge (pathCategory O H) a b} {x : @Quiver.Hom O H a b}
    (e : D.HorizontalIso p (@Quiver.Hom.toPath O H a b x)) :
    R.foldIso e (@Quiver.Path.nil O H b) = e :=
  (rfl)

@[simp]
theorem foldIso_cons {a b c d : O} {p : Edge (pathCategory O H) a b} {x : @Quiver.Hom O H a b}
    (e : D.HorizontalIso p (@Quiver.Hom.toPath O H a b x)) (q : Edge (pathCategory O H) b c)
    (f : @Quiver.Hom O H c d) :
    R.foldIso e (@Quiver.Path.cons O H b c d q f) =
      (D.hWhiskerRight (@Quiver.Hom.toPath O H c d f)).mapIso (R.foldIso e q) ≪≫
        R.mulIso (R.foldRep x q) f :=
  (rfl)

/-- The generator representing a horizontal path: the chosen identity generator for the empty
path, `f` for the path `[f]`, and the left-associated chosen composite
`(⋯((f₁ ⋆ f₂) ⋆ f₃) ⋯) ⋆ fₙ` for a path `[f₁, …, fₙ]` with `n ≥ 2`, obtained by folding the
last arrow into the generator representing the rest with `foldRep`. Its body is exposed because
the type of `repIso` computes with it. -/
@[expose]
def rep {a : O} : {b : O} → Edge (pathCategory O H) a b → @Quiver.Hom O H a b
  | _, @Quiver.Path.nil _ .(H) _ => R.unit a
  | _, @Quiver.Path.cons _ .(H) _ _ _ (@Quiver.Path.nil _ .(H) _) f => f
  | _, @Quiver.Path.cons _ .(H) _ _ _ (@Quiver.Path.cons _ .(H) _ _ _ p g) f =>
    R.foldRep (rep (@Quiver.Path.cons _ H _ _ _ p g)) (@Quiver.Hom.toPath O H _ _ f)

/-- The comparison of a horizontal path with its chosen composite: the nullary comparison for
the empty path, the identity for a path of length one, and for a longer path `p ++ [f]` the
fold `foldIso` of the comparison for `p` along `[f]`: the comparison for `p`, whiskered by `[f]`,
followed by the binary comparison `[rep p, f] ≅ [rep p ⋆ f]`. -/
def repIso {a : O} : {b : O} → (p : Edge (pathCategory O H) a b) →
    D.HorizontalIso p (@Quiver.Hom.toPath O H a b (R.rep p))
  | _, @Quiver.Path.nil _ .(H) _ => R.unitIso a
  | _, @Quiver.Path.cons _ .(H) _ _ _ (@Quiver.Path.nil _ .(H) _) _ => Iso.refl _
  | _, @Quiver.Path.cons _ .(H) _ _ _ (@Quiver.Path.cons _ .(H) _ _ _ p g) f =>
    R.foldIso (repIso (@Quiver.Path.cons _ H _ _ _ p g)) (@Quiver.Hom.toPath O H _ _ f)

/-- The generator representing the empty path is the chosen identity generator. -/
@[simp]
theorem rep_nil (a : O) : R.rep (@Quiver.Path.nil O H a) = R.unit a :=
  rfl

/-- The generator representing the path `[f]`, written with constructors, is `f`. -/
@[simp]
theorem rep_cons_nil {a b : O} (f : @Quiver.Hom O H a b) :
    R.rep (@Quiver.Path.cons O H a a b (@Quiver.Path.nil O H a) f) = f :=
  rfl

/-- Appending a generator `f` to a nonempty path `p ++ [g]` composes its representing generator
with `f`. -/
@[simp]
theorem rep_cons_cons {a b c d : O} (p : Edge (pathCategory O H) a b)
    (g : @Quiver.Hom O H b c) (f : @Quiver.Hom O H c d) :
    R.rep (@Quiver.Path.cons O H a c d (@Quiver.Path.cons O H a b c p g) f) =
      R.mul (R.rep (@Quiver.Path.cons O H a b c p g)) f :=
  R.foldRep_cons _ (@Quiver.Path.nil O H c) f

/-- The recursive comparison of the empty path is the chosen nullary comparison. -/
@[simp]
theorem repIso_nil (a : O) : R.repIso (@Quiver.Path.nil O H a) = R.unitIso a :=
  (rfl)

/-- The recursive comparison of the path `[f]`, written with constructors, is its identity. -/
@[simp]
theorem repIso_cons_nil {a b : O} (f : @Quiver.Hom O H a b) :
    R.repIso (@Quiver.Path.cons O H a a b (@Quiver.Path.nil O H a) f) = Iso.refl _ :=
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
  R.foldIso_cons _ (@Quiver.Path.nil O H c) f

/-- Concatenation formula: the generator representing a nonempty path `p ++ [g]` followed by a
path `q` folds `q` starting from the generator representing `p ++ [g]`. (For the empty prefix,
`Quiver.Path.nil_comp` reduces `[] ++ q` to `q`.) -/
@[simp]
theorem rep_cons_comp {a b c d : O} (p : Edge (pathCategory O H) a b) (g : @Quiver.Hom O H b c)
    (q : Edge (pathCategory O H) c d) :
    R.rep ((@Quiver.Path.cons O H a b c p g).comp q) =
      R.foldRep (R.rep (@Quiver.Path.cons O H a b c p g)) q := by
  induction q with
  | nil => rw [Quiver.Path.comp_nil, foldRep_nil]
  | cons q f ih =>
    rw [Quiver.Path.comp_cons, foldRep_cons, ← ih]
    cases q with
    | nil => rw [Quiver.Path.comp_nil, rep_cons_cons]
    | cons q f' => rw [Quiver.Path.comp_cons, rep_cons_cons]

/-- Whiskering a transported comparison by `[f]` and applying the binary comparison transports
the binary comparison of the original generator. -/
private theorem mapIso_trans_eqToIso_trans_mulIso {a c d : O} {P : Edge (pathCategory O H) a c}
    {y z : @Quiver.Hom O H a c} (h : z = y)
    (B : D.HorizontalIso P (@Quiver.Hom.toPath O H a c z)) (f : @Quiver.Hom O H c d) :
    (D.hWhiskerRight (@Quiver.Hom.toPath O H c d f)).mapIso (B ≪≫ eqToIso
        (congrArg (fun x ↦ (⟨@Quiver.Hom.toPath O H a c x⟩ : D.HorizontalGlobular a c)) h)) ≪≫
      R.mulIso y f =
    ((D.hWhiskerRight (@Quiver.Hom.toPath O H c d f)).mapIso B ≪≫ R.mulIso z f) ≪≫ eqToIso
      (congrArg (fun x ↦ (⟨@Quiver.Hom.toPath O H a d (R.mul x f)⟩ : D.HorizontalGlobular a d))
        h) := by
  subst h
  simp

/-- Concatenation formula: the comparison of a nonempty path `p ++ [g]` followed by a path `q`
folds `q` starting from the comparison of `p ++ [g]`, followed by the transport along
`rep_cons_comp`. (For the empty prefix, `Quiver.Path.nil_comp` reduces `[] ++ q` to `q`.) -/
theorem repIso_cons_comp {a b c d : O} (p : Edge (pathCategory O H) a b)
    (g : @Quiver.Hom O H b c) (q : Edge (pathCategory O H) c d) :
    R.repIso ((@Quiver.Path.cons O H a b c p g).comp q) =
      R.foldIso (R.repIso (@Quiver.Path.cons O H a b c p g)) q ≪≫
        eqToIso (congrArg (fun x ↦ (⟨@Quiver.Hom.toPath O H a d x⟩ : D.HorizontalGlobular a d))
          (R.rep_cons_comp p g q).symm) := by
  induction q with
  | nil =>
    rw [foldIso_nil]
    exact (Iso.trans_refl _).symm
  | cons q f ih =>
    rw [foldIso_cons]
    have step := mapIso_trans_eqToIso_trans_mulIso R (R.rep_cons_comp p g q).symm
      (R.foldIso (R.repIso (@Quiver.Path.cons O H a b c p g)) q) f
    rw [← ih] at step
    cases q with
    | nil => exact (R.repIso_cons_cons p g f).trans step
    | cons q f' => exact (R.repIso_cons_cons ((p.cons g).comp q) f' f).trans step

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

/-- If there is a horizontal path `p` from `a` to `b` but no horizontal generator from `a` to `b`,
then `p` is isomorphic to no path of length one, so the horizontal paths of `D` are not
representable. Taking `p` to be the empty path, this applies to an object without a horizontal
generating loop. -/
theorem not_horizontallyRepresentable_of_isEmpty_hom {a b : O} (p : Edge (pathCategory O H) a b)
    [IsEmpty (@Quiver.Hom O H a b)] : ¬ D.HorizontallyRepresentable :=
  fun hD ↦ isEmptyElim (hD.exists_iso p).choose

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

/-- If there is a horizontal path from `a` to `b` but no horizontal generator from `a` to `b`,
then `D` is not representable. -/
theorem not_representable_of_isEmpty_horizontal_hom {a b : O} (p : Edge (pathCategory O H) a b)
    [IsEmpty (@Quiver.Hom O H a b)] : ¬ D.Representable :=
  fun hD ↦ D.not_horizontallyRepresentable_of_isEmpty_hom p hD.horizontallyRepresentable

/-- If there is a vertical path from `a` to `b` but no vertical generator from `a` to `b`, then
`D` is not representable. -/
theorem not_representable_of_isEmpty_vertical_hom {a b : O} (p : Edge (pathCategory O V) a b)
    [IsEmpty (@Quiver.Hom O V a b)] : ¬ D.Representable :=
  fun hD ↦ D.transpose.not_horizontallyRepresentable_of_isEmpty_hom p hD.verticallyRepresentable

/-- If there is a horizontal path from `a` to `b` but no horizontal generator from `a` to `b`,
then `D` has no representation. -/
theorem isEmpty_representation_of_isEmpty_horizontal_hom {a b : O}
    (p : Edge (pathCategory O H) a b) [IsEmpty (@Quiver.Hom O H a b)] :
    IsEmpty D.Representation :=
  ⟨fun R ↦ D.not_representable_of_isEmpty_horizontal_hom p (D.representable_of_representation R)⟩

/-- If there is a vertical path from `a` to `b` but no vertical generator from `a` to `b`, then
`D` has no representation. -/
theorem isEmpty_representation_of_isEmpty_vertical_hom {a b : O}
    (p : Edge (pathCategory O V) a b) [IsEmpty (@Quiver.Hom O V a b)] :
    IsEmpty D.Representation :=
  ⟨fun R ↦ D.not_representable_of_isEmpty_vertical_hom p (D.representable_of_representation R)⟩

end ImplicitDoubleCategory

end TauCeti
