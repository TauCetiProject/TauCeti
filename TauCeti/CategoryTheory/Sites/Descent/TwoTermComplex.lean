/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.TwoTermComplex

/-!
# The prestack of quotient groupoids of a presheaf of two-term complexes

A presheaf of two-term complexes of abelian groups on a category `C` is a functor
`K : Cᵒᵖ ⥤ Arrow AddCommGrpCat`: over `U` it is a homomorphism `d_U : E⁰(U) ⟶ E¹(U)`, and the
restriction maps form commutative squares. Taking the quotient groupoid `[E¹(U)/E⁰(U)]` of each
`d_U` (`AddMonoidHom.QuotientGroupoid`) gives a pseudofunctor `Pseudofunctor.quotientGroupoid K`
on `C`. Its fibre over `U` has the elements of `E¹(U)` as objects, and an arrow `x ⟶ y` is an
element `a` of `E⁰(U)` with `d_U a + x = y`, its label; pulling back along `V ⟶ U` restricts
elements and labels.

This is the prestack which Deligne's construction `h¹/h⁰` stackifies: for a two-term complex of
abelian sheaves, the associated stack of `Pseudofunctor.quotientGroupoid K` is the strictly
commutative Picard stack `h¹/h⁰(E) = [E¹/E⁰]`. The stackification of a prestack is
`TauCeti.Stack.stackification`, in
`TauCeti.CategoryTheory.Sites.Descent.Stackification.Pseudofunctor`; this file supplies the
prestack itself.

* Morphisms of the prestack glue: `Pseudofunctor.isPrestack_quotientGroupoid` proves that it is a
  prestack for a Grothendieck topology `J` as soon as `E⁰` is a sheaf and `E¹` is separated. The
  presheaf of arrows `x ⟶ y` over `U` is the presheaf of labels `a` with `d a + x = y`, a
  subpresheaf of `E⁰` cut out by an equation in `E¹`.
* A morphism `φ : K ⟶ K'` of presheaves of two-term complexes induces a strong transformation
  `Pseudofunctor.quotientGroupoidMap φ`, which is an equivalence on the fibre over `U` exactly when
  `φ` is a quasi-isomorphism over `U` (`Pseudofunctor.isEquivalence_quotientGroupoidMap_app_iff`).
* A chain homotopy between two such morphisms induces an invertible modification between the
  induced strong transformations (`Pseudofunctor.quotientGroupoidMapIsoOfHomotopy`).

The fibres are the quotient groupoids of `AddMonoidHom.QuotientGroupoid`, but only up to
unfolding the pseudofunctor, so the lemmas about quotient groupoids do not apply to them by
rewriting. The API in the namespace `Pseudofunctor.quotientGroupoid` (`objEquiv`, `label`,
`homMk`, `isoMk`) therefore restates the description of objects and arrows with the fibre types of
the pseudofunctor, and computes pullbacks, the comparison isomorphisms of the pseudofunctor and
Mathlib's `LocallyDiscreteOpToCat.pullHom` on labels.

## Main declarations

* `CategoryTheory.Pseudofunctor.quotientGroupoid`: the pseudofunctor of quotient groupoids of a
  presheaf of two-term complexes of abelian groups.
* `CategoryTheory.Pseudofunctor.quotientGroupoid.objEquiv`,
  `CategoryTheory.Pseudofunctor.quotientGroupoid.label`,
  `CategoryTheory.Pseudofunctor.quotientGroupoid.homMk`: objects are elements of `E¹`, arrows are
  labelled by elements of `E⁰`.
* `CategoryTheory.Pseudofunctor.quotientGroupoid.objEquiv_symm_map_obj`,
  `CategoryTheory.Pseudofunctor.quotientGroupoid.label_pullHom`: pullback restricts elements and
  labels.
* `CategoryTheory.Pseudofunctor.isPrestack_quotientGroupoid`: the prestack condition.
* `CategoryTheory.Pseudofunctor.quotientGroupoidMap`: the strong transformation induced by a
  morphism of presheaves of two-term complexes.
* `CategoryTheory.Pseudofunctor.isEquivalence_quotientGroupoidMap_app_iff`: it is an equivalence
  over `U` exactly when it is a quasi-isomorphism over `U`.
* `CategoryTheory.Pseudofunctor.quotientGroupoidMapIsoOfHomotopy`: the invertible modification
  induced by a chain homotopy.

## References

* P. Deligne, *La formule de dualité globale*, SGA 4, Exposé XVIII, §1.4.
* K. Behrend and B. Fantechi, *The intrinsic normal cone*, Invent. Math. 128 (1997), §2.
* [Stacks Project, Definition 026F](https://stacks.math.columbia.edu/tag/026F)
-/

public section

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] (K : Cᵒᵖ ⥤ Arrow AddCommGrpCat.{w})

/-- The pseudofunctor of quotient groupoids of a presheaf `K` of two-term complexes of abelian
groups: its fibre over `U` is the quotient groupoid `[E¹(U)/E⁰(U)]` of the complex `K(U)`, and its
pullback functors are induced by the restriction maps of `K`. It is a prestack for `J` when `E⁰`
is a sheaf and `E¹` is separated (`Pseudofunctor.isPrestack_quotientGroupoid`); its associated
stack is then Deligne's Picard stack `h¹/h⁰`. -/
-- The body is exposed: the fibre API below (`objEquiv`, `label`, `homMk`, `isoMk`) is defined by
-- unfolding the fibres to `AddMonoidHom.QuotientGroupoid`, and without exposure the compiler
-- rejects these definitions because their compilation types would differ in other modules.
@[expose]
def quotientGroupoid : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w} :=
  (K ⋙ AddMonoidHom.QuotientGroupoid.functor ⋙ Grpd.forgetToCat).toPseudofunctor'

namespace quotientGroupoid

variable {K} {X : LocallyDiscrete Cᵒᵖ}

variable (X) in
/-- The objects of the fibre of `quotientGroupoid K` over `X` are the elements of `E¹(X)`. -/
def objEquiv : (K.obj X.as).right ≃ (quotientGroupoid K).obj X :=
  AddMonoidHom.QuotientGroupoid.objEquiv (K.obj X.as).hom.hom

/-- The label of an arrow `x ⟶ y` of the fibre of `quotientGroupoid K` over `X`: the element `a`
of `E⁰(X)` with `d a + x = y` (`quotientGroupoid.apply_label_add`). -/
def label {M N : (quotientGroupoid K).obj X} (φ : M ⟶ N) : (K.obj X.as).left :=
  AddMonoidHom.QuotientGroupoid.label (d := (K.obj X.as).hom.hom) φ

/-- An arrow of a fibre of `quotientGroupoid K` translates its source to its target by the image
of its label. -/
theorem apply_label_add {M N : (quotientGroupoid K).obj X} (φ : M ⟶ N) :
    (K.obj X.as).hom.hom (label φ) + (objEquiv X).symm M = (objEquiv X).symm N :=
  AddMonoidHom.QuotientGroupoid.apply_label_add (d := (K.obj X.as).hom.hom) φ

/-- The arrow `x ⟶ y` of the fibre of `quotientGroupoid K` over `X` labelled by `a`, for `a` with
`d a + x = y`. -/
def homMk {M N : (quotientGroupoid K).obj X} (a : (K.obj X.as).left)
    (h : (K.obj X.as).hom.hom a + (objEquiv X).symm M = (objEquiv X).symm N) : M ⟶ N :=
  AddMonoidHom.QuotientGroupoid.homMk (d := (K.obj X.as).hom.hom) a h

/-- The arrow `homMk a h` is labelled by `a`. -/
@[simp]
theorem label_homMk {M N : (quotientGroupoid K).obj X} (a : (K.obj X.as).left)
    (h : (K.obj X.as).hom.hom a + (objEquiv X).symm M = (objEquiv X).symm N) :
    label (homMk a h) = a :=
  AddMonoidHom.QuotientGroupoid.label_homMk (d := (K.obj X.as).hom.hom) a h

/-- Arrows of the fibres of `quotientGroupoid K` are determined by their labels. -/
@[ext]
theorem hom_ext {M N : (quotientGroupoid K).obj X} {φ ψ : M ⟶ N} (h : label φ = label ψ) :
    φ = ψ :=
  AddMonoidHom.QuotientGroupoid.hom_ext (d := (K.obj X.as).hom.hom) h

/-- An arrow is the arrow `homMk` given by its label. -/
@[simp]
theorem homMk_label {M N : (quotientGroupoid K).obj X} (φ : M ⟶ N) :
    homMk (label φ) (apply_label_add φ) = φ :=
  hom_ext (label_homMk _ _)

/-- Identities are labelled by `0`. -/
@[simp]
theorem label_id (M : (quotientGroupoid K).obj X) : label (𝟙 M) = 0 :=
  AddMonoidHom.QuotientGroupoid.label_id (d := (K.obj X.as).hom.hom) M

/-- Composition adds labels. -/
@[simp]
theorem label_comp {M N P : (quotientGroupoid K).obj X} (φ : M ⟶ N) (ψ : N ⟶ P) :
    label (φ ≫ ψ) = label φ + label ψ :=
  AddMonoidHom.QuotientGroupoid.label_comp (d := (K.obj X.as).hom.hom) φ ψ

/-- The arrows `eqToHom h` are labelled by `0`. -/
@[simp]
theorem label_eqToHom {M N : (quotientGroupoid K).obj X} (h : M = N) : label (eqToHom h) = 0 :=
  AddMonoidHom.QuotientGroupoid.label_eqToHom (d := (K.obj X.as).hom.hom) h

/-- Inverting an arrow negates its label. -/
@[simp]
theorem label_inv {M N : (quotientGroupoid K).obj X} (φ : M ⟶ N) [IsIso φ] :
    label (inv φ) = -label φ :=
  eq_neg_of_add_eq_zero_right (by rw [← label_comp, IsIso.hom_inv_id, label_id])

/-- The isomorphism `x ≅ y` of the fibre of `quotientGroupoid K` over `X` labelled by `a`, for `a`
with `d a + x = y`; its inverse is labelled by `-a`. -/
def isoMk {M N : (quotientGroupoid K).obj X} (a : (K.obj X.as).left)
    (h : (K.obj X.as).hom.hom a + (objEquiv X).symm M = (objEquiv X).symm N) : M ≅ N where
  hom := homMk a h
  inv := homMk (-a) (by rw [← h, map_neg, neg_add_cancel_left])
  hom_inv_id := hom_ext (by simp)
  inv_hom_id := hom_ext (by simp)

/-- The isomorphism `isoMk a h` has underlying arrow `homMk a h`. -/
@[simp]
theorem isoMk_hom {M N : (quotientGroupoid K).obj X} (a : (K.obj X.as).left)
    (h : (K.obj X.as).hom.hom a + (objEquiv X).symm M = (objEquiv X).symm N) :
    (isoMk a h).hom = homMk a h := (rfl)

/-- The inverse of the isomorphism `isoMk a h` is labelled by `-a`. -/
@[simp]
theorem label_isoMk_inv {M N : (quotientGroupoid K).obj X} (a : (K.obj X.as).left)
    (h : (K.obj X.as).hom.hom a + (objEquiv X).symm M = (objEquiv X).symm N) :
    label (isoMk a h).inv = -a :=
  label_homMk _ _

/-- Pulling back an object of `quotientGroupoid K` along `f` restricts the underlying element of
`E¹` along `f`. -/
@[simp]
theorem objEquiv_symm_map_obj {Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y)
    (M : (quotientGroupoid K).obj X) :
    (objEquiv Y).symm (((quotientGroupoid K).map f).toFunctor.obj M) =
      (K.map f.as).right.hom ((objEquiv X).symm M) :=
  AddMonoidHom.QuotientGroupoid.objEquiv_symm_map_obj _ _ _ _

/-- Pulling back the object of `quotientGroupoid K` given by an element of `E¹` restricts that
element along `f`. -/
@[simp]
theorem map_obj_objEquiv {Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (K.obj X.as).right) :
    ((quotientGroupoid K).map f).toFunctor.obj (objEquiv X x) =
      objEquiv Y ((K.map f.as).right.hom x) :=
  (objEquiv Y).symm.injective (by simp)

/-- Pulling back an arrow of `quotientGroupoid K` along `f` restricts its label along `f`. -/
@[simp]
theorem label_map_map {Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y)
    {M N : (quotientGroupoid K).obj X} (φ : M ⟶ N) :
    label (((quotientGroupoid K).map f).toFunctor.map φ) = (K.map f.as).left.hom (label φ) :=
  AddMonoidHom.QuotientGroupoid.label_map_map _ _ _ _

private theorem map_comp_eq {Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (quotientGroupoid K).map (f ≫ g) = (quotientGroupoid K).map f ≫ (quotientGroupoid K).map g := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  exact (K ⋙ AddMonoidHom.QuotientGroupoid.functor ⋙ Grpd.forgetToCat).map_comp f g

private theorem map_id_eq (X : LocallyDiscrete Cᵒᵖ) :
    (quotientGroupoid K).map (𝟙 X) = 𝟙 ((quotientGroupoid K).obj X) :=
  (K ⋙ AddMonoidHom.QuotientGroupoid.functor ⋙ Grpd.forgetToCat).map_id X.as

-- The comparison isomorphisms of `quotientGroupoid K` are those of `Functor.toPseudofunctor'`,
-- which are `eqToIso` for every functor (Mathlib's `Functor.toPseudofunctor'_mapComp` and
-- `Functor.toPseudofunctor'_mapId`).
private theorem mapComp_eq {Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (quotientGroupoid K).mapComp f g = eqToIso (map_comp_eq f g) :=
  Functor.toPseudofunctor'_mapComp _ f g

private theorem mapId_eq (X : LocallyDiscrete Cᵒᵖ) :
    (quotientGroupoid K).mapId X = eqToIso (map_id_eq X) :=
  Functor.toPseudofunctor'_mapId _ X

/-- The unit comparison isomorphisms of `quotientGroupoid K` are labelled by `0`. -/
@[simp]
theorem label_mapId_hom_app (M : (quotientGroupoid K).obj X) :
    label (((quotientGroupoid K).mapId X).hom.toNatTrans.app M) = 0 := by
  rw [mapId_eq, eqToIso.hom, Cat.eqToHom_app, label_eqToHom]

/-- The inverses of the unit comparison isomorphisms of `quotientGroupoid K` are labelled by
`0`. -/
@[simp]
theorem label_mapId_inv_app (M : (quotientGroupoid K).obj X) :
    label (((quotientGroupoid K).mapId X).inv.toNatTrans.app M) = 0 := by
  rw [mapId_eq, eqToIso.inv, Cat.eqToHom_app, label_eqToHom]

/-- The composition comparison isomorphisms of `quotientGroupoid K` are labelled by `0`. -/
@[simp]
theorem label_mapComp_hom_app {Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : (quotientGroupoid K).obj X) :
    label (((quotientGroupoid K).mapComp f g).hom.toNatTrans.app M) = 0 := by
  rw [mapComp_eq, eqToIso.hom, Cat.eqToHom_app, label_eqToHom]

/-- The inverses of the composition comparison isomorphisms of `quotientGroupoid K` are labelled
by `0`. -/
@[simp]
theorem label_mapComp_inv_app {Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : (quotientGroupoid K).obj X) :
    label (((quotientGroupoid K).mapComp f g).inv.toNatTrans.app M) = 0 := by
  rw [mapComp_eq, eqToIso.inv, Cat.eqToHom_app, label_eqToHom]

/-- The comparison isomorphisms `Pseudofunctor.mapComp'` of `quotientGroupoid K` are labelled by
`0`. -/
@[simp]
theorem label_mapComp'_hom_app {Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (h : f ≫ g = fg) (M : (quotientGroupoid K).obj X) :
    label (((quotientGroupoid K).mapComp' f g fg h).hom.toNatTrans.app M) = 0 := by
  subst h
  rw [mapComp'_eq_mapComp, label_mapComp_hom_app]

/-- The inverses of the comparison isomorphisms `Pseudofunctor.mapComp'` of `quotientGroupoid K`
are labelled by `0`. -/
@[simp]
theorem label_mapComp'_inv_app {Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (h : f ≫ g = fg) (M : (quotientGroupoid K).obj X) :
    label (((quotientGroupoid K).mapComp' f g fg h).inv.toNatTrans.app M) = 0 := by
  subst h
  rw [mapComp'_eq_mapComp, label_mapComp_inv_app]

open LocallyDiscreteOpToCat in
/-- Mathlib's pullback `pullHom φ g` of a local arrow `φ` of `quotientGroupoid K` along `g`
restricts its label along `g`. These are the restriction maps of the presheaves of arrows
`Pseudofunctor.presheafHom`. -/
@[simp]
theorem label_pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : (quotientGroupoid K).obj (.mk (op X₁))⦄
    ⦃M₂ : (quotientGroupoid K).obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((quotientGroupoid K).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((quotientGroupoid K).map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    label (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) = (K.map g.op).left.hom (label φ) := by
  simp [pullHom]

end quotientGroupoid

open quotientGroupoid

/-- **The prestack condition.** If `E⁰` is a sheaf and `E¹` is separated for `J`, then arrows of
the quotient groupoids glue: `quotientGroupoid K` is a prestack for `J`. Over `(T ⟶ S)`, the
arrows `x ⟶ y` are the sections `a` of `E⁰` with `d a + x = y`. -/
theorem isPrestack_quotientGroupoid (J : GrothendieckTopology C)
    (h₀ : Presieve.IsSheaf J (K ⋙ Arrow.leftFunc ⋙ forget AddCommGrpCat))
    (h₁ : Presieve.IsSeparated J (K ⋙ Arrow.rightFunc ⋙ forget AddCommGrpCat)) :
    (quotientGroupoid K).IsPrestack J where
  isSheaf {S} M N := by
    -- A compatible family of arrows glues to a section of `E⁰`, which satisfies the equation
    -- `d a + x = y` because `E¹` is separated.
    rw [isSheaf_iff_isSheaf_of_type]
    intro T R hR x hx
    have h₀' := (Over.forget S).op_comp_isSheaf_of_isSheaf_type (J.over S) h₀
    let y : Presieve.FamilyOfElements
        ((Over.forget S).op ⋙ K ⋙ Arrow.leftFunc ⋙ forget AddCommGrpCat) R.arrows :=
      fun Z g hg ↦ label (x g hg)
    have hy : y.Compatible := by
      intro Z₁ Z₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ w
      have := congrArg label (hx g₁ g₂ hf₁ hf₂ w)
      simp only [presheafHom_map, TypeCat.ofHom_apply, label_pullHom] at this
      simpa [y] using this
    obtain ⟨t, ht, huniq⟩ := h₀' R hR y hy
    have hcond : (K.obj (op T.left)).hom.hom t +
        (objEquiv _).symm (((quotientGroupoid K).map T.hom.op.toLoc).toFunctor.obj M) =
        (objEquiv _).symm (((quotientGroupoid K).map T.hom.op.toLoc).toFunctor.obj N) := by
      refine (h₁ _ ((GrothendieckTopology.mem_over_iff _ _).mp hR)).ext fun W h hh ↦ ?_
      rw [Sieve.overEquiv_iff] at hh
      -- `t` restricts along `h` to the label of the member of `x` over `h`, an arrow from the
      -- restriction of `x` to that of `y`.
      have e₁ : (K.map h.op).left.hom t = label (x _ hh) := ht _ hh
      have e₂ := apply_label_add (x _ hh)
      rw [objEquiv_symm_map_obj, objEquiv_symm_map_obj] at e₂ ⊢
      have hw : (K.map h.op).right.hom ((K.obj (op T.left)).hom.hom t) =
          (K.obj (op W)).hom.hom ((K.map h.op).left.hom t) :=
        congr($((K.map h.op).w).hom t).symm
      have hcomp (z : (K.obj (op S)).right) :
          (K.map h.op).right.hom ((K.map T.hom.op).right.hom z) =
            (K.map (h ≫ T.hom).op).right.hom z := by
        simp
      -- The restriction maps of `K ⋙ Arrow.rightFunc ⋙ forget AddCommGrpCat` are those of `E¹`.
      exact (by rw [map_add, hw, e₁, hcomp, hcomp]; exact e₂ :
        (K.map h.op).right.hom ((K.obj (op T.left)).hom.hom t +
          (K.map T.hom.op).right.hom ((objEquiv _).symm M)) =
        (K.map h.op).right.hom ((K.map T.hom.op).right.hom ((objEquiv _).symm N)))
    refine ⟨homMk t hcond, fun Z g hg ↦ hom_ext ?_, fun φ hφ ↦ ?_⟩
    · simpa [y] using ht g hg
    · refine hom_ext ((huniq _ fun Z g hg ↦ ?_).trans (label_homMk _ _).symm)
      simp [y, ← hφ g hg]

section Map

variable {K} {K' : Cᵒᵖ ⥤ Arrow AddCommGrpCat.{w}}

/-- The functor between the fibres over `X` induced by `φ : K ⟶ K'`. -/
private abbrev mapApp (φ : K ⟶ K') (X : LocallyDiscrete Cᵒᵖ) :
    (quotientGroupoid K).obj X ⥤ (quotientGroupoid K').obj X :=
  AddMonoidHom.QuotientGroupoid.map (φ.app X.as).left.hom (φ.app X.as).right.hom
    (congrArg AddCommGrpCat.Hom.hom (φ.app X.as).w).symm

private theorem objEquiv_symm_mapApp_obj (φ : K ⟶ K') (X : LocallyDiscrete Cᵒᵖ)
    (M : (quotientGroupoid K).obj X) :
    (objEquiv X).symm ((mapApp φ X).obj M) = (φ.app X.as).right.hom ((objEquiv X).symm M) :=
  AddMonoidHom.QuotientGroupoid.objEquiv_symm_map_obj _ _ _ _

private theorem label_mapApp_map (φ : K ⟶ K') (X : LocallyDiscrete Cᵒᵖ)
    {M N : (quotientGroupoid K).obj X} (g : M ⟶ N) :
    label ((mapApp φ X).map g) = (φ.app X.as).left.hom (label g) :=
  AddMonoidHom.QuotientGroupoid.label_map_map _ _ _ _

/-- The strong transformation `quotientGroupoid K ⟶ quotientGroupoid K'` induced by a morphism
`φ : K ⟶ K'` of presheaves of two-term complexes: over `U` it is the functor of quotient groupoids
induced by the chain map `φ_U`, sending `x` to `φ¹_U x` and the arrow labelled `a` to the arrow
labelled `φ⁰_U a`. Its naturality isomorphisms are labelled by `0`. -/
def quotientGroupoidMap (φ : K ⟶ K') : StrongTrans (quotientGroupoid K) (quotientGroupoid K') where
  app X := (mapApp φ X).toCatHom
  naturality {X Y} f := Cat.Hom.isoMk <| NatIso.ofComponents
    (fun M ↦ isoMk 0 (by
      simp only [Functor.toCatHom_toFunctor, Functor.comp_obj, map_zero,
        zero_add, objEquiv_symm_mapApp_obj, objEquiv_symm_map_obj]
      exact congr($(congrArg Arrow.Hom.right (φ.naturality f.as)).hom _)))
    (fun g ↦ hom_ext (by
      simp only [Functor.toCatHom_toFunctor, Functor.comp_map, label_comp,
        label_map_map, label_mapApp_map, isoMk_hom, label_homMk, add_zero, zero_add]
      exact congr($(congrArg Arrow.Hom.left (φ.naturality f.as)).hom _)))
  naturality_naturality {X Y f g} η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl := Subsingleton.elim η (𝟙 f)
    ext M
    simp
  naturality_id X := by
    ext M
    simp [label_mapApp_map]
  naturality_comp f g := by
    ext M
    simp [label_mapApp_map]

/-- The strong transformation induced by `φ` applies `φ¹` to the underlying elements. -/
@[simp]
theorem objEquiv_symm_quotientGroupoidMap_app_obj (φ : K ⟶ K') (X : LocallyDiscrete Cᵒᵖ)
    (M : (quotientGroupoid K).obj X) :
    (objEquiv X).symm (((quotientGroupoidMap φ).app X).toFunctor.obj M) =
      (φ.app X.as).right.hom ((objEquiv X).symm M) :=
  objEquiv_symm_mapApp_obj φ X M

/-- The strong transformation induced by `φ` applies `φ⁰` to labels. -/
@[simp]
theorem label_quotientGroupoidMap_app_map (φ : K ⟶ K') (X : LocallyDiscrete Cᵒᵖ)
    {M N : (quotientGroupoid K).obj X} (g : M ⟶ N) :
    label (((quotientGroupoidMap φ).app X).toFunctor.map g) = (φ.app X.as).left.hom (label g) :=
  label_mapApp_map φ X g

/-- The naturality isomorphisms of the strong transformation induced by `φ` are labelled by
`0`. -/
@[simp]
theorem label_quotientGroupoidMap_naturality_hom_app (φ : K ⟶ K') {X Y : LocallyDiscrete Cᵒᵖ}
    (f : X ⟶ Y) (M : (quotientGroupoid K).obj X) :
    label (((quotientGroupoidMap φ).naturality f).hom.toNatTrans.app M) = 0 := by
  simp [quotientGroupoidMap]

/-- The inverses of the naturality isomorphisms of the strong transformation induced by `φ` are
labelled by `0`. -/
@[simp]
theorem label_quotientGroupoidMap_naturality_inv_app (φ : K ⟶ K') {X Y : LocallyDiscrete Cᵒᵖ}
    (f : X ⟶ Y) (M : (quotientGroupoid K).obj X) :
    label (((quotientGroupoidMap φ).naturality f).inv.toNatTrans.app M) = 0 := by
  simp [quotientGroupoidMap]

/-- **Quasi-isomorphism invariance.** The functor between the fibres over `X` induced by `φ` is an
equivalence exactly when `φ` is a quasi-isomorphism over `X`: `φ⁰` restricts to a bijection
`H⁰ = ker d → ker d'` and `φ¹` induces a bijection `H¹ = E¹ ⧸ range d → E'¹ ⧸ range d'`. -/
theorem isEquivalence_quotientGroupoidMap_app_iff (φ : K ⟶ K') (X : LocallyDiscrete Cᵒᵖ) :
    ((quotientGroupoidMap φ).app X).toFunctor.IsEquivalence ↔
      Set.BijOn (φ.app X.as).left.hom (K.obj X.as).hom.hom.ker (K'.obj X.as).hom.hom.ker ∧
        Function.Bijective (QuotientAddGroup.map _ _ (φ.app X.as).right.hom
          (AddMonoidHom.range_le_comap_range_of_comp_eq
            (congrArg AddCommGrpCat.Hom.hom (φ.app X.as).w).symm)) :=
  AddMonoidHom.QuotientGroupoid.isEquivalence_map_iff _ _ _

/-- The component at `x` over `X` of the isomorphism of functors between fibres induced by a
chain homotopy `s` is labelled by `-s x`. -/
private theorem label_mapIsoOfHomotopy_hom_app {φ ψ : K ⟶ K'}
    (s : K ⋙ Arrow.rightFunc ⟶ K' ⋙ Arrow.leftFunc)
    (h₀ : ∀ U, (φ.app U).left.hom - (ψ.app U).left.hom = (s.app U).hom.comp (K.obj U).hom.hom)
    (h₁ : ∀ U, (φ.app U).right.hom - (ψ.app U).right.hom = (K'.obj U).hom.hom.comp (s.app U).hom)
    (X : LocallyDiscrete Cᵒᵖ) (M : (quotientGroupoid K).obj X) :
    label ((Cat.Hom.isoMk (AddMonoidHom.QuotientGroupoid.mapIsoOfHomotopy
      (congrArg AddCommGrpCat.Hom.hom (φ.app X.as).w).symm
      (congrArg AddCommGrpCat.Hom.hom (ψ.app X.as).w).symm
      (s.app X.as).hom (h₀ X.as) (h₁ X.as))).hom.toNatTrans.app M) =
      -(s.app X.as).hom ((objEquiv X).symm M) :=
  AddMonoidHom.QuotientGroupoid.label_mapIsoOfHomotopy_hom_app _ _ _ _ _ _

open scoped StrongTrans in
/-- A chain homotopy `s : E¹ ⟶ E'⁰` between morphisms `φ` and `ψ` of presheaves of two-term
complexes, that is `φ⁰ - ψ⁰ = s ∘ d` and `φ¹ - ψ¹ = d' ∘ s` over every `U`, induces an invertible
modification between the induced strong transformations. Its component at `x` over `U` is the
arrow `φ¹ x ⟶ ψ¹ x` labelled `-s x`. -/
def quotientGroupoidMapIsoOfHomotopy {φ ψ : K ⟶ K'}
    (s : K ⋙ Arrow.rightFunc ⟶ K' ⋙ Arrow.leftFunc)
    (h₀ : ∀ U, (φ.app U).left.hom - (ψ.app U).left.hom = (s.app U).hom.comp (K.obj U).hom.hom)
    (h₁ : ∀ U, (φ.app U).right.hom - (ψ.app U).right.hom = (K'.obj U).hom.hom.comp (s.app U).hom) :
    Iso (C := quotientGroupoid K ⟶ quotientGroupoid K')
      (quotientGroupoidMap φ) (quotientGroupoidMap ψ) :=
  StrongTrans.isoMk
    (fun X ↦ Cat.Hom.isoMk
      (AddMonoidHom.QuotientGroupoid.mapIsoOfHomotopy _ _ (s.app X.as).hom (h₀ X.as) (h₁ X.as)))
    (fun {X Y} f ↦ by
      ext M
      simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Arrow.rightFunc_obj, Arrow.leftFunc_obj,
        Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans, NatTrans.comp_app,
        Functor.whiskerLeft_app, label_comp, label_quotientGroupoidMap_naturality_hom_app, add_zero,
        Cat.whiskerRight_toNatTrans, Functor.whiskerRight_app, label_map_map, zero_add]
      -- The components of the isomorphisms of functors are labelled by `-s x`.
      refine (label_mapIsoOfHomotopy_hom_app s h₀ h₁ Y _).trans (Eq.trans ?_
        (congrArg (K'.map f.as).left.hom (label_mapIsoOfHomotopy_hom_app s h₀ h₁ X M)).symm)
      rw [objEquiv_symm_map_obj, map_neg]
      exact congrArg Neg.neg congr($(s.naturality f.as).hom ((objEquiv X).symm M)))

open scoped StrongTrans in
/-- The component at `x` over `X` of the modification induced by a chain homotopy `s` is labelled
by `-s x`. -/
@[simp]
theorem label_quotientGroupoidMapIsoOfHomotopy_hom_app {φ ψ : K ⟶ K'}
    (s : K ⋙ Arrow.rightFunc ⟶ K' ⋙ Arrow.leftFunc)
    (h₀ : ∀ U, (φ.app U).left.hom - (ψ.app U).left.hom = (s.app U).hom.comp (K.obj U).hom.hom)
    (h₁ : ∀ U, (φ.app U).right.hom - (ψ.app U).right.hom = (K'.obj U).hom.hom.comp (s.app U).hom)
    (X : LocallyDiscrete Cᵒᵖ) (M : (quotientGroupoid K).obj X) :
    label (((quotientGroupoidMapIsoOfHomotopy s h₀ h₁).hom.as.app X).toNatTrans.app M) =
      -(s.app X.as).hom ((objEquiv X).symm M) := by
  -- The component is `Cat.Hom.isoMk` of the isomorphism of functors between fibres. `simp` cannot
  -- rewrite it with `label_mapIsoOfHomotopy_hom_app`, whose statement types that isomorphism on
  -- the underlying `AddMonoidHom.QuotientGroupoid` fibres, so the lemma is applied directly.
  dsimp only [quotientGroupoidMapIsoOfHomotopy, StrongTrans.isoMk_hom_as_app]
  exact label_mapIsoOfHomotopy_hom_app s h₀ h₁ X M

open scoped StrongTrans in
/-- The component at `x` over `X` of the inverse of the modification induced by a chain homotopy
`s` is labelled by `s x`. -/
@[simp]
theorem label_quotientGroupoidMapIsoOfHomotopy_inv_app {φ ψ : K ⟶ K'}
    (s : K ⋙ Arrow.rightFunc ⟶ K' ⋙ Arrow.leftFunc)
    (h₀ : ∀ U, (φ.app U).left.hom - (ψ.app U).left.hom = (s.app U).hom.comp (K.obj U).hom.hom)
    (h₁ : ∀ U, (φ.app U).right.hom - (ψ.app U).right.hom = (K'.obj U).hom.hom.comp (s.app U).hom)
    (X : LocallyDiscrete Cᵒᵖ) (M : (quotientGroupoid K).obj X) :
    label (((quotientGroupoidMapIsoOfHomotopy s h₀ h₁).inv.as.app X).toNatTrans.app M) =
      (s.app X.as).hom ((objEquiv X).symm M) := by
  have h := congrArg (fun m ↦ label ((m.as.app X).toNatTrans.app M))
    (quotientGroupoidMapIsoOfHomotopy s h₀ h₁).hom_inv_id
  simp only [StrongTrans.homCategory_comp_as_app, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
    label_comp, label_quotientGroupoidMapIsoOfHomotopy_hom_app, StrongTrans.homCategory_id_as_app,
    Cat.Hom.toNatTrans_id, NatTrans.id_app, label_id] at h
  exact (neg_add_eq_zero.mp h).symm

end Map

end CategoryTheory.Pseudofunctor
