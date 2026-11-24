/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.Algebra.Group.Subgroup.Ker
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map
import Mathlib.Tactic.Abel

/-!
# The quotient groupoid of a two-term complex of abelian groups

A homomorphism `d : A →+ B` of abelian groups is a two-term complex `A → B`, placed in degrees
`0` and `1`. Its *quotient groupoid* `[B/A]` has the elements of `B` as objects, and an arrow
`x ⟶ y` is an element `a : A` with `d a + x = y`, its *label*; composition adds labels. It is
the action groupoid of `A` acting on `B` by translation through `d`, and it is built here as
Mathlib's `CategoryTheory.ActionCategory` of that action, so that the action-groupoid API of
`TauCeti.CategoryTheory.Groupoid.ActionCategory` applies to it.

This is Deligne's construction `h¹/h⁰` of the strictly commutative Picard category attached to a
two-term complex, evaluated on a single group of sections: for a two-term complex of abelian
sheaves, the quotient groupoids of its groups of sections form the prestack whose associated
stack is the Picard stack `h¹/h⁰`. The groupoid sees exactly the cohomology of the complex.

* Its isomorphism classes are the cokernel `H¹ = B ⧸ range d`
  (`AddMonoidHom.QuotientGroupoid.isomorphismClassesEquiv`).
* The automorphism group of every object is the kernel `H⁰ = ker d`
  (`AddMonoidHom.QuotientGroupoid.autMulEquiv`).
* In particular the groupoid is equivalent to the point exactly when `d` is bijective
  (`AddMonoidHom.QuotientGroupoid.nonempty_equivalence_punit_iff`).
* A commutative square from `d` to `d' : A' →+ B'`, that is a chain map, induces a functor
  (`AddMonoidHom.QuotientGroupoid.map`), functorially in the square; together these form a
  functor from arrows of `AddCommGrpCat` to groupoids (`AddMonoidHom.QuotientGroupoid.functor`).
* A chain homotopy between two chain maps induces a natural isomorphism between the induced
  functors (`AddMonoidHom.QuotientGroupoid.mapIsoOfHomotopy`).
* The functor induced by a chain map is faithful exactly when the map is injective on `H⁰`,
  essentially surjective exactly when it is surjective on `H¹`, and full exactly when it is
  surjective on `H⁰` and injective on `H¹`. Hence it is an equivalence exactly when the chain map
  is a quasi-isomorphism (`AddMonoidHom.QuotientGroupoid.isEquivalence_map_iff`).

## Main declarations

* `AddMonoidHom.TranslationSpace d`: the type `B` with `A` acting by translation through `d`.
* `AddMonoidHom.TranslationSpace.orbitRel_of_iff`,
  `AddMonoidHom.TranslationSpace.stabilizerMulEquiv`: its orbits are the cosets of `range d` and
  its stabilizers are `ker d`. Through the orbit and stabilizer dictionary of the action groupoid,
  these give the cohomology of the quotient groupoid.
* `AddMonoidHom.QuotientGroupoid d`: the quotient groupoid `[B/A]` of `d : A →+ B`.
* `AddMonoidHom.QuotientGroupoid.objEquiv`, `AddMonoidHom.QuotientGroupoid.label`,
  `AddMonoidHom.QuotientGroupoid.homMk`: objects are elements of `B`, arrows are labelled by `A`.
* `AddMonoidHom.QuotientGroupoid.isomorphismClassesEquiv`: isomorphism classes are `B ⧸ range d`.
* `AddMonoidHom.QuotientGroupoid.autMulEquiv`: automorphisms are `ker d`.
* `AddMonoidHom.QuotientGroupoid.nonempty_equivalence_punit_iff`: the groupoid is contractible
  exactly when `d` is bijective.
* `AddMonoidHom.QuotientGroupoid.map`, `AddMonoidHom.QuotientGroupoid.mapIsoOfHomotopy`: chain maps
  give functors and chain homotopies give natural isomorphisms.
* `AddMonoidHom.QuotientGroupoid.functor`: the quotient groupoid as a functor
  `Arrow AddCommGrpCat ⥤ Grpd`.
* `AddMonoidHom.QuotientGroupoid.faithful_map_iff`, `AddMonoidHom.QuotientGroupoid.full_map_iff`,
  `AddMonoidHom.QuotientGroupoid.essSurj_map_iff`,
  `AddMonoidHom.QuotientGroupoid.isEquivalence_map_iff`: the functor of a chain map is an
  equivalence exactly when the chain map is a quasi-isomorphism.

## References

* P. Deligne, *La formule de dualité globale*, SGA 4, Exposé XVIII, §1.4.
* K. Behrend and B. Fantechi, *The intrinsic normal cone*, Invent. Math. 128 (1997), §2 and
  Proposition 2.1.
-/

public section

open CategoryTheory

universe u w

namespace AddMonoidHom

variable {A B A' B' A'' B'' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A']
  [AddCommGroup B'] [AddCommGroup A''] [AddCommGroup B'']

/-- The type `B`, on which `A` acts through `d : A →+ B` by translation: `a +ᵥ x = d a + x`. It is
a type synonym so that this action is not an instance on `B` itself. -/
@[expose]
def TranslationSpace (_d : A →+ B) : Type _ := B

namespace TranslationSpace

variable (d : A →+ B)

instance : AddAction A d.TranslationSpace := AddAction.compHom B d

/-- The identification of `B` with `d.TranslationSpace`. -/
def of : B ≃ d.TranslationSpace := Equiv.refl B

/-- `A` acts on `d.TranslationSpace` by translation through `d`. -/
@[simp]
theorem vadd_of (a : A) (x : B) : a +ᵥ of d x = of d (d a + x) := (rfl)

/-- The multiplicative form of the translation action, used by the action groupoid. -/
theorem ofAdd_smul_of (a : A) (x : B) : Multiplicative.ofAdd a • of d x = of d (d a + x) := (rfl)

variable {d}

/-- Two points of the translation space lie in the same orbit exactly when they differ by an
element of the range of `d`. -/
theorem orbitRel_of_iff {x y : B} :
    MulAction.orbitRel (Multiplicative A) d.TranslationSpace (of d x) (of d y) ↔
      x - y ∈ d.range := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Multiplicative.ofAdd.surjective.exists]
  simp only [ofAdd_smul_of, (of d).injective.eq_iff, mem_range, eq_sub_iff_add_eq]

/-- An element of `A` stabilizes a point of the translation space exactly when it lies in the
kernel of `d`. -/
theorem mem_stabilizer_iff {a : Multiplicative A} {x : d.TranslationSpace} :
    a ∈ MulAction.stabilizer (Multiplicative A) x ↔ Multiplicative.toAdd a ∈ d.ker := by
  obtain ⟨y, rfl⟩ := (of d).surjective x
  rw [MulAction.mem_stabilizer_iff, ← ofAdd_toAdd a, ofAdd_smul_of, (of d).injective.eq_iff,
    toAdd_ofAdd, add_eq_right, mem_ker]

variable (d)

/-- The stabilizer of every point of the translation space is the kernel of `d`. Both sides are
subtypes of `A`, read through `Multiplicative`, so each element keeps its underlying element of
`A`. -/
def stabilizerMulEquiv (x : d.TranslationSpace) :
    MulAction.stabilizer (Multiplicative A) x ≃* Multiplicative d.ker where
  toFun a := Multiplicative.ofAdd ⟨Multiplicative.toAdd (a : Multiplicative A),
    mem_stabilizer_iff.mp a.property⟩
  invFun k := ⟨Multiplicative.ofAdd ((Multiplicative.toAdd k : d.ker) : A),
    mem_stabilizer_iff.mpr (Multiplicative.toAdd k).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_toAdd_stabilizerMulEquiv_apply (x : d.TranslationSpace)
    (a : MulAction.stabilizer (Multiplicative A) x) :
    ((Multiplicative.toAdd (stabilizerMulEquiv d x a) : d.ker) : A) =
      Multiplicative.toAdd (a : Multiplicative A) := (rfl)

@[simp]
theorem coe_stabilizerMulEquiv_symm_apply (x : d.TranslationSpace) (k : Multiplicative d.ker) :
    (((stabilizerMulEquiv d x).symm k : MulAction.stabilizer (Multiplicative A) x) :
      Multiplicative A) = Multiplicative.ofAdd ((Multiplicative.toAdd k : d.ker) : A) := (rfl)

end TranslationSpace

/-- The quotient groupoid `[B/A]` of the two-term complex `d : A →+ B`: Deligne's `h¹/h⁰` of the
complex, evaluated on a single group. Its objects are the elements of `B`
(`AddMonoidHom.QuotientGroupoid.objEquiv`), and an arrow `x ⟶ y` is an element `a : A` with
`d a + x = y` (`AddMonoidHom.QuotientGroupoid.label`). It is the action groupoid of `A` acting on
`B` by translation through `d`. -/
abbrev QuotientGroupoid (d : A →+ B) : Type _ :=
  ActionCategory (Multiplicative A) d.TranslationSpace

namespace QuotientGroupoid

section Basic

variable (d : A →+ B)

/-- The objects of the quotient groupoid of `d : A →+ B` are the elements of `B`. -/
def objEquiv : B ≃ d.QuotientGroupoid :=
  (TranslationSpace.of d).trans (ActionCategory.objEquiv _ _)

/-- The object `x` of the quotient groupoid is the object of the action groupoid at the point `x`
of the translation space. -/
theorem objEquiv_apply (x : B) :
    objEquiv d x = ActionCategory.objEquiv _ _ (TranslationSpace.of d x) := (rfl)

variable {d}

/-- The label `a : A` of an arrow `x ⟶ y` of the quotient groupoid; it satisfies
`d a + x = y` (`AddMonoidHom.QuotientGroupoid.apply_label_add`). -/
def label {X Y : d.QuotientGroupoid} (f : X ⟶ Y) : A :=
  Multiplicative.toAdd f.hom

/-- The label of an arrow is the element of `Multiplicative A` underlying the arrow of the action
groupoid, read additively. -/
@[simp]
theorem ofAdd_label {X Y : d.QuotientGroupoid} (f : X ⟶ Y) :
    Multiplicative.ofAdd (label f) = f.hom := (rfl)

/-- An arrow of the quotient groupoid translates its source to its target by the image of its
label. -/
theorem apply_label_add {X Y : d.QuotientGroupoid} (f : X ⟶ Y) :
    d (label f) + (objEquiv d).symm X = (objEquiv d).symm Y := by
  obtain ⟨x, rfl⟩ := (objEquiv d).surjective X
  obtain ⟨y, rfl⟩ := (objEquiv d).surjective Y
  have := ActionCategory.hom_smul (x := TranslationSpace.of d x) (y := TranslationSpace.of d y) f
  rw [← ofAdd_toAdd f.hom, TranslationSpace.ofAdd_smul_of] at this
  simpa [label] using (TranslationSpace.of d).injective this

/-- The arrow `x ⟶ y` labelled by `a`, for `a : A` with `d a + x = y`. -/
def homMk {X Y : d.QuotientGroupoid} (a : A)
    (h : d a + (objEquiv d).symm X = (objEquiv d).symm Y) : X ⟶ Y :=
  Functor.Elements.homMk (Multiplicative.ofAdd a) <|
    (TranslationSpace.ofAdd_smul_of d a _).trans (congrArg (TranslationSpace.of d) h)

@[simp]
theorem label_homMk {X Y : d.QuotientGroupoid} (a : A)
    (h : d a + (objEquiv d).symm X = (objEquiv d).symm Y) : label (homMk a h) = a := (rfl)

/-- Arrows of the quotient groupoid are determined by their labels. -/
@[ext]
theorem hom_ext {X Y : d.QuotientGroupoid} {f g : X ⟶ Y} (h : label f = label g) : f = g :=
  Functor.Elements.hom_ext h

@[simp]
theorem homMk_label {X Y : d.QuotientGroupoid} (f : X ⟶ Y) :
    homMk (label f) (apply_label_add f) = f :=
  hom_ext rfl

@[simp]
theorem label_id (X : d.QuotientGroupoid) : label (𝟙 X) = 0 := by
  rw [label, ActionCategory.id_hom, toAdd_one]

@[simp]
theorem label_eqToHom {X Y : d.QuotientGroupoid} (h : X = Y) : label (eqToHom h) = 0 := by
  apply Multiplicative.ofAdd.injective
  simp [ActionCategory.eqToHom_hom]

@[simp]
theorem label_comp {X Y Z : d.QuotientGroupoid} (f : X ⟶ Y) (g : Y ⟶ Z) :
    label (f ≫ g) = label f + label g := by
  rw [label, label, label, ActionCategory.comp_hom, toAdd_mul, add_comm]

@[simp]
theorem label_inv {X Y : d.QuotientGroupoid} (f : X ⟶ Y) : label (inv f) = -label f := by
  apply Multiplicative.ofAdd.injective
  simp

/-- The arrows `x ⟶ y` of the quotient groupoid are the elements `a : A` with `d a + x = y`. -/
def homEquiv (x y : B) :
    (objEquiv d x ⟶ objEquiv d y) ≃ {a : A // d a + x = y} where
  toFun f := ⟨label f, apply_label_add f⟩
  invFun a := homMk a.val (by simpa using a.property)
  left_inv f := homMk_label f
  right_inv _ := rfl

@[simp]
theorem coe_homEquiv_apply {x y : B} (f : objEquiv d x ⟶ objEquiv d y) :
    (homEquiv x y f : A) = label f := (rfl)

@[simp]
theorem homEquiv_symm_apply {x y : B} (a : {a : A // d a + x = y}) :
    (homEquiv x y).symm a = homMk a.val (by simpa using a.property) := (rfl)

end Basic

section Cohomology

variable {d : A →+ B}

/-- Two objects of the quotient groupoid are isomorphic exactly when they differ by an element of
the range of `d`. -/
theorem isIsomorphic_objEquiv_iff {x y : B} :
    IsIsomorphic (objEquiv d x) (objEquiv d y) ↔ y - x ∈ d.range := by
  simp [objEquiv_apply, ActionCategory.isIsomorphic_iff_orbitRel, TranslationSpace.orbitRel_of_iff,
    sub_mem_comm_iff]

variable (d) in
/-- The isomorphism classes of the quotient groupoid of `d : A →+ B` are the cokernel
`H¹ = B ⧸ range d` of `d`. -/
def isomorphismClassesEquiv :
    _root_.Quotient (isIsomorphicSetoid d.QuotientGroupoid) ≃ B ⧸ d.range :=
  ((Quotient.congr (TranslationSpace.of d) fun x y => by
    simp [QuotientAddGroup.leftRel_apply, TranslationSpace.orbitRel_of_iff, sub_mem_comm_iff,
      neg_add_eq_sub]).trans (ActionCategory.orbitQuotientEquivIsomorphismClasses _ _)).symm

@[simp]
theorem isomorphismClassesEquiv_mk (x : B) :
    isomorphismClassesEquiv d (_root_.Quotient.mk _ (objEquiv d x)) = (x : B ⧸ d.range) := by
  rw [isomorphismClassesEquiv, Equiv.symm_apply_eq, Equiv.trans_apply, Quotient.congr_mk]
  simp [objEquiv_apply]

variable (d) in
/-- The automorphisms of any object of the quotient groupoid of `d : A →+ B` are the kernel
`H⁰ = ker d` of `d`: an automorphism is its label. The group law of `Aut` is composition, which
adds labels. -/
def autMulEquiv (X : d.QuotientGroupoid) : Aut X ≃* Multiplicative d.ker :=
  (Aut.autMulEquivOfIso (eqToIso ((ActionCategory.objEquiv _ _).apply_symm_apply X).symm)).trans <|
    (ActionCategory.stabilizerMulEquivAut _ _).symm.trans (TranslationSpace.stabilizerMulEquiv d _)

@[simp]
theorem coe_toAdd_autMulEquiv_apply (X : d.QuotientGroupoid) (e : Aut X) :
    ((Multiplicative.toAdd (autMulEquiv d X e) : d.ker) : A) = label e.asIso.hom := by
  apply Multiplicative.ofAdd.injective
  simp [autMulEquiv, ActionCategory.comp_hom]

@[simp]
theorem label_autMulEquiv_symm_apply_asIso_hom (X : d.QuotientGroupoid)
    (a : Multiplicative d.ker) :
    label ((autMulEquiv d X).symm a).asIso.hom = (Multiplicative.toAdd a : d.ker) := by
  apply Multiplicative.ofAdd.injective
  simp [autMulEquiv]

variable (d) in
/-- The quotient groupoid of `d : A →+ B` is equivalent to the point exactly when `d` is
bijective, that is when both `H⁰ = ker d` and `H¹ = B ⧸ range d` vanish. -/
theorem nonempty_equivalence_punit_iff :
    Nonempty (d.QuotientGroupoid ≌ Discrete PUnit.{w + 1}) ↔ Function.Bijective d := by
  rw [equiv_punit_iff_unique]
  constructor
  · rintro ⟨-, hunique⟩
    refine ⟨(injective_iff_map_eq_zero d).mpr fun a ha => ?_, fun y => ?_⟩
    · obtain ⟨u⟩ := hunique (objEquiv d 0) (objEquiv d 0)
      have := congrArg label ((u.uniq (homMk a (by simpa using ha))).trans (u.uniq (𝟙 _)).symm)
      rwa [label_homMk, label_id] at this
    · obtain ⟨u⟩ := hunique (objEquiv d 0) (objEquiv d y)
      exact ⟨label u.default, by simpa using apply_label_add u.default⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨⟨objEquiv d 0⟩, fun X Y => ?_⟩
    have : Subsingleton (X ⟶ Y) := ⟨fun f g => hom_ext <| hinj <| by
      rw [eq_sub_of_add_eq (apply_label_add f), eq_sub_of_add_eq (apply_label_add g)]⟩
    obtain ⟨a, ha⟩ := hsurj ((objEquiv d).symm Y - (objEquiv d).symm X)
    exact ⟨uniqueOfSubsingleton (homMk a (by rw [ha, sub_add_cancel]))⟩

end Cohomology

section Map

variable {d : A →+ B} {d' : A' →+ B'} {d'' : A'' →+ B''}

/-- The map `f₁ : B →+ B'` of a commutative square, as a map of translation spaces equivariant
along `f₀`. -/
private def translationSpaceMap (f₀ : A →+ A') (f₁ : B →+ B') (h : f₁.comp d = d'.comp f₀) :
    d.TranslationSpace →ₑ[toMultiplicative f₀] d'.TranslationSpace where
  toFun x := TranslationSpace.of d' (f₁ ((TranslationSpace.of d).symm x))
  map_smul' a x := by
    obtain ⟨y, rfl⟩ := (TranslationSpace.of d).surjective x
    obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective a
    simpa [TranslationSpace.ofAdd_smul_of] using DFunLike.congr_fun h a

@[simp]
private theorem translationSpaceMap_of (f₀ : A →+ A') (f₁ : B →+ B') (h : f₁.comp d = d'.comp f₀)
    (x : B) :
    translationSpaceMap f₀ f₁ h (TranslationSpace.of d x) = TranslationSpace.of d' (f₁ x) :=
  congrArg (TranslationSpace.of d' ∘ f₁) ((TranslationSpace.of d).symm_apply_apply x)

/-- The functor between quotient groupoids induced by a chain map `(f₀, f₁)` from `d : A →+ B` to
`d' : A' →+ B'`, that is a commutative square `f₁ ∘ d = d' ∘ f₀`. It sends `x` to `f₁ x` and
the arrow labelled `a` to the arrow labelled `f₀ a`. -/
def map (f₀ : A →+ A') (f₁ : B →+ B') (h : f₁.comp d = d'.comp f₀) :
    d.QuotientGroupoid ⥤ d'.QuotientGroupoid :=
  ActionCategory.map (toMultiplicative f₀) (translationSpaceMap f₀ f₁ h)

variable (f₀ : A →+ A') (f₁ : B →+ B') (h : f₁.comp d = d'.comp f₀)

@[simp]
theorem map_obj_objEquiv (x : B) : (map f₀ f₁ h).obj (objEquiv d x) = objEquiv d' (f₁ x) := by
  rw [map, objEquiv_apply, objEquiv_apply, ActionCategory.map_obj, translationSpaceMap_of]

@[simp]
theorem objEquiv_symm_map_obj (X : d.QuotientGroupoid) :
    (objEquiv d').symm ((map f₀ f₁ h).obj X) = f₁ ((objEquiv d).symm X) := by
  obtain ⟨x, rfl⟩ := (objEquiv d).surjective X
  simp

@[simp]
theorem label_map_map {X Y : d.QuotientGroupoid} (g : X ⟶ Y) :
    label ((map f₀ f₁ h).map g) = f₀ (label g) := by
  apply Multiplicative.ofAdd.injective
  rw [ofAdd_label, map, ActionCategory.map_map_hom, ← ofAdd_label g, toMultiplicative_apply_apply,
    toAdd_ofAdd]

variable (d) in
/-- The identity chain map induces the identity functor. -/
theorem map_id :
    map (AddMonoidHom.id A) (AddMonoidHom.id B) (by rfl : (AddMonoidHom.id B).comp d = _) = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun X => by obtain ⟨x, rfl⟩ := (objEquiv d).surjective X; simp)
    fun _ _ _ => hom_ext (by simp)

/-- The composite of two chain maps induces the composite of the induced functors. -/
theorem map_comp (g₀ : A' →+ A'') (g₁ : B' →+ B'') (h' : g₁.comp d' = d''.comp g₀) :
    map f₀ f₁ h ⋙ map g₀ g₁ h' = map (g₀.comp f₀) (g₁.comp f₁) (by
      rw [comp_assoc, h, ← comp_assoc, h', comp_assoc]) :=
  CategoryTheory.Functor.ext (fun X => by obtain ⟨x, rfl⟩ := (objEquiv d).surjective X; simp)
    fun _ _ _ => hom_ext (by simp)

/-- The quotient groupoid as a functor on two-term complexes of abelian groups: a two-term complex
is an arrow `d : A ⟶ B` of `AddCommGrpCat`, and a chain map is a morphism of arrows, that is a
commutative square. Composing a presheaf of two-term complexes with this functor gives the
prestack of quotient groupoids, whose associated stack is the Picard stack `h¹/h⁰`. -/
-- The body is exposed: the arrow `functor.map φ` is a functor between the quotient groupoids, and
-- stating this requires `functor.obj X` to unfold to the quotient groupoid of `X`.
@[expose]
def functor : Arrow AddCommGrpCat.{u} ⥤ Grpd.{u, u} where
  obj X := Grpd.of X.hom.hom.QuotientGroupoid
  map φ := map φ.left.hom φ.right.hom (congrArg AddCommGrpCat.Hom.hom φ.w).symm
  map_id X := map_id X.hom.hom
  map_comp _ _ := (map_comp _ _ _ _ _ _).symm

@[simp]
theorem functor_obj (X : Arrow AddCommGrpCat.{u}) :
    functor.obj X = Grpd.of X.hom.hom.QuotientGroupoid := (rfl)

@[simp]
theorem functor_map {X Y : Arrow AddCommGrpCat.{u}} (φ : X ⟶ Y) :
    functor.map φ = map φ.left.hom φ.right.hom (congrArg AddCommGrpCat.Hom.hom φ.w).symm := (rfl)

/-- A chain homotopy `s : B →+ A'` between two chain maps `(f₀, f₁)` and `(g₀, g₁)` from `d` to
`d'`, that is `f₀ - g₀ = s ∘ d` and `f₁ - g₁ = d' ∘ s`, induces a natural isomorphism between the
induced functors. Its component at `x` is the arrow `f₁ x ⟶ g₁ x` labelled `-s x`. -/
def mapIsoOfHomotopy {f₀ g₀ : A →+ A'} {f₁ g₁ : B →+ B'} (hf : f₁.comp d = d'.comp f₀)
    (hg : g₁.comp d = d'.comp g₀) (s : B →+ A') (h₀ : f₀ - g₀ = s.comp d)
    (h₁ : f₁ - g₁ = d'.comp s) : map f₀ f₁ hf ≅ map g₀ g₁ hg :=
  NatIso.ofComponents
    (fun X => (Groupoid.isoEquivHom _ _).symm <| homMk (-s ((objEquiv d).symm X)) <| by
      have := DFunLike.congr_fun h₁ ((objEquiv d).symm X)
      simp only [sub_apply, comp_apply] at this
      simp [← this])
    fun {X Y} g => hom_ext <| by
      have h₀' := DFunLike.congr_fun h₀ (label g)
      simp only [sub_apply, comp_apply] at h₀'
      simp only [label_comp, label_map_map, Groupoid.isoEquivHom_symm_apply_hom, label_homMk,
        ← apply_label_add g, map_add, sub_eq_iff_eq_add.mp h₀']
      abel

@[simp]
theorem label_mapIsoOfHomotopy_hom_app {f₀ g₀ : A →+ A'} {f₁ g₁ : B →+ B'}
    (hf : f₁.comp d = d'.comp f₀) (hg : g₁.comp d = d'.comp g₀) (s : B →+ A')
    (h₀ : f₀ - g₀ = s.comp d) (h₁ : f₁ - g₁ = d'.comp s) (X : d.QuotientGroupoid) :
    label ((mapIsoOfHomotopy hf hg s h₀ h₁).hom.app X) = -s ((objEquiv d).symm X) := (rfl)

end Map

section Equivalence

variable {d : A →+ B} {d' : A' →+ B'} (f₀ : A →+ A') (f₁ : B →+ B') (h : f₁.comp d = d'.comp f₀)

/-- The functor induced by a chain map is faithful exactly when the chain map is injective on
`H⁰ = ker d`. -/
theorem faithful_map_iff : (map f₀ f₁ h).Faithful ↔ Set.InjOn f₀ d.ker := by
  rw [map, ActionCategory.faithful_map_iff, (TranslationSpace.of d).surjective.forall]
  simp only [Multiplicative.ofAdd.surjective.forall, TranslationSpace.ofAdd_smul_of,
    (TranslationSpace.of d).injective.eq_iff, add_left_inj, toMultiplicative_apply_apply,
    toAdd_ofAdd, Multiplicative.ofAdd.injective.eq_iff, forall_const]
  constructor
  · intro hinj a ha b hb hab
    exact hinj a b ((mem_ker.mp ha).trans (mem_ker.mp hb).symm) hab
  · intro hinj a b hab hf
    refine sub_eq_zero.mp (hinj (mem_ker.mpr ?_) (zero_mem d.ker) ?_) <;>
      simp [hab, hf]

/-- The functor induced by a chain map is full exactly when the chain map is surjective on
`H⁰ = ker d` and injective on `H¹ = B ⧸ range d`; the latter says that an element of `B` whose
image lies in the range of `d'` lies in the range of `d` (compare
`QuotientAddGroup.map_injective_iff`). -/
theorem full_map_iff :
    (map f₀ f₁ h).Full ↔ Set.SurjOn f₀ d.ker d'.ker ∧ d'.range.comap f₁ ≤ d.range := by
  have h' (a : A) : f₁ (d a) = d' (f₀ a) := DFunLike.congr_fun h a
  rw [map, ActionCategory.full_map_iff]
  simp only [(TranslationSpace.of d).surjective.forall, Multiplicative.ofAdd.surjective.forall,
    Multiplicative.ofAdd.surjective.exists, translationSpaceMap_of, TranslationSpace.ofAdd_smul_of,
    (TranslationSpace.of d).injective.eq_iff, (TranslationSpace.of d').injective.eq_iff,
    toMultiplicative_apply_apply, toAdd_ofAdd, Multiplicative.ofAdd.injective.eq_iff]
  constructor
  · intro hlift
    refine ⟨fun a' ha' => ?_, fun x hx => ?_⟩
    · obtain ⟨a, rfl, ha⟩ := hlift 0 0 a' (by simp [mem_ker.mp ha'])
      exact ⟨a, mem_ker.mpr (by rwa [add_zero] at ha), rfl⟩
    · obtain ⟨a', ha'⟩ := mem_range.mp (AddSubgroup.mem_comap.mp hx)
      obtain ⟨a, -, ha⟩ := hlift 0 x a' (by simp [ha'])
      exact mem_range.mpr ⟨a, by rwa [add_zero] at ha⟩
  · rintro ⟨hker, hcoker⟩ x x' a' hx
    obtain ⟨a₀, ha₀⟩ := mem_range.mp (hcoker (x := x' - x) (AddSubgroup.mem_comap.mpr
      (mem_range.mpr ⟨a', by simp [← hx]⟩)))
    obtain ⟨k, hk, hfk⟩ := @hker (a' - f₀ a₀) (mem_ker.mpr (by simp [← h', ha₀, ← hx]))
    exact ⟨a₀ + k, by simp [hfk], by simp [mem_ker.mp hk, ha₀]⟩

/-- The functor induced by a chain map is essentially surjective exactly when the chain map is
surjective on `H¹ = B ⧸ range d`. -/
theorem essSurj_map_iff :
    (map f₀ f₁ h).EssSurj ↔
      Function.Surjective (QuotientAddGroup.map _ _ f₁ (range_le_comap_range_of_comp_eq h)) := by
  rw [map, ActionCategory.essSurj_map_iff, (TranslationSpace.of d').surjective.forall,
    Function.Surjective, (QuotientAddGroup.mk_surjective (s := d'.range)).forall]
  simp_rw [(TranslationSpace.of d).surjective.exists, translationSpaceMap_of,
    TranslationSpace.orbitRel_of_iff, (QuotientAddGroup.mk_surjective (s := d.range)).exists,
    QuotientAddGroup.map_mk, QuotientAddGroup.eq, neg_add_eq_sub, sub_mem_comm_iff]

/-- **Quasi-isomorphism invariance of the quotient groupoid.** The functor induced by a chain map
`(f₀, f₁)` from `d` to `d'` is an equivalence exactly when the chain map is a quasi-isomorphism:
`f₀` restricts to a bijection `H⁰ = ker d → ker d' = H⁰` and `f₁` induces a bijection
`H¹ = B ⧸ range d → B' ⧸ range d' = H¹`. -/
theorem isEquivalence_map_iff :
    (map f₀ f₁ h).IsEquivalence ↔
      Set.BijOn f₀ d.ker d'.ker ∧
        Function.Bijective (QuotientAddGroup.map _ _ f₁ (range_le_comap_range_of_comp_eq h)) := by
  rw [Set.BijOn, Function.Bijective, QuotientAddGroup.map_injective_iff,
    ← faithful_map_iff f₀ f₁ h, ← essSurj_map_iff f₀ f₁ h]
  constructor
  · intro hF
    have hfull := (full_map_iff f₀ f₁ h).mp hF.full
    exact ⟨⟨fun a ha => AddSubgroup.mem_comap.mp (ker_le_comap_ker_of_comp_eq h ha), hF.faithful,
      hfull.1⟩, hfull.2, hF.essSurj⟩
  · rintro ⟨⟨-, hfaith, hsurj⟩, hcoker, hess⟩
    have := (full_map_iff f₀ f₁ h).mpr ⟨hsurj, hcoker⟩
    exact { faithful := hfaith, full := this, essSurj := hess }

end Equivalence

end QuotientGroupoid

end AddMonoidHom
