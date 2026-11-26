/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import TauCeti.CategoryTheory.Category.Pointed.Fin
public import TauCeti.CategoryTheory.Monoidal.Braided.ListTensor

/-!
# The category of operators of a symmetric monoidal category

For a symmetric monoidal category `C`, the category of operators `C^⊗` has as objects the finite
families `(X₁, …, Xₙ)` of objects of `C`, lying over the objects `⟨n⟩` of the category `Fin_*`
of finite pointed sets (`TauCeti.FinPointed`). A morphism `(X_i) ⟶ (Y_j)` over a pointed map
`f : ⟨m⟩ ⟶ ⟨n⟩` is a family of maps `⊗_{f(i) = j} X_i ⟶ Y_j`, one for each `j` other than the
basepoint, out of the ordered tensor products over the fibers of `f` (`TauCeti.listTensor`).
Composition reorders and regroups the factors by the canonical isomorphisms of symmetric
monoidal coherence (`TauCeti.listTensorPermIso`, `TauCeti.listTensorFlatMapIso`). The nerve of
the functor `C^⊗ ⥤ Fin_*` is the symmetric monoidal quasicategory underlying `C`.

The functor `C^⊗ ⥤ Fin_*` is a cofibered category in the sense of Mathlib's
`CategoryTheory.Functor.IsStronglyCocartesian`: every map `f : ⟨m⟩ ⟶ ⟨n⟩` has, at every family
`X` over `⟨m⟩`, the strongly coCartesian lift `X ⟶ f_! X` whose target is the family of the
tensor products over the fibers of `f` and whose components are identities. Its fiber over `⟨n⟩`
is equivalent to `C^n`: a morphism over the identity of `⟨n⟩` is a family of maps of the members.
This is the Segal condition in the category of operators.

## Main definitions

* `TauCeti.CategoryOfOperators C`: the category of operators `C^⊗`.
* `TauCeti.CategoryOfOperators.toFinPointed C`: the functor `C^⊗ ⥤ Fin_*`.
* `TauCeti.CategoryOfOperators.pushforward`, `TauCeti.CategoryOfOperators.toPushforward`: the
  pushforward `f_! X` of a family and the coCartesian lift `X ⟶ f_! X`.
* `TauCeti.CategoryOfOperators.ι C n`: the inclusion `C^n ⥤ C^⊗` of the families over `⟨n⟩`.

## Main results

* `TauCeti.CategoryOfOperators.isStronglyCocartesian_toPushforward`: the lift `X ⟶ f_! X` is
  strongly coCartesian.
* `TauCeti.CategoryOfOperators.fiberEquivalence`: the fiber of `C^⊗` over `⟨n⟩` is equivalent to
  `C^n`.

## References

* J. Lurie, *Higher Algebra*, Construction 2.0.0.1.
-/

public section

universe w v u

open CategoryTheory MonoidalCategory

namespace TauCeti

/-- The category of operators `C^⊗` of a symmetric monoidal category `C` (Lurie, *Higher
Algebra*, Construction 2.0.0.1). An object is a finite family of objects of `C`, lying over the
object `⟨n⟩` of `Fin_*` that counts its members; the family is indexed by the elements
`1, …, n` of `⟨n⟩` other than the basepoint, numbered by `Fin n`. The objects live in an
arbitrary universe `w`, that of `Fin_*`. -/
structure CategoryOfOperators (C : Type u) : Type (max u w) where
  /-- The family over `base` with members `obj`. -/
  mk ::
  /-- The object `⟨n⟩` of `Fin_*` over which the family lies. -/
  base : FinPointed.{w}
  /-- The members of the family. -/
  obj : Fin base.len → C

namespace CategoryOfOperators

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A morphism of `C^⊗` from `X` to `Y`: a map `f : X.base ⟶ Y.base` of `Fin_*`, and for each
element `j` of `Y.base` other than the basepoint, a map to `Y.obj j` from the ordered tensor
product of the `X.obj i` over the fiber of `f` over `j`. The members of `X` sent to the basepoint
are forgotten. -/
structure Hom (X Y : CategoryOfOperators.{w} C) : Type (max v w) where
  /-- The underlying map of `Fin_*`. -/
  base : X.base ⟶ Y.base
  /-- The component at `j`, out of the tensor product over the fiber of `base` over `j`. -/
  app (j : Fin Y.base.len) : listTensor X.obj (base.fiber j) ⟶ Y.obj j

/-- The pushforward `f_! X` of a family `X` along `f : X.base ⟶ n`: the family over `n` of the
ordered tensor products of the members of `X` over the fibers of `f`. It is the target of the
coCartesian lift `X.toPushforward f` of `f`. -/
@[expose, implicit_reducible, simps]
def pushforward (X : CategoryOfOperators.{w} C) {n : FinPointed.{w}} (f : X.base ⟶ n) :
    CategoryOfOperators.{w} C :=
  ⟨n, fun j ↦ listTensor X.obj (f.fiber j)⟩

variable [SymmetricCategory C]

namespace Hom

/-- The identity of a family: its component at `j` identifies the tensor product over the fiber
`[j]` of the identity with `X.obj j`. -/
@[expose, reducible]
noncomputable def id (X : CategoryOfOperators.{w} C) : Hom X X where
  base := 𝟙 X.base
  app j := (listTensorPermIso X.obj (.of_eq (FinPointed.fiber_id j))).hom ≫ (ρ_ (X.obj j)).hom

/-- The composite of `f : X ⟶ Y` and `g : Y ⟶ Z`: its component at `l` reorders the factors over
the fiber of `f.base ≫ g.base` over `l` into the concatenation of the fibers of `f` over the fiber
of `g` over `l`, groups them along that concatenation, applies the components of `f` to the groups
and then the component of `g` at `l`. -/
@[expose, reducible]
noncomputable def comp {X Y Z : CategoryOfOperators.{w} C} (f : Hom X Y) (g : Hom Y Z) :
    Hom X Z where
  base := f.base ≫ g.base
  app l := (listTensorPermIso X.obj (FinPointed.perm_fiber_comp f.base g.base l)).hom ≫
    (listTensorFlatMapIso X.obj f.base.fiber (g.base.fiber l)).hom ≫
    listTensorMap f.app (g.base.fiber l) ≫ g.app l

/-- The morphism over the identity of `X.base` given by a family of maps out of the members of
`X`. -/
@[expose, reducible]
noncomputable def ofFamily (X : CategoryOfOperators.{w} C) {Y : Fin X.base.len → C}
    (φ : ∀ j, X.obj j ⟶ Y j) : Hom X ⟨X.base, Y⟩ where
  base := 𝟙 X.base
  app j := (id X).app j ≫ φ j

private lemma ext' {X Y : CategoryOfOperators.{w} C} {f g : Hom X Y} (h : f.base = g.base)
    (h' : ∀ j, f.app j = (listTensorPermIso X.obj (.of_eq (by rw [h]))).hom ≫ g.app j) :
    f = g := by
  obtain ⟨b, f⟩ := f
  obtain ⟨b', g⟩ := g
  obtain rfl : b = b' := h
  simp only [listTensorPermIso_self, Iso.refl_hom, Category.id_comp] at h'
  rw [funext h']

/-- The identity family of maps gives the identity. -/
lemma ofFamily_id (X : CategoryOfOperators.{w} C) : ofFamily X (fun j ↦ 𝟙 (X.obj j)) = id X :=
  ext' rfl fun j ↦ by simp

lemma id_comp {X Y : CategoryOfOperators.{w} C} (f : Hom X Y) : (id X).comp f = f := by
  refine ext' (Category.id_comp _) fun l ↦ ?_
  dsimp only [comp, id]
  rw [← listTensorMap_comp_assoc,
    ← listTensorPermIso_flatMap_left_hom_assoc X.obj (fun j ↦ .of_eq (FinPointed.fiber_id j)),
    reassoc_of% listTensorFlatMapIso_hom_listTensorMap_rightUnitor X.obj (f.base.fiber l),
    ← eqToIso.hom, ← listTensorPermIso_of_eq X.obj (List.flatMap_singleton' _)
      (.of_eq (List.flatMap_singleton' _)),
    listTensorPermIso_hom_listTensorPermIso_hom_assoc,
    listTensorPermIso_hom_listTensorPermIso_hom_assoc]

private lemma comp_ofFamily_app' {X Y : CategoryOfOperators.{w} C} {Z : Fin Y.base.len → C}
    (f : Hom X Y) (φ : ∀ j, Y.obj j ⟶ Z j) (j : Fin Y.base.len) :
    (f.comp (ofFamily Y φ)).app j =
      (listTensorPermIso X.obj
        (.of_eq (congrArg (FinPointed.Hom.fiber · j) (Category.comp_id f.base)))).hom ≫
        f.app j ≫ φ j := by
  dsimp only [comp, ofFamily, id]
  simp only [Category.assoc]
  have hρ : listTensorMap f.app [j] ≫ (ρ_ (Y.obj j)).hom = (ρ_ _).hom ≫ f.app j := by
    simp [tensorHom_id]
  rw [listTensorPermIso_hom_naturality_assoc,
    ← listTensorPermIso_flatMap_right_hom_assoc X.obj f.base.fiber _
      fun a _ b _ h ↦ f.base.disjoint_fiber h,
    reassoc_of% hρ,
    reassoc_of% listTensorFlatMapIso_singleton_hom_rightUnitor_hom X.obj f.base.fiber j,
    ← eqToIso.hom, ← listTensorPermIso_of_eq X.obj (List.flatMap_singleton _ _)
      (.of_eq (List.flatMap_singleton _ _)),
    listTensorPermIso_hom_listTensorPermIso_hom_assoc,
    listTensorPermIso_hom_listTensorPermIso_hom_assoc]

lemma comp_id {X Y : CategoryOfOperators.{w} C} (f : Hom X Y) : f.comp (id Y) = f := by
  rw [← ofFamily_id]
  exact ext' (Category.comp_id _) fun j ↦ by rw [comp_ofFamily_app', Category.comp_id (f.app j)]

lemma assoc {X Y Z W : CategoryOfOperators.{w} C} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  refine ext' (Category.assoc _ _ _) fun p ↦ ?_
  simp only [comp, ← listTensorMap_comp, Category.assoc]
  have key := listTensorFlatMapIso_hom_flatMap X.obj f.base.fiber g.base.fiber (h.base.fiber p)
  rw [eq_comm, eqToHom_comp_iff] at key
  rw [← listTensorPermIso_flatMap_left_hom_assoc X.obj (FinPointed.perm_fiber_comp f.base g.base),
    reassoc_of% key, listTensorPermIso_hom_naturality_assoc,
    listTensorFlatMapIso_hom_naturality_assoc,
    ← listTensorPermIso_flatMap_right_hom_assoc X.obj f.base.fiber _
      fun a _ b _ h ↦ f.base.disjoint_fiber h,
    ← eqToIso.hom, ← listTensorPermIso_of_eq X.obj List.flatMap_assoc.symm
      (.of_eq List.flatMap_assoc.symm)]
  simp only [listTensorPermIso_hom_listTensorPermIso_hom_assoc]

end Hom

noncomputable instance : Category.{max v w} (CategoryOfOperators.{w} C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

variable {X Y Z : CategoryOfOperators.{w} C}

/-- Two morphisms of `C^⊗` are equal when their underlying maps of `Fin_*` are, and their
components agree up to the reordering identifying the fibers of these maps. -/
@[ext (iff := false)]
lemma hom_ext {f g : X ⟶ Y} (h : f.base = g.base)
    (h' : ∀ j, f.app j = (listTensorPermIso X.obj (.of_eq (by rw [h]))).hom ≫ g.app j) :
    f = g :=
  Hom.ext' h h'

/-- The components of equal morphisms of `C^⊗` agree up to the reordering identifying the
fibers of their underlying maps. -/
lemma congr_app {f g : X ⟶ Y} (h : f = g) (j : Fin Y.base.len) :
    f.app j = (listTensorPermIso X.obj (.of_eq (by rw [h]))).hom ≫ g.app j := by
  subst h
  simp

@[simp]
lemma id_base (X : CategoryOfOperators.{w} C) : Hom.base (𝟙 X) = 𝟙 X.base :=
  rfl

@[simp]
lemma id_app (X : CategoryOfOperators.{w} C) (j : Fin X.base.len) :
    Hom.app (𝟙 X) j =
      (listTensorPermIso X.obj (.of_eq (FinPointed.fiber_id j))).hom ≫ (ρ_ (X.obj j)).hom :=
  rfl

@[simp]
lemma comp_base (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base :=
  rfl

lemma comp_app (f : X ⟶ Y) (g : Y ⟶ Z) (l : Fin Z.base.len) :
    (f ≫ g).app l =
      (listTensorPermIso X.obj (FinPointed.perm_fiber_comp f.base g.base l)).hom ≫
        (listTensorFlatMapIso X.obj f.base.fiber (g.base.fiber l)).hom ≫
        listTensorMap f.app (g.base.fiber l) ≫ g.app l :=
  rfl

/-- Postcomposing with a morphism over an identity given by maps of the members of a family
postcomposes the components with these maps. -/
@[simp]
lemma comp_ofFamily_app {Z' : Fin Y.base.len → C} (f : X ⟶ Y) (φ : ∀ j, Y.obj j ⟶ Z' j)
    (j : Fin Y.base.len) :
    (f ≫ (Hom.ofFamily Y φ : Y ⟶ ⟨Y.base, Z'⟩)).app j =
      (listTensorPermIso X.obj
        (.of_eq (congrArg (FinPointed.Hom.fiber · j) (Category.comp_id f.base)))).hom ≫
        f.app j ≫ φ j :=
  Hom.comp_ofFamily_app' f φ j

/-! ### The functor to `Fin_*` -/

variable (C) in
/-- The functor `C^⊗ ⥤ Fin_*` sending a family over `⟨n⟩` to `⟨n⟩`. -/
@[expose, implicit_reducible, simps]
def toFinPointed : CategoryOfOperators.{w} C ⥤ FinPointed.{w} where
  obj X := X.base
  map f := f.base

/-- Every morphism of `C^⊗` lifts its underlying map of `Fin_*`. -/
instance isHomLift_base (f : X ⟶ Y) : (toFinPointed C).IsHomLift f.base f :=
  inferInstanceAs ((toFinPointed C).IsHomLift ((toFinPointed C).map f) f)

/-- A morphism `f` lifts a map `g` of `Fin_*` exactly when `g` is its underlying map. -/
lemma isHomLift_iff {f : X ⟶ Y} {g : X.base ⟶ Y.base} :
    (toFinPointed C).IsHomLift g f ↔ f.base = g :=
  ⟨fun h ↦ (@IsHomLift.eq_of_isHomLift _ _ _ _ (toFinPointed C) X Y g f h).symm,
    fun h ↦ h ▸ isHomLift_base f⟩

/-! ### CoCartesian lifts -/

/-- The coCartesian lift of `f : X.base ⟶ n` starting at `X`: the morphism
`X ⟶ X.pushforward f` over `f` all of whose components are identities. -/
@[expose, reducible]
noncomputable def toPushforward (X : CategoryOfOperators.{w} C) {n : FinPointed.{w}}
    (f : X.base ⟶ n) : X ⟶ X.pushforward f :=
  (⟨f, fun _ ↦ 𝟙 _⟩ : Hom X (X.pushforward f))

@[simp]
lemma toPushforward_base (X : CategoryOfOperators.{w} C) {n : FinPointed.{w}}
    (f : X.base ⟶ n) : (X.toPushforward f).base = f :=
  rfl

@[simp]
lemma toPushforward_app (X : CategoryOfOperators.{w} C) {n : FinPointed.{w}}
    (f : X.base ⟶ n) (j : Fin n.len) :
    (X.toPushforward f).app j = 𝟙 (listTensor X.obj (f.fiber j)) :=
  rfl

/-- The components of a composite with the coCartesian lift `X ⟶ f_! X` of `f`. -/
lemma toPushforward_comp_app {n : FinPointed.{w}} (f : X.base ⟶ n) (g : X.pushforward f ⟶ Y)
    (l : Fin Y.base.len) :
    (X.toPushforward f ≫ g).app l =
      (listTensorPermIso X.obj (FinPointed.perm_fiber_comp f g.base l)).hom ≫
        (listTensorFlatMapIso X.obj f.fiber (g.base.fiber l)).hom ≫ g.app l := by
  have h : listTensorMap (X.toPushforward f).app (g.base.fiber l) ≫ g.app l = g.app l :=
    (congrArg (· ≫ g.app l) (listTensorMap_id (fun j ↦ listTensor X.obj (f.fiber j)) _)).trans
      (Category.id_comp _)
  rw [comp_app, h]

/-- A morphism out of `X` over `f ≫ g` factors through the coCartesian lift of `f`. -/
@[implicit_reducible]
private noncomputable def pushforwardDesc {n : FinPointed.{w}} (f : X.base ⟶ n) (g : n ⟶ Y.base)
    (φ : X ⟶ Y) (hφ : φ.base = f ≫ g) : X.pushforward f ⟶ Y :=
  (⟨g, fun l ↦ (listTensorFlatMapIso X.obj f.fiber (g.fiber l)).inv ≫
    (listTensorPermIso X.obj ((FinPointed.perm_fiber_comp f g l).symm.trans
      (.of_eq (congrArg (FinPointed.Hom.fiber · l) hφ.symm)))).hom ≫ φ.app l⟩ : Hom _ _)

private lemma pushforwardDesc_base {n : FinPointed.{w}} (f : X.base ⟶ n) (g : n ⟶ Y.base)
    (φ : X ⟶ Y) (hφ : φ.base = f ≫ g) : (pushforwardDesc f g φ hφ).base = g :=
  (rfl)

private lemma toPushforward_comp_pushforwardDesc {n : FinPointed.{w}} (f : X.base ⟶ n)
    (g : n ⟶ Y.base) (φ : X ⟶ Y) (hφ : φ.base = f ≫ g) :
    X.toPushforward f ≫ pushforwardDesc f g φ hφ = φ := by
  refine hom_ext hφ.symm fun l ↦ ?_
  rw [toPushforward_comp_app]
  dsimp only [pushforwardDesc]
  rw [Iso.hom_inv_id_assoc, listTensorPermIso_hom_listTensorPermIso_hom_assoc]

private lemma pushforwardDesc_toPushforward_comp {n : FinPointed.{w}} (f : X.base ⟶ n)
    (χ : X.pushforward f ⟶ Y) :
    pushforwardDesc f χ.base (X.toPushforward f ≫ χ) rfl = χ := by
  refine hom_ext rfl fun l ↦ ?_
  dsimp only [pushforwardDesc]
  rw [toPushforward_comp_app, listTensorPermIso_hom_listTensorPermIso_hom_assoc,
    listTensorPermIso_self, Iso.refl_hom, Category.id_comp, Iso.inv_hom_id_assoc,
    listTensorPermIso_self, Iso.refl_hom, Category.id_comp]

/-- **The coCartesian lifts of the category of operators.** The morphism `X ⟶ f_! X` over `f`
whose components are identities is strongly coCartesian: a morphism out of `X` over `f ≫ g`
factors uniquely through it by a morphism over `g`. -/
instance isStronglyCocartesian_toPushforward (X : CategoryOfOperators.{w} C)
    {n : FinPointed.{w}} (f : X.base ⟶ n) :
    (toFinPointed C).IsStronglyCocartesian f (X.toPushforward f) where
  toIsHomLift := isHomLift_base (X.toPushforward f)
  universal_property' {Y} g φ _ := by
    have hφ : φ.base = f ≫ g := isHomLift_iff.1 ‹_›
    refine ⟨pushforwardDesc f g φ hφ,
      ⟨isHomLift_iff.2 rfl, toPushforward_comp_pushforwardDesc f g φ hφ⟩, ?_⟩
    rintro χ ⟨hχ, rfl⟩
    obtain rfl : χ.base = g := isHomLift_iff.1 hχ
    exact (pushforwardDesc_toPushforward_comp f χ).symm

/-! ### The fibers -/

variable (C) in
/-- The inclusion `C^n ⥤ C^⊗` of the families over `⟨n⟩`, sending a family of maps to the
morphism over the identity of `⟨n⟩` that they give. -/
@[expose, implicit_reducible, simps obj]
noncomputable def ι (n : FinPointed.{w}) :
    (Fin n.len → C) ⥤ CategoryOfOperators.{w} C where
  obj Y := ⟨n, Y⟩
  map {Y Y'} φ := Hom.ofFamily (⟨n, Y⟩ : CategoryOfOperators.{w} C) (Y := Y') φ
  map_id Y := Hom.ofFamily_id _
  map_comp {Y Y' Y''} φ ψ := by
    refine hom_ext (Category.comp_id _).symm fun j ↦ ?_
    rw [comp_ofFamily_app]
    simp [Hom.ofFamily]

@[simp]
lemma ι_map_base {n : FinPointed.{w}} {Y Y' : Fin n.len → C} (φ : Y ⟶ Y') :
    ((ι C n).map φ).base = 𝟙 n :=
  rfl

@[simp]
lemma ι_map_app {n : FinPointed.{w}} {Y Y' : Fin n.len → C} (φ : Y ⟶ Y')
    (j : Fin n.len) :
    ((ι C n).map φ).app j =
      (listTensorPermIso Y (.of_eq (FinPointed.fiber_id j))).hom ≫ (ρ_ (Y j)).hom ≫ φ j := by
  simp [ι, Hom.ofFamily]

/-- The families over `⟨n⟩` lie over `⟨n⟩`. -/
lemma ι_comp_toFinPointed (n : FinPointed.{w}) :
    ι C n ⋙ toFinPointed C = (Functor.const _).obj n :=
  rfl

instance (n : FinPointed.{w}) : (ι C n).Faithful where
  map_injective {Y Y'} φ ψ h := by
    funext j
    have h' := congr_app h j
    rw [ι_map_app, ι_map_app] at h'
    simpa using h'

variable (C) in
/-- The inclusion of the families over `⟨n⟩`, as a functor `C^n ⥤ (C^⊗)_⟨n⟩` to the fiber
of `toFinPointed C` over `⟨n⟩`. It is an equivalence (`fiberEquivalence`). -/
noncomputable def toFiber (n : FinPointed.{w}) : (Fin n.len → C) ⥤ (toFinPointed C).Fiber n :=
  Functor.Fiber.inducedFunctor (ι_comp_toFinPointed n)

instance (n : FinPointed.{w}) : (toFiber C n).Faithful :=
  Functor.Faithful.of_comp_eq (Functor.Fiber.inducedFunctor_comp _)

/-- A morphism of families over `⟨n⟩` lying over the identity is a family of maps of their
members. -/
lemma exists_ι_map_eq {n : FinPointed.{w}} {Y Y' : Fin n.len → C}
    (χ : (ι C n).obj Y ⟶ (ι C n).obj Y') (hχ : χ.base = 𝟙 n) :
    ∃ φ : Y ⟶ Y', (ι C n).map φ = χ := by
  refine ⟨fun j ↦ (ρ_ (Y j)).inv ≫ (listTensorPermIso Y
      ((List.Perm.of_eq (FinPointed.fiber_id j)).symm.trans
        (.of_eq (congrArg (FinPointed.Hom.fiber · j) hχ.symm)))).hom ≫ χ.app j,
    hom_ext hχ.symm fun j ↦ ?_⟩
  rw [ι_map_app]
  simp [listTensorPermIso_hom_listTensorPermIso_hom_assoc]

instance (n : FinPointed.{w}) : (toFiber C n).Full where
  map_surjective {Y Y'} χ := by
    obtain ⟨φ, hφ⟩ := exists_ι_map_eq χ.val (isHomLift_iff.1 χ.property)
    exact ⟨φ, Functor.Fiber.hom_ext hφ⟩

instance (n : FinPointed.{w}) : (toFiber C n).EssSurj where
  mem_essImage := by
    rintro ⟨⟨b, Y⟩, rfl⟩
    exact ⟨Y, ⟨Iso.refl _⟩⟩

instance (n : FinPointed.{w}) : (toFiber C n).IsEquivalence where

variable (C) in
/-- **The Segal condition for the category of operators.** The fiber of `C^⊗` over `⟨n⟩` is
equivalent to `C^n`, by the inclusion of the families over `⟨n⟩`. -/
noncomputable def fiberEquivalence (n : FinPointed.{w}) :
    (Fin n.len → C) ≌ (toFinPointed C).Fiber n :=
  (toFiber C n).asEquivalence

end CategoryOfOperators

end TauCeti
