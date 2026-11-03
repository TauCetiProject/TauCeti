/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Center.Linear
public import TauCeti.CategoryTheory.Semisimple.Basic
public import TauCeti.CategoryTheory.Simple.Classes

/-!
# Central endomorphisms from scalars on simple objects

Let `C` be a finite semisimple `R`-linear category. A family of scalars `c : SimpleClasses C → R`
indexed by the isomorphism classes of simple objects determines a natural endomorphism of the
identity functor of `C`, that is, an element of Mathlib's centre `CatCenter C`: it acts on every
simple object `S` as multiplication by `c [S]`, and on an arbitrary object through any
decomposition into simple objects. The construction does not depend on the decomposition,
because a morphism from a simple object `S` into `X` is followed by the endomorphism exactly when
it is multiplied by `c [S]`, and such morphisms are jointly epimorphic.

This is how the scalars of a character of the universal grading group act on a fusion category.
The construction is a ring homomorphism, so invertible families of scalars give natural
automorphisms of the identity.

## Main declarations

* `TauCeti.simpleScalarsToCatCenter`: the ring homomorphism `(SimpleClasses C → R) →+* CatCenter C`;
* `TauCeti.comp_simpleScalarsToCatCenter_app`: precomposed with a morphism `s` out of a simple
  object `S`, the central endomorphism given by `c` is `c [S] • s`;
* `TauCeti.simpleScalarsToCatCenter_app_of_simple`: on a simple object `X` it is `c [X] • 𝟙 X`;
* `CategoryTheory.CatCenter.eq_simpleScalarsToCatCenter_iff`: a central endomorphism is the one
  given by `c` exactly when it acts on every simple object `X` by `c [X]`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u w

variable (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Abelian C] [Linear R C]
  [IsFiniteSemisimpleCategory C]

variable {R C} in
/-- Every object has an endomorphism through which each morphism `s` from a simple object `S`
factors as `c [S] • s`: on a decomposition into simple objects, scale each summand. -/
private theorem exists_comp_eq_smul (c : SimpleClasses C → R) (X : C) :
    ∃ a : X ⟶ X, ∀ (S : C) [Simple S] (s : S ⟶ X), s ≫ a = c (SimpleClasses.classOf S) • s := by
  obtain ⟨ι, _, b, _, _, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples X
  let m := biproduct.map fun i ↦ c (SimpleClasses.classOf (b i)) • 𝟙 (b i)
  refine ⟨e.hom ≫ m ≫ e.inv, fun S _ s ↦ ?_⟩
  -- Each component `S ⟶ b i` is zero or an isomorphism, so it scales by `c [S]` either way.
  have h : s ≫ e.hom ≫ m = c (SimpleClasses.classOf S) • (s ≫ e.hom) := by
    refine biproduct.hom_ext _ _ fun i ↦ ?_
    simp only [m, Category.assoc, biproduct.map_π, Linear.comp_smul, Category.comp_id,
      Linear.smul_comp]
    by_cases hs : s ≫ e.hom ≫ biproduct.π b i = 0
    · simp [hs]
    · rw [SimpleClasses.classOf_eq_of_ne_zero hs]
  rw [reassoc_of% h, Linear.smul_comp, Category.assoc, e.hom_inv_id, Category.comp_id]

variable {R C} in
/-- The component at `X` of the central endomorphism given by scalars on simple classes. -/
private def app (c : SimpleClasses C → R) (X : C) : X ⟶ X :=
  (exists_comp_eq_smul c X).choose

variable {R C} in
private theorem comp_app (c : SimpleClasses C → R) {S X : C} [Simple S] (s : S ⟶ X) :
    s ≫ app c X = c (SimpleClasses.classOf S) • s :=
  (exists_comp_eq_smul c X).choose_spec S s

variable {R C} in
/-- The central endomorphism given by scalars on simple classes, before it is bundled into a ring
homomorphism. -/
private def toCatCenter (c : SimpleClasses C → R) : CatCenter C := End.of
  { app := app c
    naturality X Y f := (𝟭 C).hom_ext_of_simple fun S _ s ↦ by
      dsimp only [Functor.id_map, Functor.id_obj]
      rw [← Category.assoc, comp_app, ← Category.assoc, comp_app, Linear.smul_comp] }

variable {R C} in
private theorem comp_toCatCenter_app (c : SimpleClasses C → R) {S X : C} [Simple S]
    (s : S ⟶ X) : s ≫ (toCatCenter c).app X = c (SimpleClasses.classOf S) • s :=
  comp_app c s

/-- The ring homomorphism sending scalars indexed by the simple classes of a finite semisimple
`R`-linear category to the natural endomorphism of the identity functor acting on each simple
object `S` by the scalar of its class. -/
def simpleScalarsToCatCenter : (SimpleClasses C → R) →+* CatCenter C where
  toFun := toCatCenter
  map_one' := CatCenter.ext _ _ fun X ↦ (𝟭 C).hom_ext_of_simple fun S _ s ↦ by
    simp [comp_toCatCenter_app]
  map_mul' c d := CatCenter.ext _ _ fun X ↦ (𝟭 C).hom_ext_of_simple fun S _ s ↦ by
    dsimp only [Functor.id_map, Functor.id_obj]
    rw [CatCenter.mul_app, ← Category.assoc, comp_toCatCenter_app c s, Linear.smul_comp,
      comp_toCatCenter_app d s, comp_toCatCenter_app, Pi.mul_apply, mul_smul]
  map_zero' := CatCenter.ext _ _ fun X ↦ (𝟭 C).hom_ext_of_simple fun S _ s ↦ by
    simp [comp_toCatCenter_app]
  map_add' c d := CatCenter.ext _ _ fun X ↦ (𝟭 C).hom_ext_of_simple fun S _ s ↦ by
    simp [comp_toCatCenter_app, add_smul]

variable {R C}

/-- Precomposed with a morphism `s` out of a simple object `S`, the central endomorphism given by
scalars `c` on simple classes is multiplication of `s` by `c [S]`. -/
@[reassoc]
theorem comp_simpleScalarsToCatCenter_app (c : SimpleClasses C → R) {S X : C} [Simple S]
    (s : S ⟶ X) :
    s ≫ (simpleScalarsToCatCenter R C c).app X = c (SimpleClasses.classOf S) • s :=
  comp_toCatCenter_app c s

/-- The central endomorphism given by scalars `c` on simple classes acts on a simple object `X` as
multiplication by `c [X]`. -/
@[simp]
theorem simpleScalarsToCatCenter_app_of_simple (c : SimpleClasses C → R) (X : C) [Simple X] :
    (simpleScalarsToCatCenter R C c).app X = c (SimpleClasses.classOf X) • 𝟙 X := by
  simpa using comp_simpleScalarsToCatCenter_app c (𝟙 X)

/-- A natural endomorphism of the identity functor is the one given by scalars `c` on simple
classes exactly when it acts on every simple object `X` as multiplication by `c [X]`. -/
theorem _root_.CategoryTheory.CatCenter.eq_simpleScalarsToCatCenter_iff (z : CatCenter C)
    (c : SimpleClasses C → R) :
    z = simpleScalarsToCatCenter R C c ↔
      ∀ (X : C) [Simple X], z.app X = c (SimpleClasses.classOf X) • 𝟙 X := by
  refine ⟨fun h X _ ↦ by simp [h], fun h ↦ ?_⟩
  exact CatCenter.ext _ _ fun X ↦ (𝟭 C).hom_ext_of_simple fun S _ s ↦ by
    dsimp only [Functor.id_map, Functor.id_obj]
    rw [comp_simpleScalarsToCatCenter_app, CatCenter.naturality, h,
      Linear.smul_comp, Category.id_comp]

end TauCeti
