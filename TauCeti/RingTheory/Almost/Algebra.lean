/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.CommMon
public import TauCeti.CategoryTheory.Monoidal.Internal.Module
public import TauCeti.RingTheory.Almost.Monoidal

/-!
# Almost algebras over a basic setup

Let `S = (V, m)` be a basic setup. An *almost `V`-algebra* is a commutative unital monoid object
in the symmetric monoidal category `TauCeti.Almost.Module S` of almost `V`-modules, with monoid
morphisms (Gabber–Ramero §2.2). Almost commutative algebra, such as almost finite
étale algebras and the almost purity theorem for perfectoid rings, takes place in this category.

Almostification `M ↦ M^a` is braided monoidal, so it sends commutative monoid objects of
`ModuleCat V`, that is commutative `V`-algebras, to almost algebras. This gives the functor
`R ↦ R^a` from commutative `V`-algebras to almost `V`-algebras, whose underlying almost module is
the almostification of the underlying `V`-module of `R`. It inverts exactly the algebra maps that
are almost isomorphisms, and `R^a` is zero exactly when `m` maps to zero in `R`; in particular
`(V ⧸ m)^a = 0`. For the classical setup `(V, V)` it is full and faithful.

Conversely, the functor of almost elements `M ↦ M_* = Hom(V^a, M)` is lax braided, so for an
almost algebra `A` the `V`-module `A_*` is a commutative `V`-algebra, with product
`a · b = μ ∘ (a ⊗ b) ∘ (V^a ≅ V^a ⊗ V^a)`. The adjunction `M ↦ M^a ⊣ M ↦ M_*` of almost modules
lifts to an adjunction `R ↦ R^a ⊣ A ↦ A_*` between commutative `V`-algebras and almost algebras
whose counit `(A_*)^a → A` is an isomorphism. Hence `A ↦ A_*` is fully faithful, morphisms of
almost algebras `A → B` are the same as `V`-algebra maps `A_* → B_*`, and every almost algebra is
of the form `R^a`. For every `V`-algebra `R`, the unit `R → (R^a)_*` is an almost isomorphism; for
the classical setup it is an isomorphism, and almostification of algebras is an equivalence.

## Main definitions

* `TauCeti.Almost.Algebra`: the category `CommMon (Almost.Module S)` of almost `V`-algebras.
* `TauCeti.Almost.Algebra.toAlmost`: the almostification functor `R ↦ R^a` from commutative
  `V`-algebras to almost `V`-algebras.
* `TauCeti.Almost.Algebra.elements`: the functor `A ↦ A_*` of almost elements, from almost
  `V`-algebras to commutative `V`-algebras.
* `TauCeti.Almost.Algebra.adj`: the adjunction `toAlmost S ⊣ elements S`.
* `TauCeti.Almost.Algebra.counitIso`: the counit isomorphism `(A_*)^a ≅ A`.
* `TauCeti.Almost.Algebra.homEquiv`: morphisms `A ⟶ B` of almost algebras are `V`-algebra maps
  `A_* →ₐ[V] B_*`.
* `TauCeti.Almost.Algebra.classicalEquiv`: for the classical setup, almostification is an
  equivalence `CommAlgCat V ≌ Algebra (BasicSetup.classical V)`.

## Main results

* `TauCeti.Almost.Algebra.toAlmost_obj_X`: the underlying almost module of `R^a` is the
  almostification of the underlying `V`-module of `R`.
* `TauCeti.Almost.Algebra.isIso_toAlmost_map_iff`: `f^a` is an isomorphism of almost algebras
  iff `f` is an almost isomorphism of `V`-modules.
* `TauCeti.Almost.Algebra.isZero_toAlmost_obj_X_iff`: `R^a` is zero iff `m` is contained in the
  kernel of `V → R`.
* `TauCeti.Almost.Algebra.elements_one`, `TauCeti.Almost.Algebra.elements_mul`: the unit and
  the product of the algebra `A_*` of almost elements.
* `TauCeti.Almost.Algebra.fullyFaithfulElements`: `A ↦ A_*` is fully faithful, and
  `TauCeti.Almost.Algebra.essSurj_toAlmost`: every almost algebra is `R^a` for some `R`.
* `TauCeti.Almost.Algebra.isAlmostIso_adj_unit_app`: the unit `R → (R^a)_*` is an almost
  isomorphism.
* `TauCeti.Almost.Algebra.full_toAlmost_classical`,
  `TauCeti.Almost.Algebra.faithful_toAlmost_classical` and
  `TauCeti.Almost.Algebra.isEquivalence_toAlmost_classical`: for the classical setup,
  almostification of algebras is an equivalence.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.2, Remark 4.2.8.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped MonObj

namespace TauCeti.Almost

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- The category of **almost `V`-algebras** for a basic setup `S = (V, m)`: commutative monoid
objects in the symmetric monoidal category of almost `V`-modules (Gabber–Ramero §2.2; Scholze,
*Perfectoid spaces*, §4). -/
abbrev Algebra : Type (u + 1) :=
  CommMon (Module S)

namespace Algebra

/-- The **almostification** functor `R ↦ R^a` from commutative `V`-algebras to almost
`V`-algebras: a commutative `V`-algebra is a commutative monoid object in `ModuleCat V`, and the
braided monoidal functor `Almost.Module.toAlmost S` sends it to a commutative monoid object in
almost modules. -/
@[expose]
noncomputable def toAlmost : CommAlgCat.{u} V ⥤ Algebra S :=
  ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse ⋙ (Module.toAlmost S).mapCommMon

/-- The underlying almost module of `R^a` is the almostification of the underlying `V`-module of
`R`. -/
@[simp]
theorem toAlmost_obj_X (R : CommAlgCat.{u} V) :
    ((toAlmost S).obj R).X = (Module.toAlmost S).obj (ModuleCat.of V R) :=
  (rfl)

/-- The underlying morphism of almost modules of `f^a` is the almostification of the underlying
linear map of `f`. -/
@[simp]
theorem toAlmost_map_hom_hom {R R' : CommAlgCat.{u} V} (f : R ⟶ R') :
    ((toAlmost S).map f).hom.hom = (Module.toAlmost S).map (ModuleCat.ofHom f.hom.toLinearMap) :=
  (rfl)

/-- The unit of `R^a` is the almostification of the unit `V → R` of `R`. -/
@[simp]
theorem toAlmost_obj_one (R : CommAlgCat.{u} V) :
    η[((toAlmost S).obj R).X] = Functor.LaxMonoidal.ε (Module.toAlmost S) ≫
      (Module.toAlmost S).map (ModuleCat.ofHom (Algebra.linearMap V R)) :=
  rfl

/-- The multiplication of `R^a` is the almostification of the multiplication `R ⊗[V] R → R`
of `R`. -/
@[simp]
theorem toAlmost_obj_mul (R : CommAlgCat.{u} V) :
    μ[((toAlmost S).obj R).X] =
      Functor.LaxMonoidal.μ (Module.toAlmost S) (ModuleCat.of V R) (ModuleCat.of V R) ≫
        (Module.toAlmost S).map (ModuleCat.ofHom (LinearMap.mul' V R)) :=
  rfl

/-- **`f^a` is an isomorphism iff `f` is an almost isomorphism.** An algebra map becomes invertible
after almostification exactly when its kernel and cokernel are killed by `m`. -/
@[simp]
theorem isIso_toAlmost_map_iff {R R' : CommAlgCat.{u} V} (f : R ⟶ R') :
    IsIso ((toAlmost S).map f) ↔ S.IsAlmostIso f.hom.toLinearMap := by
  rw [← ModuleCat.hom_ofHom f.hom.toLinearMap, ← Module.isIso_toAlmost_map_iff,
    ← toAlmost_map_hom_hom]
  -- The underlying morphism `g.hom.hom` of a homomorphism `g` of commutative monoid objects is
  -- `(CommMon.forget _).map g` by definition.
  exact (isIso_iff_of_reflects_iso _ (CommMon.forget (Module S))).symm

/-- **`R^a` is zero iff `m` maps to zero in `R`.** -/
theorem isZero_toAlmost_obj_X_iff (R : CommAlgCat.{u} V) :
    IsZero ((toAlmost S).obj R).X ↔ S.ideal ≤ RingHom.ker (algebraMap V R) := by
  rw [toAlmost_obj_X, Module.isZero_toAlmost_obj_iff, BasicSetup.isAlmostZero_iff]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε x ↦ ?_⟩
  · simpa [Algebra.smul_def] using h ε hε 1
  · simp [Algebra.smul_def, RingHom.mem_ker.mp (h hε)]

/-- For the classical setup `(V, V)`, almostification of algebras is full. -/
instance full_toAlmost_classical : (toAlmost (BasicSetup.classical V)).Full :=
  inferInstanceAs (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse ⋙
    (Module.toAlmost (BasicSetup.classical V)).mapCommMon).Full

/-- For the classical setup `(V, V)`, almostification of algebras is faithful. -/
instance faithful_toAlmost_classical : (toAlmost (BasicSetup.classical V)).Faithful :=
  inferInstanceAs (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse ⋙
    (Module.toAlmost (BasicSetup.classical V)).mapCommMon).Faithful

/-! ### Almost elements of almost algebras -/

/-- The functor of **almost elements** `A ↦ A_* = Hom(V^a, A)` from almost `V`-algebras to
commutative `V`-algebras: the lax braided functor `Almost.Module.elements S` sends commutative
monoid objects of almost modules to commutative `V`-algebras. The product of `A_*` is described by
`elements_one` and `elements_mul` (Gabber–Ramero §2.2; Scholze, *Perfectoid spaces*, §4). -/
@[expose]
noncomputable def elements : Algebra S ⥤ CommAlgCat.{u} V :=
  (Module.elements S).mapCommMon ⋙ ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor

/-- The underlying type of the algebra `A_*` of almost elements is `Hom(V^a, A)`. -/
theorem elements_obj_carrier (A : Algebra S) :
    ((elements S).obj A : Type u) = ((Module.toAlmost S).obj (ModuleCat.of V V) ⟶ A.X) :=
  (rfl)

/-- A morphism `f : A ⟶ B` of almost algebras acts on almost elements by composition. -/
@[simp]
theorem elements_map_apply {A B : Algebra S} (f : A ⟶ B) (x : (elements S).obj A) :
    (elements S).map f x =
      (x : (Module.toAlmost S).obj (ModuleCat.of V V) ⟶ A.X) ≫ f.hom.hom :=
  (rfl)

/-- The unit of the algebra `A_*` is the almost element `V^a ≅ 𝟙_ → A` given by the unit of
`A`. -/
theorem elements_one (A : Algebra S) :
    ((1 : (elements S).obj A) : (Module.toAlmost S).obj (ModuleCat.of V V) ⟶ A.X) =
      Functor.OplaxMonoidal.η (Module.toAlmost S) ≫ η[A.X] :=
  congrArg (· ≫ η[A.X]) (Module.elements_ε_hom_apply_one S)

/-- The product of two almost elements `x, y : V^a → A` is the composite
`V^a ≅ V^a ⊗ V^a → A ⊗ A → A` of `x ⊗ y` with the multiplication of `A`. -/
theorem elements_mul (A : Algebra S) (x y : (elements S).obj A) :
    ((x * y : (elements S).obj A) : (Module.toAlmost S).obj (ModuleCat.of V V) ⟶ A.X) =
      (λ_ ((Module.toAlmost S).obj (𝟙_ (ModuleCat.{u} V)))).inv ≫
        Functor.LaxMonoidal.ε (Module.toAlmost S) ▷ _ ≫
          ((x : (Module.toAlmost S).obj (ModuleCat.of V V) ⟶ A.X) ⊗ₘ y) ≫ μ[A.X] :=
  (congrArg (· ≫ μ[A.X]) (Module.elements_μ_hom_tmul S A.X A.X x y)).trans
    -- The two sides differ by reassociation and by unfolding `V^a = (𝟙_ (ModuleCat V))^a`.
    (by simp only [Category.assoc]; rfl)

/-- **Almostification of algebras is left adjoint to almost elements** `A ↦ A_*`: the adjunction
`Almost.Module.adjElements` of almost modules lifted to commutative monoid objects (Scholze,
*Perfectoid spaces*, §4; Bhatt, Remark 4.2.8). -/
noncomputable def adj : toAlmost S ⊣ elements S :=
  ModuleCat.commMonModuleEquivalenceCommAlgebra.symm.toAdjunction.comp
    (Module.adjElements S).mapCommMon

/-- The unit `R → (R^a)_*` sends `r` to the almostification of the map `V → R`, `1 ↦ r`. -/
@[simp]
theorem adj_unit_app_apply (R : CommAlgCat.{u} V) (r : R) :
    ConcreteCategory.hom (C := CommAlgCat.{u} V) (X := R)
      (Y := (elements S).obj ((toAlmost S).obj R)) ((adj S).unit.app R) r =
      (Module.toAlmost S).map (ModuleCat.ofHom (LinearMap.toSpanSingleton V R r)) :=
  Module.adjElements_unit_app_hom_apply S (ModuleCat.of V R) r

/-- The counit `(A_*)^a → A` is the counit of the adjunction of almost modules. -/
@[simp]
theorem adj_counit_app_hom_hom (A : Algebra S) :
    ((adj S).counit.app A).hom.hom = (Module.adjElements S).counit.app A.X := by
  -- The counit is assembled from the counit of `Module.adjElements S` and identities, among
  -- them the unit of the equivalence `CommMon (ModuleCat V) ≌ CommAlgCat V`.
  have h : (Module.toAlmost S).map (ModuleCat.commMonModuleEquivalenceCommAlgebra.unitInv.app
      ((Module.elements S).mapCommMon.obj A)).hom.hom = 𝟙 _ :=
    (Module.toAlmost S).map_id _
  simp only [Functor.comp_obj, Functor.id_obj, adj, Equivalence.symm_functor,
    Equivalence.symm_inverse, Adjunction.comp_counit_app, Equivalence.toAdjunction_counit,
    Equivalence.symm_counit, Adjunction.mapCommMon_counit, NatTrans.comp_app, CommMon.comp_hom,
    Functor.mapCommMon_map_hom_hom, Functor.mapCommMonCompIso_inv_app_hom_hom,
    Functor.mapCommMonNatTrans_app_hom_hom, Functor.mapCommMonIdIso_hom_app_hom_hom]
  refine (congrArg (· ≫ _) h).trans ?_
  exact (Category.id_comp _).trans ((Category.id_comp _).trans (Category.comp_id _))

/-- The counit `(A_*)^a → A` is an isomorphism, since almost elements of almost modules form a
fully faithful functor. -/
instance isIso_adj_counit : IsIso (adj S).counit := by
  have (A : Algebra S) : IsIso ((adj S).counit.app A) := by
    refine (isIso_iff_of_reflects_iso _ (CommMon.forget (Module S))).mp ?_
    have : IsIso ((Module.adjElements S).counit.app A.X) := inferInstance
    rw [CommMon.forget_map, adj_counit_app_hom_hom]
    exact this
  exact NatIso.isIso_of_isIso_app _

/-- **Almost elements of almost algebras form a fully faithful functor**, since the counit
`(A_*)^a → A` is an isomorphism. -/
noncomputable def fullyFaithfulElements : (elements S).FullyFaithful :=
  (adj S).fullyFaithfulROfIsIsoCounit

instance : (elements S).Full :=
  (fullyFaithfulElements S).full

instance : (elements S).Faithful :=
  (fullyFaithfulElements S).faithful

/-- Almost algebras form a reflective subcategory of commutative `V`-algebras, through almost
elements. -/
noncomputable instance : Reflective (elements S) where
  L := toAlmost S
  adj := adj S

instance : (toAlmost S).IsLeftAdjoint :=
  (adj S).isLeftAdjoint

/-- **Almost algebras form a complete category**, as a reflective subcategory of commutative
`V`-algebras. -/
instance hasLimits : HasLimits (Algebra S) :=
  hasLimits_of_reflective (elements S)

/-- **Almost algebras form a cocomplete category**, as a reflective subcategory of commutative
`V`-algebras. -/
instance hasColimits : HasColimits (Algebra S) :=
  hasColimits_of_reflective (elements S)

/-- The counit isomorphism `(A_*)^a ≅ A` of the adjunction `toAlmost S ⊣ elements S`. -/
noncomputable def counitIso : elements S ⋙ toAlmost S ≅ 𝟭 (Algebra S) :=
  asIso (adj S).counit

@[simp]
theorem counitIso_hom : (counitIso S).hom = (adj S).counit :=
  (rfl)

@[simp]
theorem counitIso_inv : (counitIso S).inv = inv (adj S).counit :=
  (rfl)

/-- **Every almost algebra is the almostification of a `V`-algebra**, namely of its algebra of
almost elements. -/
instance essSurj_toAlmost : (toAlmost S).EssSurj where
  mem_essImage A := ⟨(elements S).obj A, ⟨(counitIso S).app A⟩⟩

/-- **Morphisms of almost algebras are algebra maps of almost elements**: `f ↦ f_*` is a bijection
from `A ⟶ B` to `A_* →ₐ[V] B_*`. -/
noncomputable def homEquiv (A B : Algebra S) :
    (A ⟶ B) ≃ ((elements S).obj A →ₐ[V] (elements S).obj B) :=
  (fullyFaithfulElements S).homEquiv.trans (ConcreteCategory.homEquiv (C := CommAlgCat.{u} V))

/-- The algebra map `A_* →ₐ[V] B_*` of `f : A ⟶ B` is `(elements S).map f`; it acts by composition
(`elements_map_apply`). -/
@[simp]
theorem homEquiv_apply {A B : Algebra S} (f : A ⟶ B) :
    homEquiv S A B f = ((elements S).map f).hom :=
  (rfl)

/-- The morphism of almost algebras corresponding to an algebra map `g : A_* →ₐ[V] B_*` acts on
almost elements by `g`. -/
@[simp]
theorem elements_map_homEquiv_symm_apply {A B : Algebra S}
    (g : (elements S).obj A →ₐ[V] (elements S).obj B) :
    (elements S).map ((homEquiv S A B).symm g) = CommAlgCat.ofHom g := by
  ext1
  rw [← homEquiv_apply, Equiv.apply_symm_apply, CommAlgCat.hom_ofHom]

/-- The morphism of almost algebras corresponding to an algebra map `g : A_* →ₐ[V] B_*` is
`A ≅ (A_*)^a → (B_*)^a ≅ B`. -/
theorem homEquiv_symm_apply {A B : Algebra S}
    (g : (elements S).obj A →ₐ[V] (elements S).obj B) :
    (homEquiv S A B).symm g = inv ((adj S).counit.app A) ≫
      (toAlmost S).map (ConcreteCategory.ofHom (C := CommAlgCat.{u} V) g) ≫
        (adj S).counit.app B :=
  (rfl)

/-- For every commutative `V`-algebra `R`, the unit `R → (R^a)_*` is an almost isomorphism. -/
theorem isAlmostIso_adj_unit_app (R : CommAlgCat.{u} V) :
    S.IsAlmostIso ((adj S).unit.app R).hom.toLinearMap := by
  rw [← isIso_toAlmost_map_iff]
  infer_instance

/-- For the classical setup `(V, V)`, almostification of algebras is an equivalence of
categories. -/
instance isEquivalence_toAlmost_classical : (toAlmost (BasicSetup.classical V)).IsEquivalence where

/-- For the classical setup `(V, V)`, almostification is an equivalence between commutative
`V`-algebras and almost `V`-algebras. -/
noncomputable def classicalEquiv : CommAlgCat.{u} V ≌ Algebra (BasicSetup.classical V) :=
  (toAlmost (BasicSetup.classical V)).asEquivalence

@[simp]
theorem classicalEquiv_functor :
    (classicalEquiv (V := V)).functor = toAlmost (BasicSetup.classical V) :=
  (rfl)

end Algebra

end TauCeti.Almost
