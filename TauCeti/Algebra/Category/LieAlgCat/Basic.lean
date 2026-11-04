/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.CategoryTheory.Elementwise

/-!
# Categories of Lie algebras and finite-dimensional Lie algebras

`TauCeti.LieAlgCat R` bundles Lie algebras over `R`, with Lie homomorphisms as morphisms.
`TauCeti.FGLieAlgCat R` is its full subcategory of algebras finite as modules. Over a field,
these are precisely the finite-dimensional Lie algebras.

The finite-dimensional real subcategory is the codomain for differentiation of Lie groups
and smooth homomorphisms.

## Main definitions and results

* `TauCeti.LieAlgCat`: the bundled category, with object constructor `of`.
* `TauCeti.LieAlgCat.isFG` and `TauCeti.FGLieAlgCat`: the finite-generation property and
  its full subcategory, with object constructor `FGLieAlgCat.of`.
* `TauCeti.LieAlgCat.Hom.hom` and `TauCeti.LieAlgCat.ofHom`: conversions between
  categorical morphisms and Lie homomorphisms.
* `TauCeti.LieAlgCat.hom_id`, `TauCeti.LieAlgCat.hom_comp`: identity and composition
  of the underlying Lie homomorphisms.
* `TauCeti.LieAlgCat.hom_ofHom`, `TauCeti.LieAlgCat.ofHom_hom`: the conversion laws.
* `TauCeti.LieAlgCat.ofHom_id`, `TauCeti.LieAlgCat.ofHom_comp`: conversion preserves
  identities and composition.
* `TauCeti.LieAlgCat.hom_ext`: equality of morphisms from their Lie homomorphisms.
* `LieEquiv.toLieAlgCatIso` and `CategoryTheory.Iso.toLieEquiv`: conversion between Lie
  equivalences and categorical isomorphisms, with inverse-application and round-trip laws.

## References

* Mathlib's `Mathlib.Algebra.Category.AlgCat.Basic`, for the concrete-category construction.
* Mathlib's `Mathlib.Algebra.Category.FGModuleCat.Basic`, for the finite-subcategory construction.
* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Corollary 3.44, for the real finite-dimensional category.
-/

public section

open CategoryTheory

universe u r

namespace TauCeti

/-- Lie algebras over a commutative ring. -/
structure LieAlgCat (R : Type r) [CommRing R] where
  /-- The underlying type. -/
  carrier : Type u
  /-- The additive group and Lie bracket. -/
  [lieRing : LieRing carrier]
  /-- The Lie algebra structure over `R`. -/
  [lieAlgebra : LieAlgebra R carrier]

attribute [instance] LieAlgCat.lieRing LieAlgCat.lieAlgebra

instance {R : Type r} [CommRing R] : CoeSort (LieAlgCat.{u} R) (Type u) :=
  ⟨LieAlgCat.carrier⟩

namespace LieAlgCat

variable {R : Type r} [CommRing R]

/-- Bundle a Lie algebra. -/
abbrev of (R : Type r) [CommRing R] (L : Type u) [LieRing L] [LieAlgebra R L] : LieAlgCat R := ⟨L⟩

/-- A Lie homomorphism between bundled Lie algebras. -/
@[ext]
structure Hom (L K : LieAlgCat.{u} R) where
  /-- The underlying Lie homomorphism. Use `Hom.hom` to access it. -/
  hom' : L →ₗ⁅R⁆ K

instance : Category (LieAlgCat.{u} R) where
  Hom L K := Hom L K
  id _ := ⟨1⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (LieAlgCat.{u} R) (fun L K ↦ L →ₗ⁅R⁆ K) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {L K M : LieAlgCat.{u} R}

/-- The Lie homomorphism underlying a categorical morphism. -/
abbrev Hom.hom (f : L ⟶ K) : L →ₗ⁅R⁆ K := ConcreteCategory.hom f

/-- Regard a Lie homomorphism as a categorical morphism. -/
abbrev ofHom (f : L →ₗ⁅R⁆ K) : L ⟶ K := ConcreteCategory.ofHom f

/-- The underlying homomorphism of the identity is the identity Lie homomorphism. -/
@[simp]
theorem hom_id : (𝟙 L : L ⟶ L).hom = 1 := rfl

/-- The underlying homomorphism of a composite is the composite of the underlying maps. -/
@[simp]
theorem hom_comp (f : L ⟶ K) (g : K ⟶ M) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- Constructing a categorical morphism preserves its underlying Lie homomorphism. -/
@[simp]
theorem hom_ofHom (f : L →ₗ⁅R⁆ K) : (ofHom f).hom = f := rfl

/-- A categorical morphism is recovered from its underlying Lie homomorphism. -/
@[simp]
theorem ofHom_hom (f : L ⟶ K) : ofHom f.hom = f := rfl

/-- Converting the identity Lie homomorphism gives the identity categorical morphism. -/
@[simp]
theorem ofHom_id : ofHom (1 : L →ₗ⁅R⁆ L) = 𝟙 L := rfl

/-- Converting a composite Lie homomorphism gives the composite categorical morphism. -/
@[simp]
theorem ofHom_comp (f : L →ₗ⁅R⁆ K) (g : K →ₗ⁅R⁆ M) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/-- Categorical morphisms are equal if their underlying Lie homomorphisms agree. -/
@[ext]
theorem hom_ext {f g : L ⟶ K} (h : f.hom = g.hom) : f = g := ConcreteCategory.ext h

end LieAlgCat

end TauCeti

variable {R : Type r} [CommRing R]

/-- A Lie equivalence gives an isomorphism of the associated Lie algebra objects. -/
def LieEquiv.toLieAlgCatIso {L K : Type u} [LieRing L] [LieAlgebra R L]
    [LieRing K] [LieAlgebra R K] (e : L ≃ₗ⁅R⁆ K) :
    TauCeti.LieAlgCat.of R L ≅ TauCeti.LieAlgCat.of R K where
  hom := TauCeti.LieAlgCat.ofHom e.toLieHom
  inv := TauCeti.LieAlgCat.ofHom e.symm.toLieHom
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

/-- The forward Lie homomorphism of the categorical isomorphism is the original map. -/
@[simp]
theorem LieEquiv.toLieAlgCatIso_hom_hom {L K : Type u} [LieRing L] [LieAlgebra R L]
    [LieRing K] [LieAlgebra R K] (e : L ≃ₗ⁅R⁆ K) : e.toLieAlgCatIso.hom.hom = e.toLieHom := by
  simp only [LieEquiv.toLieAlgCatIso, TauCeti.LieAlgCat.hom_ofHom]

/-- The inverse Lie homomorphism of the categorical isomorphism is the inverse map. -/
@[simp]
theorem LieEquiv.toLieAlgCatIso_inv_hom {L K : Type u} [LieRing L] [LieAlgebra R L]
    [LieRing K] [LieAlgebra R K] (e : L ≃ₗ⁅R⁆ K) : e.toLieAlgCatIso.inv.hom = e.symm.toLieHom := by
  simp only [LieEquiv.toLieAlgCatIso, TauCeti.LieAlgCat.hom_ofHom]

/-- An isomorphism of Lie algebra objects gives a Lie equivalence of their carriers. -/
def CategoryTheory.Iso.toLieEquiv {L K : TauCeti.LieAlgCat.{u} R} (e : L ≅ K) :
    L ≃ₗ⁅R⁆ K :=
  { e.hom.hom with
    invFun := e.inv.hom
    left_inv := CategoryTheory.Iso.hom_inv_id_apply e
    right_inv := CategoryTheory.Iso.inv_hom_id_apply e }

/-- The Lie homomorphism of an isomorphism's Lie equivalence is its forward map. -/
@[simp]
theorem CategoryTheory.Iso.toLieEquiv_toLieHom {L K : TauCeti.LieAlgCat.{u} R}
    (e : L ≅ K) : e.toLieEquiv.toLieHom = e.hom.hom := by
  simp only [CategoryTheory.Iso.toLieEquiv]

/-- The Lie equivalence associated to a categorical isomorphism applies its forward map. -/
@[simp]
theorem CategoryTheory.Iso.toLieEquiv_apply {L K : TauCeti.LieAlgCat.{u} R}
    (e : L ≅ K) (x : L) : e.toLieEquiv x = e.hom.hom x := by
  simp only [← LieEquiv.coe_toLieHom, toLieEquiv_toLieHom]

/-- The inverse Lie equivalence associated to an isomorphism applies its inverse map. -/
@[simp]
theorem CategoryTheory.Iso.toLieEquiv_symm_apply {L K : TauCeti.LieAlgCat.{u} R}
    (e : L ≅ K) (x : K) : e.toLieEquiv.symm x = e.inv.hom x := by
  simp only [LieEquiv.symm_apply_eq, toLieEquiv_apply, CategoryTheory.Iso.inv_hom_id_apply]

/-- Converting a Lie equivalence to a categorical isomorphism and back recovers it. -/
@[simp]
theorem LieEquiv.toLieAlgCatIso_toLieEquiv {L K : Type u} [LieRing L] [LieAlgebra R L]
    [LieRing K] [LieAlgebra R K] (e : L ≃ₗ⁅R⁆ K) : e.toLieAlgCatIso.toLieEquiv = e := by
  ext x
  rw [CategoryTheory.Iso.toLieEquiv_apply, LieEquiv.toLieAlgCatIso_hom_hom]
  exact congrFun (LieEquiv.coe_toLieHom e) x

/-- Converting a categorical isomorphism to a Lie equivalence and back recovers it. -/
@[simp]
theorem CategoryTheory.Iso.toLieEquiv_toLieAlgCatIso {L K : TauCeti.LieAlgCat.{u} R}
    (e : L ≅ K) : e.toLieEquiv.toLieAlgCatIso = e := by
  apply CategoryTheory.Iso.ext
  apply TauCeti.LieAlgCat.hom_ext
  simp only [LieEquiv.toLieAlgCatIso_hom_hom, CategoryTheory.Iso.toLieEquiv_toLieHom]
namespace TauCeti

/-- Finite generation of the underlying module of a Lie algebra. -/
abbrev LieAlgCat.isFG (R : Type r) [CommRing R] : ObjectProperty (LieAlgCat.{u} R) :=
  fun L ↦ Module.Finite R L

/-- The full subcategory of Lie algebras finite as modules. -/
abbrev FGLieAlgCat (R : Type r) [CommRing R] := (LieAlgCat.isFG.{u} R).FullSubcategory

instance {R : Type r} [CommRing R] : CoeSort (FGLieAlgCat.{u} R) (Type u) :=
  ⟨fun L ↦ L.obj⟩

instance {R : Type r} [CommRing R] (L : FGLieAlgCat.{u} R) : LieRing L :=
  inferInstanceAs (LieRing L.obj)

instance {R : Type r} [CommRing R] (L : FGLieAlgCat.{u} R) : LieAlgebra R L :=
  inferInstanceAs (LieAlgebra R L.obj)

instance {R : Type r} [CommRing R] (L : FGLieAlgCat.{u} R) : Module.Finite R L := L.property

/-- Bundle a Lie algebra whose underlying module is finitely generated. -/
abbrev FGLieAlgCat.of (R : Type r) [CommRing R] (L : Type u) [LieRing L] [LieAlgebra R L]
    [Module.Finite R L] : FGLieAlgCat R :=
  ⟨LieAlgCat.of R L, inferInstanceAs (Module.Finite R L)⟩

end TauCeti
