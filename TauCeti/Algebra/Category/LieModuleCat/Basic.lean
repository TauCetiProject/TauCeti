/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.RingTheory.Finiteness.Prod
public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.Algebra.Lie.Prod

/-!
# Categories of Lie modules and of finite Lie modules

For a Lie algebra `L` over a commutative ring `R`, `TauCeti.LieModuleCat R L` bundles the
`L`-modules over `R`, with morphisms the morphisms of Lie modules `M →ₗ⁅R,L⁆ N`.
`TauCeti.FGLieModuleCat R L` is its full subcategory of modules finite over `R`; over a field
these are the finite-dimensional representations of `L`.

Both categories are preadditive, with the pointwise addition of morphisms, and have binary
biproducts, given by the product `M × N` with its componentwise action
(`TauCeti.Prod.instLieRingModule`). These are the structures the split Grothendieck group
`TauCeti.SplitK0` needs, so that isomorphism classes of finite-dimensional representations can be
added.

## Main definitions

* `TauCeti.LieModuleCat`: the bundled category, with object constructor `LieModuleCat.of`.
* `TauCeti.LieModuleCat.Hom.hom` and `TauCeti.LieModuleCat.ofHom`: conversions between
  categorical morphisms and morphisms of Lie modules; `TauCeti.FGLieModuleCat.ofHom` is the
  analogue of `ofHom` for finite Lie modules.
* `LieModuleEquiv.toLieModuleCatIso` and `CategoryTheory.Iso.toLieModuleEquiv`: conversion between
  equivalences of Lie modules and categorical isomorphisms; `LieModuleEquiv.toFGLieModuleCatIso`
  and `CategoryTheory.Iso.fgLieModuleCatIsoToLieModuleEquiv` are their analogues for finite Lie
  modules.
* `TauCeti.LieModuleCat.binaryBicone`: the product bicone on `M × N`, a biproduct by
  `TauCeti.LieModuleCat.binaryBiconeIsBilimit`.
* `TauCeti.LieModuleCat.biprodIsoProd` and `TauCeti.FGLieModuleCat.biprodLieModuleEquiv`: the
  identifications of the chosen biproduct `M ⊞ N` with the product `M × N`, under which the
  biproduct projections and inclusions are those of `M × N`
  (`TauCeti.LieModuleCat.biprodIsoProd_inv_comp_fst`,
  `TauCeti.LieModuleCat.inl_comp_biprodIsoProd_hom`,
  `TauCeti.FGLieModuleCat.biprodLieModuleEquiv_apply`,
  `TauCeti.FGLieModuleCat.biprodLieModuleEquiv_symm_apply`, ...).
* `TauCeti.LieModuleCat.isFG` and `TauCeti.FGLieModuleCat`: the finiteness property and its full
  subcategory, with object constructor `FGLieModuleCat.of`.

## References

* Mathlib's `Mathlib.Algebra.Category.ModuleCat.Basic`, for the concrete-category and preadditive
  constructions.
* Tau Ceti's `TauCeti.Algebra.Category.LieAlgCat.Basic`, for the finite full subcategory.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace TauCeti

/-- Modules over a Lie algebra `L` over a commutative ring `R`. -/
structure LieModuleCat (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L] where
  /-- The underlying type. -/
  carrier : Type w
  /-- The additive group structure. -/
  [isAddCommGroup : AddCommGroup carrier]
  /-- The module structure over `R`. -/
  [isModule : Module R carrier]
  /-- The action of `L`. -/
  [isLieRingModule : LieRingModule L carrier]
  /-- The compatibility of the action of `L` with the scalars. -/
  [isLieModule : LieModule R L carrier]

attribute [instance] LieModuleCat.isAddCommGroup LieModuleCat.isModule
  LieModuleCat.isLieRingModule LieModuleCat.isLieModule

namespace LieModuleCat

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

instance : CoeSort (LieModuleCat.{w} R L) (Type w) :=
  ⟨LieModuleCat.carrier⟩

/-- Bundle a Lie module. -/
abbrev of (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L] (M : Type w)
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] : LieModuleCat.{w} R L :=
  ⟨M⟩

/-- A morphism of Lie modules between bundled Lie modules. -/
@[ext]
structure Hom (M N : LieModuleCat.{w} R L) where
  /-- The underlying morphism of Lie modules. Use `Hom.hom` to access it. -/
  hom' : M →ₗ⁅R,L⁆ N

instance : Category (LieModuleCat.{w} R L) where
  Hom M N := Hom M N
  id M := ⟨LieModuleHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (LieModuleCat.{w} R L) (fun M N ↦ M →ₗ⁅R,L⁆ N) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {M N P : LieModuleCat.{w} R L}
variable {X Y Z : Type w} [AddCommGroup X] [Module R X] [LieRingModule L X] [LieModule R L X]
  [AddCommGroup Y] [Module R Y] [LieRingModule L Y] [LieModule R L Y]
  [AddCommGroup Z] [Module R Z] [LieRingModule L Z] [LieModule R L Z]

/-- The morphism of Lie modules underlying a categorical morphism. -/
abbrev Hom.hom (f : M ⟶ N) : M →ₗ⁅R,L⁆ N := ConcreteCategory.hom f

/-- Regard a morphism of Lie modules as a categorical morphism. -/
abbrev ofHom (f : X →ₗ⁅R,L⁆ Y) : of R L X ⟶ of R L Y := ConcreteCategory.ofHom f

/-- The underlying morphism of the identity is the identity morphism of Lie modules. -/
@[simp]
theorem hom_id : (𝟙 M : M ⟶ M).hom = LieModuleHom.id := rfl

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
@[simp]
theorem hom_comp (f : M ⟶ N) (g : N ⟶ P) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- Constructing a categorical morphism preserves its underlying morphism. -/
@[simp]
theorem hom_ofHom (f : X →ₗ⁅R,L⁆ Y) : (ofHom f).hom = f := rfl

/-- A categorical morphism is recovered from its underlying morphism. -/
@[simp]
theorem ofHom_hom (f : M ⟶ N) : ofHom f.hom = f := rfl

/-- The identity morphism of Lie modules gives the identity morphism. -/
@[simp]
theorem ofHom_id : ofHom (LieModuleHom.id : X →ₗ⁅R,L⁆ X) = 𝟙 (of R L X) := rfl

/-- A composite of morphisms of Lie modules gives the composite of the categorical morphisms. -/
@[simp]
theorem ofHom_comp (f : X →ₗ⁅R,L⁆ Y) (g : Y →ₗ⁅R,L⁆ Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/-- Categorical morphisms are equal if their underlying morphisms agree. -/
@[ext]
theorem hom_ext {f g : M ⟶ N} (h : f.hom = g.hom) : f = g := ConcreteCategory.ext h

/-- Taking underlying morphisms is injective. -/
theorem hom_injective : Function.Injective (Hom.hom : (M ⟶ N) → (M →ₗ⁅R,L⁆ N)) :=
  fun _ _ h ↦ hom_ext h

/-! ### The preadditive structure -/

instance : Add (M ⟶ N) where
  add f g := ofHom (f.hom + g.hom)

/-- The underlying morphism of a sum is the sum of the underlying morphisms. -/
@[simp] theorem hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

instance : Zero (M ⟶ N) where
  zero := ofHom 0

/-- The underlying morphism of the zero morphism is zero. -/
@[simp] theorem hom_zero : (0 : M ⟶ N).hom = 0 := rfl

instance : SMul ℕ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

/-- The underlying morphism of a natural multiple is that multiple of the underlying morphism. -/
@[simp] theorem hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance : Neg (M ⟶ N) where
  neg f := ofHom (-f.hom)

/-- The underlying morphism of a negative is the negative of the underlying morphism. -/
@[simp] theorem hom_neg (f : M ⟶ N) : (-f).hom = -f.hom := rfl

instance : Sub (M ⟶ N) where
  sub f g := ofHom (f.hom - g.hom)

/-- The underlying morphism of a difference is the difference of the underlying morphisms. -/
@[simp] theorem hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

instance : SMul ℤ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

/-- The underlying morphism of an integral multiple is that multiple of the underlying morphism. -/
@[simp] theorem hom_zsmul (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

/-- The zero morphism of Lie modules gives the zero morphism. -/
@[simp] theorem ofHom_zero : ofHom (0 : X →ₗ⁅R,L⁆ Y) = 0 := rfl

/-- A sum of morphisms of Lie modules gives the sum of the categorical morphisms. -/
@[simp] theorem ofHom_add (f g : X →ₗ⁅R,L⁆ Y) : ofHom (f + g) = ofHom f + ofHom g := rfl

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup Hom.hom hom_injective
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Preadditive (LieModuleCat.{w} R L) where
  add_comp _ _ _ _ _ g := hom_ext <| LieModuleHom.ext fun _ ↦ map_add g.hom _ _
  comp_add _ _ _ _ _ _ := hom_ext <| LieModuleHom.ext fun _ ↦ rfl

/-! ### The zero object and binary biproducts -/

/-- A Lie module with at most one element is a zero object. -/
theorem isZero_of_subsingleton (M : LieModuleCat.{w} R L) [Subsingleton M] : IsZero M where
  unique_to X := ⟨⟨⟨ofHom 0⟩, fun f ↦ hom_ext <| LieModuleHom.ext fun x ↦ by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  unique_from X := ⟨⟨⟨ofHom 0⟩, fun _ ↦ hom_ext <| LieModuleHom.ext fun _ ↦
    Subsingleton.elim _ _⟩⟩

instance : HasZeroObject (LieModuleCat.{w} R L) :=
  have : Subsingleton (TrivialLieModule R L PUnit.{w + 1}) := inferInstanceAs (Subsingleton PUnit)
  ⟨⟨of R L (TrivialLieModule R L PUnit.{w + 1}), isZero_of_subsingleton _⟩⟩

variable (M N) in
/-- The product bicone of two Lie modules: the product `M × N` with its two projections and two
inclusions. Its point is exposed, so that it is the product `M × N` by definition. -/
@[expose]
def binaryBicone : BinaryBicone M N where
  pt := of R L (M × N)
  fst := ofHom (LieModuleHom.fst R L M N)
  snd := ofHom (LieModuleHom.snd R L M N)
  inl := ofHom (LieModuleHom.inl R L M N)
  inr := ofHom (LieModuleHom.inr R L M N)
  inl_fst := hom_ext <| LieModuleHom.ext fun _ ↦ by simp
  inl_snd := hom_ext <| LieModuleHom.ext fun _ ↦ by simp
  inr_fst := hom_ext <| LieModuleHom.ext fun _ ↦ by simp
  inr_snd := hom_ext <| LieModuleHom.ext fun _ ↦ by simp

/-- The point of the product bicone is the product of the two Lie modules. -/
@[simp]
theorem binaryBicone_pt : (binaryBicone M N).pt = of R L (M × N) := (rfl)

/-- The first projection of the product bicone is the first projection of `M × N`. -/
@[simp]
theorem binaryBicone_fst : (binaryBicone M N).fst = ofHom (LieModuleHom.fst R L M N) := (rfl)

/-- The second projection of the product bicone is the second projection of `M × N`. -/
@[simp]
theorem binaryBicone_snd : (binaryBicone M N).snd = ofHom (LieModuleHom.snd R L M N) := (rfl)

/-- The first inclusion of the product bicone is the first inclusion into `M × N`. -/
@[simp]
theorem binaryBicone_inl : (binaryBicone M N).inl = ofHom (LieModuleHom.inl R L M N) := (rfl)

/-- The second inclusion of the product bicone is the second inclusion into `M × N`. -/
@[simp]
theorem binaryBicone_inr : (binaryBicone M N).inr = ofHom (LieModuleHom.inr R L M N) := (rfl)

variable (M N) in
/-- The two idempotents of the product bicone add up to the identity. -/
theorem binaryBicone_total :
    (binaryBicone M N).fst ≫ (binaryBicone M N).inl +
      (binaryBicone M N).snd ≫ (binaryBicone M N).inr = 𝟙 (binaryBicone M N).pt :=
  -- The bicone is exposed, so its total identity is that of the product `M × N`.
  have h : ofHom (LieModuleHom.fst R L M N) ≫ ofHom (LieModuleHom.inl R L M N) +
      ofHom (LieModuleHom.snd R L M N) ≫ ofHom (LieModuleHom.inr R L M N) =
        𝟙 (of R L (M × N)) :=
    hom_ext <| LieModuleHom.ext fun p ↦ by
      rw [hom_add, hom_comp, hom_comp]
      simp
  h

variable (M N) in
/-- **The product of two Lie modules is their biproduct.** -/
def binaryBiconeIsBilimit : (binaryBicone M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (binaryBicone_total M N)

instance : HasBinaryBiproducts (LieModuleCat.{w} R L) where
  has_binary_biproduct M N := hasBinaryBiproduct_of_total _ (binaryBicone_total M N)

variable (M N) in
/-- The biproduct of two Lie modules is isomorphic to their product. -/
noncomputable def biprodIsoProd : M ⊞ N ≅ of R L (M × N) :=
  (biprod.uniqueUpToIso M N (binaryBiconeIsBilimit M N)).symm

variable (M N) in
/-- Under `biprodIsoProd`, the first biproduct projection is the first projection of `M × N`. -/
@[simp]
theorem biprodIsoProd_inv_comp_fst :
    (biprodIsoProd M N).inv ≫ biprod.fst = ofHom (LieModuleHom.fst R L M N) :=
  biprod.lift_fst _ _

variable (M N) in
/-- Under `biprodIsoProd`, the second biproduct projection is the second projection of
`M × N`. -/
@[simp]
theorem biprodIsoProd_inv_comp_snd :
    (biprodIsoProd M N).inv ≫ biprod.snd = ofHom (LieModuleHom.snd R L M N) :=
  biprod.lift_snd _ _

variable (M N) in
/-- Under `biprodIsoProd`, the first biproduct inclusion is the first inclusion into `M × N`. -/
@[simp]
theorem inl_comp_biprodIsoProd_hom :
    biprod.inl ≫ (biprodIsoProd M N).hom = ofHom (LieModuleHom.inl R L M N) :=
  biprod.inl_desc _ _

variable (M N) in
/-- Under `biprodIsoProd`, the second biproduct inclusion is the second inclusion into
`M × N`. -/
@[simp]
theorem inr_comp_biprodIsoProd_hom :
    biprod.inr ≫ (biprodIsoProd M N).hom = ofHom (LieModuleHom.inr R L M N) :=
  biprod.inr_desc _ _

/-- The coordinates of `biprodIsoProd` are the two biproduct projections. -/
@[simp]
theorem biprodIsoProd_hom_apply (x : ↑(M ⊞ N)) :
    (biprodIsoProd M N).hom.hom x =
      ((biprod.fst : M ⊞ N ⟶ M).hom x, (biprod.snd : M ⊞ N ⟶ N).hom x) := by
  have h₁ := (Iso.eq_inv_comp _).1 (biprodIsoProd_inv_comp_fst M N).symm
  have h₂ := (Iso.eq_inv_comp _).1 (biprodIsoProd_inv_comp_snd M N).symm
  exact Prod.ext (by simpa using congrArg (fun f ↦ f.hom x) h₁)
    (by simpa using congrArg (fun f ↦ f.hom x) h₂)

end LieModuleCat

end TauCeti

/-! ### Isomorphisms and equivalences of Lie modules -/

section Iso

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

open TauCeti

/-- An equivalence of Lie modules gives an isomorphism of the associated objects. -/
def LieModuleEquiv.toLieModuleCatIso {M N : Type w} [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] [AddCommGroup N] [Module R N] [LieRingModule L N]
    [LieModule R L N] (e : M ≃ₗ⁅R,L⁆ N) : LieModuleCat.of R L M ≅ LieModuleCat.of R L N where
  hom := LieModuleCat.ofHom e
  inv := LieModuleCat.ofHom e.symm
  hom_inv_id := LieModuleCat.hom_ext <| LieModuleHom.ext e.symm_apply_apply
  inv_hom_id := LieModuleCat.hom_ext <| LieModuleHom.ext e.apply_symm_apply

/-- The forward morphism of the isomorphism attached to an equivalence is the equivalence. -/
@[simp]
theorem LieModuleEquiv.toLieModuleCatIso_hom_hom {M N : Type w} [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] [AddCommGroup N] [Module R N] [LieRingModule L N]
    [LieModule R L N] (e : M ≃ₗ⁅R,L⁆ N) : e.toLieModuleCatIso.hom.hom = e := (rfl)

/-- The inverse morphism of the isomorphism attached to an equivalence is its inverse. -/
@[simp]
theorem LieModuleEquiv.toLieModuleCatIso_inv_hom {M N : Type w} [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] [AddCommGroup N] [Module R N] [LieRingModule L N]
    [LieModule R L N] (e : M ≃ₗ⁅R,L⁆ N) : e.toLieModuleCatIso.inv.hom = e.symm := (rfl)

/-- An isomorphism of Lie module objects gives an equivalence of their carriers. -/
def CategoryTheory.Iso.toLieModuleEquiv {M N : LieModuleCat.{w} R L} (e : M ≅ N) :
    M ≃ₗ⁅R,L⁆ N :=
  { e.hom.hom with
    invFun := e.inv.hom
    left_inv := fun x ↦ congrArg (fun f : M ⟶ M ↦ f.hom x) e.hom_inv_id
    right_inv := fun x ↦ congrArg (fun f : N ⟶ N ↦ f.hom x) e.inv_hom_id }

/-- The equivalence attached to an isomorphism applies its forward morphism. -/
@[simp]
theorem CategoryTheory.Iso.toLieModuleEquiv_apply {M N : LieModuleCat.{w} R L} (e : M ≅ N)
    (x : M) : e.toLieModuleEquiv x = e.hom.hom x := (rfl)

/-- The inverse of the equivalence attached to an isomorphism applies its inverse morphism. -/
@[simp]
theorem CategoryTheory.Iso.toLieModuleEquiv_symm_apply {M N : LieModuleCat.{w} R L} (e : M ≅ N)
    (x : N) : e.toLieModuleEquiv.symm x = e.inv.hom x := (rfl)

/-- The morphism of Lie modules underlying the equivalence attached to an isomorphism is its
forward morphism. -/
@[simp]
theorem CategoryTheory.Iso.toLieModuleEquiv_toLieModuleHom {M N : LieModuleCat.{w} R L}
    (e : M ≅ N) : (e.toLieModuleEquiv : M →ₗ⁅R,L⁆ N) = e.hom.hom := (rfl)

/-- The equivalence attached to the isomorphism attached to an equivalence is that
equivalence. -/
@[simp]
theorem LieModuleEquiv.toLieModuleCatIso_toLieModuleEquiv {M N : Type w} [AddCommGroup M]
    [Module R M] [LieRingModule L M] [LieModule R L M] [AddCommGroup N] [Module R N]
    [LieRingModule L N] [LieModule R L N] (e : M ≃ₗ⁅R,L⁆ N) :
    e.toLieModuleCatIso.toLieModuleEquiv = e := by
  ext x
  rw [Iso.toLieModuleEquiv_apply, toLieModuleCatIso_hom_hom, coe_toLieModuleHom]

/-- The isomorphism attached to the equivalence attached to an isomorphism is that
isomorphism. -/
@[simp]
theorem CategoryTheory.Iso.toLieModuleEquiv_toLieModuleCatIso {M N : LieModuleCat.{w} R L}
    (e : M ≅ N) : e.toLieModuleEquiv.toLieModuleCatIso = e :=
  Iso.ext <| LieModuleCat.hom_ext <| by ext; simp

namespace TauCeti.LieModuleCat

/-- The inverse of `biprodIsoProd` is the sum of the two biproduct inclusions. -/
@[simp]
theorem biprodIsoProd_inv_apply {M N : LieModuleCat.{w} R L} (p : M × N) :
    (biprodIsoProd M N).inv.hom p =
      (biprod.inl : M ⟶ M ⊞ N).hom p.1 + (biprod.inr : N ⟶ M ⊞ N).hom p.2 := by
  rw [← Iso.toLieModuleEquiv_symm_apply, LieModuleEquiv.symm_apply_eq,
    Iso.toLieModuleEquiv_apply, map_add]
  have h₁ := congrArg (fun f ↦ f.hom p.1) (inl_comp_biprodIsoProd_hom M N)
  have h₂ := congrArg (fun f ↦ f.hom p.2) (inr_comp_biprodIsoProd_hom M N)
  simp only [hom_comp, LieModuleHom.comp_apply, hom_ofHom] at h₁ h₂
  simp [h₁, h₂]

end TauCeti.LieModuleCat

end Iso

/-! ### Finite Lie modules -/

namespace TauCeti

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Finite generation of the underlying module of a Lie module. -/
abbrev LieModuleCat.isFG (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L] :
    ObjectProperty (LieModuleCat.{w} R L) :=
  fun M ↦ Module.Finite R M

/-- The full subcategory of Lie modules finite over the ring of scalars. Over a field, these are
the finite-dimensional representations of `L`. -/
abbrev FGLieModuleCat (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L] :=
  (LieModuleCat.isFG.{w} R L).FullSubcategory

namespace FGLieModuleCat

instance : CoeSort (FGLieModuleCat.{w} R L) (Type w) :=
  ⟨fun M ↦ M.obj⟩

instance (M : FGLieModuleCat.{w} R L) : Module.Finite R M.obj.carrier := M.property

/-- Bundle a Lie module finite over the ring of scalars. -/
abbrev of (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L] (M : Type w)
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] [Module.Finite R M] :
    FGLieModuleCat.{w} R L :=
  ⟨LieModuleCat.of R L M, inferInstanceAs (Module.Finite R M)⟩

/-- Morphisms of finite Lie modules are equal if their underlying morphisms of Lie modules
agree. -/
@[ext]
theorem hom_ext {M N : FGLieModuleCat.{w} R L} {f g : M ⟶ N} (h : f.hom.hom = g.hom.hom) :
    f = g :=
  ObjectProperty.hom_ext _ (LieModuleCat.hom_ext h)

/-- Regard a morphism of Lie modules between modules finite over the ring of scalars as a
morphism of finite Lie modules. -/
abbrev ofHom {X Y : Type w} [AddCommGroup X] [Module R X] [LieRingModule L X] [LieModule R L X]
    [Module.Finite R X] [AddCommGroup Y] [Module R Y] [LieRingModule L Y] [LieModule R L Y]
    [Module.Finite R Y] (f : X →ₗ⁅R,L⁆ Y) : of R L X ⟶ of R L Y :=
  ObjectProperty.homMk (LieModuleCat.ofHom f)

/-- An isomorphism of finite Lie modules gives an equivalence of their carriers. -/
def _root_.CategoryTheory.Iso.fgLieModuleCatIsoToLieModuleEquiv {M N : FGLieModuleCat.{w} R L}
    (e : M ≅ N) : M ≃ₗ⁅R,L⁆ N :=
  ((LieModuleCat.isFG R L).ι.mapIso e).toLieModuleEquiv

/-- The equivalence attached to an isomorphism of finite Lie modules applies its forward
morphism. -/
@[simp]
theorem _root_.CategoryTheory.Iso.fgLieModuleCatIsoToLieModuleEquiv_apply
    {M N : FGLieModuleCat.{w} R L} (e : M ≅ N) (x : M.obj) :
    e.fgLieModuleCatIsoToLieModuleEquiv x = e.hom.hom.hom x := by
  simp [Iso.fgLieModuleCatIsoToLieModuleEquiv]

/-- The inverse of the equivalence attached to an isomorphism of finite Lie modules applies its
inverse morphism. -/
@[simp]
theorem _root_.CategoryTheory.Iso.fgLieModuleCatIsoToLieModuleEquiv_symm_apply
    {M N : FGLieModuleCat.{w} R L} (e : M ≅ N) (x : N.obj) :
    e.fgLieModuleCatIsoToLieModuleEquiv.symm x = e.inv.hom.hom x := by
  simp [Iso.fgLieModuleCatIsoToLieModuleEquiv]

/-- The morphism of Lie modules underlying the equivalence attached to an isomorphism of finite
Lie modules is its forward morphism. -/
@[simp]
theorem _root_.CategoryTheory.Iso.fgLieModuleCatIsoToLieModuleEquiv_toLieModuleHom
    {M N : FGLieModuleCat.{w} R L} (e : M ≅ N) :
    (e.fgLieModuleCatIsoToLieModuleEquiv : M.obj →ₗ⁅R,L⁆ N.obj) = e.hom.hom.hom := by
  ext
  simp

section Equiv

variable {X Y : Type w} [AddCommGroup X] [Module R X] [LieRingModule L X] [LieModule R L X]
  [Module.Finite R X] [AddCommGroup Y] [Module R Y] [LieRingModule L Y] [LieModule R L Y]
  [Module.Finite R Y]

/-- An equivalence of Lie modules finite over the ring of scalars gives an isomorphism of finite
Lie modules. -/
def _root_.LieModuleEquiv.toFGLieModuleCatIso (e : X ≃ₗ⁅R,L⁆ Y) : of R L X ≅ of R L Y :=
  (LieModuleCat.isFG R L).isoMk e.toLieModuleCatIso

/-- The forward morphism of the isomorphism attached to an equivalence of finite Lie modules is
the equivalence. -/
@[simp]
theorem _root_.LieModuleEquiv.toFGLieModuleCatIso_hom_hom_hom (e : X ≃ₗ⁅R,L⁆ Y) :
    e.toFGLieModuleCatIso.hom.hom.hom = e := by
  simp [LieModuleEquiv.toFGLieModuleCatIso]

/-- The inverse morphism of the isomorphism attached to an equivalence of finite Lie modules is
its inverse. -/
@[simp]
theorem _root_.LieModuleEquiv.toFGLieModuleCatIso_inv_hom_hom (e : X ≃ₗ⁅R,L⁆ Y) :
    e.toFGLieModuleCatIso.inv.hom.hom = e.symm := by
  simp [LieModuleEquiv.toFGLieModuleCatIso]

/-- The equivalence attached to the isomorphism attached to an equivalence of finite Lie modules
is that equivalence. -/
@[simp]
theorem _root_.LieModuleEquiv.toFGLieModuleCatIso_fgLieModuleCatIsoToLieModuleEquiv
    (e : X ≃ₗ⁅R,L⁆ Y) : e.toFGLieModuleCatIso.fgLieModuleCatIsoToLieModuleEquiv = e := by
  ext x
  rw [Iso.fgLieModuleCatIsoToLieModuleEquiv_apply, LieModuleEquiv.toFGLieModuleCatIso_hom_hom_hom,
    LieModuleEquiv.coe_toLieModuleHom]

end Equiv

/-- The isomorphism attached to the equivalence attached to an isomorphism of finite Lie modules
is that isomorphism. -/
@[simp]
theorem _root_.CategoryTheory.Iso.fgLieModuleCatIsoToLieModuleEquiv_toFGLieModuleCatIso
    {M N : FGLieModuleCat.{w} R L} (e : M ≅ N) :
    e.fgLieModuleCatIsoToLieModuleEquiv.toFGLieModuleCatIso = e :=
  Iso.ext <| hom_ext <| by simp

instance : (LieModuleCat.isFG.{w} R L).IsClosedUnderIsomorphisms where
  of_iso e hM := by
    have : Module.Finite R _ := hM
    exact Module.Finite.equiv e.toLieModuleEquiv.toLinearEquiv

instance : (LieModuleCat.isFG.{w} R L).ContainsZero where
  exists_zero :=
    have : Subsingleton (TrivialLieModule R L PUnit.{w + 1}) := inferInstanceAs (Subsingleton PUnit)
    have : Finite (TrivialLieModule R L PUnit.{w + 1}) := inferInstanceAs (Finite PUnit)
    ⟨LieModuleCat.of R L (TrivialLieModule R L PUnit.{w + 1}),
      LieModuleCat.isZero_of_subsingleton _, Module.Finite.of_finite⟩

instance : (LieModuleCat.isFG.{w} R L).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN ↦ by
    have : Module.Finite R M := hM
    have : Module.Finite R N := hN
    exact Module.Finite.equiv (LieModuleCat.biprodIsoProd M N).toLieModuleEquiv.symm.toLinearEquiv

instance : HasBinaryBiproducts (FGLieModuleCat.{w} R L) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The biproduct of two finite Lie modules is equivalent to their product. -/
noncomputable def biprodLieModuleEquiv (M N : FGLieModuleCat.{w} R L) :
    (M ⊞ N : FGLieModuleCat.{w} R L).obj ≃ₗ⁅R,L⁆ M.obj × N.obj :=
  have := preservesBinaryBiproducts_of_preservesBiproducts (LieModuleCat.isFG.{w} R L).ι
  (((LieModuleCat.isFG R L).ι.mapBiprod M N).trans
    (LieModuleCat.biprodIsoProd M.obj N.obj)).toLieModuleEquiv

/-- The coordinates of `biprodLieModuleEquiv` are the two biproduct projections. -/
@[simp]
theorem biprodLieModuleEquiv_apply (M N : FGLieModuleCat.{w} R L) (x : (M ⊞ N).obj) :
    biprodLieModuleEquiv M N x =
      ((biprod.fst : M ⊞ N ⟶ M).hom.hom x, (biprod.snd : M ⊞ N ⟶ N).hom.hom x) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts (LieModuleCat.isFG.{w} R L).ι
  have h₁ : ((LieModuleCat.isFG R L).ι.mapBiprod M N).hom ≫ biprod.fst =
      (biprod.fst : M ⊞ N ⟶ M).hom := by
    rw [Functor.mapBiprod_hom, biprod.lift_fst, ObjectProperty.ι_map]
  have h₂ : ((LieModuleCat.isFG R L).ι.mapBiprod M N).hom ≫ biprod.snd =
      (biprod.snd : M ⊞ N ⟶ N).hom := by
    rw [Functor.mapBiprod_hom, biprod.lift_snd, ObjectProperty.ι_map]
  rw [biprodLieModuleEquiv, Iso.toLieModuleEquiv_apply, Iso.trans_hom, LieModuleCat.hom_comp,
    LieModuleHom.comp_apply, LieModuleCat.biprodIsoProd_hom_apply]
  have h₁' := congrArg (fun f ↦ f.hom x) h₁
  have h₂' := congrArg (fun f ↦ f.hom x) h₂
  simp only [LieModuleCat.hom_comp, LieModuleHom.comp_apply] at h₁' h₂'
  exact Prod.ext h₁' h₂'

/-- The inverse of `biprodLieModuleEquiv` is the sum of the two biproduct inclusions. -/
@[simp]
theorem biprodLieModuleEquiv_symm_apply (M N : FGLieModuleCat.{w} R L) (p : M.obj × N.obj) :
    (biprodLieModuleEquiv M N).symm p =
      (biprod.inl : M ⟶ M ⊞ N).hom.hom p.1 + (biprod.inr : N ⟶ M ⊞ N).hom.hom p.2 := by
  have := preservesBinaryBiproducts_of_preservesBiproducts (LieModuleCat.isFG.{w} R L).ι
  have h₁ : biprod.inl ≫ ((LieModuleCat.isFG R L).ι.mapBiprod M N).inv =
      (biprod.inl : M ⟶ M ⊞ N).hom := by
    rw [Functor.mapBiprod_inv, biprod.inl_desc, ObjectProperty.ι_map]
  have h₂ : biprod.inr ≫ ((LieModuleCat.isFG R L).ι.mapBiprod M N).inv =
      (biprod.inr : N ⟶ M ⊞ N).hom := by
    rw [Functor.mapBiprod_inv, biprod.inr_desc, ObjectProperty.ι_map]
  rw [biprodLieModuleEquiv, Iso.toLieModuleEquiv_symm_apply, Iso.trans_inv, LieModuleCat.hom_comp,
    LieModuleHom.comp_apply, LieModuleCat.biprodIsoProd_inv_apply, map_add]
  have h₁' := congrArg (fun f ↦ f.hom p.1) h₁
  have h₂' := congrArg (fun f ↦ f.hom p.2) h₂
  simp only [LieModuleCat.hom_comp, LieModuleHom.comp_apply] at h₁' h₂'
  exact congrArg₂ (· + ·) h₁' h₂'

end FGLieModuleCat

end TauCeti
