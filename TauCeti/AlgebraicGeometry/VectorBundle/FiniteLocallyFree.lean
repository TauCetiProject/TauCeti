/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.Biprod
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Finite locally free sheaves on a scheme

A sheaf of `𝒪_X`-modules on a scheme `X` is finite locally free if it is locally free and finitely
presented (`SheafOfModules.isFiniteLocallyFree`). These are the sheaves of sections of algebraic
vector bundles of finite rank. This file packages them as the full subcategory
`FiniteLocallyFreeSheaf X` of `X.Modules` and equips it with the structure inherited from
`X.Modules`:

* it is closed under isomorphisms, and its objects are quasi-coherent;
* it is a symmetric monoidal category, with the tensor product and unit `𝒪_X` of `X.Modules`, and
  its inclusion into `X.Modules` is braided monoidal;
* it is an additive category: it contains the zero sheaf and is closed under direct sums, so it
  has finite biproducts, computed in `X.Modules`.

Invertible sheaves are finite locally free, and finite locally free sheaves are finitely
presented; the corresponding inclusions of full subcategories are fully faithful.

Since `X.Modules` is not reducibly the category of sheaves of modules over the structure sheaf,
instance search does not find the site-level instances for it, and they are restated here for
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree X`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree X`: finite local freeness as a property
  of `𝒪_X`-modules;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf X`: the full subcategory of finite locally
  free sheaves in `X.Modules`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.free X I`: the free sheaf on a finite type
  `I`;
* `AlgebraicGeometry.Scheme.Modules.isMonoidal_isFiniteLocallyFree`: finite local freeness is a
  monoidal property of `𝒪_X`-modules;
* `AlgebraicGeometry.Scheme.Modules.containsZero_isFiniteLocallyFree` and
  `AlgebraicGeometry.Scheme.Modules.isClosedUnderFiniteProducts_isFiniteLocallyFree`, from which
  `FiniteLocallyFreeSheaf X` has finite biproducts;
* `FiniteLocallyFreeSheaf.toFinitelyPresented` and `InvertibleSheaf.toFiniteLocallyFree`: the
  fully faithful inclusions.

## References

* [The Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

/-- Finite local freeness of `𝒪_X`-modules, as a property of objects of `X.Modules`: an
`𝒪_X`-module is finite locally free if it is locally free and finitely presented. -/
abbrev _root_.AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree : ObjectProperty X.Modules :=
  _root_.SheafOfModules.isFiniteLocallyFree X.ringCatSheaf

/-- Finite local freeness of `𝒪_X`-modules is invariant under isomorphism. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isClosedUnderIsomorphisms_isFiniteLocallyFree :
    (Scheme.Modules.isFiniteLocallyFree X).IsClosedUnderIsomorphisms :=
  inferInstanceAs
    (_root_.SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).IsClosedUnderIsomorphisms

/-- Finite local freeness is a monoidal property of `𝒪_X`-modules: the structure sheaf is finite
locally free, and finite locally free sheaves are closed under tensor products. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isMonoidal_isFiniteLocallyFree :
    (Scheme.Modules.isFiniteLocallyFree X).IsMonoidal :=
  SheafOfModules.isMonoidal_isFiniteLocallyFree (R := X.sheaf)

/-- The zero `𝒪_X`-module is finite locally free. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.containsZero_isFiniteLocallyFree :
    (Scheme.Modules.isFiniteLocallyFree X).ContainsZero :=
  SheafOfModules.containsZero_isFiniteLocallyFree (R := X.ringCatSheaf)

/-- Finite locally free `𝒪_X`-modules are closed under finite products, which are the finite
direct sums in `X.Modules`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isClosedUnderFiniteProducts_isFiniteLocallyFree :
    (Scheme.Modules.isFiniteLocallyFree X).IsClosedUnderFiniteProducts :=
  SheafOfModules.isClosedUnderFiniteProducts_isFiniteLocallyFree (R := X.ringCatSheaf)

/-- The full category of finite locally free sheaves on a scheme, that is, of locally free and
finitely presented `𝒪_X`-modules. Its morphisms are morphisms of `𝒪_X`-modules. -/
abbrev FiniteLocallyFreeSheaf : Type _ :=
  (Scheme.Modules.isFiniteLocallyFree X).FullSubcategory

namespace FiniteLocallyFreeSheaf

variable {X}

instance (E : FiniteLocallyFreeSheaf X) : E.obj.IsLocallyFree :=
  E.property.1

instance (E : FiniteLocallyFreeSheaf X) : E.obj.IsFinitePresentation :=
  E.property.2

/-- A finite locally free sheaf is quasi-coherent. -/
instance (E : FiniteLocallyFreeSheaf X) : E.obj.IsQuasicoherent :=
  -- Mathlib's instance deriving quasi-coherence from local freeness is stated for sheaves of
  -- modules, and instance search does not unfold `X.Modules`, so the underlying object is
  -- rebound with the type of sheaves of modules.
  let F : _root_.SheafOfModules X.ringCatSheaf := E.obj
  have : F.IsLocallyFree := E.property.1
  inferInstanceAs F.IsQuasicoherent

/-- The category of finite locally free sheaves has finite biproducts, computed in
`X.Modules`; together with its preadditive structure this makes it an additive category. -/
instance : HasFiniteBiproducts (FiniteLocallyFreeSheaf X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable (X)

/-- The free sheaf on a finite type, as a finite locally free sheaf. -/
def free (I : Type u) [Finite I] : FiniteLocallyFreeSheaf X :=
  ⟨_root_.SheafOfModules.free (R := X.ringCatSheaf) I, inferInstance,
    SheafOfModules.isFinitePresentation_free I⟩

@[simp]
lemma free_obj (I : Type u) [Finite I] :
    (free X I).obj = _root_.SheafOfModules.free (R := X.ringCatSheaf) I :=
  (rfl)

/-- The fully faithful inclusion of finite locally free sheaves into finitely presented
sheaves. -/
abbrev toFinitelyPresented : FiniteLocallyFreeSheaf X ⥤ FinitelyPresentedSheaf X :=
  ObjectProperty.ιOfLE fun _ hE ↦ hE.2

-- The two full subcategories live in `X.Modules` and in the definitionally equal category of
-- sheaves of modules, which instance search does not identify; so the instances for `ιOfLE` are
-- applied explicitly.
instance : (toFinitelyPresented X).Full :=
  ObjectProperty.full_ιOfLE _

instance : (toFinitelyPresented X).Faithful :=
  ObjectProperty.faithful_ιOfLE _

end FiniteLocallyFreeSheaf

/-- The fully faithful inclusion of invertible sheaves into finite locally free sheaves: an
invertible sheaf is locally free of rank one, hence locally free and finitely presented. -/
abbrev InvertibleSheaf.toFiniteLocallyFree : InvertibleSheaf X ⥤ FiniteLocallyFreeSheaf X :=
  ObjectProperty.ιOfLE fun M hM ↦
    have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M := hM
    ⟨TauCeti.SheafOfModules.IsInvertible.isLocallyFree M,
      TauCeti.SheafOfModules.IsInvertible.isFinitePresentation (M := M)⟩

end

end AlgebraicGeometry

end TauCeti
