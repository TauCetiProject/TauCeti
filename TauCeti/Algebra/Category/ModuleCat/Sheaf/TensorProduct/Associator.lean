/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.IsMonoidalW
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic

/-!
# Associativity of the tensor product of sheaves of modules

Let `R` be a sheaf of commutative rings on a small site. The tensor product of sheaves of
`R`-modules `SheafOfModules.tensorProduct R M N` is the sheafification of the sectionwise tensor
product `M ⊗ N` of the underlying presheaves of modules. This file constructs the associativity
isomorphism `(M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)`.

Both sides are sheafifications of iterated sectionwise tensor products in which an inner tensor
product has already been sheafified. The unit `M ⊗ N ⟶ a(M ⊗ N)` of the sheafification
adjunction is a local isomorphism, and tensoring preserves local isomorphisms
(`PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`), so sheafifying
`(M ⊗ N) ⊗ P ⟶ a(M ⊗ N) ⊗ P` gives an isomorphism, and similarly on the other side. The
associator is the sheafification of the sectionwise associator read through these two
isomorphisms. The scheme-level line-bundle associator
`TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorProductAssoc` is its specialization.

## Main declarations

* `SheafOfModules.isIso_sheafification_map_of_inverseImage_W_toPresheaf`: sheafification inverts
  local isomorphisms of presheaves of modules;
* `SheafOfModules.tensorProductAssoc`: the associativity isomorphism of the sheafified tensor
  product;
* `SheafOfModules.tensorProductAssoc_hom`: its forward map, spelled out through the sectionwise
  associator.

The site is assumed small, with modules in the universe of its objects and morphisms, because the
comparison of local isomorphisms passes through Mathlib's presentation of presheaves of modules
by free presheaves of modules. No formalization is vendored.
-/

public section

open CategoryTheory Category MonoidalCategory

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})

/-- Sheafification of presheaves of modules inverts local isomorphisms: morphisms whose
underlying morphism of presheaves of abelian groups becomes an isomorphism after
sheafification. -/
theorem isIso_sheafification_map_of_inverseImage_W_toPresheaf
    {M₀ N₀ : PresheafOfModules.{u} (ringCatSheaf R).obj} {g : M₀ ⟶ N₀}
    (hg : (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _) g) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map g) := by
  rwa [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 (ringCatSheaf R).obj)] at hg

/-- The unit `M₀ ⟶ a(M₀)` of the sheafification adjunction for presheaves of modules is a local
isomorphism. -/
theorem inverseImage_W_toPresheaf_sheafificationAdjunction_unit_app
    (M₀ : PresheafOfModules.{u} (ringCatSheaf R).obj) :
    (J.W (A := AddCommGrpCat.{u})).inverseImage (PresheafOfModules.toPresheaf _)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app M₀) :=
  J.W_toSheafify M₀.presheaf

/-- Sheafifying the whiskered unit `(M ⊗ N) ⊗ P ⟶ a(M ⊗ N) ⊗ P` gives an isomorphism. -/
instance (M₀ P₀ : PresheafOfModules.{u} (ringCatSheaf R).obj) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app M₀ ▷
        P₀)) :=
  isIso_sheafification_map_of_inverseImage_W_toPresheaf R
    (PresheafOfModules.inverseImage_W_toPresheaf_whiskerRight J
      (inverseImage_W_toPresheaf_sheafificationAdjunction_unit_app R M₀) P₀)

/-- Sheafifying the whiskered unit `M ⊗ (N ⊗ P) ⟶ M ⊗ a(N ⊗ P)` gives an isomorphism. -/
instance (M₀ P₀ : PresheafOfModules.{u} (ringCatSheaf R).obj) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      (M₀ ◁ (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        P₀)) :=
  isIso_sheafification_map_of_inverseImage_W_toPresheaf R
    (PresheafOfModules.inverseImage_W_toPresheaf_whiskerLeft J M₀
      (inverseImage_W_toPresheaf_sheafificationAdjunction_unit_app R P₀))

/-- Associativity of the tensor product of sheaves of `R`-modules. Through the defining
identifications `tensorProductIso`, it is the sheafification of the sectionwise associator,
composed with the inverse of the sheafified unit `a((M ⊗ N) ⊗ P) ≅ a(a(M ⊗ N) ⊗ P)` and with the
sheafified unit `a(M ⊗ (N ⊗ P)) ≅ a(M ⊗ a(N ⊗ P))`. -/
def tensorProductAssoc (M N P : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R (tensorProduct R M N) P ≅ tensorProduct R M (tensorProduct R N P) :=
  tensorProductIso R (tensorProduct R M N) P ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso
      (whiskerRightIso ((_root_.SheafOfModules.forget _).mapIso (tensorProductIso R M N))
        P.val) ≪≫
    (asIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        (M.val ⊗ N.val) ▷ P.val))).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (α_ M.val N.val P.val) ≪≫
    asIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      (M.val ◁ (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        (N.val ⊗ P.val))) ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso
      (whiskerLeftIso M.val
        ((_root_.SheafOfModules.forget _).mapIso (tensorProductIso R N P))).symm ≪≫
    (tensorProductIso R M (tensorProduct R N P)).symm

/-- The forward map of `tensorProductAssoc`: the sheafified sectionwise associator, read through
the defining identifications of the tensor products and the sheafified units. -/
theorem tensorProductAssoc_hom (M N P : SheafOfModules.{u} (ringCatSheaf R)) :
    (tensorProductAssoc R M N P).hom =
      (tensorProductIso R (tensorProduct R M N) P).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((_root_.SheafOfModules.forget _).map (tensorProductIso R M N).hom ▷ P.val) ≫
        (asIso ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
            (M.val ⊗ N.val) ▷ P.val))).inv ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          (α_ M.val N.val P.val).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          (M.val ◁ (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
            (N.val ⊗ P.val)) ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          (M.val ◁ (_root_.SheafOfModules.forget _).map (tensorProductIso R N P).inv) ≫
        (tensorProductIso R M (tensorProduct R N P)).inv :=
  (rfl)

end SheafOfModules

end

end TauCeti
