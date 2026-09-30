/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.IsMonoidalW
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic

/-!
# The symmetric monoidal category of sheaves of modules

Let `R` be a sheaf of commutative rings on a small site `(C, J)`. This file equips the category of
sheaves of `R`-modules with a symmetric monoidal category structure whose tensor product is the
sheafification of the sectionwise tensor product of the underlying presheaves of modules, and
whose unit is `R` itself.

The structure is obtained by localization. Sheafification `PresheafOfModules ⥤ SheafOfModules`
is a localization functor with respect to the local isomorphisms of presheaves of modules
(Mathlib's `PresheafOfModules.sheafification` instance of `Functor.IsLocalization`), and local
isomorphisms are stable under the sectionwise tensor product
(`PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`). Mathlib's localized monoidal
structure `CategoryTheory.LocalizedMonoidal` (with its braided and symmetric refinements) then
provides the monoidal category structure, the coherence laws, and the braiding on the target of
the localization functor, for which sheafification is a braided monoidal functor.

## Main declarations

* `SheafOfModules.monoidalCategory` and `SheafOfModules.symmetricCategory`: the symmetric
  monoidal category structure on sheaves of `R`-modules;
* `SheafOfModules.tensorUnit_eq`: its unit is the sheaf of modules `R` itself;
* `SheafOfModules.sheafificationMonoidal` and `SheafOfModules.sheafificationBraided`:
  sheafification of presheaves of modules is a braided monoidal functor, whose unit comparison is
  `SheafOfModules.sheafificationUnitIso` (`SheafOfModules.sheafification_ε`);
* `SheafOfModules.tensorUnderlyingIso`: the identification of `M ⊗ N` with the sheafification of
  the sectionwise tensor product of the underlying presheaves of modules, natural in `M` and `N`
  (`SheafOfModules.tensorUnderlyingIso_naturality`) and compatible with the braiding and
  the unitors.
* `SheafOfModules.sheafificationForgetAdjunction` and `SheafOfModules.forgetLaxMonoidal`:
  sheafification is left adjoint to the inclusion of sheaves of modules into presheaves of
  modules, which is therefore lax monoidal, with unit map the identity
  (`SheafOfModules.forget_ε`) and tensor map the unit of sheafification
  (`SheafOfModules.forget_μ`).

The tensor object `M ⊗ N` and the sheaf `SheafOfModules.tensorProduct R M N` are both
sheafifications of `M.val ⊗ N.val`, through `tensorUnderlyingIso` and `tensorProductIso`
respectively.

The site is assumed small, with modules in the universe of its objects and morphisms, because the
stability of local isomorphisms under tensor products is established in that generality.
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

/-- Local isomorphisms of presheaves of modules over the sheaf of rings underlying a sheaf of
commutative rings form a monoidal morphism property. -/
instance isMonoidal_inverseImage_W_toPresheaf :
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)).IsMonoidal :=
  PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf J (R := R.obj)

/-- Sheafifying the unit presheaf of modules recovers the sheaf of modules `R` itself. This is
the unit datum from which the localized monoidal structure is built. -/
def sheafificationUnitIso :
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).obj
      (𝟙_ (PresheafOfModules.{u} (ringCatSheaf R).obj)) ≅
        _root_.SheafOfModules.unit (ringCatSheaf R) :=
  sheafificationIso (ringCatSheaf R) (_root_.SheafOfModules.unit _)

/-- The forward map of `sheafificationUnitIso` is the counit of the sheafification adjunction at
the sheaf of modules `R`. -/
theorem sheafificationUnitIso_hom :
    (sheafificationUnitIso R).hom =
      (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).counit.app
        (_root_.SheafOfModules.unit (ringCatSheaf R)) :=
  sheafificationIso_hom _ _

/-- The monoidal category structure on sheaves of `R`-modules: the tensor product is the
sheafification of the sectionwise tensor product, and the unit is `R`. It is the localized
monoidal structure along sheafification. -/
instance monoidalCategory : MonoidalCategory (SheafOfModules.{u} (ringCatSheaf R)) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)))

/-- The symmetric monoidal category structure on sheaves of `R`-modules, whose braiding is
induced by the symmetry of the sectionwise tensor product. -/
instance symmetricCategory : SymmetricCategory (SheafOfModules.{u} (ringCatSheaf R)) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)))

/-- The unit of the monoidal structure on sheaves of `R`-modules is `R` itself. -/
@[simp]
theorem tensorUnit_eq :
    𝟙_ (SheafOfModules.{u} (ringCatSheaf R)) = _root_.SheafOfModules.unit (ringCatSheaf R) :=
  rfl

/-- Sheafification of presheaves of modules is a monoidal functor. -/
instance sheafificationMonoidal :
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)).Monoidal

/-- Sheafification of presheaves of modules is a braided monoidal functor. -/
instance sheafificationBraided :
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)) (sheafificationUnitIso R)).Braided

/-- The unit comparison of the monoidal functor sheafification is the inverse of
`sheafificationUnitIso`. -/
@[simp]
theorem sheafification_ε :
    Functor.LaxMonoidal.ε (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)) =
      (sheafificationUnitIso R).inv :=
  rfl

/-- The inverse unit comparison of the monoidal functor sheafification is
`sheafificationUnitIso`. -/
@[simp]
theorem sheafification_η :
    Functor.OplaxMonoidal.η (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)) =
      (sheafificationUnitIso R).hom :=
  rfl

variable {R}

/-- The tensor product of two sheaves of `R`-modules is the sheafification of the sectionwise
tensor product of their underlying presheaves of modules. -/
def _root_.SheafOfModules.tensorUnderlyingIso (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    M ⊗ N ≅ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).obj
      (M.val ⊗ N.val) :=
  ((sheafificationIso _ M).symm ⊗ᵢ (sheafificationIso _ N).symm) ≪≫
    Functor.Monoidal.μIso _ M.val N.val

/-- The forward map of `tensorUnderlyingIso`: the inverses of `sheafificationIso` on both
factors, followed by the tensor map of sheafification. -/
theorem _root_.SheafOfModules.tensorUnderlyingIso_hom (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.tensorUnderlyingIso N).hom =
      ((sheafificationIso _ M).inv ⊗ₘ (sheafificationIso _ N).inv) ≫
        Functor.LaxMonoidal.μ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
          M.val N.val := by
  simp [SheafOfModules.tensorUnderlyingIso]

/-- The inverse map of `tensorUnderlyingIso`: the inverse tensor map of sheafification, followed
by `sheafificationIso` on both factors. -/
theorem _root_.SheafOfModules.tensorUnderlyingIso_inv (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.tensorUnderlyingIso N).inv =
      Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
          M.val N.val ≫
        ((sheafificationIso _ M).hom ⊗ₘ (sheafificationIso _ N).hom) := by
  simp [SheafOfModules.tensorUnderlyingIso]

/-- `tensorUnderlyingIso` is natural: under it, the tensor product of two morphisms of sheaves of
modules is the sheafification of the sectionwise tensor product of their underlying morphisms. -/
@[reassoc]
theorem _root_.SheafOfModules.tensorUnderlyingIso_naturality
    {M M' N N' : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g) ≫ (M'.tensorUnderlyingIso N').hom =
      (M.tensorUnderlyingIso N).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).map (f.val ⊗ₘ g.val) := by
  simp only [SheafOfModules.tensorUnderlyingIso, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom, assoc]
  rw [tensorHom_comp_tensorHom_assoc, sheafificationIso_inv_naturality,
    sheafificationIso_inv_naturality, ← tensorHom_comp_tensorHom_assoc,
    Functor.LaxMonoidal.μ_natural]

/-- Under `tensorUnderlyingIso`, the braiding of sheaves of modules is the sheafification of the
braiding of the sectionwise tensor product. -/
@[reassoc]
theorem _root_.SheafOfModules.braiding_hom_tensorUnderlyingIso_hom
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (β_ M N).hom ≫ (N.tensorUnderlyingIso M).hom =
      (M.tensorUnderlyingIso N).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).map
          (β_ M.val N.val).hom := by
  simp only [SheafOfModules.tensorUnderlyingIso, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom, BraidedCategory.braiding_naturality_assoc,
    Functor.Braided.braided, assoc]

/-- The left unitor of sheaves of modules is the sheafification of the left unitor of the
sectionwise tensor product, read through the unit comparison `sheafificationUnitIso`. -/
theorem _root_.SheafOfModules.leftUnitor_hom_eq (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (λ_ M).hom = ((sheafificationUnitIso R).inv ⊗ₘ (sheafificationIso _ M).inv) ≫
      Functor.LaxMonoidal.μ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
        (𝟙_ _) M.val ≫
      (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).map (λ_ M.val).hom ≫
        (sheafificationIso _ M).hom := by
  rw [Functor.Monoidal.map_leftUnitor, sheafification_η]
  simp only [assoc, Functor.Monoidal.μ_δ_assoc, tensorHom_def', ← comp_whiskerRight_assoc,
    Iso.inv_hom_id, id_whiskerRight, id_comp]
  -- The unit `SheafOfModules.unit` produced by the unit comparison is `𝟙_` by `tensorUnit_eq`.
  exact ((leftUnitor_naturality_assoc _ _).trans (by rw [Iso.inv_hom_id, comp_id])).symm

/-- The right unitor of sheaves of modules is the sheafification of the right unitor of the
sectionwise tensor product, read through the unit comparison `sheafificationUnitIso`. -/
theorem _root_.SheafOfModules.rightUnitor_hom_eq (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (ρ_ M).hom = ((sheafificationIso _ M).inv ⊗ₘ (sheafificationUnitIso R).inv) ≫
      Functor.LaxMonoidal.μ (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj))
        M.val (𝟙_ _) ≫
      (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)).map (ρ_ M.val).hom ≫
        (sheafificationIso _ M).hom := by
  rw [Functor.Monoidal.map_rightUnitor, sheafification_η]
  simp only [assoc, Functor.Monoidal.μ_δ_assoc, tensorHom_def, ← whiskerLeft_comp_assoc,
    Iso.inv_hom_id, whiskerLeft_id]
  -- The unit `SheafOfModules.unit` produced by the unit comparison is `𝟙_` by `tensorUnit_eq`.
  exact ((rightUnitor_naturality_assoc _ _).trans (by rw [Iso.inv_hom_id, comp_id])).symm

section Forget

variable (R)

/-- Sheafification of presheaves of modules is left adjoint to the inclusion
`SheafOfModules.forget` of sheaves of modules. This is Mathlib's
`PresheafOfModules.sheafificationAdjunction` along the identity of the sheaf of rings, whose
right adjoint `forget ⋙ restrictScalars (𝟙 _)` is definitionally `forget`. -/
def sheafificationForgetAdjunction :
    PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj) ⊣
      _root_.SheafOfModules.forget (ringCatSheaf R) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)

/-- The counit of `sheafificationForgetAdjunction` at a sheaf of modules `M` is the
identification `sheafificationIso` of the sheafification of `M.val` with `M`. -/
lemma sheafificationForgetAdjunction_counit_app (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (sheafificationForgetAdjunction R).counit.app M = (sheafificationIso _ M).hom :=
  (sheafificationIso_hom _ M).symm

/-- The inclusion of sheaves of modules into presheaves of modules is lax monoidal, as the right
adjoint of the monoidal functor sheafification. Its tensor map `M.val ⊗ N.val ⟶ (M ⊗ N).val` is
the unit of sheafification (`SheafOfModules.forget_μ`), and its unit map is the identity
(`SheafOfModules.forget_ε`). -/
instance forgetLaxMonoidal : (_root_.SheafOfModules.forget (ringCatSheaf R)).LaxMonoidal :=
  (sheafificationForgetAdjunction R).rightAdjointLaxMonoidal

/-- The unit map of the inclusion of sheaves of modules into presheaves of modules is the
identity. -/
@[simp]
lemma forget_ε : Functor.LaxMonoidal.ε (_root_.SheafOfModules.forget (ringCatSheaf R)) = 𝟙 _ := by
  have h : (sheafificationUnitIso R).hom =
      (sheafificationForgetAdjunction R).counit.app (𝟙_ _) :=
    sheafificationUnitIso_hom R
  rw [forgetLaxMonoidal, Adjunction.rightAdjointLaxMonoidal_ε, sheafification_η, h]
  exact ((sheafificationForgetAdjunction R).homEquiv_unit _ _ _).trans
    ((sheafificationForgetAdjunction R).right_triangle_components (𝟙_ _))

/-- The tensor map `M.val ⊗ N.val ⟶ (M ⊗ N).val` of the inclusion of sheaves of modules into
presheaves of modules is the unit of sheafification, followed by the identification
`tensorUnderlyingIso` of `M ⊗ N` with the sheafification of `M.val ⊗ N.val`. -/
lemma forget_μ (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N =
      (sheafificationForgetAdjunction R).unit.app (M.val ⊗ N.val) ≫
        (_root_.SheafOfModules.forget (ringCatSheaf R)).map (M.tensorUnderlyingIso N).inv := by
  rw [forgetLaxMonoidal, Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit,
    SheafOfModules.tensorUnderlyingIso_inv, ← sheafificationForgetAdjunction_counit_app,
    ← sheafificationForgetAdjunction_counit_app]
  rfl

end Forget

end SheafOfModules

end

end TauCeti
