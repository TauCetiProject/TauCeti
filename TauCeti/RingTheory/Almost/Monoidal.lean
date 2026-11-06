/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.RingTheory.Almost.Module

/-!
# The symmetric monoidal structure on almost modules

For a basic setup `S = (V, m)`, almost isomorphisms of `V`-modules are stable under tensor
products: if `f` is an almost isomorphism, so are `X ⊗ f` and `f ⊗ X` for every `V`-module `X`
(Gabber–Ramero (2.2.5)). In the language of Mathlib, the morphism property
`S.almostZero.isoModSerre` of `ModuleCat V` is monoidal, so the category `Almost.Module S` of almost
`V`-modules inherits from `ModuleCat V` the localized symmetric monoidal structure, for which the
almostification functor `M ↦ M^a` is symmetric monoidal: `M^a ⊗ N^a ≅ (M ⊗[V] N)^a`, and the
tensor unit is `V^a`, which is isomorphic to `m^a` (Gabber–Ramero §2.2; Scholze, *Perfectoid
spaces*, §4). The tensor product of almost modules is additive, `V`-linear and right exact in each
variable.

## Main results

* `TauCeti.Almost.BasicSetup.isoModSerre_isMonoidal`: almost isomorphisms form a monoidal class of
  morphisms of `ModuleCat V`.
* `TauCeti.Almost.Module.instMonoidalCategory` and `TauCeti.Almost.Module.instSymmetricCategory`:
  the localized symmetric monoidal structure on `Almost.Module S`.
* `TauCeti.Almost.Module.toAlmostMonoidal` and `TauCeti.Almost.Module.toAlmostBraided`: the
  almostification functor is braided monoidal.
* `TauCeti.Almost.Module.instMonoidalPreadditive` and `TauCeti.Almost.Module.instMonoidalLinear`:
  the tensor product of almost modules is additive and `V`-linear in each variable.
* `TauCeti.Almost.Module.preservesFiniteColimits_tensorLeft` and
  `TauCeti.Almost.Module.preservesFiniteColimits_tensorRight`: the tensor product of almost modules
  is right exact in each variable.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2, (2.2.5)
  and (2.2.11).
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4, Proposition 4.5.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Proposition 4.1.7.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace TauCeti.Almost

variable {V : Type u} [CommRing V] (S : BasicSetup V)

namespace BasicSetup

/-- **Almost isomorphisms are monoidal** (Gabber–Ramero (2.2.5)): they are stable under
composition and under tensoring with any `V`-module on either side. This is what equips the
category of almost modules with the localized monoidal structure. -/
instance isoModSerre_isMonoidal :
    (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.IsMonoidal where
  whiskerLeft X _ _ g hg := by
    rw [← isAlmostIso_iff_isoModSerre] at hg ⊢
    exact hg.lTensor X
  whiskerRight f hf Y := by
    rw [← isAlmostIso_iff_isoModSerre] at hf ⊢
    exact hf.rTensor Y

end BasicSetup

namespace Module

/-- The **monoidal structure on almost modules**, localized from the tensor product of
`V`-modules: `M^a ⊗ N^a ≅ (M ⊗[V] N)^a`, with unit `V^a`. -/
noncomputable instance instMonoidalCategory : MonoidalCategory (Module S) :=
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := toAlmost S) (W := S.almostZero.isoModSerre) (Iso.refl _)))

/-- The tensor product of almost modules is symmetric, with braiding localized from that of
`V`-modules. -/
noncomputable instance instSymmetricCategory : SymmetricCategory (Module S) :=
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := toAlmost S) (W := S.almostZero.isoModSerre) (Iso.refl _)))

/-- **Almostification is a monoidal functor**: `M^a ⊗ N^a ≅ (M ⊗[V] N)^a` and `𝟙_ ≅ V^a`. -/
noncomputable instance toAlmostMonoidal : (toAlmost S).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := toAlmost S) (W := S.almostZero.isoModSerre) (Iso.refl _)).Monoidal

/-- Almostification is a braided monoidal functor. -/
noncomputable instance toAlmostBraided : (toAlmost S).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := toAlmost S) (W := S.almostZero.isoModSerre) (Iso.refl _)).Braided

variable {S} in
/-- Every almost module `X` is some `M^a`, and almostification intertwines tensoring on the left
with `M^a` and tensoring on the left with `M`. -/
private noncomputable def tensorLeftIso (X : Module S) :
    toAlmost S ⋙ tensorLeft X ≅ tensorLeft ((toAlmost S).objPreimage X) ⋙ toAlmost S :=
  Functor.isoWhiskerLeft _ ((tensoringLeft _).mapIso ((toAlmost S).objObjPreimageIso X)).symm ≪≫
    Functor.Monoidal.commTensorLeft (toAlmost S) _

/-- Tensoring on the left with an almost module is additive. -/
instance tensorLeft_additive (X : Module S) : (tensorLeft X).Additive :=
  (Localization.functor_additive_iff (toAlmost S) S.almostZero.isoModSerre _).mpr
    (Functor.additive_of_iso (tensorLeftIso X).symm)

/-- Tensoring on the left with an almost module is `V`-linear. -/
instance tensorLeft_linear (X : Module S) : (tensorLeft X).Linear V :=
  letI : Localization.Lifting (toAlmost S) S.almostZero.isoModSerre
      (tensorLeft ((toAlmost S).objPreimage X) ⋙ toAlmost S) (tensorLeft X) :=
    ⟨tensorLeftIso X⟩
  (Localization.functor_linear_iff (toAlmost S) S.almostZero.isoModSerre V
    (tensorLeft ((toAlmost S).objPreimage X) ⋙ toAlmost S) _).mp inferInstance

/-- **Tensoring on the left with an almost module is right exact.** -/
instance preservesFiniteColimits_tensorLeft (X : Module S) :
    PreservesFiniteColimits (tensorLeft X) :=
  (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff (toAlmost S)
    S.almostZero _).mp (preservesFiniteColimits_of_natIso (tensorLeftIso X).symm)

/-- Tensoring on the right with an almost module is additive. -/
instance tensorRight_additive (X : Module S) : (tensorRight X).Additive :=
  Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- Tensoring on the right with an almost module is `V`-linear. -/
instance tensorRight_linear (X : Module S) : (tensorRight X).Linear V :=
  Functor.linear_of_iso _ (BraidedCategory.tensorLeftIsoTensorRight X)

/-- **Tensoring on the right with an almost module is right exact.** -/
instance preservesFiniteColimits_tensorRight (X : Module S) :
    PreservesFiniteColimits (tensorRight X) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- The tensor product of almost modules is additive in each variable. -/
instance instMonoidalPreadditive : MonoidalPreadditive (Module S) where
  whiskerLeft_zero {X _ _} := (tensorLeft X).map_zero _ _
  zero_whiskerRight {X _ _} := (tensorRight X).map_zero _ _
  whiskerLeft_add {X _ _} f g := (tensorLeft X).map_add (f := f) (g := g)
  add_whiskerRight {X _ _} f g := (tensorRight X).map_add (f := f) (g := g)

/-- The tensor product of almost modules is `V`-linear in each variable. -/
instance instMonoidalLinear : MonoidalLinear V (Module S) where
  whiskerLeft_smul X _ _ r f := (tensorLeft X).map_smul r f
  smul_whiskerRight r _ _ f X := (tensorRight X).map_smul r f

end Module

end TauCeti.Almost
