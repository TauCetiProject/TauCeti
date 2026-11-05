/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import Mathlib.CategoryTheory.Localization.Linear
public import TauCeti.RingTheory.Almost.Firm

/-!
# Almost modules over a basic setup

Let `S = (V, m)` be a basic setup. The category `TauCeti.Almost.Module S` of almost `V`-modules is
the Serre quotient of `ModuleCat V` by the almost zero modules, that is, its localization at the
almost isomorphisms `S.almostZero.isoModSerre`, the morphisms with almost zero kernel and cokernel.
It is realised as the localized category `MorphismProperty.Localization'` fixed by the instance
`TauCeti.Almost.BasicSetup.hasLocalization`, so its Hom-types live in the universe of the
`V`-modules. The localization functor `M ↦ M^a` is `TauCeti.Almost.Module.toAlmost S`.

The general theory of Serre quotients then applies: the category of almost modules is abelian, the
functor `toAlmost S` is exact and essentially surjective, it sends `M` to a zero object exactly when
`M` is almost zero, and it sends `f` to an isomorphism exactly when `f` is an almost isomorphism.
An exact functor out of `ModuleCat V` that kills almost zero modules factors, uniquely up to
isomorphism, through an exact functor out of `Module S` (`TauCeti.Almost.Module.lift`). A functor
`G` out of `Module S` is exact iff `toAlmost S ⋙ G` is
(`CategoryTheory.ObjectProperty.SerreClassLocalization.exactFunctor_comp_iff`). For the classical
setup `(V, V)` nothing is inverted beyond the isomorphisms, and `toAlmost` is an equivalence
(`TauCeti.Almost.Module.classicalEquiv`).

All almost vanishing statements about almost modules, such as the almost acyclicity of
`O⁺` on perfectoid spaces, are statements in this category.

## Main definitions

* `TauCeti.Almost.Module`: the category of almost `V`-modules for a basic setup `S`.
* `TauCeti.Almost.Module.toAlmost`: the localization functor `M ↦ M^a`.
* `TauCeti.Almost.Module.lift`: the factorisation through `toAlmost S` of an exact functor killing
  almost zero modules.
* `TauCeti.Almost.Module.classicalEquiv`: for the classical setup, `ModuleCat V ≌ Module S`.
* `TauCeti.Almost.Module.firmEquiv`: the equivalence `Module S ≌ S.Firm`, with comparison
  `TauCeti.Almost.Module.toAlmostCompFirmIso` on almostifications.

## Main results

* `TauCeti.Almost.Module.isLocalization_toAlmost`: `toAlmost S` is a localization functor for the
  almost isomorphisms.
* `TauCeti.Almost.Module.instAbelian`: the category of almost modules is abelian.
* `TauCeti.Almost.Module.isZero_toAlmost_obj_iff`: `M^a` is zero iff `M` is almost zero.
* `TauCeti.Almost.Module.isIso_toAlmost_map_iff`: `f^a` is an isomorphism iff `f` is an almost
  isomorphism; `mono_toAlmost_map_iff` and `epi_toAlmost_map_iff` treat monomorphisms and
  epimorphisms, and `toAlmost_map_eq_zero_iff` zero morphisms.
* `TauCeti.Almost.Module.isZero_of_ideal_eq_bot`: for the zero setup `(V, 0)` every almost module is
  zero.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2, (2.2.2).
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4, Definition 4.3.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Proposition 4.1.7.
-/

public section

universe u

open CategoryTheory Limits TensorProduct

namespace TauCeti.Almost

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- The category of **almost `V`-modules** for a basic setup `S = (V, m)` (Gabber–Ramero (2.2.2),
Scholze, *Perfectoid spaces*, Definition 4.3): the Serre quotient of `ModuleCat V` by the almost
zero modules, i.e. the localization of `ModuleCat V` at the almost isomorphisms. Its Hom-types
live in the universe of the `V`-modules. -/
def Module : Type (u + 1) :=
  (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.Localization'

namespace Module

noncomputable instance : Category.{u} (Module S) :=
  inferInstanceAs
    (Category (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.Localization')

/-- The **almostification** functor `M ↦ M^a`, the localization functor from `V`-modules to almost
`V`-modules. -/
noncomputable def toAlmost : ModuleCat.{u} V ⥤ Module S :=
  (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.Q'

instance isLocalization_toAlmost : (toAlmost S).IsLocalization S.almostZero.isoModSerre :=
  inferInstanceAs
    ((S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.Q'.IsLocalization _)

/-- The preadditive structure on almost modules, for which `toAlmost` is additive. -/
noncomputable instance : Preadditive (Module S) :=
  Localization.preadditive (toAlmost S) S.almostZero.isoModSerre

instance : (toAlmost S).Additive :=
  Localization.functor_additive (toAlmost S) S.almostZero.isoModSerre

/-- **Almost modules form an abelian category.** -/
noncomputable instance instAbelian : Abelian (Module S) :=
  ObjectProperty.SerreClassLocalization.abelian (toAlmost S) S.almostZero

/-- The `V`-linear structure on almost modules, for which `toAlmost` is `V`-linear. In particular
the Hom-types of `Module S` are `V`-modules. -/
noncomputable instance : Linear V (Module S) :=
  Localization.linear V (toAlmost S) S.almostZero.isoModSerre

instance : (toAlmost S).Linear V :=
  Localization.functor_linear V (toAlmost S) S.almostZero.isoModSerre

instance : PreservesFiniteLimits (toAlmost S) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits (toAlmost S) S.almostZero

instance : PreservesFiniteColimits (toAlmost S) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits (toAlmost S) S.almostZero

instance : (toAlmost S).EssSurj :=
  Localization.essSurj (toAlmost S) S.almostZero.isoModSerre

/-- **`M^a` is zero iff `M` is almost zero.** -/
@[simp]
theorem isZero_toAlmost_obj_iff (M : ModuleCat.{u} V) :
    IsZero ((toAlmost S).obj M) ↔ S.IsAlmostZero M :=
  (ObjectProperty.SerreClassLocalization.isZero_obj_iff (toAlmost S) S.almostZero M).trans
    (S.almostZero_iff M)

/-- **`f^a` is an isomorphism iff `f` is an almost isomorphism.** -/
@[simp]
theorem isIso_toAlmost_map_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    IsIso ((toAlmost S).map f) ↔ S.IsAlmostIso f.hom := by
  rw [ObjectProperty.SerreClassLocalization.isIso_map_iff (toAlmost S) S.almostZero,
    S.isAlmostIso_iff_isoModSerre]

/-- `f^a` is a monomorphism iff the kernel of `f` is almost zero. -/
@[simp]
theorem mono_toAlmost_map_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    Mono ((toAlmost S).map f) ↔ S.IsAlmostZero (LinearMap.ker f.hom) := by
  rw [ObjectProperty.SerreClassLocalization.mono_map_iff (toAlmost S) S.almostZero,
    ObjectProperty.monoModSerre_iff, S.almostZero.prop_iff_of_iso (ModuleCat.kernelIsoKer f),
    S.almostZero_iff]

/-- `f^a` is an epimorphism iff the cokernel of `f` is almost zero. -/
@[simp]
theorem epi_toAlmost_map_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    Epi ((toAlmost S).map f) ↔ S.IsAlmostZero (N ⧸ LinearMap.range f.hom) := by
  rw [ObjectProperty.SerreClassLocalization.epi_map_iff (toAlmost S) S.almostZero,
    ObjectProperty.epiModSerre_iff,
    S.almostZero.prop_iff_of_iso (ModuleCat.cokernelIsoRangeQuotient f), S.almostZero_iff]

/-- `f^a` is zero iff the range of `f` is almost zero. -/
@[simp]
theorem toAlmost_map_eq_zero_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    (toAlmost S).map f = 0 ↔ S.IsAlmostZero (LinearMap.range f.hom) := by
  rw [ObjectProperty.SerreClassLocalization.map_eq_zero_iff (toAlmost S) S.almostZero,
    S.almostZero.prop_iff_of_iso (Abelian.imageIsoImage f ≪≫ ModuleCat.imageIsoRange f),
    S.almostZero_iff]

/-- The inclusion `m ⊆ V` becomes an isomorphism of almost modules. -/
instance isIso_toAlmost_map_subtype :
    IsIso ((toAlmost S).map (ModuleCat.ofHom S.ideal.subtype)) :=
  (isIso_toAlmost_map_iff S _).mpr S.isAlmostIso_subtype

/-- The action map is inverted by almostification. -/
instance isIso_toAlmost_map_tildeAct (M : ModuleCat.{u} V) :
    IsIso ((toAlmost S).map (ModuleCat.ofHom (S.tildeAct M) :
      ModuleCat.of V (S.tilde ⊗[V] M) ⟶ M)) :=
  (isIso_toAlmost_map_iff S _).mpr (S.isAlmostIso_tildeAct M)

/-- For the zero setup `(V, 0)`, every almost module is zero. -/
theorem isZero_of_ideal_eq_bot (hS : S.ideal = ⊥) (X : Module S) : IsZero X := by
  refine ((isZero_toAlmost_obj_iff S _).mpr ?_).of_iso ((toAlmost S).objObjPreimageIso X).symm
  rw [BasicSetup.isAlmostZero_iff, hS]
  simp

/-! ### The universal property -/

section lift

variable {D : Type*} [Category* D] [Abelian D] (F : ModuleCat.{u} V ⥤ D)
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The factorisation `Module S ⥤ D` of an exact functor `F : ModuleCat V ⥤ D` to an abelian
category that kills almost zero modules. -/
noncomputable def lift (hF : ∀ M : ModuleCat.{u} V, S.IsAlmostZero M → IsZero (F.obj M)) :
    Module S ⥤ D :=
  Localization.lift F ((S.isoModSerre_isInvertedBy_iff F).mpr hF) (toAlmost S)

variable (hF : ∀ M : ModuleCat.{u} V, S.IsAlmostZero M → IsZero (F.obj M))

/-- The factorisation `lift` of `F` satisfies `toAlmost S ⋙ lift S F hF ≅ F`. -/
noncomputable def fac : toAlmost S ⋙ lift S F hF ≅ F :=
  Localization.fac F ((S.isoModSerre_isInvertedBy_iff F).mpr hF) (toAlmost S)

/-- `lift S F hF` is a lifting of `F` along `toAlmost S`, with comparison isomorphism `fac`. Through
this instance Mathlib's `Localization.liftNatTrans` and `Localization.liftNatIso` lift natural
transformations between such functors, and `Localization.natTrans_ext` shows they are determined
by their components at the objects `M^a`. -/
noncomputable instance :
    Localization.Lifting (toAlmost S) S.almostZero.isoModSerre F (lift S F hF) :=
  ⟨fac S F hF⟩

instance : PreservesFiniteLimits (lift S F hF) :=
  (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff (toAlmost S)
    S.almostZero _).mp (preservesFiniteLimits_of_natIso (fac S F hF).symm)

instance : PreservesFiniteColimits (lift S F hF) :=
  (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff (toAlmost S)
    S.almostZero _).mp (preservesFiniteColimits_of_natIso (fac S F hF).symm)

/-- Uniqueness of the factorisation: every functor `G` with `toAlmost S ⋙ G ≅ F` is isomorphic to
`lift S F hF`. -/
noncomputable def liftUniq (G : Module S ⥤ D) (e : toAlmost S ⋙ G ≅ F) : G ≅ lift S F hF :=
  letI : Localization.Lifting (toAlmost S) S.almostZero.isoModSerre F G := ⟨e⟩
  Localization.liftNatIso (toAlmost S) S.almostZero.isoModSerre F F G _ (Iso.refl F)

end lift

/-! ### The firm-module model -/

/-- The equivalence between the Serre quotient of modules and the firm-module model. -/
noncomputable def firmEquiv : Module S ≌ S.Firm :=
  Localization.uniq (toAlmost S) S.firm S.almostZero.isoModSerre

/-- The firm representative of an almostification is its firmification. -/
noncomputable def toAlmostCompFirmIso : toAlmost S ⋙ (firmEquiv S).functor ≅ S.firm :=
  Localization.compUniqFunctor (toAlmost S) S.firm S.almostZero.isoModSerre

noncomputable instance :
    Localization.Lifting (toAlmost S) S.almostZero.isoModSerre S.firm (firmEquiv S).functor :=
  ⟨toAlmostCompFirmIso S⟩

instance : (firmEquiv S).functor.Linear V :=
  (Localization.functor_linear_iff (toAlmost S) S.almostZero.isoModSerre V S.firm
    (firmEquiv S).functor).mp inferInstance

instance : (firmEquiv S).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### The classical setup -/

instance isEquivalence_toAlmost_classical : (toAlmost (BasicSetup.classical V)).IsEquivalence := by
  have : (𝟭 (ModuleCat.{u} V)).IsLocalization (BasicSetup.classical V).almostZero.isoModSerre :=
    Functor.IsLocalization.for_id _ (BasicSetup.isoModSerre_classical (V := V)).le
  exact Functor.isEquivalence_of_iso ((Functor.leftUnitor _).symm ≪≫
    Localization.compUniqFunctor (𝟭 _) (toAlmost _) (BasicSetup.classical V).almostZero.isoModSerre)

/-- For the classical setup `(V, V)`, almostification is an equivalence between `V`-modules and
almost `V`-modules. -/
noncomputable def classicalEquiv : ModuleCat.{u} V ≌ Module (BasicSetup.classical V) :=
  (toAlmost (BasicSetup.classical V)).asEquivalence

@[simp]
theorem classicalEquiv_functor :
    (classicalEquiv (V := V)).functor = toAlmost (BasicSetup.classical V) :=
  (rfl)

end Module

end TauCeti.Almost
