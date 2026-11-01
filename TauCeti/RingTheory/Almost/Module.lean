/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import TauCeti.RingTheory.Almost.Firm

/-!
# Almost modules

Let `S = (V, m)` be a basic setup. The category of *almost `V`-modules* is the Serre quotient of
`ModuleCat V` by the almost zero modules, that is, its localization at the almost isomorphisms
(Gabber–Ramero (2.2.2); Scholze, *Perfectoid spaces*, Definition 4.3). We realise it as the
localized category `S.almostZero.isoModSerre.Localization'` fixed by the firm-module instance
`TauCeti.Almost.BasicSetup.hasLocalization`, so that its Hom-types live in the universe of the
`V`-modules. All almost-vanishing statements of almost mathematics ("`M` is almost zero", "`f` is
an almost isomorphism") become statements about objects and morphisms of this category, and the
category is abelian with an exact localization functor `M ↦ M^a`.

This file defines the category and the localization functor, and translates Mathlib's theory of
Serre quotients into the language of basic setups: `M^a` is zero iff `M` is almost zero; `f^a` is
a monomorphism, an epimorphism or zero iff respectively the kernel, the cokernel or the image of `f`
is almost zero; `f^a` is an isomorphism iff `f` is an almost isomorphism; and an exact functor out
of `ModuleCat V` factors through almost modules iff it kills the almost zero modules. For the
classical setup `(V, V)` almostification is an equivalence of categories.

## Main definitions

* `TauCeti.Almost.Module S`: the abelian category of almost `V`-modules.
* `TauCeti.Almost.toAlmost S`: the exact, essentially surjective localization functor
  `ModuleCat V ⥤ TauCeti.Almost.Module S`, `M ↦ M^a`.
* `TauCeti.Almost.Module.classicalEquiv`: for the classical setup, `ModuleCat V` is equivalent to
  the category of almost `V`-modules.

## Main results

* `TauCeti.Almost.isZero_toAlmost_obj_iff`: `M^a` is zero iff `M` is almost zero.
* `TauCeti.Almost.isIso_toAlmost_map_iff`: `f^a` is an isomorphism iff `f` is an almost
  isomorphism.
* `TauCeti.Almost.mono_toAlmost_map_iff`, `TauCeti.Almost.epi_toAlmost_map_iff` and
  `TauCeti.Almost.toAlmost_map_eq_zero_iff`: `f^a` is a monomorphism, an epimorphism or zero iff
  the kernel, the cokernel or the image of `f` is almost zero.
* `TauCeti.Almost.exists_exact_comp_toAlmost_iso_iff`: an exact functor out of `ModuleCat V` factors
  through `toAlmost S` by an exact functor iff it kills the almost zero modules.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2, (2.2.2).
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4, Lemma 4.2 and Definition 4.3.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Proposition 4.1.7.
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti.Almost

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- The category of almost `V`-modules over a basic setup `S = (V, m)`: the Serre quotient of
`ModuleCat V` by the almost zero modules, realised as the localized category at the almost
isomorphisms fixed by `TauCeti.Almost.BasicSetup.hasLocalization`. Its Hom-types live in the
universe of the `V`-modules.

Inside the namespace `TauCeti.Almost` this name shadows the typeclass `Module`, which must then
be written `_root_.Module`. -/
abbrev Module : Type (u + 1) :=
  (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.Localization'

/-- The almostification functor `M ↦ M^a` from `V`-modules to almost `V`-modules, the
localization functor at the almost isomorphisms. -/
noncomputable def toAlmost : ModuleCat.{u} V ⥤ Module S :=
  (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.Q'

instance : (toAlmost S).IsLocalization S.almostZero.isoModSerre :=
  inferInstanceAs
    ((S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.Q'.IsLocalization _)

instance : (toAlmost S).Additive :=
  inferInstanceAs (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.Q'.Additive

/-- The category of almost `V`-modules is abelian, as the Serre quotient of `ModuleCat V` by the
almost zero modules. -/
noncomputable instance : Abelian (Module S) :=
  ObjectProperty.SerreClassLocalization.abelian (toAlmost S) S.almostZero

/-- Almostification is left exact. -/
instance : PreservesFiniteLimits (toAlmost S) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits (toAlmost S) S.almostZero

/-- Almostification is right exact. -/
instance : PreservesFiniteColimits (toAlmost S) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits (toAlmost S) S.almostZero

/-- Every almost module is isomorphic to the almostification of a `V`-module. -/
instance : (toAlmost S).EssSurj :=
  Localization.essSurj _ S.almostZero.isoModSerre

/-- The almostification `M^a` is zero iff `M` is almost zero. -/
@[simp]
theorem isZero_toAlmost_obj_iff (M : ModuleCat.{u} V) :
    IsZero ((toAlmost S).obj M) ↔ S.IsAlmostZero M :=
  (ObjectProperty.SerreClassLocalization.isZero_obj_iff (toAlmost S) S.almostZero M).trans
    (S.almostZero_iff M)

/-- The almostification `f^a` of a morphism of `V`-modules is an isomorphism iff `f` is an almost
isomorphism. -/
@[simp]
theorem isIso_toAlmost_map_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    IsIso ((toAlmost S).map f) ↔ S.IsAlmostIso f.hom :=
  (ObjectProperty.SerreClassLocalization.isIso_map_iff (toAlmost S) S.almostZero f).trans
    (S.isAlmostIso_iff_isoModSerre f).symm

/-- The almostification `f^a` is a monomorphism iff the kernel of `f` is almost zero. -/
@[simp]
theorem mono_toAlmost_map_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    Mono ((toAlmost S).map f) ↔ S.IsAlmostZero (LinearMap.ker f.hom) := by
  rw [ObjectProperty.SerreClassLocalization.mono_map_iff (toAlmost S) S.almostZero,
    ObjectProperty.monoModSerre_iff, S.almostZero.prop_iff_of_iso (ModuleCat.kernelIsoKer f),
    BasicSetup.almostZero_iff]

/-- The almostification `f^a` is an epimorphism iff the cokernel of `f` is almost zero. -/
@[simp]
theorem epi_toAlmost_map_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    Epi ((toAlmost S).map f) ↔ S.IsAlmostZero (N ⧸ LinearMap.range f.hom) := by
  rw [ObjectProperty.SerreClassLocalization.epi_map_iff (toAlmost S) S.almostZero,
    ObjectProperty.epiModSerre_iff,
    S.almostZero.prop_iff_of_iso (ModuleCat.cokernelIsoRangeQuotient f),
    BasicSetup.almostZero_iff]

/-- The almostification `f^a` is zero iff the image of `f` is almost zero, that is, iff `m` kills
the image of `f`. -/
@[simp]
theorem toAlmost_map_eq_zero_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    (toAlmost S).map f = 0 ↔ S.IsAlmostZero (LinearMap.range f.hom) := by
  rw [ObjectProperty.SerreClassLocalization.map_eq_zero_iff (toAlmost S) S.almostZero,
    S.almostZero.prop_iff_of_iso (Abelian.imageIsoImage f ≪≫ ModuleCat.imageIsoRange f),
    BasicSetup.almostZero_iff]

/-- **Exact functors out of almost modules.** An exact functor `F` from `V`-modules to an abelian
category factors as `toAlmost S ⋙ G` for an exact functor `G` out of almost `V`-modules iff `F`
kills every almost zero module. Such a factorization is unique up to unique isomorphism, by
Mathlib's `ObjectProperty.SerreClassLocalization.fullyFaithfulWhiskeringLeft`. -/
theorem exists_exact_comp_toAlmost_iso_iff {D : Type*} [Category* D] [Abelian D]
    (F : ModuleCat.{u} V ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (∃ G : Module S ⥤ D, PreservesFiniteLimits G ∧ PreservesFiniteColimits G ∧
      Nonempty (toAlmost S ⋙ G ≅ F)) ↔
      ∀ M : ModuleCat.{u} V, S.IsAlmostZero M → IsZero (F.obj M) := by
  let F' : ModuleCat.{u} V ⥤ₑ D := ⟨F, ‹PreservesFiniteLimits F›, ‹PreservesFiniteColimits F›⟩
  have hF : (∀ M : ModuleCat.{u} V, S.IsAlmostZero M → IsZero (F.obj M)) ↔
      (ObjectProperty.SerreClassLocalization.whiskeringLeft (toAlmost S) S.almostZero D).essImage
        F' := by
    rw [ObjectProperty.SerreClassLocalization.essImage_whiskeringLeft]
    -- The essential image is stated as a predicate `fun G ↦ _`; beta-reduce it at `F'`.
    dsimp only
    rw [ObjectProperty.isoModSerre_isInvertedBy_iff]
    exact forall_congr' fun M ↦ imp_congr_left (S.almostZero_iff M).symm
  rw [hF]
  refine ⟨fun ⟨G, hl, hc, ⟨e⟩⟩ ↦ ⟨⟨G, ⟨hl, hc⟩⟩, ⟨ObjectProperty.isoMk _ e⟩⟩,
    fun ⟨G, ⟨e⟩⟩ ↦ ⟨G.obj, G.property.1, G.property.2, ⟨(ObjectProperty.ι _).mapIso e⟩⟩⟩

/-- For the classical setup `(V, V)` the almost isomorphisms are the isomorphisms, so
almostification is an equivalence of categories. -/
instance isEquivalence_toAlmost_classical : (toAlmost (BasicSetup.classical V)).IsEquivalence :=
  have : (𝟭 (ModuleCat.{u} V)).IsLocalization (BasicSetup.classical V).almostZero.isoModSerre :=
    Functor.IsLocalization.for_id _ (BasicSetup.isoModSerre_classical (V := V)).le
  Functor.isEquivalence_of_iso ((Functor.leftUnitor _).symm ≪≫
    Localization.compUniqFunctor (𝟭 _) (toAlmost (BasicSetup.classical V))
      (BasicSetup.classical V).almostZero.isoModSerre)

namespace Module

/-- For the classical setup `(V, V)`, almostification is an equivalence between `V`-modules and
almost `V`-modules. -/
noncomputable def classicalEquiv : ModuleCat.{u} V ≌ Module (BasicSetup.classical V) :=
  (toAlmost (BasicSetup.classical V)).asEquivalence

@[simp]
theorem classicalEquiv_functor :
    (classicalEquiv (V := V)).functor = toAlmost (BasicSetup.classical V) :=
  (rfl)

/-- For the zero setup `(V, 0)` every almost module is zero. -/
theorem isZero_of_zero (M : Module (BasicSetup.zero V)) : IsZero M :=
  ((isZero_toAlmost_obj_iff _ _).mpr BasicSetup.isAlmostZero_zero).of_iso
    ((toAlmost (BasicSetup.zero V)).objObjPreimageIso M).symm

end Module

end TauCeti.Almost
