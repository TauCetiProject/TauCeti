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
# The category of almost modules

For a basic setup `S = (V, m)`, the category `TauCeti.Almost.Module S` of almost `V`-modules is the
Serre quotient of `ModuleCat V` by the almost zero modules: the localization of `ModuleCat V` at the
almost isomorphisms, the morphisms with almost zero kernel and cokernel. It is realised as Mathlib's
`MorphismProperty.Localization'` for the instance `TauCeti.Almost.BasicSetup.hasLocalization`,
whose localized category is the category of firm modules, so that its Hom-types live in the same
universe as the `V`-modules. The localization functor `M ↦ M^a` is `TauCeti.Almost.toAlmost S`.

All almost-vanishing statements of almost mathematics (an almost zero cohomology group, an almost
isomorphism of modules) are statements in this category: `M^a` is a zero object iff `M` is almost
zero, and `f^a` is an isomorphism iff `f` is an almost isomorphism. The category is abelian, and
Mathlib endows it with a `V`-linear structure for which `toAlmost S` is `V`-linear.

## Main definitions

* `TauCeti.Almost.Module S`: the category of almost `V`-modules.
* `TauCeti.Almost.toAlmost S`: the almostification functor `ModuleCat V ⥤ Almost.Module S`.
* `TauCeti.Almost.Module.classicalEquiv`: for the classical setup `(V, V)`, almostification is an
  equivalence `ModuleCat V ≌ Almost.Module (classical V)`.

## Main results

* `TauCeti.Almost.Module.instAbelian`: almost modules form an abelian category.
* `TauCeti.Almost.isZero_toAlmost_obj_iff`: `M^a` is zero iff `M` is almost zero.
* `TauCeti.Almost.isIso_toAlmost_map_iff`: `f^a` is an isomorphism iff `f` is an almost
  isomorphism; `mono_toAlmost_map_iff` and `epi_toAlmost_map_iff` treat monomorphisms and
  epimorphisms, and `toAlmost_map_eq_zero_iff` zero morphisms.
* `TauCeti.Almost.toAlmost` is exact and essentially surjective. Since it is a localization
  functor for a Serre class, Mathlib's `ObjectProperty.SerreClassLocalization.exactFunctor_comp_iff`
  shows that a functor out of almost modules is exact iff its composite with `toAlmost S` is.
* `TauCeti.Almost.mem_essImage_whiskeringLeft_toAlmost_iff`: an exact functor out of `ModuleCat V`
  factors through `toAlmost S` via an exact functor iff it kills the almost zero modules.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2, (2.2.2).
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4, Definition 4.3.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Proposition 4.1.7.
-/

public section

universe u v w

open CategoryTheory Limits

namespace TauCeti.Almost

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- The category of **almost `V`-modules** over a basic setup `S = (V, m)` (Scholze, *Perfectoid
spaces*, Definition 4.3): the localization of `ModuleCat V` at the almost isomorphisms, that is,
the Serre quotient of `ModuleCat V` by the almost zero modules. Its Hom-types live in `Type u`. -/
abbrev Module : Type (u + 1) :=
  (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.Localization'

/-- The almostification functor `M ↦ M^a` from `V`-modules to almost `V`-modules. -/
noncomputable abbrev toAlmost : ModuleCat.{u} V ⥤ Module S :=
  (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre.Q'

namespace Module

/-- **Almost modules form an abelian category**, as a Serre quotient of `ModuleCat V`. -/
noncomputable instance instAbelian : Abelian (Module S) :=
  ObjectProperty.SerreClassLocalization.abelian (toAlmost S) S.almostZero

end Module

/-- Almostification is left exact. -/
instance : PreservesFiniteLimits (toAlmost S) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits _ S.almostZero

/-- Almostification is right exact. -/
instance : PreservesFiniteColimits (toAlmost S) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits _ S.almostZero

/-- Every almost module is isomorphic to the almostification of a `V`-module. -/
instance : (toAlmost S).EssSurj :=
  Localization.essSurj _ (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre

variable {S}

/-- The almostification `M^a` of a `V`-module is a zero object iff `M` is almost zero. -/
@[simp]
theorem isZero_toAlmost_obj_iff (M : ModuleCat.{u} V) :
    IsZero ((toAlmost S).obj M) ↔ S.IsAlmostZero M :=
  (ObjectProperty.SerreClassLocalization.isZero_obj_iff _ S.almostZero M).trans (S.almostZero_iff M)

/-- The almostification `f^a` of a linear map is an isomorphism iff `f` is an almost isomorphism:
its kernel and cokernel are almost zero. -/
@[simp]
theorem isIso_toAlmost_map_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    IsIso ((toAlmost S).map f) ↔ S.IsAlmostIso f.hom := by
  rw [ObjectProperty.SerreClassLocalization.isIso_map_iff _ S.almostZero,
    S.isAlmostIso_iff_isoModSerre]

/-- The almostification `f^a` of a linear map is a monomorphism iff the kernel of `f` is almost
zero. -/
@[simp]
theorem mono_toAlmost_map_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    Mono ((toAlmost S).map f) ↔ S.IsAlmostZero (LinearMap.ker f.hom) := by
  rw [ObjectProperty.SerreClassLocalization.mono_map_iff _ S.almostZero,
    ObjectProperty.monoModSerre_iff, S.almostZero.prop_iff_of_iso (ModuleCat.kernelIsoKer f),
    S.almostZero_iff]

/-- The almostification `f^a` of a linear map is an epimorphism iff the cokernel of `f` is almost
zero. -/
@[simp]
theorem epi_toAlmost_map_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    Epi ((toAlmost S).map f) ↔ S.IsAlmostZero (N ⧸ LinearMap.range f.hom) := by
  rw [ObjectProperty.SerreClassLocalization.epi_map_iff _ S.almostZero,
    ObjectProperty.epiModSerre_iff,
    S.almostZero.prop_iff_of_iso (ModuleCat.cokernelIsoRangeQuotient f), S.almostZero_iff]

/-- The almostification `f^a` of a linear map is zero iff the range of `f` is almost zero. -/
@[simp]
theorem toAlmost_map_eq_zero_iff {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    (toAlmost S).map f = 0 ↔ S.IsAlmostZero (LinearMap.range f.hom) := by
  rw [ObjectProperty.SerreClassLocalization.map_eq_zero_iff _ S.almostZero,
    S.almostZero.prop_iff_of_iso (Abelian.imageIsoImage f ≪≫ ModuleCat.imageIsoRange f),
    S.almostZero_iff]

variable {E : Type w} [Category.{v} E] [Abelian E]

variable (S E) in
/-- **The universal property of almost modules among exact functors.** An exact functor `F` out of
`ModuleCat V` is isomorphic to `toAlmost S ⋙ G` for an exact functor `G` out of almost modules iff
`F` kills every almost zero module. Such a factorization is unique up to unique isomorphism, since
precomposition with `toAlmost S` is fully faithful on exact functors
(`ObjectProperty.SerreClassLocalization.fullyFaithfulWhiskeringLeft`). -/
theorem mem_essImage_whiskeringLeft_toAlmost_iff (F : ModuleCat.{u} V ⥤ₑ E) :
    (ObjectProperty.SerreClassLocalization.whiskeringLeft (toAlmost S) S.almostZero E).essImage F ↔
      ∀ M : ModuleCat.{u} V, S.IsAlmostZero M → IsZero (F.obj.obj M) := by
  have := F.property.1
  have := F.property.2
  rw [ObjectProperty.SerreClassLocalization.essImage_whiskeringLeft]
  exact (S.almostZero.isoModSerre_isInvertedBy_iff F.obj).trans
    (forall_congr' fun M ↦ imp_congr (S.almostZero_iff M) Iff.rfl)

/-- For the classical setup `(V, V)` every almost isomorphism is an isomorphism, so
almostification is an equivalence of categories. -/
instance isEquivalence_toAlmost_classical : (toAlmost (BasicSetup.classical V)).IsEquivalence :=
  have := Functor.IsLocalization.for_id
    ((BasicSetup.classical V).almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre
    (BasicSetup.isoModSerre_classical (V := V)).le
  Functor.isEquivalence_of_iso (Localization.compUniqFunctor (𝟭 _) (toAlmost _)
    ((BasicSetup.classical V).almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre)

namespace Module

/-- For the classical setup `(V, V)`, almostification is an equivalence
`ModuleCat V ≌ Almost.Module (classical V)`: almost mathematics over the classical setup is
ordinary module theory. -/
noncomputable def classicalEquiv : ModuleCat.{u} V ≌ Module (BasicSetup.classical V) :=
  (toAlmost (BasicSetup.classical V)).asEquivalence

@[simp]
theorem classicalEquiv_functor :
    (classicalEquiv (V := V)).functor = toAlmost (BasicSetup.classical V) :=
  (rfl)

end Module

end TauCeti.Almost
