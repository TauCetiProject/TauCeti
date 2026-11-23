/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Local
public import Mathlib.Condensed.Solid
public import TauCeti.Topology.Category.Profinite.Basic

/-!
# Solid condensed modules are closed under limits

Mathlib defines a condensed `R`-module `A` to be solid, `CondensedMod.IsSolid R A`, when for
every profinite set `S` precomposition with the solidification map
`Condensed.profiniteSolidification R : R[S] ⟶ R[S]^solid` is a bijection
`(R[S]^solid ⟶ A) ≃ (R[S] ⟶ A)`. In other words, the solid condensed modules are exactly the
objects that are local with respect to the solidification maps, in the sense of
`CategoryTheory.MorphismProperty.isLocal`. This file records that identification and its
formal consequences:

* the extension of maps along a solidification map, `CondensedMod.IsSolid.desc`, with its
  factorization and uniqueness;
* the solid condensed modules are closed under isomorphisms, under limits of every shape
  (in particular products and kernels), and contain the zero objects;
* hence the full subcategory of solid condensed `R`-modules, and in particular the category
  `TauCeti.SolidAb` of solid condensed abelian groups, has all the limits that condensed
  modules have, created by its inclusion, together with kernels and a zero object;
* for a finite profinite set `S`, the solidification map `R[S] ⟶ R[S]^solid` is an
  isomorphism, because `R[S]^solid` is a right Kan extension along the fully faithful
  functor `FintypeCat.toProfinite`.

These are the parts of the structure theory of solid abelian groups that do not depend on the
computation of `ℤ[S]^solid` as a product of copies of `ℤ`: closure under colimits and
extensions, and the solidification reflection, need that computation.

## References

* D. Clausen and P. Scholze, *Lectures on condensed mathematics*, Lecture V, Definition 5.1
  and Theorem 5.8.
-/

public section

universe v w u

open CategoryTheory Limits Condensed

namespace CondensedMod

variable {R : Type (u + 1)} [Ring R]

/-- A condensed module is solid if and only if, for every profinite set `S`, precomposition
with the solidification map `R[S] ⟶ R[S]^solid` is a bijection on morphisms into it. -/
theorem isSolid_iff_bijective (A : CondensedMod.{u} R) :
    A.IsSolid ↔ ∀ S : Profinite.{u}, Function.Bijective
      (fun g : (profiniteSolid R).obj S ⟶ A ↦ (profiniteSolidification R).app S ≫ g) :=
  ⟨fun h S ↦ (isIso_iff_bijective _).1 (h.isIso_solidification_map S),
    fun h ↦ ⟨fun S ↦ (isIso_iff_bijective _).2 (h S)⟩⟩

/-- The solid condensed modules are exactly the objects that are local with respect to the
solidification maps `R[S] ⟶ R[S]^solid`, for `S` ranging over profinite sets. -/
theorem isSolid_eq_isLocal :
    (IsSolid R : ObjectProperty (CondensedMod.{u} R)) =
      (MorphismProperty.ofHoms (profiniteSolidification.{u} R).app).isLocal := by
  funext A
  refine propext ((isSolid_iff_bijective A).trans ⟨?_, fun h S ↦ h _ (.mk S)⟩)
  rintro h _ _ _ ⟨S⟩
  exact h S

namespace IsSolid

variable {A : CondensedMod.{u} R} [A.IsSolid] {S : Profinite.{u}}

/-- The extension of a morphism `R[S] ⟶ A` into a solid condensed module along the
solidification map `R[S] ⟶ R[S]^solid`. -/
noncomputable def desc (f : (profiniteFree R).obj S ⟶ A) : (profiniteSolid R).obj S ⟶ A :=
  ((isSolid_iff_bijective A).1 inferInstance S).2 f |>.choose

@[reassoc (attr := simp)]
theorem solidification_desc (f : (profiniteFree R).obj S ⟶ A) :
    (profiniteSolidification R).app S ≫ desc f = f :=
  ((isSolid_iff_bijective A).1 inferInstance S).2 f |>.choose_spec

/-- Two morphisms from `R[S]^solid` into a solid condensed module agree as soon as they agree
after precomposition with the solidification map. -/
@[ext]
theorem hom_ext {g₁ g₂ : (profiniteSolid R).obj S ⟶ A}
    (h : (profiniteSolidification R).app S ≫ g₁ = (profiniteSolidification R).app S ≫ g₂) :
    g₁ = g₂ :=
  ((isSolid_iff_bijective A).1 inferInstance S).1 h

@[simp]
theorem desc_solidification_comp (g : (profiniteSolid R).obj S ⟶ A) :
    desc ((profiniteSolidification R).app S ≫ g) = g :=
  hom_ext (by simp)

@[reassoc (attr := simp)]
theorem desc_comp {B : CondensedMod.{u} R} [B.IsSolid] (f : (profiniteFree R).obj S ⟶ A)
    (g : A ⟶ B) : desc f ≫ g = desc (f ≫ g) :=
  hom_ext (by simp)

end IsSolid

instance : ObjectProperty.IsClosedUnderIsomorphisms (C := CondensedMod.{u} R) (IsSolid R) := by
  rw [isSolid_eq_isLocal]
  infer_instance

instance (J : Type*) [Category* J] :
    ObjectProperty.IsClosedUnderLimitsOfShape (C := CondensedMod.{u} R) (IsSolid R) J := by
  rw [isSolid_eq_isLocal]
  infer_instance

/-- A zero condensed module is solid. -/
theorem isSolid_of_isZero {A : CondensedMod.{u} R} (hA : IsZero A) : A.IsSolid :=
  (isSolid_iff_bijective A).2 fun _ ↦
    ⟨fun _ _ _ ↦ hA.eq_of_tgt _ _, fun _ ↦ ⟨hA.from_ _, hA.eq_of_tgt _ _⟩⟩

instance : ObjectProperty.ContainsZero (C := CondensedMod.{u} R) (IsSolid R) where
  exists_zero := ⟨_, isZero_zero _, isSolid_of_isZero (isZero_zero _)⟩

instance : ObjectProperty.IsClosedUnderKernels (C := CondensedMod.{u} R) (IsSolid R) where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact ObjectProperty.prop_of_isLimit _ hk (by rintro (_ | _) <;> assumption)

/-- A limit of solid condensed modules is solid. -/
instance isSolid_limit {J : Type*} [Category* J] (F : J ⥤ CondensedMod.{u} R) [HasLimit F]
    [∀ j, (F.obj j).IsSolid] : (limit F).IsSolid :=
  ObjectProperty.prop_limit _ F fun _ ↦ inferInstance

/-- A product of solid condensed modules is solid. -/
instance isSolid_pi {ι : Type*} (A : ι → CondensedMod.{u} R) [HasProduct A]
    [∀ i, (A i).IsSolid] : (∏ᶜ A).IsSolid :=
  ObjectProperty.prop_pi _ A fun _ ↦ inferInstance

/-- The kernel of a morphism between solid condensed modules is solid. -/
instance isSolid_kernel {A B : CondensedMod.{u} R} (f : A ⟶ B) [A.IsSolid] [B.IsSolid] :
    (kernel f).IsSolid :=
  ObjectProperty.prop_kernel _ f ‹_› ‹_›

/-- The full subcategory of solid condensed `R`-modules has every size of limit that condensed
`R`-modules have; these limits are created by the inclusion into `CondensedMod R`. -/
instance hasLimitsOfSize_fullSubcategory_isSolid
    [HasLimitsOfSize.{v, w} (CondensedMod.{u} R)] :
    HasLimitsOfSize.{v, w} (ObjectProperty.FullSubcategory (IsSolid R)) where
  has_limits_of_shape _ _ := inferInstance

end CondensedMod

namespace Condensed

variable (R : Type (u + 1)) [Ring R]

/-- On finite sets, `R[-]^solid` agrees with `R[-]`: the counit of the right Kan extension
`profiniteSolid R` of `finFree R` along the fully faithful functor `FintypeCat.toProfinite`
is an isomorphism. -/
instance isIso_profiniteSolidCounit : IsIso (profiniteSolidCounit.{u} R) :=
  (profiniteSolidIsPointwiseRightKanExtension R).isIso_hom

/-- For a finite set `T`, the solidification map `R[T] ⟶ R[T]^solid` followed by the counit
`R[T]^solid ⟶ R[T]` of the right Kan extension `profiniteSolid R` is the identity. -/
@[reassoc (attr := simp)]
theorem profiniteSolidification_app_comp_profiniteSolidCounit_app (T : FintypeCat.{u}) :
    (profiniteSolidification R).app (FintypeCat.toProfinite.obj T) ≫
      (profiniteSolidCounit R).app T = 𝟙 _ :=
  (profiniteSolid R).liftOfIsRightKanExtension_fac_app (profiniteSolidCounit R) _ (𝟙 _) T

/-- The solidification map `R[T] ⟶ R[T]^solid` of a finite set `T` is an isomorphism; its
inverse is the counit `profiniteSolidCounit R`, see
`Condensed.inv_profiniteSolidification_app_toProfinite`. -/
instance isIso_profiniteSolidification_app_toProfinite (T : FintypeCat.{u}) :
    IsIso ((profiniteSolidification R).app (FintypeCat.toProfinite.obj T)) := by
  have : IsIso ((profiniteSolidification R).app (FintypeCat.toProfinite.obj T) ≫
      (profiniteSolidCounit R).app T) := by
    rw [profiniteSolidification_app_comp_profiniteSolidCounit_app]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((profiniteSolidCounit R).app T)

/-- The inverse of the solidification map `R[T] ⟶ R[T]^solid` of a finite set `T` is the
counit `profiniteSolidCounit R` of the right Kan extension. -/
@[simp]
theorem inv_profiniteSolidification_app_toProfinite (T : FintypeCat.{u}) :
    inv ((profiniteSolidification R).app (FintypeCat.toProfinite.obj T)) =
      (profiniteSolidCounit R).app T :=
  IsIso.inv_eq_of_hom_inv_id (profiniteSolidification_app_comp_profiniteSolidCounit_app R T)

/-- For a finite profinite set `S`, the solidification map `R[S] ⟶ R[S]^solid` is an
isomorphism. -/
instance isIso_profiniteSolidification_app (S : Profinite.{u}) [Finite S] :
    IsIso ((profiniteSolidification R).app S) := by
  have := Fintype.ofFinite S
  let e := Profinite.isoToProfiniteOfFintype S
  have h : (profiniteSolidification R).app S = (profiniteFree R).map e.hom ≫
      (profiniteSolidification R).app _ ≫ (profiniteSolid R).map e.inv := by
    rw [NatTrans.naturality_assoc, ← Functor.map_comp, e.hom_inv_id]
    simp
  rw [h]
  infer_instance

end Condensed

namespace TauCeti

/-- The category of solid condensed abelian groups: the full subcategory of `CondensedAb` on
the condensed abelian groups that are solid in the sense of `CondensedMod.IsSolid`. -/
abbrev SolidAb : Type (u + 2) :=
  ObjectProperty.FullSubcategory (CondensedMod.IsSolid (ULift.{u + 1} ℤ))

end TauCeti
