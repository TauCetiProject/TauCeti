/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.WeakKernels
public import TauCeti.CategoryTheory.ObjectProperty.Retract

/-!
# Projective objects and projective dimension in `mod C`

Let `C` be a nonempty preadditive category with binary biproducts. The Yoneda embedding
`TauCeti.modYoneda` sends `C` to projective objects of the category `mod C` of finitely presented
functors `Cᵒᵖ ⥤ AddCommGrpCat`, and every object of `mod C` is a quotient of one of them. When `C`
is idempotent complete, the projective objects of `mod C` are exactly the representable functors,
so the homological algebra of `mod C` can be read off from `C`.

When `C` also has weak kernels, `mod C` is abelian, and the main result
(`TauCeti.hasKernels_iff_forall_hasProjectiveDimensionLE_two`) states that, for idempotent complete
`C`, every object of `mod C` has projective dimension at most two exactly when `C` has kernels.
A functor `F` presented by `f : X ⟶ Y` sits in an exact sequence
`0 ⟶ K ⟶ (-, X) ⟶ (-, Y) ⟶ F ⟶ 0`, where `K` is projective exactly when `F` has projective
dimension at most two. If `f` has a kernel, then `K` is `(-, ker f)`; conversely a projective `K`
is representable, and it represents a kernel of `f`. Since abelian categories have kernels, every
finitely presented functor on an abelian category has projective dimension at most two.

## Main declarations

* `TauCeti.modYoneda`: the Yoneda embedding of `C` into `mod C`.
* `TauCeti.projective_iff_mem_essImage_modYoneda`: for idempotent complete `C`, the projective
  objects of `mod C` are the representable functors.
* `TauCeti.hasProjectiveDimensionLE_two_of_hasKernels`: if `C` has kernels, then every object of
  `mod C` has projective dimension at most two.
* `TauCeti.hasKernels_iff_forall_hasProjectiveDimensionLE_two`: the characterization above.

## References

* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer, 1966, 189-231.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The Yoneda embedding of `C` into `mod C`, sending `X` to the representable functor `(-, X)`. -/
abbrev modYoneda : C ⥤ (isFinitelyPresentedFunctor C).FullSubcategory :=
  (isFinitelyPresentedFunctor C).lift preadditiveYoneda
    isFinitelyPresentedFunctor_preadditiveYoneda_obj

instance : (modYoneda : C ⥤ _).Additive where
  map_add := ObjectProperty.hom_ext _ preadditiveYoneda.map_add

/-- The Yoneda embedding of `C` into `mod C` preserves small limits, since `preadditiveYoneda`
does and the inclusion of `mod C` into the functor category reflects them. -/
instance (J : Type*) [Category* J] [Small.{v} J] :
    PreservesLimitsOfShape J (modYoneda : C ⥤ (isFinitelyPresentedFunctor C).FullSubcategory) :=
  have : PreservesLimitsOfShape J ((modYoneda : C ⥤ _) ⋙ (isFinitelyPresentedFunctor C).ι) :=
    inferInstanceAs (PreservesLimitsOfShape J (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v}))
  preservesLimitsOfShape_of_reflects_of_preserves _ (isFinitelyPresentedFunctor C).ι

/-- Every object of `mod C` is a quotient of a representable functor. -/
theorem exists_epi_modYoneda_obj (F : (isFinitelyPresentedFunctor C).FullSubcategory) :
    ∃ (Y : C) (p : modYoneda.obj Y ⟶ F), Epi p := by
  obtain ⟨Y, p, hp⟩ := isFinitelyGeneratedFunctor_def.1 F.property.isFinitelyGeneratedFunctor
  exact ⟨Y, ObjectProperty.homMk p, (isFinitelyPresentedFunctor C).ι.epi_of_epi_map hp⟩

variable [HasBinaryBiproducts C] [Nonempty C]

/-- Representable functors are projective objects of `mod C`. -/
instance projective_modYoneda_obj (Y : C) : Projective (modYoneda.obj Y) where
  factors {E G} f e _ := by
    have := (isFinitelyPresentedFunctor C).preservesEpimorphisms_ι_of_isNormalMonoCategory
    have : Epi e.hom := inferInstanceAs (Epi ((isFinitelyPresentedFunctor C).ι.map e))
    obtain ⟨Y', q, hq⟩ := isFinitelyGeneratedFunctor_def.1 E.property.isFinitelyGeneratedFunctor
    obtain ⟨u, hu⟩ := exists_preadditiveYoneda_map_comp_eq (q ≫ e.hom) f.hom
    exact ⟨ObjectProperty.homMk (preadditiveYoneda.map u ≫ q),
      ObjectProperty.hom_ext _ (by simpa using hu)⟩

/-- `mod C` has enough projectives, given by representable functors. -/
instance : EnoughProjectives (isFinitelyPresentedFunctor C).FullSubcategory where
  presentation F := by
    obtain ⟨Y, p, hp⟩ := exists_epi_modYoneda_obj F
    exact ⟨{ p := modYoneda.obj Y, f := p }⟩

/-- For idempotent complete `C`, the projective objects of `mod C` are the representable functors.
-/
theorem projective_iff_mem_essImage_modYoneda [IsIdempotentComplete C]
    {F : (isFinitelyPresentedFunctor C).FullSubcategory} :
    Projective F ↔ (modYoneda : C ⥤ _).essImage F := by
  refine ⟨fun _ ↦ ?_, fun ⟨Y, ⟨e⟩⟩ ↦ Projective.of_iso e inferInstance⟩
  -- A projective object is a retract of a representable functor, cut out by an idempotent of `C`.
  obtain ⟨Y, p, hp⟩ := exists_epi_modYoneda_obj F
  exact (modYoneda : C ⥤ _).essImage.prop_of_retract
    ⟨Projective.factorThru (𝟙 F) p, p, Projective.factorThru_comp _ _⟩
    (Functor.obj_mem_essImage _ Y)

/-- If `C` has kernels, every object of `mod C` has projective dimension at most two. A functor
presented by `f : X ⟶ Y` has the projective resolution
`0 ⟶ (-, ker f) ⟶ (-, X) ⟶ (-, Y) ⟶ F ⟶ 0`. -/
theorem hasProjectiveDimensionLE_two_of_hasKernels [HasKernels C]
    (F : (isFinitelyPresentedFunctor C).FullSubcategory) : HasProjectiveDimensionLE F 2 := by
  obtain ⟨X, Y, f, p, hfp, ⟨hc⟩⟩ := isFinitelyPresentedFunctor_iff_exists_isColimit.1 F.property
  have hc' : IsColimit (CokernelCofork.ofπ (f := modYoneda.map f)
      (ObjectProperty.homMk p : modYoneda.obj Y ⟶ F) (ObjectProperty.hom_ext _ hfp)) :=
    isColimitOfReflects (isFinitelyPresentedFunctor C).ι
      ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm (hc :))
  have : Projective (kernel (modYoneda.map f)) :=
    Projective.of_iso (PreservesKernel.iso modYoneda f) inferInstance
  have := (hasProjectiveDimensionLT_cokernel_iff_kernel (modYoneda.map f) 0).2 inferInstance
  have e : cokernel (modYoneda.map f) ≅ F :=
    (colimit.isColimit _).coconePointUniqueUpToIso hc'
  exact hasProjectiveDimensionLT_of_iso e 3

variable [HasWeakKernels C]

/-- For idempotent complete `C`, if every object of `mod C` has projective dimension at most two,
then `C` has kernels. -/
theorem hasKernels_of_forall_hasProjectiveDimensionLE_two [IsIdempotentComplete C]
    (h : ∀ F : (isFinitelyPresentedFunctor C).FullSubcategory, HasProjectiveDimensionLE F 2) :
    HasKernels C where
  has_limit {Y Z} g := by
    have : HasProjectiveDimensionLT (kernel (modYoneda.map g)) 1 :=
      (hasProjectiveDimensionLT_cokernel_iff_kernel (modYoneda.map g) 0).1 (h _)
    -- The kernel of `(-, g)` is projective, hence representable, and represents a kernel of `g`.
    obtain ⟨X, ⟨e⟩⟩ := projective_iff_mem_essImage_modYoneda.1
      (inferInstance : Projective (kernel (modYoneda.map g)))
    obtain ⟨k, hk⟩ := modYoneda.map_surjective (e.hom ≫ kernel.ι _)
    have w : k ≫ g = 0 := modYoneda.map_injective (by
      rw [Functor.map_comp, hk, Category.assoc, kernel.condition, comp_zero, Functor.map_zero])
    have hl : IsLimit (KernelFork.ofι (modYoneda.map k) (f := modYoneda.map g)
        (by rw [← Functor.map_comp, w, Functor.map_zero])) :=
      have hι : e.inv ≫ modYoneda.map k = kernel.ι _ := by rw [hk, e.inv_hom_id_assoc]
      IsLimit.ofIsoLimit (kernelIsKernel _) (Fork.ext e.symm hι)
    exact HasLimit.mk ⟨KernelFork.ofι k w, isLimitOfReflects modYoneda
      ((KernelFork.isLimitMapConeEquiv _ _).symm (hl :))⟩

/-- **Projective dimension at most two.** An idempotent complete preadditive category `C` with
binary biproducts and weak kernels has kernels exactly when every finitely presented functor
`Cᵒᵖ ⥤ AddCommGrpCat` has projective dimension at most two in `mod C`. -/
theorem hasKernels_iff_forall_hasProjectiveDimensionLE_two [IsIdempotentComplete C] :
    HasKernels C ↔
      ∀ F : (isFinitelyPresentedFunctor C).FullSubcategory, HasProjectiveDimensionLE F 2 :=
  ⟨fun _ ↦ hasProjectiveDimensionLE_two_of_hasKernels,
    hasKernels_of_forall_hasProjectiveDimensionLE_two⟩

-- In particular, over an abelian category `D`, every object of `mod D` has projective dimension at
-- most two.
example {D : Type u} [Category.{v} D] [Abelian D] [Nonempty D]
    (F : (isFinitelyPresentedFunctor D).FullSubcategory) : HasProjectiveDimensionLE F 2 :=
  hasProjectiveDimensionLE_two_of_hasKernels F

end TauCeti
