/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.WeakKernels
public import TauCeti.CategoryTheory.ObjectProperty.Retract

/-!
# Projective objects and projective dimension in `mod C`

Let `C` be a preadditive category. The Yoneda embedding `TauCeti.modYoneda` sends `C` to
projective objects of the category `mod C` of finitely presented functors `Cᵒᵖ ⥤ AddCommGrpCat`,
and every object of `mod C` is a quotient of a finite sum of them, which is again projective; so
`mod C` has enough projectives. When `C` has finite biproducts, every object of `mod C` is a
quotient of a single representable functor, and when `C` is moreover idempotent complete, the
projective objects of `mod C` are exactly the representable functors, so the homological algebra
of `mod C` can be read off from `C`.

When `C` has finite biproducts and weak kernels, `mod C` is abelian, and the main result
(`TauCeti.hasKernels_iff_forall_hasProjectiveDimensionLE_two`) states that, for idempotent complete
`C`, every object of `mod C` has projective dimension at most two exactly when `C` has kernels.
A functor `F` presented by `f : X ⟶ Y` sits in an exact sequence
`0 ⟶ K ⟶ (-, X) ⟶ (-, Y) ⟶ F ⟶ 0`, where `K` is projective exactly when `F` has projective
dimension at most two. If `f` has a kernel, then `K` is `(-, ker f)`; conversely a projective `K`
is representable, and it represents a kernel of `f`. Since abelian categories have kernels, every
finitely presented functor on an abelian category has projective dimension at most two.

## Main declarations

* `TauCeti.projective_modYoneda_obj`: representable functors are projective in `mod C`, which has
  enough projectives.
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

/-- An object of `mod C` whose underlying functor is a finite sum of representable functors is
projective: a morphism out of it to the target of an epimorphism `E ⟶ G` lifts summand by
summand, since `E` is additive. -/
private theorem projective_of_obj_eq_sigma
    (P : (isFinitelyPresentedFunctor C).FullSubcategory) {n : ℕ} (Y : Fin n → C)
    (hP : P.obj = ∐ fun i ↦ preadditiveYoneda.obj (Y i)) : Projective P where
  factors {E G} f e _ := by
    have := (isFinitelyPresentedFunctor C).preservesEpimorphisms_ι_of_isNormalMonoCategory
    have : Epi e.hom := inferInstanceAs (Epi ((isFinitelyPresentedFunctor C).ι.map e))
    have := E.property.additive
    obtain ⟨P, hP'⟩ := P
    subst hP
    obtain ⟨s, hs⟩ := exists_comp_eq_sigma_preadditiveYoneda_obj_of_epi e.hom f.hom
    exact ⟨ObjectProperty.homMk s, ObjectProperty.hom_ext _ hs⟩

/-- Representable functors are projective objects of `mod C`. -/
instance projective_modYoneda_obj (Y : C) : Projective (modYoneda.obj Y) where
  factors {E G} f e _ := by
    have := (isFinitelyPresentedFunctor C).preservesEpimorphisms_ι_of_isNormalMonoCategory
    have : Epi e.hom := inferInstanceAs (Epi ((isFinitelyPresentedFunctor C).ι.map e))
    have := E.property.additive
    obtain ⟨s, hs⟩ := exists_comp_eq_preadditiveYoneda_obj_of_epi e.hom f.hom
    exact ⟨ObjectProperty.homMk s, ObjectProperty.hom_ext _ hs⟩

/-- `mod C` has enough projectives: every object is a quotient of a finite sum of representable
functors. -/
instance : EnoughProjectives (isFinitelyPresentedFunctor C).FullSubcategory where
  presentation F := by
    obtain ⟨n, Y, p, hp⟩ :=
      isFinitelyGeneratedFunctor_def.1 F.property.isFinitelyGeneratedFunctor
    let P : (isFinitelyPresentedFunctor C).FullSubcategory :=
      ⟨_, (isFinitelyPresentedFunctor C).prop_coproduct fun i ↦
        isFinitelyPresentedFunctor_preadditiveYoneda_obj (Y i)⟩
    have : Projective P := projective_of_obj_eq_sigma P Y rfl
    have : Epi (ObjectProperty.homMk p : P ⟶ F) :=
      (isFinitelyPresentedFunctor C).ι.epi_of_epi_map hp
    exact ⟨{ p := P, f := ObjectProperty.homMk p }⟩

variable [HasFiniteBiproducts C]

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
  obtain ⟨X, Y, f, p, hfp, hp, hS⟩ := (isFinitelyPresentedFunctor_iff_exists_single _).1 F.property
  have hc' : IsColimit (CokernelCofork.ofπ (f := modYoneda.map f)
      (ObjectProperty.homMk p : modYoneda.obj Y ⟶ F) (ObjectProperty.hom_ext _ hfp)) :=
    isColimitOfReflects (isFinitelyPresentedFunctor C).ι
      ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm (hS.gIsCokernel :))
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
finite biproducts and weak kernels has kernels exactly when every finitely presented functor
`Cᵒᵖ ⥤ AddCommGrpCat` has projective dimension at most two in `mod C`. -/
theorem hasKernels_iff_forall_hasProjectiveDimensionLE_two [IsIdempotentComplete C] :
    HasKernels C ↔
      ∀ F : (isFinitelyPresentedFunctor C).FullSubcategory, HasProjectiveDimensionLE F 2 :=
  ⟨fun _ ↦ hasProjectiveDimensionLE_two_of_hasKernels,
    hasKernels_of_forall_hasProjectiveDimensionLE_two⟩

-- In particular, over an abelian category `D`, every object of `mod D` has projective dimension at
-- most two.
attribute [local instance] Abelian.hasFiniteBiproducts in
example {D : Type u} [Category.{v} D] [Abelian D]
    (F : (isFinitelyPresentedFunctor D).FullSubcategory) : HasProjectiveDimensionLE F 2 :=
  hasProjectiveDimensionLE_two_of_hasKernels F

end TauCeti
