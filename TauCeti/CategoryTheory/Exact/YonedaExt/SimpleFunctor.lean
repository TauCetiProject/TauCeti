/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Resolution.ProjectiveResolution
public import TauCeti.CategoryTheory.Exact.YonedaExt.AlmostSplit
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.AlmostSplit
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

/-!
# The minimal projective resolution of the simple functor of an almost-split conflation

For a conflation `X ⟶ Y ⟶ Z` whose deflation is right almost split, the representable functors
on its terms give a projective resolution of `S_Z = Hom(-, Z) / rad(-, Z)` in the category of
additive functors:
`0 ⟶ Hom(-, X) ⟶ Hom(-, Y) ⟶ Hom(-, Z) ⟶ S_Z ⟶ 0`.

This resolution is minimal exactly when the conflation is almost split. The augmentation is
always a projective cover, and the degree-two map onto the second syzygy is an isomorphism.
Thus the only cover condition to check is the map `Hom(-, Y) ⟶ rad(-, Z)` onto the first syzygy.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, LMS Student Texts 65, CUP (2006), Theorem IV.6.11(a)(ii) for module categories.
-/

public section

universe v u

open CategoryTheory Limits Preadditive

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ModCat

/-- The radical subfunctor `rad(-, Z)` of the representable module on `Z`. -/
abbrev radical (Z : C) : ModCat.{v} C := ⟨radicalFunctor Z, (additiveFunctor_iff _).2
  { map_add := by
      intro W W' k l
      let i := radicalFunctorι Z
      have : Mono (i.app W') := inferInstanceAs (Mono ((radicalFunctorι Z).app W'))
      rw [← cancel_mono (i.app W'), add_comp, i.naturality, i.naturality, i.naturality]
      simp [comp_add] }⟩

/-- The quotient `Hom(-, Z) / rad(-, Z)` as a module on the preadditive category. -/
noncomputable abbrev simple (Z : C) : ModCat.{v} C :=
  ⟨simpleFunctor Z, (additiveFunctor_iff _).2 inferInstance⟩

end ModCat

namespace ExactStructure.Extension

variable [HasZeroObject C] [HasBinaryBiproducts C] {E : ExactStructure C} {X Z : C}
  (e : E.Extension Z X)

/-- A conflation ending at an object with local endomorphism ring is almost split exactly
when the Yoneda map of its deflation factors as a projective cover of the radical followed
by the radical inclusion. This is the minimality condition in degree one of
`simpleFunctorResolution`.
-/
theorem isAlmostSplit_iff_exists_isRepresentableProjectiveCover_radicalFunctorLift
    [IsLocalRing (End Z)] :
    e.shortComplex.IsAlmostSplit ↔ ∃ hg : e.g ∈ jacobsonRadical e.obj Z,
      IsRepresentableProjectiveCover (radicalFunctorLift e.g hg) := by
  constructor
  · intro h
    let hg := h.isRightAlmostSplit_g
    refine ⟨hg.mem_jacobsonRadical,
      (isRepresentableProjectiveCover_radicalFunctorLift_iff _).2 ⟨hg, fun b hb ↦ ?_⟩⟩
    have hK := e.isKernelCokernelPair
    have hz : (𝟙 e.obj - b) ≫ e.g = 0 := by simp [sub_comp, hb]
    let t := hK.lift _ hz
    have ht : t ≫ e.f = 𝟙 e.obj - b := hK.lift_f _ hz
    have hrad := h.isLeftAlmostSplit_f.mem_jacobsonRadical
    simpa [ht] using (mem_jacobsonRadical_iff_isIso_id_sub_comp_left.1 hrad t)
  · rintro ⟨hrad, hp⟩
    obtain ⟨hg, hmin⟩ := (isRepresentableProjectiveCover_radicalFunctorLift_iff hrad).1 hp
    refine ⟨e.shortExact, isLeftAlmostSplit_iff.2 ⟨?_, ?_⟩, hg⟩
    · exact fun h ↦ hg.not_isSplitEpi
        ((Ext1.mk_eq_zero_iff_isSplitEpi e).1 ((Ext1.mk_eq_zero_iff_isSplitMono e).2 h))
    · intro W f hf
      rw [← Ext1.mk_pushout_eq_zero_iff, Ext1.pushout_mk, Ext1.mk_eq_zero_iff_isSplitEpi]
      by_contra hp
      obtain ⟨t, ht⟩ := hg.factors _ (e.pushout f).g hp
      have hb : (e.pushoutInl f ≫ t) ≫ e.g = e.g := by simp [Category.assoc, ht]
      have := hmin _ hb
      have hinv := (IsIso.inv_comp_eq (e.pushoutInl f ≫ t)).2 hb.symm
      have hzero : ((e.pushout f).f ≫ t ≫ inv (e.pushoutInl f ≫ t)) ≫ e.g = 0 := by
        simp [Category.assoc, hinv, ht]
      let r := e.isKernelCokernelPair.lift _ hzero
      have hr : r ≫ e.f = (e.pushout f).f ≫ t ≫ inv (e.pushoutInl f ≫ t) :=
        e.isKernelCokernelPair.lift_f _ hzero
      have := e.isKernelCokernelPair.mono_f
      apply hf
      refine IsSplitMono.mk' ⟨r, (cancel_mono e.f).1 ?_⟩
      rw [Category.assoc, hr, ← e.f_pushoutInl_assoc, Category.id_comp]
      simp only [← Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The short exact sequence `0 ⟶ Hom(-, X) ⟶ Hom(-, Y) ⟶ rad(-, Z) ⟶ 0` of a conflation
with right almost split deflation. -/
theorem shortExact_radicalFunctorLift (hg : IsRightAlmostSplit e.g) :
    ∃ w : preadditiveYoneda.map e.f ≫ radicalFunctorLift e.g hg.mem_jacobsonRadical = 0,
      (ShortComplex.mk _ _ w).ShortExact := by
  let p := radicalFunctorLift e.g hg.mem_jacobsonRadical
  have w : preadditiveYoneda.map e.f ≫ p = 0 := by
    rw [← cancel_mono (radicalFunctorι Z), Category.assoc, radicalFunctorLift_comp_ι,
      ← Functor.map_comp, e.zero, Functor.map_zero, zero_comp]
  have := hg.isLocalRing_end
  obtain ⟨_, hp⟩ := isRightAlmostSplit_iff_exists_epi_radicalFunctorLift.1 hg
  -- Yoneda preserves the kernel of the deflation. Factoring the deflation through the
  -- radical inclusion leaves that kernel unchanged.
  have hK := KernelFork.mapIsLimit _ e.isKernelCokernelPair.fIsKernel preadditiveYoneda
  have hk : IsLimit (KernelFork.ofι (preadditiveYoneda.map e.f) w) :=
    isKernelOfComp (radicalFunctorι Z) _ hK w (radicalFunctorLift_comp_ι _ _)
  exact ⟨w, ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hk)
    (mono_of_isLimit_fork hk) hp⟩

/-- The two-step projective resolution of the simple functor associated to a conflation
with right almost split deflation. Its terms are the representables on `Z`, `e.obj`, and
`X` in degrees zero, one, and two, respectively. -/
noncomputable def simpleFunctorResolution (hg : IsRightAlmostSplit e.g) :
    FiniteResolution (ExactStructure.abelian (ModCat.{v} C)) Projective (ModCat.simple Z) := by
  let Y := ModCat.yoneda C
  let i : ModCat.radical Z ⟶ Y.obj Z := ObjectProperty.homMk (radicalFunctorι Z)
  let π : Y.obj Z ⟶ ModCat.simple Z := ObjectProperty.homMk (simpleFunctorπ Z)
  let p : Y.obj e.obj ⟶ ModCat.radical Z :=
    ObjectProperty.homMk (radicalFunctorLift e.g hg.mem_jacobsonRadical)
  have h₀ : i ≫ π = 0 := ObjectProperty.hom_ext _ (radicalFunctorι_comp_simpleFunctorπ Z)
  have hS := e.shortExact_radicalFunctorLift hg
  have h₁ : Y.map e.f ≫ p = 0 := ObjectProperty.hom_ext _ hS.choose
  let ι := (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι
  refine .step inferInstance i π h₀ (abelian_conflation _ |>.2 ?_)
    (.step inferInstance (Y.map e.f) p h₁ (abelian_conflation _ |>.2 ?_)
      (.base inferInstance))
  · exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful ι (shortExact_radicalFunctor Z)
  · exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful ι hS.choose_spec

/-- The finite projective resolution of the simple functor has two short exact steps. -/
@[simp]
theorem simpleFunctorResolution_length (hg : IsRightAlmostSplit e.g) :
    (e.simpleFunctorResolution hg).length = 2 := by
  simp [simpleFunctorResolution]

variable {e} in
/-- The augmentation term of the simple functor resolution represents `Z`. -/
@[simp]
theorem simpleFunctorResolution_term_zero (hg : IsRightAlmostSplit e.g) :
    (e.simpleFunctorResolution hg).term 0 = (ModCat.yoneda C).obj Z :=
  (rfl)

variable {e} in
/-- The degree-one term of the simple functor resolution represents the middle object. -/
@[simp]
theorem simpleFunctorResolution_term_one (hg : IsRightAlmostSplit e.g) :
    (e.simpleFunctorResolution hg).term 1 = (ModCat.yoneda C).obj e.obj :=
  (rfl)

variable {e} in
/-- The degree-two term of the simple functor resolution represents `X`. -/
@[simp]
theorem simpleFunctorResolution_term_two (hg : IsRightAlmostSplit e.g) :
    (e.simpleFunctorResolution hg).term 2 = (ModCat.yoneda C).obj X :=
  (rfl)

/-- The first syzygy of the simple functor in this resolution is the radical functor. -/
@[simp]
theorem simpleFunctorResolution_syzygy_one (hg : IsRightAlmostSplit e.g) :
    (e.simpleFunctorResolution hg).syzygy 1 = ModCat.radical Z :=
  (rfl)

/-- The augmentation of the simple functor resolution is the quotient by the radical. -/
@[simp]
theorem simpleFunctorResolution_aug (hg : IsRightAlmostSplit e.g) :
    (e.simpleFunctorResolution hg).aug =
      eqToHom (simpleFunctorResolution_term_zero hg) ≫
        ObjectProperty.homMk (Y := ModCat.simple Z) (simpleFunctorπ Z) := by
  simp only [simpleFunctorResolution, FiniteResolution.aug_step]
  erw [eqToHom_refl, Category.id_comp]

/-- The differential in degree one is the Yoneda map of the deflation. -/
@[simp]
theorem simpleFunctorResolution_d_zero (hg : IsRightAlmostSplit e.g) :
    (e.simpleFunctorResolution hg).d 0 =
      eqToHom (simpleFunctorResolution_term_one hg) ≫ (ModCat.yoneda C).map e.g ≫
        eqToHom (simpleFunctorResolution_term_zero hg).symm := by
  simp only [simpleFunctorResolution, FiniteResolution.d_step_zero, FiniteResolution.aug_step]
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ObjectProperty.hom_ext _ (radicalFunctorLift_comp_ι _ _)

/-- The differential in degree two is the Yoneda map of the inflation. -/
@[simp]
theorem simpleFunctorResolution_d_one (hg : IsRightAlmostSplit e.g) :
    (e.simpleFunctorResolution hg).d 1 =
      eqToHom (simpleFunctorResolution_term_two hg) ≫ (ModCat.yoneda C).map e.f ≫
        eqToHom (simpleFunctorResolution_term_one hg).symm := by
  simp only [simpleFunctorResolution, FiniteResolution.d_step_succ, FiniteResolution.d_step_zero,
    FiniteResolution.aug_base, Category.id_comp]
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

end ExactStructure.Extension

end TauCeti
