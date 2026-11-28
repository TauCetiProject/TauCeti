/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.HomotopyCategory.Functor
public import TauCeti.Algebra.Homology.HomotopyCategory.Linear
public import TauCeti.Algebra.Homology.HomotopyCategory.PreservesHomology
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution

/-!
# Additivity, commutation with exact functors, and dimension shifting for right derived functors

Injective resolutions are additive after passing to the homotopy category: the sum of
two lifts is a lift of the sum, and lifts of the same morphism are homotopic. Thus right
derived functors of additive functors are additive. In the same way, over an `R`-linear
category a scalar multiple of a lift is a lift of the scalar multiple, so right derived functors
of `R`-linear functors are `R`-linear (`CategoryTheory.Functor.linear_rightDerived`). If the
functor is exact, its positive right derived functors vanish.

`CategoryTheory.NatIso.rightDerived` transports a natural isomorphism to right derived
functors, with the induced transformations as its hom and inverse.

Right derived functors also commute with exact functors which preserve injective objects
(`CategoryTheory.Functor.rightDerivedCompIso`): if `F ⋙ G ≅ H ⋙ F'` where `G` preserves
homology and `H` preserves homology and injective objects, then `RⁿF ⋙ G ≅ H ⋙ RⁿF'`.

The proof uses Mathlib's `InjectiveResolution.descHomotopy`, the uniqueness theorem for
lifts between injective resolutions.

## Dimension shifting

For a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective, an injective resolution of `Q`
extends to one of `X` (`CategoryTheory.InjectiveResolution.ofShortExact`), which shifts the
right derived functors by one degree:

* `R^{n+2} G (X) ≅ R^{n+1} G (Q)` (`CategoryTheory.Functor.rightDerivedObjX₁IsoOfShortExact`), so
  `R^{n+1} G (Q)` vanishes if and only if `R^{n+2} G (X)` does
  (`CategoryTheory.Functor.isZero_rightDerived_obj_X₃_iff`);
* if `G` is left exact, then `R¹ G (X)` is the cokernel of `G I ⟶ G Q`
  (`CategoryTheory.Functor.rightDerivedOneIsoCokernel`), so `G I ⟶ G Q` is an epimorphism if and
  only if `R¹ G (X)` vanishes (`CategoryTheory.Functor.epi_map_g_iff_isZero_rightDerived_one`),
  and `0 ⟶ G X ⟶ G I ⟶ G Q ⟶ 0` is short exact if and only if `R¹ G (X)` vanishes
  (`CategoryTheory.Functor.shortExact_map_iff_isZero_rightDerived_one`).

These are the dimension-shifting steps of inductive arguments on vanishing derived functors,
such as Leray's acyclicity theorem.

The composition comparison is computed on arbitrary chosen resolutions by
`Functor.rightDerivedCompIso_app_injectiveResolution`. Its special case with the identity as the
outer functor, `RⁿF ≅ H' ⋙ RⁿF''` for `F ≅ H' ⋙ F''`, is `Functor.rightDerivedPrecompIso`.
The case of exact postcomposition, `RⁿF ⋙ G ≅ Rⁿ(F ⋙ G)`, is `Functor.rightDerivedPostcompIso`.
-/

public section

open CategoryTheory

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

/-- Choosing injective resolutions preserves addition in the homotopy category. -/
instance additive_injectiveResolutions : (injectiveResolutions C).Additive where
  map_add {X Y} f g := by
    let I := injectiveResolution X
    let J := injectiveResolution Y
    have h := InjectiveResolution.descHomotopy (f + g)
      (InjectiveResolution.desc (f + g) J I)
      (InjectiveResolution.desc f J I + InjectiveResolution.desc g J I)
      (by simp) (by simp [Preadditive.comp_add, Preadditive.add_comp])
    exact (HomotopyCategory.eq_of_homotopy _ _ h).trans
      (Functor.map_add (HomotopyCategory.quotient C (ComplexShape.up ℕ)))

/-- Choosing injective resolutions preserves scalar multiplication in the homotopy category. -/
instance linear_injectiveResolutions (R : Type*) [Semiring R] [Linear R C] :
    (injectiveResolutions C).Linear R where
  map_smul {X Y} f a := by
    let I := injectiveResolution X
    let J := injectiveResolution Y
    have h := InjectiveResolution.descHomotopy (a • f)
      (InjectiveResolution.desc (a • f) J I) (a • InjectiveResolution.desc f J I)
      (by simp) (by
        rw [Linear.comp_smul, InjectiveResolution.desc_commutes]
        -- morphisms out of `X[0]` are determined by their component in degree `0`
        refine HomologicalComplex.from_single_hom_ext ?_
        simp only [HomologicalComplex.comp_f, HomologicalComplex.smul_f_apply,
          HomologicalComplex.single_map_f_self, Linear.smul_comp, Linear.comp_smul,
          Category.assoc])
    exact (HomotopyCategory.eq_of_homotopy _ _ h).trans
      (Functor.map_smul (HomotopyCategory.quotient C (ComplexShape.up ℕ)) _ _)

variable {C} {D : Type*} [Category* D] [Abelian D]

/-- Right derived functors of an additive functor are additive. -/
instance Functor.additive_rightDerived (F : C ⥤ D) [F.Additive] (q : ℕ) :
    (F.rightDerived q).Additive :=
  inferInstanceAs ((injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙
    HomotopyCategory.homologyFunctor D _ q).Additive)

/-- Right derived functors of a linear functor are linear. -/
instance Functor.linear_rightDerived (R : Type*) [Semiring R] [CategoryTheory.Linear R C]
    [CategoryTheory.Linear R D] (F : C ⥤ D) [F.Additive] [F.Linear R] (q : ℕ) :
    (F.rightDerived q).Linear R :=
  inferInstanceAs ((injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙
    HomotopyCategory.homologyFunctor D _ q).Linear R)

/-- A natural isomorphism between additive functors induces an isomorphism between their
right derived functors in each degree. -/
noncomputable def NatIso.rightDerived {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := e.hom.rightDerived n
  inv := e.inv.rightDerived n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- The forward map of the derived isomorphism is the derived forward transformation. -/
@[simp]
lemma NatIso.rightDerived_hom {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : (NatIso.rightDerived e n).hom = e.hom.rightDerived n :=
  (rfl)

/-- The inverse map of the derived isomorphism is the derived inverse transformation. -/
@[simp]
lemma NatIso.rightDerived_inv {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (n : ℕ) : (NatIso.rightDerived e n).inv = e.inv.rightDerived n :=
  (rfl)

/-- An exact additive functor has no positive right derived functors. -/
theorem Functor.isZero_rightDerived_succ (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (X : C) (q : ℕ) : Limits.IsZero ((F.rightDerived (q + 1)).obj X) := by
  let I := injectiveResolution X
  refine Limits.IsZero.of_iso ?_ (I.isoRightDerivedObj F (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 1 + 1) (by simp) (by simp)]
  exact (I.exact_succ q).map F

/-- **Right derived functors commute with exact functors preserving injective objects.**
Let `F : C ⥤ D` and `F' : C' ⥤ D'` be additive functors, `G : D ⥤ D'` an additive functor
preserving homology, and `H : C ⥤ C'` an additive functor preserving homology and injective
objects, with `F ⋙ G ≅ H ⋙ F'`. Then `RⁿF ⋙ G ≅ H ⋙ RⁿF'` for every `n`.

Indeed `H` sends an injective resolution of `X` to an injective resolution of `H.obj X`, and `G`
commutes with taking homology. -/
noncomputable def Functor.rightDerivedCompIso {C' : Type*} [Category* C'] [Abelian C']
    [HasInjectiveResolutions C'] {D' : Type*} [Category* D'] [Abelian D']
    (F : C ⥤ D) [F.Additive] (G : D ⥤ D') [G.Additive] [G.PreservesHomology]
    (H : C ⥤ C') [H.Additive] [H.PreservesInjectiveObjects] [H.PreservesHomology]
    (F' : C' ⥤ D') [F'.Additive] (e : F ⋙ G ≅ H ⋙ F') (n : ℕ) :
    F.rightDerived n ⋙ G ≅ H ⋙ F'.rightDerived n :=
  -- `RⁿF` is `injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ homologyFunctor _ _ n`
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (injectiveResolutions C ⋙ F.mapHomotopyCategory _)
      (G.mapHomotopyCategoryCompHomologyFunctorIso _ n).symm ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (injectiveResolutions C)
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.mapHomotopyCategoryCompIso e _ ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ F')) _).symm) _ ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight H.injectiveResolutionsCompIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft H (Functor.associator _ _ _).symm

/-! ### Dimension shifting

Let `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` be a short exact sequence with `I` injective. An injective resolution
`Q ⟶ R⁰ ⟶ R¹ ⟶ ⋯` of `Q` extends to the injective resolution `X ⟶ I ⟶ R⁰ ⟶ R¹ ⟶ ⋯` of `X`
(`InjectiveResolution.ofShortExact`). Computing the right derived functors of `G` with these two
resolutions shifts degrees by one, without the long exact sequence of right derived functors. -/

section DimensionShift

open Limits

namespace Functor

variable (G : C ⥤ D) [G.Additive] {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]

include hS in
/-- **Dimension shifting.** For a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective,
`R^{n+2} G (X) ≅ R^{n+1} G (Q)`: an injective resolution of `Q` computes the right side, and its
extension `X ⟶ I ⟶ R⁰ ⟶ R¹ ⟶ ⋯` (`InjectiveResolution.ofShortExact`) computes the left side,
with the same differentials one degree higher. -/
noncomputable def rightDerivedObjX₁IsoOfShortExact (n : ℕ) :
    (G.rightDerived (n + 2)).obj S.X₁ ≅ (G.rightDerived (n + 1)).obj S.X₃ :=
  let R := injectiveResolution S.X₃
  (R.ofShortExact hS).isoRightDerivedObj G (n + 2) ≪≫
    HomologicalComplex.homologyIsoSc' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp) ≪≫
    -- the short complexes in degrees `n + 2` and `n + 1` agree by unfolding `augment`
    (HomologicalComplex.homologyIsoSc' ((G.mapHomologicalComplex _).obj R.cocomplex) n (n + 1)
      (n + 2) (by simp) (by simp)).symm ≪≫
    (R.isoRightDerivedObj G (n + 1)).symm

include hS in
/-- **Dimension shifting.** For a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective,
`R^{n+1} G (Q)` vanishes if and only if `R^{n+2} G (X)` does. -/
theorem isZero_rightDerived_obj_X₃_iff (n : ℕ) :
    IsZero ((G.rightDerived (n + 1)).obj S.X₃) ↔ IsZero ((G.rightDerived (n + 2)).obj S.X₁) :=
  (G.rightDerivedObjX₁IsoOfShortExact hS n).isZero_iff.symm

omit [HasInjectiveResolutions C] in
/-- For an injective resolution `R` of `Q`, the short complex in degree one of `G` applied to the
resolution `X ⟶ I ⟶ R⁰ ⟶ R¹ ⟶ ⋯` (`InjectiveResolution.ofShortExact`) is
`G I ⟶ G (R⁰) ⟶ G (R¹)`, with differentials `G (S.g ≫ R.ι₀)` and `G (R⁰ ⟶ R¹)`. -/
-- The degree `n + 1` object of `CochainComplex.augment` is the degree `n` object of `R`, and its
-- differentials in degrees `0 ⟶ 1` and `1 ⟶ 2` are `S.g ≫ R.ι₀` and `R.cocomplex.d 0 1`, all by
-- unfolding `augment`, so the components are identities.
noncomputable def mapOfShortExactScOneIso (R : InjectiveResolution S.X₃) :
    ((G.mapHomologicalComplex _).obj (R.ofShortExact hS).cocomplex).sc' 0 1 2 ≅
      ShortComplex.mk (G.map (S.g ≫ R.ι₀)) (G.map (R.cocomplex.d 0 1))
        (by rw [← G.map_comp]; simp) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

omit [HasInjectiveResolutions C] in
/-- The middle component of the inverse of `mapOfShortExactScOneIso` is the identity of
`G (R⁰)`. -/
lemma comp_mapOfShortExactScOneIso_inv_τ₂ (R : InjectiveResolution S.X₃) {Z : D}
    (f : Z ⟶ G.obj (R.cocomplex.X 0)) :
    f ≫ (G.mapOfShortExactScOneIso hS R).inv.τ₂ = f :=
  Category.comp_id f

include hS in
/-- **The first right derived functor as a cokernel.** For a left exact functor `G` and a short
exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective, `R¹ G (X)` is the cokernel of
`G I ⟶ G Q`. Its inverse is described by `Functor.π_rightDerivedOneIsoCokernel_inv`. -/
noncomputable def rightDerivedOneIsoCokernel [PreservesFiniteLimits G] :
    (G.rightDerived 1).obj S.X₁ ≅ cokernel (G.map S.g) :=
  let R := injectiveResolution S.X₃
  -- `G (R⁰)` has kernel `G Q` along `G (R⁰ ⟶ R¹)`, as `G` is left exact.
  let T := ShortComplex.mk (G.map R.ι₀) (G.map (R.cocomplex.d 0 1))
    (by rw [← G.map_comp]; simp)
  have hT : T.Exact := R.exact_ι₀.map_of_mono_of_preservesKernel G inferInstance inferInstance
  have : Mono T.f := inferInstanceAs (Mono (G.map R.ι₀))
  have : Epi (kernel.lift T.g T.f T.zero) := hT.epi_kernelLift
  have : IsIso (kernel.lift T.g T.f T.zero) := isIso_of_mono_of_epi _
  -- `G` applied to the resolution `X ⟶ I ⟶ R⁰ ⟶ R¹ ⟶ ⋯` has short complex `G I ⟶ G (R⁰) ⟶ G (R¹)`
  -- in degree one (`mapOfShortExactScOneIso`).
  let T' := ShortComplex.mk (G.map (S.g ≫ R.ι₀)) (G.map (R.cocomplex.d 0 1))
    (by rw [← G.map_comp]; simp)
  (R.ofShortExact hS).isoRightDerivedObj G 1 ≪≫
    HomologicalComplex.homologyIsoSc' _ 0 1 2 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (G.mapOfShortExactScOneIso hS R) ≪≫
    (ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel T').homologyIso ≪≫
    cokernelIsoOfEq (show kernel.lift T'.g T'.f T'.zero = G.map S.g ≫ kernel.lift T.g T.f T.zero by
      ext; simp [T, T']) ≪≫
    cokernelCompIsIso _ _

/-- The inverse of `rightDerivedOneIsoCokernel` sends the class of a section of `G Q` to the class
of its image in `G (R⁰)`, a cycle in degree one of `G` applied to the injective resolution
`X ⟶ I ⟶ R⁰ ⟶ R¹ ⟶ ⋯` of `X` extending the chosen resolution `Q ⟶ R⁰ ⟶ R¹ ⟶ ⋯` of `Q`. -/
@[reassoc (attr := simp)]
lemma π_rightDerivedOneIsoCokernel_inv [PreservesFiniteLimits G] :
    cokernel.π (G.map S.g) ≫ (G.rightDerivedOneIsoCokernel hS).inv =
      ((G.mapHomologicalComplex _).obj
          ((injectiveResolution S.X₃).ofShortExact hS).cocomplex).liftCycles
        (G.map (injectiveResolution S.X₃).ι₀) 2 (by simp)
        (show G.map _ ≫ G.map ((injectiveResolution S.X₃).cocomplex.d 0 1) = 0 by
          rw [← G.map_comp]; simp) ≫
      HomologicalComplex.homologyπ _ 1 ≫
      (((injectiveResolution S.X₃).ofShortExact hS).isoRightDerivedObj G 1).inv := by
  simp only [rightDerivedOneIsoCokernel, Iso.trans_inv, ShortComplex.homologyMapIso_inv,
    cokernelCompIsIso_inv, Category.assoc, cokernel.π_desc_assoc,
    π_comp_cokernelIsoOfEq_inv_assoc]
  have h := (ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel
    (ShortComplex.mk (G.map (S.g ≫ (injectiveResolution S.X₃).ι₀))
      (G.map ((injectiveResolution S.X₃).cocomplex.d 0 1))
      (by rw [← G.map_comp]; simp))).π_comp_homologyIso_inv
  rw [ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel_π] at h
  rw [reassoc_of% h, ShortComplex.homologyπ_naturality_assoc,
    HomologicalComplex.π_homologyIsoSc'_inv_assoc]
  simp only [← Category.assoc]
  refine congrArg (· ≫ _) (congrArg (· ≫ _) ?_)
  rw [← cancel_mono (HomologicalComplex.iCycles _ 1)]
  -- `G.map R.ι₀` is stated as a morphism into the degree-one object `G (R⁰)` of the mapped
  -- complex, so `liftCycles_i` is applied by unification rather than by rewriting.
  refine Eq.trans ?_ (HomologicalComplex.liftCycles_i _ _ _ _ _).symm
  refine Eq.trans ?_ (G.comp_mapOfShortExactScOneIso_inv_τ₂ hS _ (G.map _))
  simp

include hS in
/-- **Dimension shifting in degree one.** For a left exact functor `G` and a short exact sequence
`0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective, `G I ⟶ G Q` is an epimorphism if and only if `R¹ G (X)`
vanishes. -/
theorem epi_map_g_iff_isZero_rightDerived_one [PreservesFiniteLimits G] :
    Epi (G.map S.g) ↔ IsZero ((G.rightDerived 1).obj S.X₁) :=
  (Preadditive.epi_iff_isZero_cokernel _).trans (G.rightDerivedOneIsoCokernel hS).isZero_iff.symm

include hS in
/-- For a left exact functor `G` and a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I`
injective, `0 ⟶ G X ⟶ G I ⟶ G Q ⟶ 0` is short exact if and only if `R¹ G (X)` vanishes. -/
theorem shortExact_map_iff_isZero_rightDerived_one [PreservesFiniteLimits G] :
    (S.map G).ShortExact ↔ IsZero ((G.rightDerived 1).obj S.X₁) :=
  ⟨fun h ↦ (G.epi_map_g_iff_isZero_rightDerived_one hS).1 h.epi_g, fun h ↦
    { exact := hS.exact.map_of_mono_of_preservesKernel G hS.mono_f inferInstance
      mono_f := have := hS.mono_f; inferInstanceAs (Mono (G.map S.f))
      epi_g := (G.epi_map_g_iff_isZero_rightDerived_one hS).2 h }⟩

end Functor

end DimensionShift

end CategoryTheory

/-! ### Chosen-resolution computation of the native composition comparison -/

universe u' v' u₂ v₂ u₃ v₃

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The chosen-resolution derived-object isomorphism factors through homotopy homology. -/
theorem _root_.CategoryTheory.InjectiveResolution.isoRightDerivedObj_eq_mapIso
    {X : C} (I : InjectiveResolution X) (F : C ⥤ D) [F.Additive] (n : ℕ) :
    I.isoRightDerivedObj F n =
      (HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n).mapIso
        ((F.mapHomotopyCategory (ComplexShape.up ℕ)).mapIso I.iso) ≪≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).app
        ((F.mapHomologicalComplex _).obj I.cocomplex) := by
  apply Iso.ext
  -- The chosen-resolution object iso is defined through the quotient homology factorization.
  change (HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n).map
      ((F.mapHomotopyCategory (ComplexShape.up ℕ)).map I.iso.hom ≫
        (F.mapHomotopyCategoryFactors (ComplexShape.up ℕ)).hom.app I.cocomplex) ≫ _ = _
  erw [CategoryTheory.Functor.mapHomotopyCategoryFactors_hom_app, Category.comp_id]
  rfl

section Component
variable {C' : Type u₂} [Category.{v₂} C'] [Abelian C'] [HasInjectiveResolutions C']
  {D' : Type u₃} [Category.{v₃} D'] [Abelian D']
  (F : C ⥤ D) [F.Additive]
  (G : D ⥤ D') [G.Additive] [G.PreservesHomology]
  (H' : C ⥤ C') [H'.Additive] [H'.PreservesInjectiveObjects] [H'.PreservesHomology]
  (F' : C' ⥤ D') [F'.Additive] (e : F ⋙ G ≅ H' ⋙ F')

private def comparisonComplexIso (K : CochainComplex C ℕ) :
    (G.mapHomologicalComplex _).obj ((F.mapHomologicalComplex _).obj K) ≅
      (F'.mapHomologicalComplex _).obj ((H'.mapHomologicalComplex _).obj K) :=
  (CategoryTheory.Functor.mapHomologicalComplexCompIso e _).app K ≪≫
    ((CategoryTheory.Functor.mapHomologicalComplexCompIso (Iso.refl (H' ⋙ F')) _).app K).symm

private noncomputable def comparisonHomotopyIso (n : ℕ) :
    (F.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
      HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n) ⋙ G ≅
      H'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
        F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
          HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n :=
  CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (F.mapHomotopyCategory _)
      (G.mapHomotopyCategoryCompHomologyFunctorIso _ n).symm ≪≫
    (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      (CategoryTheory.Functor.mapHomotopyCategoryCompIso e _ ≪≫
        (CategoryTheory.Functor.mapHomotopyCategoryCompIso (Iso.refl (H' ⋙ F')) _).symm) _ ≪≫
    CategoryTheory.Functor.associator _ _ _

private theorem derivedComparison_homotopy_canonical (X : C) (n : ℕ) :
    (CategoryTheory.Functor.rightDerivedCompIso F G H' F' e n).hom.app X =
      (comparisonHomotopyIso F G H' F' e n).hom.app ((injectiveResolutions C).obj X) ≫
        (F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
          HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map
            (H'.injectiveResolutionsCompIso.hom.app X) := by
  dsimp [CategoryTheory.Functor.rightDerivedCompIso, comparisonHomotopyIso,
    CategoryTheory.Functor.associator, CategoryTheory.Functor.rightDerived,
    CategoryTheory.Functor.rightDerivedToHomotopyCategory]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]


private theorem derivedComparison_homotopy_arbitrary {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (CategoryTheory.Functor.rightDerivedCompIso F G H' F' e n).hom.app X ≫
        (F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
          HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map
            (H'.mapInjectiveResolution I).iso.hom =
      G.map ((HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n).map
        ((F.mapHomotopyCategory (ComplexShape.up ℕ)).map I.iso.hom)) ≫
      (comparisonHomotopyIso F G H' F' e n).hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℕ)).obj I.cocomplex) := by
  let T := F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
    HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n
  -- After the canonical rewrite, the source is `(F.rightDerived n ⋙ G).obj X`, which is the
  -- homotopy-category homology of the chosen resolution only once `rightDerived` is unfolded;
  -- `rw [Category.assoc]` then fails with a motive type mismatch, so `erw` is needed.
  erw [derivedComparison_homotopy_canonical, Category.assoc, ← T.map_comp,
    injectiveResolutionsCompIso_hom_app_comp_iso_hom]
  exact ((comparisonHomotopyIso F G H' F' e n).hom.naturality I.iso.hom).symm


omit [HasInjectiveResolutions C]
  [HasInjectiveResolutions C'] [H'.PreservesInjectiveObjects] [H'.PreservesHomology] in
private theorem comparisonHomotopy_complex_component (K : CochainComplex C ℕ) (n : ℕ) :
    (comparisonHomotopyIso F G H' F' e n).app
        ((HomotopyCategory.quotient C (ComplexShape.up ℕ)).obj K) =
      G.mapIso ((HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℕ) n).app
          ((F.mapHomologicalComplex _).obj K)) ≪≫
        ((G.mapHomologicalComplexCompHomologyFunctorIso _ n).app
          ((F.mapHomologicalComplex _).obj K)).symm ≪≫
        (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).mapIso
          (comparisonComplexIso F G H' F' e K) ≪≫
        ((HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).app
          ((F'.mapHomologicalComplex _).obj ((H'.mapHomologicalComplex _).obj K))).symm := by
  apply Iso.ext
  simp only [comparisonHomotopyIso, comparisonComplexIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp, Category.comp_id, Iso.app_inv,
    Functor.mapIso_hom]
  -- `F.mapHomotopyCategory` sends the class of `K` to the class of `F` applied to `K`.
  have hG : (G.mapHomotopyCategoryCompHomologyFunctorIso (ComplexShape.up ℕ) n).inv.app
      ((F.mapHomotopyCategory (ComplexShape.up ℕ)).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℕ)).obj K)) = _ :=
    G.mapHomotopyCategoryCompHomologyFunctorIso_inv_app _ n ((F.mapHomologicalComplex _).obj K)
  have hn := (HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).inv.naturality
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H' ⋙ F')) (ComplexShape.up ℕ)).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hG, mapHomotopyCategoryCompIso_hom_app_quotient_obj,
    mapHomotopyCategoryCompIso_inv_app_quotient_obj,
    ← Functor.map_comp]
  simp only [Category.assoc]
  -- The remaining square is naturality of `homologyFunctorFactors` for the comparison map.
  rw [← hn]

/-- Compute the native derived composition comparison using any injective resolution. -/
theorem rightDerivedCompIso_app_injectiveResolution {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (CategoryTheory.Functor.rightDerivedCompIso F G H' F' e n).app X =
      G.mapIso (I.isoRightDerivedObj F n) ≪≫
        ((G.mapHomologicalComplexCompHomologyFunctorIso _ n).app
          ((F.mapHomologicalComplex _).obj I.cocomplex)).symm ≪≫
        (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).mapIso
          ((Functor.mapHomologicalComplexCompIso e _).app I.cocomplex ≪≫
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (H' ⋙ F')) _).app I.cocomplex).symm) ≪≫
        ((H'.mapInjectiveResolution I).isoRightDerivedObj F' n).symm := by
  apply Iso.ext
  -- `derivedComparison_homotopy_arbitrary` computes the comparison after the homotopy-homology
  -- image of the chosen-resolution iso of `H'.mapInjectiveResolution I`; move that iso across.
  have t : (rightDerivedCompIso F G H' F' e n).hom.app X = _ ≫
      (F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
        HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map
          (H'.mapInjectiveResolution I).iso.inv :=
    (Iso.eq_comp_inv ((F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
      HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).mapIso
        (H'.mapInjectiveResolution I).iso)).2 (derivedComparison_homotopy_arbitrary F G H' F' e I n)
  have q := congrArg Iso.hom (comparisonHomotopy_complex_component F G H' F' e I.cocomplex n)
  have hI := congrArg Iso.hom (I.isoRightDerivedObj_eq_mapIso F n)
  have hJ := congrArg Iso.inv ((H'.mapInjectiveResolution I).isoRightDerivedObj_eq_mapIso F' n)
  simp only [Iso.app_hom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv] at q hI hJ
  -- `(H'.mapInjectiveResolution I).cocomplex` is `H'` applied to `I.cocomplex` by definition; in
  -- that form the last two factors of the right side are the composite `hJ`.
  have hlast : ((HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).mapIso
        ((Functor.mapHomologicalComplexCompIso e _).app I.cocomplex ≪≫
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (H' ⋙ F')) _).app I.cocomplex).symm) ≪≫
        ((H'.mapInjectiveResolution I).isoRightDerivedObj F' n).symm).hom =
      (HomologicalComplex.homologyFunctor D' (ComplexShape.up ℕ) n).map
        (comparisonComplexIso F G H' F' e I.cocomplex).hom ≫
        (HomotopyCategory.homologyFunctorFactors D' (ComplexShape.up ℕ) n).inv.app
          ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            ((H'.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) ≫
        (F'.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
          HomotopyCategory.homologyFunctor D' (ComplexShape.up ℕ) n).map
            (H'.mapInjectiveResolution I).iso.inv :=
    congrArg (_ ≫ ·) hJ
  dsimp only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom]
  rw [t, q, hI, Iso.symm_hom, hlast, Iso.app_inv]
  -- The two sides agree up to `Functor.map_comp` and reassociation. Some of the intermediate
  -- objects agree only after unfolding `Functor.mapHomotopyCategory` and
  -- `Functor.mapInjectiveResolution`, so the steps are assembled by unification, not by `rw`:
  -- four `Category.assoc` steps reassociate the left side, then `G.map_comp` merges its first
  -- two factors.
  exact ((Category.assoc _ _ _).trans <| whisker_eq _ <| (Category.assoc _ _ _).trans <|
      whisker_eq _ <| (Category.assoc _ _ _).trans <| whisker_eq _ (Category.assoc _ _ _)).trans
    ((Category.assoc _ _ _).symm.trans (eq_whisker (G.map_comp _ _).symm _))

/-- If `F ≅ H' ⋙ F''` where `H'` preserves homology and injective objects, then
`RⁿF ≅ H' ⋙ RⁿF''`. This is `rightDerivedCompIso` with the identity functor as `G`. -/
noncomputable def rightDerivedPrecompIso (F'' : C' ⥤ D) [F''.Additive] (e' : F ≅ H' ⋙ F'')
    (n : ℕ) : F.rightDerived n ≅ H' ⋙ F''.rightDerived n :=
  (Functor.rightUnitor (F.rightDerived n)).symm ≪≫
    Functor.rightDerivedCompIso F (𝟭 D) H' F'' (Functor.rightUnitor F ≪≫ e') n

/-- `rightDerivedPrecompIso` acts by the comparison cochain map on any chosen resolution. -/
theorem rightDerivedPrecompIso_app_hom (F'' : C' ⥤ D) [F''.Additive]
    (e' : F ≅ H' ⋙ F'') {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (rightDerivedPrecompIso F H' F'' e' n).hom.app X ≫
      ((H'.mapInjectiveResolution I).isoRightDerivedObj F'' n).hom =
    (I.isoRightDerivedObj F n).hom ≫ HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex e'.hom _).app I.cocomplex ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (H' ⋙ F'')) _).inv.app I.cocomplex) n := by
  dsimp only [rightDerivedPrecompIso, Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor]
  simp_rw [← Iso.app_hom]
  -- Unfolding `rightUnitor` above leaves its explicit identity structure in the goal, so the
  -- coefficient iso `rightUnitor F ≪≫ e'` matches only up to that unfolding.
  erw [Functor.rightDerivedCompIso_app_injectiveResolution F (𝟭 D) H' F''
    (Functor.rightUnitor F ≪≫ e') I n]
  dsimp only [CategoryTheory.Functor.mapInjectiveResolution, Iso.app_hom,
    Functor.rightUnitor]
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.id_map, Category.assoc, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]
  dsimp only [Iso.app_inv]
  rw [CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso_id_inv_app,
    HomologicalComplex.homologyFunctor_map, ← HomologicalComplex.homologyMap_comp]
  congr 2
  ext j
  simp
end Component

section Postcomp

variable {D' : Type*} [Category* D'] [Abelian D']
  (F : C ⥤ D) [F.Additive] (G : D ⥤ D') [G.Additive] [G.PreservesHomology]

/-- Right deriving an additive functor commutes with postcomposition by an exact functor. -/
noncomputable def rightDerivedPostcompIso (n : ℕ) :
    F.rightDerived n ⋙ G ≅ (F ⋙ G).rightDerived n :=
  rightDerivedCompIso F G (𝟭 C) (F ⋙ G) (Functor.leftUnitor _).symm n ≪≫
    Functor.leftUnitor _

/-- On an injective resolution the postcomposition comparison is the inverse of the
comparison expressing preservation of homology. -/
@[reassoc]
lemma rightDerivedPostcompIso_hom_app_injectiveResolution {X : C}
    (I : InjectiveResolution X) (n : ℕ) :
    (F.rightDerivedPostcompIso G n).hom.app X =
      G.map (I.isoRightDerivedObj F n).hom ≫
        (G.mapHomologicalComplexCompHomologyFunctorIso _ n).inv.app
          ((F.mapHomologicalComplex _).obj I.cocomplex) ≫
        (I.isoRightDerivedObj (F ⋙ G) n).inv := by
  let E := F ⋙ G
  let c := ComplexShape.up ℕ
  let J := (𝟭 C).mapInjectiveResolution I
  let e : J.cocomplex ≅ I.cocomplex :=
    (Functor.mapHomologicalComplexIdIso C c).app I.cocomplex
  let H := HomologicalComplex.homologyFunctor D' c n
  have hcomp :
      ((Functor.mapHomologicalComplexCompIso (Functor.leftUnitor E).symm c).app I.cocomplex ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (𝟭 C ⋙ E)) c).app I.cocomplex).symm).hom =
        (E.mapHomologicalComplex c).map e.inv := by
    ext k
    simp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X, Functor.id_obj,
      Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.leftUnitor_inv_app,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
      Category.comp_id, Functor.mapHomologicalComplex_map_f]
    exact (E.map_id _).symm.trans
      (congrArg E.map (Functor.mapHomologicalComplexIdIso_inv_app_f C c I.cocomplex k).symm)
  have haug : J.ι.f 0 ≫ e.hom.f 0 = 𝟙 X ≫ I.ι.f 0 := by
    calc
      _ = (𝟭 C).map (I.ι.f 0) ≫ 𝟙 (I.cocomplex.X 0) :=
        congrArg₂ (· ≫ ·) (Functor.mapInjectiveResolution_ι_f_zero (𝟭 C) I)
          (Functor.mapHomologicalComplexIdIso_hom_app_f C c I.cocomplex 0)
      _ = _ := (Category.comp_id _).trans (Category.id_comp _).symm
  have hres := J.isoRightDerivedObj_inv_naturality (𝟙 X) I e.hom haug E n
  rw [Functor.map_id, Category.comp_id] at hres
  rw [← Iso.app_hom]
  rw [rightDerivedPostcompIso, NatIso.trans_app,
    rightDerivedCompIso_app_injectiveResolution F G (𝟭 C) E _ I]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.leftUnitor_hom_app, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv]
  refine (Category.comp_id _).trans (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_))
  calc
    _ = H.map ((E.mapHomologicalComplex c).map e.inv) ≫ (J.isoRightDerivedObj E n).inv :=
      congrArg (fun f ↦ H.map f ≫ (J.isoRightDerivedObj E n).inv) hcomp
    _ = _ := by
      rw [hres, ← Functor.comp_map, ← Functor.map_comp_assoc, Iso.inv_hom_id,
        Functor.map_id, Category.id_comp]

end Postcomp

end CategoryTheory.Functor
