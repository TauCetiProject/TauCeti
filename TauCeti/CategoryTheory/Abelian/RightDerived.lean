/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.HomotopyCategory.PreservesHomology
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution

/-!
# Additivity, commutation with exact functors, and dimension shifting for right derived functors

Injective resolutions are additive after passing to the homotopy category: the sum of
two lifts is a lift of the sum, and lifts of the same morphism are homotopic. Thus right
derived functors of additive functors are additive. If the functor is exact, its
positive right derived functors vanish.

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
  if `R^{n+2} G (X)` vanishes, so does `R^{n+1} G (Q)`
  (`CategoryTheory.Functor.isZero_rightDerived_obj_X₃_of_isZero`);
* if `G` is left exact and `R¹ G (X)` vanishes, then `0 ⟶ G X ⟶ G I ⟶ G Q ⟶ 0` is short exact
  (`CategoryTheory.Functor.shortExact_map_of_isZero_rightDerived_one`).

These are the dimension-shifting steps of inductive arguments on vanishing derived functors,
such as Leray's acyclicity theorem.
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

variable {C} {D : Type*} [Category* D] [Abelian D]

/-- Right derived functors of an additive functor are additive. -/
instance Functor.additive_rightDerived (F : C ⥤ D) [F.Additive] (q : ℕ) :
    (F.rightDerived q).Additive :=
  inferInstanceAs ((injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙
    HomotopyCategory.homologyFunctor D _ q).Additive)

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
if `R^{n+2} G (X)` vanishes, so does `R^{n+1} G (Q)`. -/
theorem isZero_rightDerived_obj_X₃_of_isZero (n : ℕ)
    (h : IsZero ((G.rightDerived (n + 2)).obj S.X₁)) :
    IsZero ((G.rightDerived (n + 1)).obj S.X₃) :=
  h.of_iso (G.rightDerivedObjX₁IsoOfShortExact hS n).symm

include hS in
/-- **Dimension shifting in degree one.** For a left exact functor `G` and a short exact sequence
`0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective, if `R¹ G (X)` vanishes, then `G I ⟶ G Q` is an
epimorphism. -/
theorem epi_map_g_of_isZero_rightDerived_one [PreservesFiniteLimits G]
    (h : IsZero ((G.rightDerived 1).obj S.X₁)) : Epi (G.map S.g) := by
  let R := injectiveResolution S.X₃
  have h' := h.of_iso ((R.ofShortExact hS).isoRightDerivedObj G 1).symm
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)] at h'
  -- `G (R⁰)` has kernel `G Q` along `G (R⁰ ⟶ R¹)`, as `G` is left exact.
  let T := ShortComplex.mk (G.map R.ι₀) (G.map (R.cocomplex.d 0 1))
    (by rw [← G.map_comp]; simp)
  have hT : T.Exact := R.exact_ι₀.map_of_mono_of_preservesKernel G inferInstance inferInstance
  have : Mono T.f := inferInstanceAs (Mono (G.map R.ι₀))
  have : Epi (kernel.lift T.g T.f T.zero) := hT.epi_kernelLift
  have : IsIso (kernel.lift T.g T.f T.zero) := isIso_of_mono_of_epi _
  rw [ShortComplex.exact_iff_epi_kernel_lift] at h'
  -- the differential `G I ⟶ G (R⁰)` of `G` applied to the augmented complex is
  -- `G (S.g ≫ R.ι₀)` by unfolding `augment`
  have h'' : Epi (kernel.lift T.g (G.map (S.g ≫ R.ι₀))
      (by rw [← G.map_comp]; simp)) := h'
  have e : kernel.lift T.g (G.map (S.g ≫ R.ι₀)) (by rw [← G.map_comp]; simp) =
      G.map S.g ≫ kernel.lift T.g T.f T.zero := by
    ext
    simp [T]
  rw [e] at h''
  exact (epi_comp_iff_of_isIso _ _).1 h''

include hS in
/-- For a left exact functor `G` and a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I`
injective, if `R¹ G (X)` vanishes, then `0 ⟶ G X ⟶ G I ⟶ G Q ⟶ 0` is short exact. -/
theorem shortExact_map_of_isZero_rightDerived_one [PreservesFiniteLimits G]
    (h : IsZero ((G.rightDerived 1).obj S.X₁)) : (S.map G).ShortExact :=
  { exact := hS.exact.map_of_mono_of_preservesKernel G hS.mono_f inferInstance
    mono_f := have := hS.mono_f; inferInstanceAs (Mono (G.map S.f))
    epi_g := G.epi_map_g_of_isZero_rightDerived_one hS h }

end Functor

end DimensionShift

end CategoryTheory
