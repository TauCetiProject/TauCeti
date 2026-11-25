/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Pullback
public import TauCeti.Algebra.Homology.Ext.Map.AcyclicResolution

/-!
# Pullback of classes of sections of resolutions

Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of an abelian sheaf `F` on a site `(C, J)`, and let
`pb` be an exact functor to abelian sheaves on a site `(D, K)` with a comparison
`c : ℤ[u(-)] ⟶ pb ℤ[-]` of free abelian sheaves. The pullback
`CategoryTheory.Sheaf.H'.pullback pb c` sends the class `[s] ∈ Hⁿ(U, F)` of a section `s` of `Kⁿ`
over `U` killed by the differential to the class of the corresponding section of `pb Kⁿ` in the
resolution `pb F ⟶ pb K` (`CategoryTheory.Sheaf.H'.pullback_resolutionClass`). For the pullback
`u^*` along a continuous functor `u`, that section is the image of `s` under the unit of
`u^* ⊣ u_*` (`CategoryTheory.Sheaf.H'.pullback_sheafPullback_resolutionClass`).

So when the sections of a resolution compute cohomology on both sides, pullback on cohomology is
induced by pullback of sections.
-/

public section

open CategoryTheory Limits Opposite Abelian TauCeti.CategoryTheory

namespace CategoryTheory.Sheaf.H'

universe v u₁ u₂

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v} D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]

section General

variable (pb : Sheaf J AddCommGrpCat.{v} ⥤ Sheaf K AddCommGrpCat.{v}) [pb.Additive]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
  {u : C ⥤ D} (c : u ⋙ freeYonedaSheafFunctor K ⟶ freeYonedaSheafFunctor J ⋙ pb)
  {F : Sheaf J AddCommGrpCat.{v}} {R : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ}
  (ι : F ⟶ R.X 0) [Mono ι] (hι : ι ≫ R.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (R.d 0 1) hι).Exact) (hR : ∀ j, R.ExactAt (j + 1))
  [Mono (pb.map ι)] (hpι : pb.map ι ≫ ((pb.mapHomologicalComplex _).obj R).d 0 1 = 0)
  (hpι' : (ShortComplex.mk (pb.map ι) (((pb.mapHomologicalComplex _).obj R).d 0 1) hpι).Exact)
  (hpR : ∀ j, ((pb.mapHomologicalComplex _).obj R).ExactAt (j + 1))

omit [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb] in
/-- The section of `pb Rⁿ` over `V` corresponding to `ℤ[V] ⟶ ℤ[u(U)] ⟶ pb ℤ[U] ⟶ pb Rⁿ`, for a
section of `Rⁿ` over `U` killed by the differential, is killed by the differential. -/
lemma d_freeYonedaSheafSectionsEquiv_comp_map {n : ℕ} {U : C} {V : D} (ψ : V ⟶ u.obj U)
    (s : (R.X n).obj.obj (op U)) (hs : (R.d n (n + 1)).hom.app (op U) s = 0) :
    (((pb.mapHomologicalComplex _).obj R).d n (n + 1)).hom.app (op V)
      (freeYonedaSheafSectionsEquiv K V (pb.obj (R.X n))
        ((freeYonedaSheafFunctor K).map ψ ≫ c.app U ≫
          pb.map ((freeYonedaSheafSectionsEquiv J U (R.X n)).symm s))) = 0 := by
  refine (freeYonedaSheafSectionsEquiv_naturality_right K _ (pb.map (R.d n (n + 1)))).symm.trans ?_
  rw [Category.assoc, Category.assoc, ← pb.map_comp,
    freeYonedaSheafSectionsEquiv_symm_naturality_right, hs, map_zero, pb.map_zero,
    Limits.comp_zero, Limits.comp_zero, map_zero]

include hι' hR hpι' hpR in
/-- **Pullback of classes of sections.** The pullback along `(pb, c)` and `ψ : V ⟶ u(U)` of the
class of a section `s` of `Rⁿ` over `U` is the class, in the resolution `pb F ⟶ pb R`, of the
section of `pb Rⁿ` over `V` corresponding to `ℤ[V] ⟶ ℤ[u(U)] ⟶ pb ℤ[U] ⟶ pb Rⁿ`. -/
theorem pullback_resolutionClass {n : ℕ} {U : C} {V : D} (ψ : V ⟶ u.obj U)
    (s : (R.X n).obj.obj (op U)) (hs : (R.d n (n + 1)).hom.app (op U) s = 0) :
    pullback pb c F n ψ (resolutionClass ι hι hι' hR U s hs) =
      resolutionClass (pb.map ι) hpι hpι' hpR V
        (freeYonedaSheafSectionsEquiv K V (pb.obj (R.X n))
          ((freeYonedaSheafFunctor K).map ψ ≫ c.app U ≫
            pb.map ((freeYonedaSheafSectionsEquiv J U (R.X n)).symm s)))
        (d_freeYonedaSheafSectionsEquiv_comp_map pb c ψ s hs) := by
  refine ((pb.obj F).H'AddEquivExt n V).injective ?_
  rw [pullback_apply, resolutionClass_def, resolutionClass_def, AddEquiv.apply_symm_apply]
  -- `H'AddEquivExt` applied to the inverse of `H'AddEquivExt` of the class of `s` is the `Ext`
  -- class `R.extMk ι … s`, but only up to unfolding the equivalence, so the goal is restated.
  change (Ext.mk₀ ((freeYonedaSheafFunctor K).map ψ ≫ c.app U)).comp
      ((R.extMk ι hι hι' hR _ _).mapExactFunctor pb) (zero_add n) = _
  rw [R.mapExactFunctor_extMk pb ι hι hι' hR hpι hpι' hpR, CochainComplex.mk₀_comp_extMk]
  congr 1
  rw [Category.assoc]
  exact ((freeYonedaSheafSectionsEquiv K V (pb.obj (R.X n))).symm_apply_apply _).symm

end General

section SheafPullback

variable (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
  [PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{v} J K)]
  {F : Sheaf J AddCommGrpCat.{v}} {R : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ}
  (ι : F ⟶ R.X 0) [Mono ι] (hι : ι ≫ R.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (R.d 0 1) hι).Exact) (hR : ∀ j, R.ExactAt (j + 1))
  [Mono ((u.sheafPullback AddCommGrpCat.{v} J K).map ι)]
  (hpι : (u.sheafPullback AddCommGrpCat.{v} J K).map ι ≫
    (((u.sheafPullback AddCommGrpCat.{v} J K).mapHomologicalComplex _).obj R).d 0 1 = 0)
  (hpι' : (ShortComplex.mk ((u.sheafPullback AddCommGrpCat.{v} J K).map ι)
    ((((u.sheafPullback AddCommGrpCat.{v} J K).mapHomologicalComplex _).obj R).d 0 1) hpι).Exact)
  (hpR : ∀ j, (((u.sheafPullback AddCommGrpCat.{v} J K).mapHomologicalComplex _).obj R).ExactAt
    (j + 1))

omit [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]
  [PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{v} J K)] in
/-- For the pullback `u^*` along a continuous functor `u`, the section of `u^* G` over `V`
corresponding to `ℤ[V] ⟶ ℤ[u(U)] ⟶ u^* ℤ[U] ⟶ u^* G`, for the map `ℤ[U] ⟶ G` given by a section `s`
of `G` over `U`, is the restriction along `ψ` of the image of `s` under the unit of
`u^* ⊣ u_*`. -/
lemma freeYonedaSheafSectionsEquiv_freeYonedaSheafToSheafPullback_comp_map
    {G : Sheaf J AddCommGrpCat.{v}} {U : C} {V : D} (ψ : V ⟶ u.obj U) (s : G.obj.obj (op U)) :
    freeYonedaSheafSectionsEquiv K V ((u.sheafPullback AddCommGrpCat.{v} J K).obj G)
        ((freeYonedaSheafFunctor K).map ψ ≫ (u.freeYonedaSheafToSheafPullback J K).app U ≫
          (u.sheafPullback AddCommGrpCat.{v} J K).map
            ((freeYonedaSheafSectionsEquiv J U G).symm s)) =
      ((u.sheafPullback AddCommGrpCat.{v} J K).obj G).obj.map ψ.op
        (((u.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app G).hom.app (op U) s) := by
  rw [freeYonedaSheafSectionsEquiv_naturality_left, freeYonedaSheafSectionsEquiv_naturality_right,
    Functor.freeYonedaSheafSectionsEquiv_freeYonedaSheafToSheafPullback_app]
  conv_rhs => rw [← AddEquiv.apply_symm_apply (freeYonedaSheafSectionsEquiv J U G) s]
  rw [Functor.sheafAdjunctionContinuous_unit_app_hom_app_freeYonedaSheafSectionsEquiv J K u
    ((freeYonedaSheafSectionsEquiv J U G).symm s)]

include hι' hR hpι' hpR in
/-- **Inverse image of classes of sections.** For the pullback `u^*` along a continuous functor
`u`, the pullback along `ψ : V ⟶ u(U)` of the class of a section `s` of `Rⁿ` over `U` is the class,
in the resolution `u^* F ⟶ u^* R`, of the restriction along `ψ` of the image of `s` under the
unit of `u^* ⊣ u_*`. -/
theorem pullback_sheafPullback_resolutionClass {n : ℕ} {U : C} {V : D} (ψ : V ⟶ u.obj U)
    (s : (R.X n).obj.obj (op U)) (hs : (R.d n (n + 1)).hom.app (op U) s = 0) :
    pullback (u.sheafPullback AddCommGrpCat.{v} J K) (u.freeYonedaSheafToSheafPullback J K) F n ψ
        (resolutionClass ι hι hι' hR U s hs) =
      resolutionClass ((u.sheafPullback AddCommGrpCat.{v} J K).map ι) hpι hpι' hpR V
        (((u.sheafPullback AddCommGrpCat.{v} J K).obj (R.X n)).obj.map ψ.op
          (((u.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app (R.X n)).hom.app (op U)
            s))
        (by
          rw [← freeYonedaSheafSectionsEquiv_freeYonedaSheafToSheafPullback_comp_map]
          exact d_freeYonedaSheafSectionsEquiv_comp_map _ _ ψ s hs) := by
  rw [pullback_resolutionClass _ _ ι hι hι' hR hpι hpι' hpR]
  congr 1
  exact freeYonedaSheafSectionsEquiv_freeYonedaSheafToSheafPullback_comp_map u ψ s

end SheafPullback

end CategoryTheory.Sheaf.H'
