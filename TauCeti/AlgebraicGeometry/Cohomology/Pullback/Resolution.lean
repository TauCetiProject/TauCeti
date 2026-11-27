/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Pullback
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution.Pullback

/-!
# Pullback on cohomology computed by resolutions

Let `g : Y ⟶ X` be a morphism of schemes whose module pullback `g^*` is exact, for instance an
open immersion, `M` a sheaf of modules on `X` and `P` an injective resolution of `M`. Then `g^* P`
is a resolution of `g^* M`, and pullback on the cohomology of an open `U` of `X`
(`AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback`) sends the class in `Hⁿ(U, M)` of a section
`s` of `Pⁿ` over `U` killed by the differential to the class in `Hⁿ(g⁻¹ U, g^* M)` of its pullback
`g^* s` (`AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback_resolutionClass`).
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [PreservesFiniteLimits (Scheme.Modules.pullback g)]
  {M : X.Modules} (P : InjectiveResolution M)

/-- **Pullback of classes of sections of a resolution.** If the module pullback along `g` is
exact, pullback on cohomology sends the class in `Hⁿ(U, M)` of a section `s` of the term `Pⁿ` of an
injective resolution of `M` to the class in `Hⁿ(g⁻¹ U, g^* M)` of the section `g^* s` of the
resolution `g^* P` of `g^* M`. -/
theorem cohomologyOnPullback_resolutionClass {n : ℕ} (U : X.Opens)
    (s : (((toSheaf X).mapHomologicalComplex _).obj P.cocomplex |>.X n).obj.obj (op U))
    (hs : ((((toSheaf X).mapHomologicalComplex _).obj P.cocomplex).d n (n + 1)).hom.app (op U) s =
      0) :
    g.cohomologyOnPullback M n U
        (CategoryTheory.Sheaf.H'.resolutionClass
          (K := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex) ((toSheaf X).map (P.ι.f 0))
          (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
          (CochainComplex.map_augmentation_exact _ P.exact₀)
          (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) U s hs) =
      CategoryTheory.Sheaf.H'.resolutionClass
        (K := ((Scheme.Modules.pullback g ⋙ toSheaf Y).mapHomologicalComplex _).obj P.cocomplex)
        ((Scheme.Modules.pullback g ⋙ toSheaf Y).map (P.ι.f 0))
        (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
        (CochainComplex.map_augmentation_exact _ P.exact₀)
        (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) (g ⁻¹ᵁ U)
        (g.pullbackSections (P.cocomplex.X n) U s) (by
          refine (g.pullbackSections_naturality (M := P.cocomplex.X n) (U := U)
            (P.cocomplex.d n (n + 1)) s).trans ?_
          rw [show (P.cocomplex.d n (n + 1)).app U s = 0 from hs, map_zero]
          rfl) := by
  let pb := (Opens.map g.base).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  have : Mono (pb.map ((toSheaf X).map (P.ι.f 0))) := Functor.map_mono _ _
  refine (cohomologyOnPullback_apply g M n U _).trans ?_
  -- The resolution `pb (toSheaf X P)` appears as `(toSheaf X ⋙ pb)` applied to `P` in the
  -- hypotheses supplied by `InjectiveResolution` and as nested `mapHomologicalComplex` in the
  -- target; these agree only up to unfolding, hence the `by exact` wrappers and `erw [key]`.
  have key := CategoryTheory.Sheaf.H'.pullback_sheafPullback_resolutionClass (Opens.map g.base)
    (R := ((toSheaf X).mapHomologicalComplex _).obj P.cocomplex)
    ((toSheaf X).map (P.ι.f 0)) (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact _ P.exact₀)
    (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ)
    (by exact CochainComplex.map_augmentation_comp_d (toSheaf X ⋙ pb) P.ι_f_zero_comp_complex_d)
    (by exact CochainComplex.map_augmentation_exact (toSheaf X ⋙ pb) P.exact₀)
    (by exact CochainComplex.map_exactAt_succ (toSheaf X ⋙ pb) P.cocomplex_exactAt_succ) (𝟙 _) s hs
  erw [key]
  let ψ : (pb.mapHomologicalComplex _).obj (((toSheaf X).mapHomologicalComplex _).obj P.cocomplex) ⟶
      ((Scheme.Modules.pullback g ⋙ toSheaf Y).mapHomologicalComplex _).obj P.cocomplex :=
    (NatTrans.mapHomologicalComplex (toSheafPullbackComparison g) _).app P.cocomplex
  have hψ : pb.map ((toSheaf X).map (P.ι.f 0)) ≫ ψ.f 0 =
      (toSheafPullbackComparison g).app M ≫ (Scheme.Modules.pullback g ⋙ toSheaf Y).map (P.ι.f 0) :=
    by exact (toSheafPullbackComparison g).naturality (P.ι.f 0)
  have h2 := CategoryTheory.Sheaf.H'.cohomologyPresheafFunctor_map_app_resolutionClass
    (K := (pb.mapHomologicalComplex _).obj (((toSheaf X).mapHomologicalComplex _).obj P.cocomplex))
    (K' := ((Scheme.Modules.pullback g ⋙ toSheaf Y).mapHomologicalComplex _).obj P.cocomplex)
    (pb.map ((toSheaf X).map (P.ι.f 0)))
    (by exact CochainComplex.map_augmentation_comp_d (toSheaf X ⋙ pb) P.ι_f_zero_comp_complex_d)
    (by exact CochainComplex.map_augmentation_exact (toSheaf X ⋙ pb) P.exact₀)
    (by exact CochainComplex.map_exactAt_succ (toSheaf X ⋙ pb) P.cocomplex_exactAt_succ)
    (g ⁻¹ᵁ U) ((Scheme.Modules.pullback g ⋙ toSheaf Y).map (P.ι.f 0))
    (CochainComplex.map_augmentation_comp_d _ P.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact _ P.exact₀)
    (CochainComplex.map_exactAt_succ _ P.cocomplex_exactAt_succ) (ψ := ψ) hψ
    ((pb.obj ((toSheaf X).obj (P.cocomplex.X n))).obj.map (𝟙 (g ⁻¹ᵁ U)).op
      ((((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).unit.app
        ((toSheaf X).obj (P.cocomplex.X n))).hom.app (op U) s)) (by
      rw [← Sheaf.H'.freeYonedaSheafSectionsEquiv_freeYonedaSheafToSheafPullback_comp_map]
      exact Sheaf.H'.d_freeYonedaSheafSectionsEquiv_comp_map _ _ _ s hs)
  refine h2.trans ?_
  have h3 : (ψ.f n).hom.app (op (g ⁻¹ᵁ U))
      ((pb.obj ((toSheaf X).obj (P.cocomplex.X n))).obj.map (𝟙 (g ⁻¹ᵁ U)).op
        ((((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).unit.app
          ((toSheaf X).obj (P.cocomplex.X n))).hom.app (op U) s)) =
      g.pullbackSections (P.cocomplex.X n) U s := by
    have e := ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.hom.app (op U))
      (g.toSheafPullbackComparison_unit (P.cocomplex.X n))) s
    refine Eq.trans ?_ (g.pullbackSections_apply (P.cocomplex.X n) U s).symm
    rw [op_id, CategoryTheory.Functor.map_id]
    exact e.symm
  congr 1

end AlgebraicGeometry.Scheme.Hom
