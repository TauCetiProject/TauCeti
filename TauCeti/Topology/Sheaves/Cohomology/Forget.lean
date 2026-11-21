/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Exactness
public import TauCeti.Algebra.Homology.Single.Kernel
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
public import TauCeti.Topology.Sheaves.Cohomology.Godement
public import TauCeti.Topology.Sheaves.Flasque.Basic

/-!
# Derived global sections of module sheaves and cohomology of the underlying abelian sheaves

Let `R` be a commutative ring and `X` a topological space. A sheaf of `R`-modules `F` on `X` has
two cohomology theories: the native right derived functors `RⁿΓ(F)` of the global sections functor
`Γ` on sheaves of `R`-modules, defined through injective resolutions in that category, and Mathlib's
`Ext`-based cohomology `Hⁿ(X, U F)` (`CategoryTheory.Sheaf.functorH`) of the underlying sheaf of
abelian groups `U F`. This file constructs a natural isomorphism between the underlying abelian
groups of the first and the second (`TauCeti.Topology.moduleCohomologyForgetComparison`).

The forgetful functor `U` need not send injective sheaves of modules to injective abelian sheaves
(the `ℤ/2`-module `ℤ/2` is injective, but not as an abelian group), so the comparison does not
come from a comparison of injective resolutions. Instead, both theories are computed by the
Godement resolution `F ⟶ G⁰(F) ⟶ G¹(F) ⟶ ⋯`:

* `RⁿΓ(F)` is the cohomology of the global sections of the Godement resolution, because its terms
  are flasque (`TauCeti.Topology.rightDerivedΓIsoGodement`);
* forgetting the module structures is exact, so `U F ⟶ U G⁰(F) ⟶ U G¹(F) ⟶ ⋯` is a resolution of
  `U F` by flasque abelian sheaves, which have no higher cohomology over any open
  (`TauCeti.Topology.subsingleton_H'_succ_of_isFlasque`); hence its sections compute the
  cohomology presheaf of `U F` (`CategoryTheory.Sheaf.H'.homologyIsoCohomologyPresheaf`),
  naturally in `F` (`CategoryTheory.Sheaf.H'.homologyMap_comp_homologyIsoCohomologyPresheaf_hom`);
* at the whole space the cohomology presheaf is `Hⁿ(X, U F)`
  (`CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH`), and the sections complex of
  `U G(F)` over `X` is the complex of abelian groups underlying `Γ(G(F))`
  (`CategoryTheory.Sheaf.ΓCompIsoSheafComposeCompΓ`).

No separation, compactness or nonemptiness hypothesis is made on `X`.

## Main definitions

* `TauCeti.Topology.moduleCohomologyForgetComparison`: the natural isomorphism between the
  underlying abelian groups of `RⁿΓ(F)` and `Hⁿ(X, U F)`.

## References

* The Stacks Project, Cohomology of Sheaves, Lemmas 20.12.2 and 20.12.3 (tags 09SX and 09SY),
  and §20.3.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {R : Type u} [CommRing R]

variable (X R) in
/-- Forgetting the module structure of a sheaf of `R`-modules sectionwise. -/
private abbrev forgetSheaf :=
  sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

section Resolution

variable (F : X.Sheaf (ModuleCat.{u} R))

/-- The Godement resolution of `F` with its module structures forgotten. -/
private abbrev godementForget :
    CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ :=
  ((forgetSheaf X R).mapHomologicalComplex _).obj ((godementResolution (ModuleCat.{u} R) X).obj F)

/-- The augmentation of the Godement resolution of `F` with its module structures forgotten. -/
private abbrev godementForgetι : (forgetSheaf X R).obj F ⟶ (godementForget F).X 0 :=
  (forgetSheaf X R).map ((toGodement (ModuleCat.{u} R) X).app F)

private lemma godementForgetι_comp_d : godementForgetι F ≫ (godementForget F).d 0 1 = 0 := by
  rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp,
    NatTrans.app_comp_resolution_obj_d_zero_one, Functor.map_zero]

private lemma exact_godementForgetι :
    (ShortComplex.mk _ _ (godementForgetι_comp_d F)).Exact := by
  -- the augmentation of the Godement resolution in degree `0` is `toGodement`
  let α : ShortComplex.mk _ _ (HomologicalComplex.single_f_d
        ((toGodementResolution (ModuleCat.{u} R) X).app F) 1) ⟶
      ShortComplex.mk ((toGodement (ModuleCat.{u} R) X).app F) _
        (NatTrans.app_comp_resolution_obj_d_zero_one _ F) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := 𝟙 _
      comm₁₂ := (Category.id_comp _).trans
        ((NatTrans.toResolution_app_f_zero _ F).symm.trans (Category.comp_id _).symm) }
  have : Epi α.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono α.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).1
    (CochainComplex.exact_f_zero_of_quasiIsoAt _)).map (forgetSheaf X R)

private lemma godementForget_exactAt (j : ℕ) : (godementForget F).ExactAt (j + 1) :=
  (NatTrans.resolution_obj_exactAt_succ _ F j).map (forgetSheaf X R)

private lemma godementForget_subsingleton_H' (V : Opens X) (j k : ℕ) :
    Subsingleton (((godementForget F).X j).H' (k + 1) V) := by
  have := isFlasque_godementResolution_obj_X (ModuleCat.{u} R) X F j
  have : TopCat.Presheaf.IsFlasque ((godementForget F).X j).obj :=
    TopCat.Presheaf.isFlasque_comp (((godementResolution (ModuleCat.{u} R) X).obj F).X j).obj
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  infer_instance

variable (X R) in
/-- The sections of the underlying abelian Godement resolution compute the cohomology presheaf of
the underlying abelian sheaf, naturally in the sheaf of modules. -/
private def godementHomologyIso (n : ℕ) :
    godementResolution (ModuleCat.{u} R) X ⋙ (forgetSheaf X R).mapHomologicalComplex _ ⋙
      (sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _ ⋙
        HomologicalComplex.homologyFunctor _ _ n ≅
      forgetSheaf X R ⋙ Sheaf.cohomologyPresheafFunctor _ n :=
  NatIso.ofComponents (fun F ↦ Sheaf.H'.homologyIsoCohomologyPresheaf (godementForgetι F)
      (godementForgetι_comp_d F) (exact_godementForgetι F) (godementForget_exactAt F)
      (godementForget_subsingleton_H' F) n)
    (fun {F F'} f ↦ Sheaf.H'.homologyMap_comp_homologyIsoCohomologyPresheaf_hom _ _ _ _ _ n _ _ _
      _ _ (by
        rw [Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, ← Functor.map_comp]
        -- in degree `0` the Godement resolution of `f` is the Godement sheaf map of `f`
        exact congrArg _ ((toGodement (ModuleCat.{u} R) X).naturality f).symm))

end Resolution

variable (X R) in
/-- **Derived global sections of module sheaves compute the cohomology of the underlying abelian
sheaves.** For sheaves of modules over a commutative ring on any topological space, the abelian
group underlying `RⁿΓ(F)` is naturally isomorphic to the `Ext`-based cohomology `Hⁿ(X, U F)` of
the underlying abelian sheaf `U F`. -/
def moduleCohomologyForgetComparison
    [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive] (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ⋙
        Sheaf.functorH (Opens.grothendieckTopology X) n :=
  -- `RⁿΓ(F)` is the cohomology of the global sections of the Godement resolution
  Functor.isoWhiskerRight (rightDerivedΓIsoGodement n) _ ≪≫
    -- forgetting the module structures commutes with cohomology
    Functor.isoWhiskerLeft (godementResolution (ModuleCat.{u} R) X ⋙
        (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _)
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplexCompHomologyFunctorIso
        _ n).symm ≪≫
    -- the global sections of the Godement terms are the sections over `⊤` of the abelian terms
    Functor.isoWhiskerLeft (godementResolution (ModuleCat.{u} R) X)
      (Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
          (Sheaf.ΓCompIsoSheafComposeCompΓ _ _ isTerminalTop ≪≫
            Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop ≪≫
              sheafSectionsNatIsoEvaluation _ _)) _ ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm ≪≫
          Functor.isoWhiskerLeft _ (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm)
        (HomologicalComplex.homologyFunctor _ _ n)) ≪≫
    -- evaluation at `⊤` commutes with the cohomology of complexes of presheaves
    Functor.isoWhiskerLeft (godementResolution (ModuleCat.{u} R) X ⋙
        (forgetSheaf X R).mapHomologicalComplex _ ⋙
        (sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _)
      (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
        (op ⊤)).mapHomologicalComplexCompHomologyFunctorIso _ n) ≪≫
    -- the sections of the abelian Godement resolution compute the cohomology presheaf
    Functor.isoWhiskerRight (godementHomologyIso X R n)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) ≪≫
    -- the cohomology presheaf at `⊤` is the cohomology of the space
    Functor.isoWhiskerLeft (forgetSheaf X R)
      (Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ n isTerminalTop)

end TauCeti.Topology
