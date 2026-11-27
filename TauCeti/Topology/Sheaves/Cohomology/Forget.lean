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
public import TauCeti.Topology.Sheaves.Cohomology.Restriction
import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology
import TauCeti.CategoryTheory.Abelian.RightDerived
import TauCeti.CategoryTheory.Sites.GlobalSections
import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal

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

The comparison is not an arbitrary isomorphism of groups. It respects the module structure: the
action of `r ∈ R` on `RⁿΓ(F)`, which is the map induced by the scalar endomorphism `r : F ⟶ F`
since right derived functors of linear functors are linear, corresponds to the map that this
endomorphism induces on `Hⁿ(X, U F)`. In degree `0` it is the identity of the global sections of
`F`, once `R⁰Γ(F)` and `H⁰(X, U F)` are both identified with them.

## Main definitions

* `TauCeti.Topology.moduleCohomologyForgetComparison`: the natural isomorphism between the
  underlying abelian groups of `RⁿΓ(F)` and `Hⁿ(X, U F)`.

## Main results

* `TauCeti.Topology.moduleCohomologyForgetComparison_hom_app_smul`: the comparison intertwines
  multiplication by `r` with the map induced by the scalar endomorphism `r` of `F`.
* `TauCeti.Topology.equiv₀_moduleCohomologyForgetComparison_hom_app_toRightDerivedZero`: in degree
  `0` the comparison is the identity on global sections.

## References

* The Stacks Project, Cohomology of Sheaves, Lemmas 20.12.2 and 20.12.3 (tags 09SX and 09SY),
  and §20.3.

Its arbitrary-resolution characteristic proves compatibility with native all-degree open
  restriction.
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
/-- Global sections of a complex of module sheaves, viewed as abelian groups, are the sections
over `⊤` of the underlying complex of abelian presheaves. -/
private def moduleForgetChainNatIso :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ) ⋙
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ) ≅
      (forgetSheaf X R).mapHomologicalComplex (.up ℕ) ⋙
        (sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ) ⋙
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).mapHomologicalComplex (.up ℕ) :=
  Functor.mapHomologicalComplexCompIso
      (Sheaf.ΓCompIsoSheafComposeCompΓ _ _ isTerminalTop ≪≫
        Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop ≪≫
          sheafSectionsNatIsoEvaluation _ _)) _ ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).symm

variable (X R) in
/-- **Derived global sections of module sheaves compute the cohomology of the underlying abelian
sheaves.** For sheaves of modules over a commutative ring on any topological space, the abelian
group underlying `RⁿΓ(F)` is naturally isomorphic to the `Ext`-based cohomology `Hⁿ(X, U F)` of
the underlying abelian sheaf `U F`. -/
def moduleCohomologyForgetComparison
    (n : ℕ) :
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
      (Functor.isoWhiskerRight (moduleForgetChainNatIso X R)
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

/-- **The comparison is compatible with the scalar action.** Multiplication by `r` on `RⁿΓ(F)`
corresponds to the map induced on `Hⁿ(X, U F)` by the scalar endomorphism `r : F ⟶ F`. -/
theorem moduleCohomologyForgetComparison_hom_app_smul (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (r : R)
    (x : ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n).obj F) :
    (moduleCohomologyForgetComparison X R n).hom.app F (r • x) =
      (Sheaf.functorH (Opens.grothendieckTopology X) n).map ((sheafCompose _
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).map (r • 𝟙 F))
        ((moduleCohomologyForgetComparison X R n).hom.app F x) := by
  have h := ConcreteCategory.congr_hom
    ((moduleCohomologyForgetComparison X R n).hom.naturality (r • 𝟙 F)) x
  -- `RⁿΓ` is linear, so it sends the scalar endomorphism `r` of `F` to multiplication by `r`
  simp only [Functor.comp_map, Functor.map_smul, ConcreteCategory.comp_apply] at h
  rw [CategoryTheory.Functor.map_id] at h
  simpa using h

/-- **Degree-zero normalization of the comparison.** In degree `0`, the comparison sends the
image in `R⁰Γ(F)` of a global section `s` of `F` to the class in `H⁰(X, U F)` that corresponds to
`s` itself under the identification of `H⁰(X, U F)` with the sections of `F` over `X`. -/
theorem equiv₀_moduleCohomologyForgetComparison_hom_app_toRightDerivedZero
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (s : (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj F) :
    Sheaf.H.equiv₀ _ isTerminalTop ((moduleCohomologyForgetComparison X R 0).hom.app F
      (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).toRightDerivedZero).app F s)) =
      (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.app F s := by
  -- The comparison is a composite of identifications of degree-zero homology, each of which acts
  -- on the class of a cycle through a map of cycles. Follow the class of the cycle `c` of the
  -- global sections of the Godement resolution given by `s` through each of them, and then the
  -- cycle itself, which ends up as the image of `s` under the augmentation.
  let K := (godementResolution (ModuleCat.{u} R) X).obj F
  let ΓK := ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K
  let c : ΓK.cycles 0 := ΓK.liftCycles ((Sheaf.Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).map (K.fromSingle₀Equiv F ((toGodementResolution (ModuleCat.{u} R) X).app
      F)).val) 1 (by simp) (Functor.map_fromSingle₀Equiv_val_comp_d _ _) s
  have hA := ConcreteCategory.congr_hom
    (toRightDerivedZero_app_comp_rightDerivedΓIsoGodement_hom_app F) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hA
  simp only [moduleCohomologyForgetComparison, godementHomologyIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Functor.comp_obj,
    ConcreteCategory.comp_apply, ModuleCat.forget₂_map]
  -- the objects of the composite agree only up to unfolding, so its factors are matched with `erw`
  erw [hA]
  -- forgetting the module structure commutes with the class map; the stated type reads
  -- `forget₂` applied to the class map, on elements, as the class map itself, as the goal shows it
  have hB : (Functor.mapHomologicalComplexCompHomologyFunctorIso
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) _ 0).inv.app ΓK (ΓK.homologyπ 0 c) =
        (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex _).obj ΓK).homologyπ 0
          (((ΓK.sc 0).mapCyclesIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).inv c) :=
    Functor.map_homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_inv_app_apply
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) _ 0 ΓK c
  -- the maps of complexes act on classes through their maps on cycles
  rw [hB, ← ConcreteCategory.comp_apply (HomologicalComplex.homologyπ _ 0),
    HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  -- evaluation at `⊤` commutes with the class map
  let P := ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (godementForget F)
  rw [Functor.homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_hom_app_apply]
  simp only [evaluation_obj_map]
  -- `erw`: the component of `NatIso.ofComponents` at the Godement resolution unfolds to
  -- `homologyIsoCohomologyPresheaf`; the component of `cohomologyPresheafEvaluationIsoFunctorH` is
  -- the abbreviation `cohomologyPresheafObjIsoH`, whose source `H' _ 0 ⊤` is the object of the
  -- composite `cohomologyPresheafFunctor ⋙ evaluation`
  erw [Sheaf.H'.homologyIsoCohomologyPresheaf_hom_app_homologyπ_apply,
    Sheaf.H.equiv₀_cohomologyPresheafObjIsoH_hom_apply]
  -- the class of the image of a section under the augmentation is that section
  refine Sheaf.H'.cohomologyZeroSectionsEquiv_resolutionClass _ _ _ _ ⊤ _ _ ?_
  -- it remains to follow the cycle through the identifications of the complexes
  refine Eq.trans ?_
    (Functor.mapCyclesIso_inv_comp_cyclesMap_comp_mapCyclesIso_hom_comp_map_iCycles_apply
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) _ 0
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) ΓK P _ c).symm
  have hJ : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map (ΓK.iCycles 0) c =
      (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
        (K.fromSingle₀Equiv F ((toGodementResolution (ModuleCat.{u} R) X).app F)).val s :=
    ConcreteCategory.congr_hom (ΓK.liftCycles_i _ _ _ _) s
  rw [hJ]
  simp only [moduleForgetChainNatIso, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, ConcreteCategory.comp_apply, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    sheafSectionsNatIsoEvaluation, Iso.refl_hom, Category.comp_id]
  rw [Sheaf.ΓCompIsoSheafComposeCompΓ_hom_app_comp_ΓNatIsoSheafSections_hom_app_apply]
  refine Eq.trans ?_ (ConcreteCategory.congr_hom ((Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) (ModuleCat.{u} R) isTerminalTop).hom.naturality
      (K.fromSingle₀Equiv F ((toGodementResolution (ModuleCat.{u} R) X).app F)).val) s).symm
  -- the augmentation `F ⟶ G⁰(F)` of the Godement resolution is `toGodement`
  exact (congrArg (fun f ↦ f.hom.app (op ⊤) ((Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) (ModuleCat.{u} R) isTerminalTop).hom.app F s))
    (NatTrans.toResolution_app_f_zero (toGodement (ModuleCat.{u} R) X) F)).symm

end TauCeti.Topology

/-! ### Arbitrary injective resolutions and compatibility with native restriction -/

namespace TauCeti.Topology
variable {X : TopCat.{u}} {R : Type u} [CommRing R]
private abbrev forgetModuleComplex (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℕ) :=
  ((forgetSheaf X R).mapHomologicalComplex (.up ℕ)).obj K
variable {F : X.Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F)
private abbrev forgottenIota := (forgetSheaf X R).map (I.ι.f 0)
/-- Underlying abelian terms of a module injective resolution are acyclic on every open.
This uses their flasqueness, without asserting that forgetting preserves injectives. -/
lemma moduleInjectiveResolution_acyclic (V : Opens X) (j k : ℕ) :
    Subsingleton (((((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).X j).H' (k + 1) V) := by
  have : TopCat.Presheaf.IsFlasque (I.cocomplex.X j).obj :=
    Sheaf.isFlasque_of_injective_moduleCat _
  have : TopCat.Presheaf.IsFlasque ((forgetModuleComplex I.cocomplex).X j).obj :=
    TopCat.Presheaf.isFlasque_comp (I.cocomplex.X j).obj
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  infer_instance

private def forgottenIHomologyIso (n : ℕ) :
    (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
      (forgetModuleComplex I.cocomplex)).homology n ≅
      ((forgetSheaf X R).obj F).cohomologyPresheaf n :=
  Sheaf.H'.homologyIsoCohomologyPresheaf (forgottenIota I)
    (CochainComplex.map_augmentation_comp_d (forgetSheaf X R) I.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact (forgetSheaf X R) I.exact₀)
    (CochainComplex.map_exactAt_succ (forgetSheaf X R) I.cocomplex_exactAt_succ)
      (moduleInjectiveResolution_acyclic I) n

variable (X R)
private def moduleComplexForgetHomologyIso (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor _ (.up ℕ) n ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
    (forgetSheaf X R).mapHomologicalComplex (.up ℕ) ⋙
      (sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ) ⋙
        HomologicalComplex.homologyFunctor _ (.up ℕ) n ⋙
          (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) :=
  Functor.isoWhiskerLeft
      ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ))
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplexCompHomologyFunctorIso
        _ n).symm ≪≫
    Functor.isoWhiskerRight (moduleForgetChainNatIso X R)
        (HomologicalComplex.homologyFunctor _ (.up ℕ) n) ≪≫
    Functor.isoWhiskerLeft ((forgetSheaf X R).mapHomologicalComplex (.up ℕ) ⋙
        (sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ))
      (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
        (op ⊤)).mapHomologicalComplexCompHomologyFunctorIso _ n)

variable {X R}
/-- Compute the module/abelian cohomology comparison using any module injective resolution. -/
def moduleCohomologyForgetIsoOfInjectiveResolution (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
      ((((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
        I.cocomplex).homology n) ≅
      (Sheaf.functorH (Opens.grothendieckTopology X) n).obj
        ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) :=
  (moduleComplexForgetHomologyIso X R n).app I.cocomplex ≪≫
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).mapIso
      (forgottenIHomologyIso I n) ≪≫
    (Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ n isTerminalTop).app
      ((forgetSheaf X R).obj F)

private lemma Godement_to_I_abelian_homology (n : ℕ)
    (φ : (godementResolution (ModuleCat.{u} R) X).obj F ⟶ I.cocomplex)
    (hφ : (toGodementResolution (ModuleCat.{u} R) X).app F ≫ φ = I.ι) :
    HomologicalComplex.homologyMap
      (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (((forgetSheaf X R).mapHomologicalComplex _).map φ)) n ≫
      (forgottenIHomologyIso I n).hom = ((godementHomologyIso X R n).app F).hom := by
  have hφ0 : (toGodement (ModuleCat.{u} R) X).app F ≫ φ.f 0 = I.ι.f 0 := by
    simpa only [HomologicalComplex.comp_f, toGodementResolution,
      NatTrans.toResolution_app_f_zero] using congrArg (fun f ↦ f.f 0) hφ
  have hψ : godementForgetι F ≫
      (((forgetSheaf X R).mapHomologicalComplex _).map φ).f 0 =
      (𝟙 ((forgetSheaf X R).obj F)) ≫ forgottenIota I := by
    rw [Category.id_comp, Functor.mapHomologicalComplex_map_f]
    exact ((forgetSheaf X R).map_comp _ _).symm.trans
      (congrArg (forgetSheaf X R).map hφ0)
  have ht := Sheaf.H'.homologyMap_comp_homologyIsoCohomologyPresheaf_hom
    (godementForgetι F) (godementForgetι_comp_d F) (exact_godementForgetι F)
    (godementForget_exactAt F) (godementForget_subsingleton_H' F) n
    (forgottenIota I)
    (CochainComplex.map_augmentation_comp_d (forgetSheaf X R) I.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact (forgetSheaf X R) I.exact₀)
    (CochainComplex.map_exactAt_succ (forgetSheaf X R) I.cocomplex_exactAt_succ)
      (moduleInjectiveResolution_acyclic I) hψ
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht
  exact ht

/-- The existing module/abelian comparison agrees with its arbitrary-resolution computation. -/
lemma moduleCohomologyForgetComparison_hom_app_injectiveResolution (n : ℕ) :
    (moduleCohomologyForgetComparison X R n).hom.app F =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((I.isoRightDerivedObj (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)) n).hom) ≫
      (moduleCohomologyForgetIsoOfInjectiveResolution I n).hom := by
  let φ := InjectiveResolution.descOfQuasiIso (𝟙 F) I
    ((toGodementResolution (ModuleCat.{u} R) X).app F)
  have hφ : (toGodementResolution (ModuleCat.{u} R) X).app F ≫ φ = I.ι := by
    dsimp only [φ]
    rw [InjectiveResolution.ι_comp_descOfQuasiIso]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hm := rightDerivedΓIsoGodement_hom_comp_homologyMap F n I φ hφ
  have ha := Godement_to_I_abelian_homology I n φ hφ
  have hn := (moduleComplexForgetHomologyIso X R n).hom.naturality φ
  -- Expand the existing Godement, homology-forgetting and terminal-evaluation factors.
  change (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      ((rightDerivedΓIsoGodement (X := X) (R := R) n).hom.app F) ≫
    (moduleComplexForgetHomologyIso X R n).hom.app ((godementResolution (ModuleCat.{u} R) X).obj
      F) ≫
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).map
      ((godementHomologyIso X R n).hom.app F) ≫
    (Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ n isTerminalTop).hom.app
      ((forgetSheaf X R).obj F) = _
  rw [← hm, Functor.map_comp]
  dsimp only [moduleCohomologyForgetIsoOfInjectiveResolution, Iso.trans_hom, Iso.app_hom]
  simp only [Category.assoc]
  -- Naturality is evaluated on the sections complex instead of its factorized functors.
  change (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _ ⋙
        HomologicalComplex.homologyFunctor _ _ n).map φ) ≫
      (moduleComplexForgetHomologyIso X R n).hom.app I.cocomplex =
      (moduleComplexForgetHomologyIso X R n).hom.app
        ((godementResolution (ModuleCat.{u} R) X).obj F) ≫
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).map
        (HomologicalComplex.homologyMap
          (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).map
            (((forgetSheaf X R).mapHomologicalComplex _).map φ)) n) at hn
  erw [reassoc_of% hn]
  have he := congrArg (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).map) ha
  rw [Functor.map_comp] at he
  dsimp only [Functor.mapIso_hom]
  erw [reassoc_of% he]
  -- The two sides differ only in `(α.app F).hom` versus `α.hom.app F`.
  rw [Iso.app_hom]

private lemma moduleComplexForget_chain_component (F : X.Sheaf (ModuleCat.{u} R)) :
    (Sheaf.ΓCompIsoSheafComposeCompΓ (Opens.grothendieckTopology X)
       (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) isTerminalTop ≪≫
      Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop ≪≫
        sheafSectionsNatIsoEvaluation _ _)).hom.app F =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map (F.ΓRes (op ⊤)) := by
  rw [Iso.trans_hom, NatTrans.comp_app, Sheaf.ΓCompIsoSheafComposeCompΓ_hom_app,
    Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes]
  -- Evaluation is the identity section comparison; cancel the terminal Γ isomorphism.
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.trans_hom,
    sheafSectionsNatIsoEvaluation, Iso.refl_hom,
    Category.comp_id, Category.assoc, Iso.inv_hom_id_app]
  -- Terminal evaluation and the sectionwise forgetful functor have the same native carrier.
  exact Category.comp_id _

private def moduleForgetChainIso (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℕ) :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
      (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj K) ≅
    (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).mapHomologicalComplex _).obj
      (((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        (forgetModuleComplex K)) :=
  (moduleForgetChainNatIso X R).app K
private lemma moduleForgetChainIso_hom_f (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℕ)
    (i : ℕ) :
    (moduleForgetChainIso K).hom.f i =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map ((K.X i).ΓRes (op ⊤)) := by
  exact moduleComplexForget_chain_component (K.X i)
private abbrev moduleSectionsComplex (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℕ) :=
  ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj K
private abbrev abelianSectionsComplex (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℕ) :=
  ((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
    (forgetModuleComplex K)
private abbrev moduleForgetCyclesComparison
    (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℕ) (n : ℕ) :=
  HomologicalComplex.cyclesComparison
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (moduleSectionsComplex K) n
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
    (abelianSectionsComplex K) (moduleForgetChainIso K).hom
private lemma moduleComplexForgetHomologyIso_cycle
    (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℕ) (n : ℕ)
    (z : (moduleSectionsComplex K).cycles n) :
    (moduleComplexForgetHomologyIso X R n).hom.app K
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((moduleSectionsComplex K).homologyπ n) z) =
      ((abelianSectionsComplex K).homologyπ n).app (op ⊤)
        (moduleForgetCyclesComparison K n z) := by
  have h := HomologicalComplex.cyclesComparison_homologyπ
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (moduleSectionsComplex K) n
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
    (abelianSectionsComplex K) (moduleForgetChainIso K).hom
  -- The named complex comparison is the composite used in the generic cycle formula.
  change (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      ((moduleSectionsComplex K).homologyπ n) ≫ (moduleComplexForgetHomologyIso X R n).hom.app K =
    moduleForgetCyclesComparison K n ≫
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).map
        ((abelianSectionsComplex K).homologyπ n) at h
  exact ConcreteCategory.congr_hom h z
private lemma moduleForgetCyclesComparison_iCycles
    (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℕ) (n : ℕ)
    (z : (moduleSectionsComplex K).cycles n) :
    ((abelianSectionsComplex K).iCycles n).app (op ⊤)
      (moduleForgetCyclesComparison K n z) =
      (K.X n).ΓRes (op ⊤) ((moduleSectionsComplex K).iCycles n z) := by
  have h := HomologicalComplex.cyclesComparison_iCycles
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (moduleSectionsComplex K) n
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
    (abelianSectionsComplex K) (moduleForgetChainIso K).hom
  rw [moduleForgetChainIso_hom_f] at h
  exact ConcreteCategory.congr_hom h z

/-- Restricting a cycle of the native module-sections complex gives an abelian section cycle. -/
lemma moduleSectionsCycle_ΓRes_d_eq_zero
    (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℕ) (n : ℕ)
    (z : (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex
      (.up ℕ)).obj K).cycles n) :
    ((((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).mapHomologicalComplex (.up ℕ)).obj
        K).d n (n + 1)).hom.app (op ⊤)
      ((K.X n).ΓRes (op ⊤)
        ((((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex
          (.up ℕ)).obj K).iCycles n z)) = 0 := by
  rw [← moduleForgetCyclesComparison_iCycles K n z]
  exact Sheaf.H'.d_hom_app_iCycles_app n (moduleForgetCyclesComparison K n z)

variable {F : X.Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F)
/-- The arbitrary-resolution comparison sends a homology class to the class of its ΓRes cycle. -/
lemma moduleCohomologyForgetIsoOfInjectiveResolution_hom_homologyπ (n : ℕ)
    (z : (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).cycles n) :
    (moduleCohomologyForgetIsoOfInjectiveResolution I n).hom
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex
          (.up ℕ)).obj I.cocomplex).homologyπ n) z) =
      (Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ n isTerminalTop).hom.app
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F)
        (Sheaf.H'.resolutionClass
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).map (I.ι.f 0))
          (CochainComplex.map_augmentation_comp_d (sheafCompose (Opens.grothendieckTopology X)
            (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) I.ι_f_zero_comp_complex_d)
          (CochainComplex.map_augmentation_exact (sheafCompose (Opens.grothendieckTopology X)
            (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) I.exact₀)
          (CochainComplex.map_exactAt_succ (sheafCompose (Opens.grothendieckTopology X)
            (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) I.cocomplex_exactAt_succ)
          (⊤ : Opens X)
          ((I.cocomplex.X n).ΓRes (op ⊤)
            ((((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex
              (.up ℕ)).obj I.cocomplex).iCycles n z))
          (moduleSectionsCycle_ΓRes_d_eq_zero I.cocomplex n z)) := by
  dsimp only [moduleCohomologyForgetIsoOfInjectiveResolution, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom]
  simp only [ConcreteCategory.comp_apply]
  rw [moduleComplexForgetHomologyIso_cycle]
  have h := congrArg (fun x ↦ (Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ n
    isTerminalTop).hom.app ((forgetSheaf X R).obj F) x)
    (Sheaf.H'.homologyIsoCohomologyPresheaf_hom_app_homologyπ_apply
      (forgottenIota I)
      (CochainComplex.map_augmentation_comp_d (forgetSheaf X R) I.ι_f_zero_comp_complex_d)
      (CochainComplex.map_augmentation_exact (forgetSheaf X R) I.exact₀)
      (CochainComplex.map_exactAt_succ (forgetSheaf X R) I.cocomplex_exactAt_succ)
        (moduleInjectiveResolution_acyclic I)
      n (op ⊤) (moduleForgetCyclesComparison I.cocomplex n z))
  simpa only [forgottenIHomologyIso, forgottenIota, evaluation_obj_map,
    moduleForgetCyclesComparison_iCycles] using h

variable (U : Opens X)
open TauCeti.Topology TopologicalSpace.Opens
private lemma moduleForgetCyclesComparison_restrict_iCycles {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (n : ℕ) (z : (moduleSectionsComplex I.cocomplex).cycles n) :
    ((abelianSectionsComplex (X := TopCat.of U) (R := R)
      (U.sheafRestrict.mapInjectiveResolution I).cocomplex).iCycles n).app
      (op ⊤) (moduleForgetCyclesComparison (X := TopCat.of U) (R := R)
        (U.sheafRestrict.mapInjectiveResolution I).cocomplex n
        (HomologicalComplex.cyclesMap (rightDerivedΓRestrictionComplexMap U I) n z)) =
    (I.cocomplex.X n).obj.map ((Over.mkIdTerminal (X := U)).from (U.overEquivalence.inverse.obj
      ⊤)).left.op
      ((I.cocomplex.X n).ΓRes (op U) ((moduleSectionsComplex I.cocomplex).iCycles n z)) := by
  rw [moduleForgetCyclesComparison_iCycles]
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (rightDerivedΓRestrictionComplexMap U I) n) z
  -- Taking cyclesMap_i and evaluating in the concrete module category gives these
  -- actual moduleSectionsComplex cycle inclusions; no forgetting-injectives property is used.
  change (moduleSectionsComplex (X := TopCat.of U) (R := R)
      (U.sheafRestrict.mapInjectiveResolution I).cocomplex).iCycles n
      (HomologicalComplex.cyclesMap (rightDerivedΓRestrictionComplexMap U I) n z) =
    (rightDerivedΓRestrictionComplexMap U I).f n ((moduleSectionsComplex I.cocomplex).iCycles n z)
      at h
  rw [h]
  have h' := ConcreteCategory.congr_hom (rightDerivedΓRestrictionComplexMap_f_ΓRes U I n)
    ((moduleSectionsComplex I.cocomplex).iCycles n z)
  rw [sheafRestrictSectionsTopIso_hom_app] at h'
  exact h'

private def moduleCycleClass {F : X.Sheaf (ModuleCat.{u} R)} (I : InjectiveResolution F)
    (n : ℕ) (z : (moduleSectionsComplex I.cocomplex).cycles n) :=
  Sheaf.H'.resolutionClass (forgottenIota I)
    (CochainComplex.map_augmentation_comp_d (forgetSheaf X R) I.ι_f_zero_comp_complex_d)
    (CochainComplex.map_augmentation_exact (forgetSheaf X R) I.exact₀)
    (CochainComplex.map_exactAt_succ (forgetSheaf X R) I.cocomplex_exactAt_succ)
    (⊤ : Opens X)
    ((I.cocomplex.X n).ΓRes (op ⊤) ((moduleSectionsComplex I.cocomplex).iCycles n z))
    (moduleSectionsCycle_ΓRes_d_eq_zero I.cocomplex n z)
private lemma moduleCycleClass_restriction {F : X.Sheaf (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (n : ℕ) (z : (moduleSectionsComplex I.cocomplex).cycles n) :
    (U.cohomologyPresheafObjIsoSheafRestrictH
      ((forgetSheaf X R).obj F) n).hom
      ((((forgetSheaf X R).obj F).cohomologyPresheaf n).map
        (homOfLE (show U ≤ ⊤ from le_top)).op (moduleCycleClass I n z)) =
    (Sheaf.cohomologyPresheafEvaluationIsoFunctorH (Opens.grothendieckTopology U) n
      isTerminalTop).hom.app
      ((forgetSheaf (TopCat.of U) R).obj (U.sheafRestrict.obj F))
      (moduleCycleClass (X := TopCat.of U) (R := R) (U.sheafRestrict.mapInjectiveResolution I) n
        (HomologicalComplex.cyclesMap (rightDerivedΓRestrictionComplexMap U I) n z)) := by
  dsimp only [moduleCycleClass]
  rw [Sheaf.H'.cohomologyPresheaf_map_resolutionClass,
    cohomologyPresheafObjIsoSheafRestrictH_resolutionClass U (forgetModuleComplex I.cocomplex)]
  congr 2
  -- The general theorem states its cocycle proof for the restricted forgotten complex, and the
  -- restricted resolution states it for the forgotten restricted complex; proofs are irrelevant.
  on_goal 2 => exact proof_irrel_heq _ _
  have hc := moduleForgetCyclesComparison_restrict_iCycles U I n z
  rw [moduleForgetCyclesComparison_iCycles] at hc
  rw [hc]
  exact congrArg (fun x ↦ (I.cocomplex.X n).obj.map
    ((Over.mkIdTerminal (X := U)).from (U.overEquivalence.inverse.obj ⊤)).left.op x)
    (ConcreteCategory.congr_hom
      (Sheaf.ΓRes_map (I.cocomplex.X n) (homOfLE (show U ≤ ⊤ from le_top)).op)
      ((moduleSectionsComplex I.cocomplex).iCycles n z))

private lemma moduleCohomologyForgetIsoOfInjectiveResolution_restriction {F : X.Sheaf
  (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      (HomologicalComplex.homologyMap (rightDerivedΓRestrictionComplexMap U I) n) ≫
      (moduleCohomologyForgetIsoOfInjectiveResolution (U.sheafRestrict.mapInjectiveResolution I)
        n).hom =
    (moduleCohomologyForgetIsoOfInjectiveResolution I n).hom ≫
      (Sheaf.cohomologyPresheafEvaluationIsoFunctorH (Opens.grothendieckTopology X) n
        isTerminalTop).inv.app ((forgetSheaf X R).obj F) ≫
      (((forgetSheaf X R).obj F).cohomologyPresheaf n).map
        (homOfLE (show U ≤ ⊤ from le_top)).op ≫
      (U.cohomologyPresheafObjIsoSheafRestrictH
        ((forgetSheaf X R).obj F) n).hom := by
  apply (cancel_epi ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
    ((moduleSectionsComplex I.cocomplex).homologyπ n))).1
  rw [← Category.assoc, ← Functor.map_comp, HomologicalComplex.homologyπ_naturality,
    Functor.map_comp, Category.assoc]
  ext z
  -- Forgetting is pointwise, so this displays the transported homology class of the cycle.
  change (moduleCohomologyForgetIsoOfInjectiveResolution (X := TopCat.of U) (R := R)
    (U.sheafRestrict.mapInjectiveResolution I) n).hom
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      ((moduleSectionsComplex (X := TopCat.of U) (R := R)
        (U.sheafRestrict.mapInjectiveResolution I).cocomplex).homologyπ n)
      (HomologicalComplex.cyclesMap (rightDerivedΓRestrictionComplexMap U I) n z)) =
    (U.cohomologyPresheafObjIsoSheafRestrictH
      ((forgetSheaf X R).obj F) n).hom
      ((((forgetSheaf X R).obj F).cohomologyPresheaf n).map
        (homOfLE (show U ≤ ⊤ from le_top)).op
        ((Sheaf.cohomologyPresheafEvaluationIsoFunctorH (Opens.grothendieckTopology X) n
          isTerminalTop).inv.app ((forgetSheaf X R).obj F)
          ((moduleCohomologyForgetIsoOfInjectiveResolution I n).hom
            ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
              ((moduleSectionsComplex I.cocomplex).homologyπ n) z))))
  rw [moduleCohomologyForgetIsoOfInjectiveResolution_hom_homologyπ,
    moduleCohomologyForgetIsoOfInjectiveResolution_hom_homologyπ]
  -- The left comparison evaluates the same cycle class on the actual open subspace.
  change (Sheaf.cohomologyPresheafEvaluationIsoFunctorH (Opens.grothendieckTopology U) n
    isTerminalTop).hom.app
    ((forgetSheaf (TopCat.of U) R).obj (U.sheafRestrict.obj F))
    (moduleCycleClass (X := TopCat.of U) (R := R) (U.sheafRestrict.mapInjectiveResolution I) n
      (HomologicalComplex.cyclesMap (rightDerivedΓRestrictionComplexMap U I) n z)) = _
  rw [Iso.hom_inv_id_app_apply]
  exact (moduleCycleClass_restriction U I n z).symm

/-- The existing module/abelian cohomology comparison commutes with native open restriction. -/
theorem moduleCohomologyForgetComparison_restriction (F : X.Sheaf (ModuleCat.{u} R)) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((rightDerivedΓRestriction U n).app F) ≫
      ((moduleCohomologyForgetComparison (TopCat.of U) R n).app
        (U.sheafRestrict.obj F)).hom =
    ((moduleCohomologyForgetComparison X R n).app F).hom ≫
      (Sheaf.cohomologyPresheafEvaluationIsoFunctorH
        (Opens.grothendieckTopology X) n isTerminalTop).inv.app
          ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) ≫
      (((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).cohomologyPresheaf n).map
        (homOfLE (show U ≤ ⊤ from le_top)).op ≫
      (U.cohomologyPresheafObjIsoSheafRestrictH
        ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) n).hom := by
  let I := injectiveResolution F
  let A := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  have hX := moduleCohomologyForgetComparison_hom_app_injectiveResolution I n
  have hU := moduleCohomologyForgetComparison_hom_app_injectiveResolution
    (X := TopCat.of U) (R := R) (U.sheafRestrict.mapInjectiveResolution I) n
  have hR := congrArg A.map (rightDerivedΓRestriction_app_injectiveResolution U I n)
  simp only [Functor.map_comp] at hR
  have hC := moduleCohomologyForgetIsoOfInjectiveResolution_restriction U I n
  have hs := (CommSq.mk hR.symm).horiz_comp (CommSq.mk hC.symm)
  exact (congrArg (fun f ↦ A.map ((rightDerivedΓRestriction U n).app F) ≫ f) hU).trans
    (hs.w.symm.trans (congrArg (· ≫ _) hX.symm))
end TauCeti.Topology
