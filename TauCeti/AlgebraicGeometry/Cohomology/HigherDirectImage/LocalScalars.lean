/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Presheaf
public import TauCeti.AlgebraicGeometry.Cohomology.Pullback.Opens
import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Local functions acting on higher direct image presheaves

For a morphism of schemes `f : X ⟶ Y` and a sheaf of modules `M` on `X`, the presheaf of
`𝒪_Y`-modules `V ↦ Hⁿ(f⁻¹ V, M)` (`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheaf`) is
identified with cohomology on preimages by
`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafToPresheafIso`. Over an open `V`, a function
`r` on `V` acts on its sections. The library's `Module` instance on `Hⁿ(f⁻¹ V, M)`
(`AlgebraicGeometry.Scheme.Modules.cohomologyOnModule`) is over the global functions of `X` only,
so to compare, we read `Hⁿ(f⁻¹ V, M)` in the cohomology `Hⁿ(f⁻¹ V, M|_{f⁻¹ V})` of the open
subscheme `f⁻¹ V`, a module over the functions on `f⁻¹ V`, through the injective map
`AlgebraicGeometry.Scheme.Opens.cohomologyOnPullbackι`. There the action of `r` is the action of
its pullback `f^* r`
(`Scheme.Hom.cohomologyOnPullbackι_higherDirectImagePresheafToPresheafIso_hom_app_smul`).
The existing `AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafToPresheafIso_hom_app_smul`
handles restrictions of global functions of `Y`, acting on `Hⁿ(f⁻¹ U, M)` itself; the lemma here
handles arbitrary functions on `V`, after applying `cohomologyOnPullbackι`.

The proof computes the identification on homology classes of cycles of the injective resolution
used to build the presheaf: the class of a cycle `s ∈ Γ(f⁻¹ V, Pⁿ)` goes to the class of `s` in
`Hⁿ(f⁻¹ V, M)`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImagePresheafToPresheafIso_hom_app_homologyπ`),
and the action of `r` on the cycle is multiplication by `f^* r`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Functor Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The complex `f_* P` of presheaves of modules on `Y`, for the chosen injective resolution `P` of
`M`, whose homology is the presheaf `V ↦ Hⁿ(f⁻¹ V, M)`. -/
private abbrev modComplex (M : X.Modules) : CochainComplex Y.PresheafOfModules ℕ :=
  ((Modules.pushforward f ⋙ Modules.toPresheafOfModules Y).mapHomologicalComplex _).obj
    (injectiveResolution M).cocomplex

/-- The complex of abelian presheaves underlying the chosen injective resolution of `M`. -/
private abbrev abComplex (M : X.Modules) : CochainComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  ((sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _).obj
    (((toSheaf X).mapHomologicalComplex _).obj (injectiveResolution M).cocomplex)

/-- Precomposition with taking preimages under `f`. -/
private abbrev preimageWhisker :
    (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opens.map f.base).op

/-- The cycles of `f_* P`, without their scalars, are the cycles of `P` on preimages. -/
private abbrev cyclesComparison (M : X.Modules) (n : ℕ) :
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj ((modComplex f M).cycles n) ⟶
      (preimageWhisker f).obj ((abComplex M).cycles n) :=
  (((modComplex f M).sc n).mapCyclesIso (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)).inv ≫
    HomologicalComplex.cyclesMap
      ((pushforwardSectionsComplexIso f).hom.app (injectiveResolution M).cocomplex) n ≫
    (((abComplex M).sc n).mapCyclesIso (preimageWhisker f)).hom

/-- On homology classes, the comparison with cohomology is the class of the corresponding cycle of
the resolution. -/
private lemma homologyπ_comp_higherDirectImagePresheafToPresheafIso_hom (M : X.Modules) (n : ℕ) :
    letI := Functor.additive_of_preserves_binary_products
      (Modules.pushforward f ⋙ Modules.toPresheafOfModules Y)
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map ((modComplex f M).homologyπ n) ≫
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((injectiveResolution M).isoRightDerivedObj
          (Modules.pushforward f ⋙ Modules.toPresheafOfModules Y) n).inv ≫
      (f.higherDirectImagePresheafToPresheafIso M n).hom =
    cyclesComparison f M n ≫ (preimageWhisker f).map
      ((abComplex M).homologyπ n ≫ ((injectiveResolution M).cohomologyPresheafIso n).hom) := by
  let := Functor.additive_of_preserves_binary_products
      (Modules.pushforward f ⋙ Modules.toPresheafOfModules Y)
  let t := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
  let Kmod := modComplex f M
  let W := preimageWhisker f
  have hG : t.map ((injectiveResolution M).isoRightDerivedObj
      (Modules.pushforward f ⋙ Modules.toPresheafOfModules Y) n).inv ≫
      (f.higherDirectImagePresheafToPresheafIso M n).hom =
      (t.mapHomologicalComplexCompHomologyFunctorIso _ n).inv.app Kmod ≫
      (HomologicalComplex.homologyFunctor _ _ n).map
        ((pushforwardSectionsComplexIso f).hom.app (injectiveResolution M).cocomplex) ≫
      (W.mapHomologicalComplexCompHomologyFunctorIso _ n).hom.app _ ≫
      W.map ((injectiveResolution M).cohomologyPresheafIso n).hom := by
    rw [higherDirectImagePresheafToPresheafIso_def]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    exact (congrArg (· ≫ _) (t.map_id _)).trans (Category.id_comp _)
  rw [hG, t.map_homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_inv_app_assoc]
  -- `pushforwardSectionsComplexIso` relates `t` applied to `f_* P` and `W` applied to `P` only up
  -- to unfolding `mapHomologicalComplex`, so the naturality rewrites need `erw`; the final `rfl`
  -- unfolds the abbreviation `cyclesComparison`.
  erw [HomologicalComplex.homologyπ_naturality_assoc,
    W.homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_hom_app_assoc]
  rw [Functor.map_comp]
  rfl

/-- On cycles, the comparison of cycles followed by the inclusion of cycles of `P` is the inclusion
of cycles of `f_* P`. -/
private lemma cyclesComparison_comp_iCycles (M : X.Modules) (n : ℕ) :
    cyclesComparison f M n ≫ (preimageWhisker f).map ((abComplex M).iCycles n) =
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map ((modComplex f M).iCycles n) := by
  let t := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
  let Kmod := modComplex f M
  let Kab := abComplex M
  let W := preimageWhisker f
  have b2 : HomologicalComplex.cyclesMap
        ((pushforwardSectionsComplexIso f).hom.app (injectiveResolution M).cocomplex) n ≫
        ((W.mapHomologicalComplex _).obj Kab).iCycles n =
      ((t.mapHomologicalComplex _).obj Kmod).iCycles n :=
    (HomologicalComplex.cyclesMap_i _ n).trans
      ((congrArg (_ ≫ ·) (pushforwardSectionsComplexIso_hom_app_f f _ n)).trans
        (Category.comp_id _))
  -- Reassociate and apply `mapCyclesIso_hom_comp_map_iCycles`, `b2` and
  -- `mapCyclesIso_inv_comp_iCycles`. The objects between
  -- the factors agree only up to unfolding `mapHomologicalComplex` (the cycles of `t` applied to
  -- `f_* P` versus `W` applied to `P`), so `rw [Category.assoc]` fails with a motive type error and
  -- the chain is built by hand.
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (W.mapCyclesIso_hom_comp_map_iCycles _ n Kab)))).trans ?_)
  exact (congrArg (((Kmod.sc n).mapCyclesIso t).inv ≫ ·) b2).trans
    (t.mapCyclesIso_inv_comp_iCycles _ n Kmod)

/-- **Classes of cycles.** Let `P` be the injective resolution of `M` used to construct the presheaf
`V ↦ Hⁿ(f⁻¹ V, M)`, so that its sections over `V` are the homology of the complex `Γ(f⁻¹ V, P)`.
The comparison with cohomology sends the homology class of a cycle `s ∈ Γ(f⁻¹ V, Pⁿ)` to the class
of `s` in `Hⁿ(f⁻¹ V, M)` (`CategoryTheory.Sheaf.H'.resolutionClass`). -/
lemma higherDirectImagePresheafToPresheafIso_hom_app_homologyπ (M : X.Modules) (n : ℕ)
    (V : Y.Opens)
    (z : ((((Modules.pushforward f ⋙ Modules.toPresheafOfModules Y).mapHomologicalComplex
        _).obj (injectiveResolution M).cocomplex).cycles n).obj (.op V)) :
    letI := Functor.additive_of_preserves_binary_products
      (Modules.pushforward f ⋙ Modules.toPresheafOfModules Y)
    (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op V)
        (((injectiveResolution M).isoRightDerivedObj
          (Modules.pushforward f ⋙ Modules.toPresheafOfModules Y) n).inv.app (.op V)
          (((((Modules.pushforward f ⋙ Modules.toPresheafOfModules Y).mapHomologicalComplex
            _).obj (injectiveResolution M).cocomplex).homologyπ n).app (.op V) z)) =
      CategoryTheory.Sheaf.H'.resolutionClass
        (K := ((toSheaf X).mapHomologicalComplex _).obj (injectiveResolution M).cocomplex)
        ((toSheaf X).map ((injectiveResolution M).ι.f 0))
        ((injectiveResolution M).map_ι_f_zero_comp_d (toSheaf X))
        ((injectiveResolution M).exact₀_map (toSheaf X))
        ((injectiveResolution M).exactAt_succ_map (toSheaf X)) (f ⁻¹ᵁ V)
        (((((Modules.pushforward f ⋙ Modules.toPresheafOfModules Y).mapHomologicalComplex
          _).obj (injectiveResolution M).cocomplex).iCycles n).app (.op V) z) (by
          have h := ConcreteCategory.congr_hom
            (congrArg (fun φ ↦ PresheafOfModules.Hom.app φ (.op V))
            ((((Modules.pushforward f ⋙ Modules.toPresheafOfModules Y).mapHomologicalComplex
              _).obj (injectiveResolution M).cocomplex).iCycles_d n (n + 1))) z
          exact h) := by
  have e1 := ConcreteCategory.congr_hom
    (NatTrans.congr_app (homologyπ_comp_higherDirectImagePresheafToPresheafIso_hom f M n) (op V)) z
  have e2 := ConcreteCategory.congr_hom
    (NatTrans.congr_app (cyclesComparison_comp_iCycles f M n) (op V)) z
  simp only [NatTrans.comp_app] at e1 e2
  -- The middle `rfl` only splits the composite `W.map (homologyπ ≫ cohomologyPresheafIso.hom)`
  -- evaluated at `op V`, which is evaluation at `op (f ⁻¹ᵁ V)`, into its two factors.
  refine e1.trans (Eq.trans (b := ((injectiveResolution M).cohomologyPresheafIso n).hom.app
    (op (f ⁻¹ᵁ V)) (((abComplex M).homologyπ n).app (op (f ⁻¹ᵁ V))
      ((cyclesComparison f M n).app (op V) z))) rfl ?_)
  rw [(injectiveResolution M).cohomologyPresheafIso_hom_app_homologyπ_apply]
  congr 1

/-- **Local functions act on `Hⁿ(f⁻¹ V, M)` through the open subscheme.** For an open `V` of `Y`,
the action of a function `r` on `V` on the sections over `V` of the presheaf of modules
`V ↦ Hⁿ(f⁻¹ V, M)` is, read in the cohomology `Hⁿ(f⁻¹ V, M|_{f⁻¹ V})` of the open subscheme
`f⁻¹ V` through `Scheme.Opens.cohomologyOnPullbackι`, the action of its pullback `f^* r`, a global
function of `f⁻¹ V`. Unlike `higherDirectImagePresheafToPresheafIso_hom_app_smul`, which handles
restrictions of global functions of `Y` acting on `Hⁿ(f⁻¹ V, M)` itself, `r` is an arbitrary
function on `V`, and the action is compared after applying `cohomologyOnPullbackι`. -/
theorem cohomologyOnPullbackι_higherDirectImagePresheafToPresheafIso_hom_app_smul (M : X.Modules)
    (n : ℕ) (V : Y.Opens) (r : Γ(Y, V)) (x : ((f.higherDirectImagePresheaf n).obj M).obj (.op V)) :
    (f ⁻¹ᵁ V).cohomologyOnPullbackι M n ((f.higherDirectImagePresheafToPresheafIso M n).hom.app
        (.op V) ((show Y.ringCatSheaf.obj.obj (.op V) from r) • x)) =
      (f ⁻¹ᵁ V).topIso.inv (f.app V r) • (f ⁻¹ᵁ V).cohomologyOnPullbackι M n
        ((f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op V) x) := by
  let := Functor.additive_of_preserves_binary_products
      (Modules.pushforward f ⋙ Modules.toPresheafOfModules Y)
  let F := Modules.pushforward f ⋙ Modules.toPresheafOfModules Y
  let P := injectiveResolution M
  let Kmod := (F.mapHomologicalComplex _).obj P.cocomplex
  let A := P.isoRightDerivedObj F n
  obtain ⟨y, rfl⟩ : ∃ y, A.inv.app (op V) y = x :=
    ⟨A.hom.app (op V) x, by
      rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, A.hom_inv_id]
      rfl⟩
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((PresheafOfModules.evaluation _ (op V)).map (Kmod.homologyπ n))).mp inferInstance y
  have e : (show Y.ringCatSheaf.obj.obj (op V) from r) •
      A.inv.app (op V) (((PresheafOfModules.evaluation _ (op V)).map (Kmod.homologyπ n)) z) =
      A.inv.app (op V)
        (((PresheafOfModules.evaluation _ (op V)).map (Kmod.homologyπ n)) (r • z)) := by
    rw [_root_.map_smul]
    exact ((A.inv.app (op V)).hom.map_smul _ _).symm
  refine (congrArg (fun w ↦ (f ⁻¹ᵁ V).cohomologyOnPullbackι M n
    ((f.higherDirectImagePresheafToPresheafIso M n).hom.app (op V) w)) e).trans ?_
  refine (congrArg ((f ⁻¹ᵁ V).cohomologyOnPullbackι M n)
    (higherDirectImagePresheafToPresheafIso_hom_app_homologyπ f M n V (r • z))).trans ?_
  refine Eq.trans ?_ (congrArg (_ • ·) (congrArg ((f ⁻¹ᵁ V).cohomologyOnPullbackι M n)
    (higherDirectImagePresheafToPresheafIso_hom_app_homologyπ f M n V z))).symm
  have key := (f ⁻¹ᵁ V).cohomologyOnPullbackι_resolutionClass_smul P (f.app V r)
    ((Kmod.iCycles n).app (op V) z) (by
      exact ConcreteCategory.congr_hom (congrArg (fun φ ↦ PresheafOfModules.Hom.app φ (op V))
        (Kmod.iCycles_d n (n + 1))) z)
  -- `key` is stated with `f.app V r` acting on sections of `P` over `f⁻¹ V`, while the goal has
  -- `r` acting on the same sections of the pushforward `f_* P` over `V`; the two scalar actions
  -- agree definitionally, so after `convert` the remaining goals are this `map_smul` and the
  -- (propositional) cocycle conditions.
  convert key using 3
  congr 2
  · exact _root_.map_smul ((Kmod.iCycles n).app (op V)).hom r z
  · exact proof_irrel_heq _ _
end AlgebraicGeometry.Scheme.Hom
