/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Opens
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Pullback.ToSheaf
public import TauCeti.Topology.Sheaves.Cohomology.Pullback
import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-!
# Pullback on the cohomology of sheaves of modules

Let `g : Y ⟶ X` be a morphism of schemes and `M` a sheaf of modules on `X`. This file constructs
the pullback map

`g.cohomologyPullback M n : Hⁿ(X, M) →+ Hⁿ(Y, g^* M)`.

It is the inverse image map on the cohomology of the underlying abelian sheaves
(`TopCat.Hom.cohomologyPullback`), followed by the map induced on cohomology by the
comparison `g⁻¹ M ⟶ g^* M` between the inverse image of the underlying abelian sheaf of `M` and
the underlying abelian sheaf of the module pullback
(`AlgebraicGeometry.Scheme.Hom.toSheafPullbackComparison`).

The pullback map is natural in `M`, commutes with the connecting maps of a short exact sequence
whose pullback is still short exact (for instance for flat `g` and quasi-coherent terms), is
semilinear for the action of global functions along `g^♯ : Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)`, and is the
pullback of global sections in degree zero. For the base change `Y = X ×_R R'` along a ring map
`R → R'`, its `R'`-linear extension is the flat base change map
`R' ⊗_R Hⁿ(X, M) ⟶ Hⁿ(X_{R'}, M_{R'})` (`TauCeti.AlgebraicGeometry.cohomologyBaseChange`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.cohomologyPullback`: the map `Hⁿ(X, M) →+ Hⁿ(Y, g^* M)`;
* `AlgebraicGeometry.Scheme.Hom.cohomologyPullback_cohomologyMap`: naturality in `M`;
* `AlgebraicGeometry.Scheme.Hom.cohomologyPullback_cohomologyδ`: compatibility with the
  connecting maps of long exact cohomology sequences;
* `AlgebraicGeometry.Scheme.Hom.cohomologyZeroEquiv_cohomologyPullback`: the degree-zero case;
* `AlgebraicGeometry.Scheme.Hom.cohomologyPullback_smul`: semilinearity over global functions.

For an open subset `U` the analogous map is `Scheme.Hom.cohomologyOnPullback`, from
`Hⁿ(U, M)` to `Hⁿ(g⁻¹ U, g^* M)`. It is semilinear over global functions, commutes with
restriction and with the connecting maps for the covers `U ∪ V` and `g⁻¹ U ∪ g⁻¹ V`, and
in degree zero is pullback of sections. These comparisons provide the commutative
Mayer–Vietoris ladders used to transport cohomological statements across a morphism of
schemes, without any affine-diagonal hypothesis.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.8.1 and Proposition III.9.3.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The pullback map `Hⁿ(X, M) →+ Hⁿ(Y, g^* M)` on the cohomology of a sheaf of modules along a
morphism of schemes `g : Y ⟶ X`. -/
def cohomologyPullback (M : X.Modules) (n : ℕ) :
    Cohomology M n →+ Cohomology ((Scheme.Modules.pullback g).obj M) n :=
  (CategoryTheory.Sheaf.H.map ((toSheafPullbackComparison g).app M) n).comp
    (g.base.cohomologyPullback ((toSheaf X).obj M) n)

private lemma cohomologyPullback_apply (M : X.Modules) (n : ℕ) (x : Cohomology M n) :
    g.cohomologyPullback M n x = CategoryTheory.Sheaf.H.map ((toSheafPullbackComparison g).app M) n
      (g.base.cohomologyPullback ((toSheaf X).obj M) n x) :=
  rfl

/-- The pullback map on cohomology is natural in the coefficient sheaf. -/
theorem cohomologyPullback_cohomologyMap {M N : X.Modules} (α : M ⟶ N) (n : ℕ)
    (x : Cohomology M n) :
    g.cohomologyPullback N n (cohomologyMap α n x) =
      cohomologyMap ((Scheme.Modules.pullback g).map α) n (g.cohomologyPullback M n x) := by
  rw [cohomologyPullback_apply, cohomologyPullback_apply, cohomologyMap_eq, cohomologyMap_eq]
  calc _ = CategoryTheory.Sheaf.H.map ((toSheafPullbackComparison g).app N) n
        (CategoryTheory.Sheaf.H.map (((Opens.map g.base).sheafPullback AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map
            ((toSheaf X).map α)) n
          (g.base.cohomologyPullback ((toSheaf X).obj M) n x)) :=
        congrArg _ (g.base.cohomologyPullback_map ((toSheaf X).map α) x)
    _ = _ := (CategoryTheory.Sheaf.H.map_comp_apply _ _ _).symm.trans
      ((congrArg (fun φ ↦ CategoryTheory.Sheaf.H.map φ n
        (g.base.cohomologyPullback ((toSheaf X).obj M) n x))
          ((toSheafPullbackComparison g).naturality α)).trans
        (CategoryTheory.Sheaf.H.map_comp_apply _ _ _))

/-- The pullback map on cohomology commutes with the connecting maps of a short exact sequence
`S` of sheaves of modules on `X` whose pullback to `Y` is short exact, for instance when `g` is flat
and the first two terms of `S` are quasi-coherent
(`AlgebraicGeometry.Scheme.Hom.shortExact_map_pullback_of_flat`). -/
theorem cohomologyPullback_cohomologyδ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hS' : (S.map (Scheme.Modules.pullback g)).ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (x : Cohomology S.X₃ n₀) :
    g.cohomologyPullback S.X₁ n₁ (cohomologyδ hS n₀ n₁ h x) =
      cohomologyδ hS' n₀ n₁ h (g.cohomologyPullback S.X₃ n₀ x) := by
  let φ := toSheafPullbackComparison g
  -- The comparison, as a morphism from the inverse image of the underlying short exact sequence
  -- of abelian sheaves to the underlying short exact sequence of the pullback.
  let ψ : ((S.map (toSheaf X)).map ((Opens.map g.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y))) ⟶
      (S.map (Scheme.Modules.pullback g)).map (toSheaf Y) :=
    { τ₁ := φ.app S.X₁
      τ₂ := φ.app S.X₂
      τ₃ := φ.app S.X₃
      comm₁₂ := (φ.naturality S.f).symm
      comm₂₃ := (φ.naturality S.g).symm }
  rw [cohomologyPullback_apply, cohomologyPullback_apply, cohomologyδ_eq, cohomologyδ_eq]
  exact (congrArg (CategoryTheory.Sheaf.H.map (φ.app S.X₁) n₁)
    (g.base.cohomologyPullback_δ (shortExact_map_toSheaf hS) h x)).trans
    (CategoryTheory.Sheaf.H.δ_naturality n₀ n₁ h
      ((shortExact_map_toSheaf hS).map_of_exact _) (shortExact_map_toSheaf hS') ψ _).symm

/-- In degree zero, under the identification of `H⁰` with global sections, the pullback map on
cohomology is the pullback of global sections. -/
@[simp]
theorem cohomologyZeroEquiv_cohomologyPullback (M : X.Modules) (x : Cohomology M 0) :
    cohomologyZeroEquiv ((Scheme.Modules.pullback g).obj M) (g.cohomologyPullback M 0 x) =
      g.pullbackSections M ⊤ (cohomologyZeroEquiv M x) := by
  rw [cohomologyZeroEquiv_apply, cohomologyZeroEquiv_apply, cohomologyPullback_apply]
  refine (CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop
    ((toSheafPullbackComparison g).app M) _).symm.trans ?_
  refine (congrArg (((toSheafPullbackComparison g).app M).hom.app (op ⊤))
    (g.base.cohomologyPullback_zero ((toSheaf X).obj M) x)).trans ?_
  refine Eq.trans ?_ (g.pullbackSections_apply M ⊤ _).symm
  exact (congrArg (fun φ ↦ φ.hom.app (op ⊤) (CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop x))
    (toSheafPullbackComparison_unit g M)).symm

/-- The pullback map on cohomology is semilinear for the action of global functions along
`g^♯ : Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)`. -/
theorem cohomologyPullback_smul (M : X.Modules) (n : ℕ) (r : Γ(X, ⊤)) (x : Cohomology M n) :
    g.cohomologyPullback M n (r • x) = g.appTop r • g.cohomologyPullback M n x := by
  rw [← Scheme.Modules.cohomologyMap_globalSectionsSmul_apply,
    ← Scheme.Modules.cohomologyMap_globalSectionsSmul_apply,
    g.cohomologyPullback_cohomologyMap, Scheme.Modules.pullback_map_globalSectionsSmul]

section Opens

/-- Pullback `Hⁿ(U, M) ⟶ Hⁿ(g⁻¹ U, g^* M)` on the cohomology of an open subset. It is the
inverse image of extensions from the free abelian sheaf on `U`, followed by the comparison
from abelian inverse image to module pullback. -/
def cohomologyOnPullback (M : X.Modules) (n : ℕ) (U : X.Opens) :
    cohomologyOn M n U ⟶ cohomologyOn ((Scheme.Modules.pullback g).obj M) n (g ⁻¹ᵁ U) :=
  CategoryTheory.Sheaf.H'.pullback
      ((Opens.map g.base).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y))
      ((Opens.map g.base).freeYonedaSheafToSheafPullback _ _) ((toSheaf X).obj M) n (𝟙 _) ≫
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n).map
      ((toSheafPullbackComparison g).app M)).app (op (g ⁻¹ᵁ U))

/-- Pullback over an open is abelian inverse image followed by the map from inverse image
to the underlying sheaf of the module pullback. -/
lemma cohomologyOnPullback_apply (M : X.Modules) (n : ℕ) (U : X.Opens)
    (x : cohomologyOn M n U) :
    g.cohomologyOnPullback M n U x =
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n).map
        ((toSheafPullbackComparison g).app M)).app (op (g ⁻¹ᵁ U))
        (CategoryTheory.Sheaf.H'.pullback
          ((Opens.map g.base).sheafPullback AddCommGrpCat.{u}
            (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y))
          ((Opens.map g.base).freeYonedaSheafToSheafPullback _ _) ((toSheaf X).obj M) n (𝟙 _) x) :=
  (rfl)

/-- Pullback over the top open agrees with pullback of whole-scheme cohomology under
the terminal-open comparison. -/
lemma cohomologyOnTopIso_hom_cohomologyOnPullback (M : X.Modules) (n : ℕ)
    (x : cohomologyOn M n ⊤) :
    (cohomologyOnTopIso ((Scheme.Modules.pullback g).obj M) n).hom
        (g.cohomologyOnPullback M n ⊤ x) =
      g.cohomologyPullback M n ((cohomologyOnTopIso M n).hom x) := by
  let F := (toSheaf X).obj M
  let pb := (Opens.map g.base).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let c := (Opens.map g.base).freeYonedaSheafToSheafPullback
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let y : CategoryTheory.Sheaf.H'.{u} (pb.obj F) n ⊤ :=
    CategoryTheory.Sheaf.H'.pullback pb c F n (U := ⊤) (V := ⊤) (𝟙 _) x
  have h := ConcreteCategory.congr_hom
    ((CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH
      (Opens.grothendieckTopology Y) n isTerminalTop).hom.naturality
        ((toSheafPullbackComparison g).app M)) y
  rw [cohomologyOnPullback_apply, cohomologyPullback_apply]
  exact h.trans (congrArg (CategoryTheory.Sheaf.H.map ((toSheafPullbackComparison g).app M) n)
    (g.base.cohomologyPresheafObjIsoH_hom_pullback F n x))

/-- Pullback on the cohomology of opens is natural in the coefficient module. -/
@[reassoc]
lemma cohomologyOnMap_comp_cohomologyOnPullback {M N : X.Modules} (α : M ⟶ N)
    (n : ℕ) (U : X.Opens) :
    cohomologyOnMap α n U ≫ g.cohomologyOnPullback N n U =
      g.cohomologyOnPullback M n U ≫
        cohomologyOnMap ((Scheme.Modules.pullback g).map α) n (g ⁻¹ᵁ U) := by
  let pb := (Opens.map g.base).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let c := (Opens.map g.base).freeYonedaSheafToSheafPullback
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let HX := CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n
  let HY := CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) n
  -- The older cohomology maps use the raw forgetful functor. Use its packaged form throughout
  -- this naturality square so that the intermediate sheaf objects have the same expressions.
  change (HX.map ((toSheaf X).map α)).app (op U) ≫
      (CategoryTheory.Sheaf.H'.pullback pb c ((toSheaf X).obj N) n (𝟙 _) ≫
        (HY.map ((toSheafPullbackComparison g).app N)).app (op (g ⁻¹ᵁ U))) =
    (CategoryTheory.Sheaf.H'.pullback pb c ((toSheaf X).obj M) n (𝟙 _) ≫
      (HY.map ((toSheafPullbackComparison g).app M)).app (op (g ⁻¹ᵁ U))) ≫
        (HY.map ((toSheaf Y).map ((Scheme.Modules.pullback g).map α))).app (op (g ⁻¹ᵁ U))
  rw [CategoryTheory.Sheaf.H'.pullback_naturality_assoc]
  have hn := congrArg (fun φ ↦ (HY.map φ).app
    (op (g ⁻¹ᵁ U))) ((toSheafPullbackComparison g).naturality α)
  simpa only [Functor.comp_map, Functor.map_comp, NatTrans.comp_app, Category.assoc]
    using congrArg (fun φ ↦ CategoryTheory.Sheaf.H'.pullback pb c
      ((toSheaf X).obj M) n (𝟙 _) ≫ φ) hn

/-- Pullback on the cohomology of opens commutes with restriction. -/
@[reassoc]
lemma cohomologyOnRes_comp_cohomologyOnPullback (M : X.Modules) (n : ℕ) {U V : X.Opens}
    (h : U ≤ V) :
    cohomologyOnRes M n h ≫ g.cohomologyOnPullback M n U =
      g.cohomologyOnPullback M n V ≫
        cohomologyOnRes ((Scheme.Modules.pullback g).obj M) n (g.preimage_mono h) := by
  let pb := (Opens.map g.base).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let c := (Opens.map g.base).freeYonedaSheafToSheafPullback
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let β := (CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n).map
    ((toSheafPullbackComparison g).app M)
  -- As in coefficient naturality, express the cohomology maps through the packaged functor.
  change (((toSheaf X).obj M).cohomologyPresheaf n).map (homOfLE h).op ≫
      (CategoryTheory.Sheaf.H'.pullback pb c ((toSheaf X).obj M) n (𝟙 _) ≫ β.app _) =
    (CategoryTheory.Sheaf.H'.pullback pb c ((toSheaf X).obj M) n (𝟙 _) ≫ β.app _) ≫
      (((toSheaf Y).obj ((Scheme.Modules.pullback g).obj M)).cohomologyPresheaf n).map
        ((Opens.map g.base).map (homOfLE h)).op
  have hn := β.naturality ((Opens.map g.base).map (homOfLE h)).op
  dsimp only [Functor.comp_obj, CategoryTheory.Sheaf.cohomologyPresheaf] at hn ⊢
  rw [← Category.assoc, CategoryTheory.Sheaf.H'.map_comp_pullback,
    Category.assoc, ← hn, ← Category.assoc,
    CategoryTheory.Sheaf.H'.pullback_comp_map]
  simp

/-- Pullback on the cohomology of an open is semilinear over global functions. -/
lemma cohomologyOnPullback_smul (M : X.Modules) (n : ℕ) (U : X.Opens)
    (r : Γ(X, ⊤)) (x : cohomologyOn M n U) :
    g.cohomologyOnPullback M n U (r • x) =
      g.appTop r • g.cohomologyOnPullback M n U x := by
  rw [Scheme.Modules.cohomologyOn_smul_def, Scheme.Modules.cohomologyOn_smul_def,
    ← ConcreteCategory.comp_apply, cohomologyOnMap_comp_cohomologyOnPullback,
    ConcreteCategory.comp_apply, Scheme.Modules.pullback_map_globalSectionsSmul]

/-- Pullback on the cohomology of an open as a semilinear map over global functions. -/
def cohomologyOnPullbackSemilinear (M : X.Modules) (n : ℕ) (U : X.Opens) :
    cohomologyOn M n U →ₛₗ[g.appTop.hom]
      cohomologyOn ((Scheme.Modules.pullback g).obj M) n (g ⁻¹ᵁ U) where
  toFun := g.cohomologyOnPullback M n U
  map_add' := map_add _
  map_smul' := g.cohomologyOnPullback_smul M n U

@[simp]
lemma cohomologyOnPullbackSemilinear_apply (M : X.Modules) (n : ℕ) (U : X.Opens)
    (x : cohomologyOn M n U) :
    g.cohomologyOnPullbackSemilinear M n U x = g.cohomologyOnPullback M n U x :=
  (rfl)

/-- In degree zero pullback on the cohomology of an open is pullback of sections. -/
@[simp]
lemma cohomologyOnZeroEquiv_cohomologyOnPullback (M : X.Modules) (U : X.Opens)
    (x : cohomologyOn M 0 U) :
    Scheme.Modules.cohomologyOnZeroEquiv ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (g.cohomologyOnPullback M 0 U x) =
      g.pullbackSections M U (Scheme.Modules.cohomologyOnZeroEquiv M U x) := by
  rw [cohomologyOnZeroEquiv_apply ((Scheme.Modules.pullback g).obj M),
    cohomologyOnZeroEquiv_apply M, cohomologyOnPullback_apply]
  let pb := (Opens.map g.base).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let c := (Opens.map g.base).freeYonedaSheafToSheafPullback
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  -- The site formulas use the packaged underlying sheaf, whereas `cohomologyOnZeroEquiv`
  -- uses the raw forgetful functor. Align both the class and the section equivalences.
  change ((toSheaf X).obj M).H' 0 U at x
  change TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv
      ((toSheaf Y).obj ((Scheme.Modules.pullback g).obj M)) (g ⁻¹ᵁ U)
      (((CategoryTheory.Sheaf.cohomologyPresheafFunctor _ 0).map
        ((toSheafPullbackComparison g).app M)).app _
        (CategoryTheory.Sheaf.H'.pullback pb c ((toSheaf X).obj M) 0 (𝟙 _) x)) =
    g.pullbackSections M U
      (TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv ((toSheaf X).obj M) U x)
  refine (TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv_naturality_right
    ((toSheafPullbackComparison g).app M) (g ⁻¹ᵁ U) _).trans ?_
  have hx := CategoryTheory.Sheaf.H'.cohomologyZeroSectionsEquiv_pullback_sheafPullback
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map g.base) ((toSheaf X).obj M) (𝟙 ((Opens.map g.base).obj U)) x
  simp only [op_id] at hx
  -- The identity restriction is over `g⁻¹ U`, also written `(Opens.map g.base).obj U`.
  erw [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at hx
  refine (congrArg (((toSheafPullbackComparison g).app M).hom.app (op (g ⁻¹ᵁ U))) hx).trans ?_
  exact (congrArg (fun φ ↦ φ.hom.app (op U)
    (TauCeti.CategoryTheory.cohomologyZeroSectionsEquiv ((toSheaf X).obj M) U x))
    (g.toSheafPullbackComparison_unit M)).symm.trans (g.pullbackSections_apply M U _).symm

/-- Pullback commutes with the connecting maps of the Mayer–Vietoris sequences for two opens
and their inverse images. No flatness or quasi-coherence hypothesis is required. -/
lemma cohomologyOnPullback_mayerVietorisδ (M : X.Modules) (U V : X.Opens)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : cohomologyOn M n₀ (U ⊓ V)) :
    g.cohomologyOnPullback M n₁ (U ⊔ V) (mayerVietorisδ M U V n₀ n₁ h x) =
      mayerVietorisδ ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) (g ⁻¹ᵁ V)
        n₀ n₁ h (g.cohomologyOnPullback M n₀ (U ⊓ V) x) := by
  let ψ : (Opens.mayerVietorisSquare (g ⁻¹ᵁ U) (g ⁻¹ᵁ V)).toSquare ⟶
      (Opens.mayerVietorisSquare U V).toSquare.map (Opens.map g.base) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      τ₄ := 𝟙 _ }
  have hδ := CategoryTheory.Sheaf.H'.δ_comp_pullback
    ((Opens.map g.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y))
    ((Opens.map g.base).freeYonedaSheafToSheafPullback _ _)
    (Opens.mayerVietorisSquare U V) (Opens.mayerVietorisSquare (g ⁻¹ᵁ U) (g ⁻¹ᵁ V))
    ψ ((toSheaf X).obj M) n₀ n₁ h
  rw [cohomologyOnPullback_apply, cohomologyOnPullback_apply]
  exact (congrArg (((CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n₁).map
    ((toSheafPullbackComparison g).app M)).app _) (ConcreteCategory.congr_hom hδ x)).trans
      (ConcreteCategory.congr_hom
        ((Opens.mayerVietorisSquare (g ⁻¹ᵁ U) (g ⁻¹ᵁ V)).δ_naturality_right _
          ((toSheafPullbackComparison g).app M) n₀ n₁ h) _)

end Opens

end AlgebraicGeometry.Scheme.Hom
