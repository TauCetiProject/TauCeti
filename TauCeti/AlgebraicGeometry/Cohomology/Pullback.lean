/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.Topology.Sheaves.Cohomology.Pullback
import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-!
# Pullback on the cohomology of sheaves of modules

Let `g : Y ⟶ X` be a morphism of schemes and `M` a sheaf of modules on `X`. This file constructs
the pullback map

`g.cohomologyPullback M n : Hⁿ(X, M) →+ Hⁿ(Y, g^* M)`.

It is the inverse image map on the cohomology of the underlying abelian sheaves
(`TauCeti.Topology.cohomologyPullback`), followed by the map induced on cohomology by the
comparison `g⁻¹ M ⟶ g^* M` between the inverse image of the underlying abelian sheaf of `M` and
the underlying abelian sheaf of the module pullback. That comparison is the mate of the equality
`g_* N = g_* N` of underlying abelian sheaves of a pushforward.

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

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.8.1 and Proposition III.9.3.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The comparison `g⁻¹ M ⟶ g^* M` from the inverse image of the underlying abelian sheaf of `M`
to the underlying abelian sheaf of its pullback as a sheaf of modules: the mate of the equality of
the underlying abelian sheaves of `g_* N` computed in both ways. -/
private def toSheafPullbackComparison :
    toSheaf X ⋙ (Opens.map g.base).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) ⟶
      Scheme.Modules.pullback g ⋙ toSheaf Y :=
  (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g)
    ((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _)).symm (𝟙 _)

/-- On sections, the unit of the module pullback is the abelian unit followed by the comparison
`g⁻¹ M ⟶ g^* M`. -/
private lemma toSheafPullbackComparison_unit (M : X.Modules) :
    (toSheaf X).map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) =
      ((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).unit.app
          ((toSheaf X).obj M) ≫
        ((Opens.map g.base).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map
          ((toSheafPullbackComparison g).app M) :=
  (Category.comp_id _).symm.trans (unit_mateEquiv_symm (G := toSheaf X) (H := toSheaf Y)
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    ((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)) (𝟙 _) M)

/-- The pullback map `Hⁿ(X, M) →+ Hⁿ(Y, g^* M)` on the cohomology of a sheaf of modules along a
morphism of schemes `g : Y ⟶ X`. -/
def cohomologyPullback (M : X.Modules) (n : ℕ) :
    Cohomology M n →+ Cohomology ((Scheme.Modules.pullback g).obj M) n :=
  (CategoryTheory.Sheaf.H.map ((toSheafPullbackComparison g).app M) n).comp
    (TauCeti.Topology.cohomologyPullback g.base ((toSheaf X).obj M) n)

private lemma cohomologyPullback_apply (M : X.Modules) (n : ℕ) (x : Cohomology M n) :
    g.cohomologyPullback M n x = CategoryTheory.Sheaf.H.map ((toSheafPullbackComparison g).app M) n
      (TauCeti.Topology.cohomologyPullback g.base ((toSheaf X).obj M) n x) :=
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
          (TauCeti.Topology.cohomologyPullback g.base ((toSheaf X).obj M) n x)) :=
        congrArg _ (TauCeti.Topology.cohomologyPullback_map g.base ((toSheaf X).map α) x)
    _ = _ := (CategoryTheory.Sheaf.H.map_comp_apply _ _ _).symm.trans
      ((congrArg (fun φ ↦ CategoryTheory.Sheaf.H.map φ n
        (TauCeti.Topology.cohomologyPullback g.base ((toSheaf X).obj M) n x))
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
    (TauCeti.Topology.cohomologyPullback_δ g.base (shortExact_map_toSheaf hS) h x)).trans
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
    (TauCeti.Topology.cohomologyPullback_zero g.base ((toSheaf X).obj M) x)).trans ?_
  refine Eq.trans ?_ (g.pullbackSections_apply M ⊤ _).symm
  exact (congrArg (fun φ ↦ φ.hom.app (op ⊤) (CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop x))
    (toSheafPullbackComparison_unit g M)).symm

/-- The pullback map on cohomology is semilinear for the action of global functions along
`g^♯ : Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)`. -/
theorem cohomologyPullback_smul (M : X.Modules) (n : ℕ) (r : Γ(X, ⊤)) (x : Cohomology M n) :
    g.cohomologyPullback M n (r • x) = g.appTop r • g.cohomologyPullback M n x := by
  rw [Scheme.Modules.cohomology_smul, Scheme.Modules.cohomology_smul, cohomologyFunctor_map,
    cohomologyFunctor_map]
  exact (g.cohomologyPullback_cohomologyMap _ n x).trans (by
    rw [Scheme.Modules.pullback_map_globalSectionsSmul]; rfl)

end AlgebraicGeometry.Scheme.Hom
