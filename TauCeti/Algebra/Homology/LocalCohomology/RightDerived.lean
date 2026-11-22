/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Tactic.CrossRefAttribute
public import TauCeti.Algebra.Category.ModuleCat.PrimaryComponent
public import TauCeti.Algebra.Homology.LocalCohomology.DegreeZero
public import TauCeti.CategoryTheory.Abelian.GrothendieckAxioms.RightDerived
public import TauCeti.CategoryTheory.Abelian.Projective.Ext

/-!
# Local cohomology as the right derived functor of ideal-power torsion

Let `R` be a commutative ring and `J` an ideal of `R`. Mathlib defines the local cohomology
functor `localCohomology J q : ModuleCat.{u} R ⥤ ModuleCat.{u} R` as the colimit over `n : ℕ` of
`Ext^q_R(R ⧸ J^n, -)`. On the other hand, the `J`-power torsion submodule
`J.primaryComponent M = ⨆ n, Submodule.torsionBySet R M (J^n)` defines a left exact additive
endofunctor `J.primaryComponentFunctor` (`Γ_J`) of `ModuleCat.{u} R`
(`TauCeti.Algebra.Category.ModuleCat.PrimaryComponent`).

This file establishes the natural isomorphism `localCohomology.isoRightDerivedPrimaryComponent J q`
between `localCohomology J q` and `J.primaryComponentFunctor.rightDerived q` for an arbitrary
commutative ring `R`, ideal `J`, and degree `q : ℕ` (Stacks Project, Tag 0954):

1. Balancing left and right derived `Hom` (`CategoryTheory.extObjIsoRightDerivedLinearCoyoneda`)
   identifies `Ext^q_R(R ⧸ J^n, -)` with the `q`-th right derived functor of `Hom_R(R ⧸ J^n, -)`
   naturally in `n`.
2. Since `ModuleCat.{u} R` satisfies Grothendieck's axiom `AB5`, filtered colimits indexed by
   `ℕᵒᵖᵒᵖ` are exact and therefore commute with right derived functors
   (`CategoryTheory.Limits.colimitRightDerivedIso`).
3. In degree `0`, `TauCeti.Algebra.Homology.LocalCohomology.DegreeZero` identifies the filtered
   colimit of `Hom_R(R ⧸ J^n, -)` with `J.primaryComponentFunctor`
   (`localCohomology.colimitLinearCoyonedaIsoPrimaryComponentFunctor`).

As an application, `localCohomology J q` is an additive functor (`localCohomology.additive`), so
`H^q_J(0) = 0` via `Functor.map_isZero`.

## Main definitions

* `localCohomology.isoRightDerivedPrimaryComponent J q`: the natural isomorphism
  `localCohomology J q ≅ J.primaryComponentFunctor.rightDerived q` (Stacks 0954).
* `localCohomology.linearEquivRightDerivedPrimaryComponent J M q`: the `R`-linear equivalence
  `(localCohomology J q).obj M ≃ₗ[R] (J.primaryComponentFunctor.rightDerived q).obj M`.

## Main results

* `localCohomology.additive`: `localCohomology J q` is additive in every degree `q`.

## References

* [The Stacks Project, Tag 0954](https://stacks.math.columbia.edu/tag/0954)
* A. Grothendieck, *Local Cohomology* (notes by R. Hartshorne), Lecture Notes in Mathematics 41,
  Springer, 1967, Proposition 2.8.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace localCohomology

variable {R : Type u} [CommRing R]

section Comparison

variable (J : Ideal R)

section DiagramComparison

universe v₁ u₁

variable {D : Type u₁} [Category.{v₁} D] (I : D ⥤ Ideal R)
  [∀ t, (((ringModIdeals I).op ⋙ linearCoyoneda R (ModuleCat.{u} R)).obj t).Additive]

/-- For any diagram `I : D ⥤ Ideal R`, balancing `Ext^q` identifies `diagram I q` with the
diagram of `q`-th right derived functors of `Hom_R(R ⧸ I(t), -)`. -/
def diagramIsoRightDerivedLinearCoyoneda (q : ℕ) :
    diagram I q ≅
      rightDerivedDiagram ((ringModIdeals I).op ⋙ linearCoyoneda R (ModuleCat.{u} R)) q :=
  NatIso.ofComponents (fun _ ↦ extObjIsoRightDerivedLinearCoyoneda R _ q) fun w ↦
    extObjIsoRightDerivedLinearCoyoneda_hom_naturality_left R ((ringModIdeals I).map w.unop) q

/-- When `ModuleCat.{u} R` has exact colimits of shape `Dᵒᵖ`, `localCohomology.ofDiagram I q` is
naturally isomorphic to the `q`-th right derived functor of `colimit_t Hom_R(R ⧸ I(t), -)`. -/
def ofDiagramIsoRightDerivedColimitLinearCoyoneda (q : ℕ)
    [HasColimitsOfShape Dᵒᵖ (ModuleCat.{u} R)]
    [HasExactColimitsOfShape Dᵒᵖ (ModuleCat.{u} R)] :
    ofDiagram I q ≅
      (colimit ((ringModIdeals I).op ⋙ linearCoyoneda R (ModuleCat.{u} R))).rightDerived q :=
  HasColimit.isoOfNatIso (diagramIsoRightDerivedLinearCoyoneda I q) ≪≫
    colimitRightDerivedIso ((ringModIdeals I).op ⋙ linearCoyoneda R (ModuleCat.{u} R)) q

end DiagramComparison

/-- **Local cohomology as right derived `J`-power torsion.** For any commutative ring `R`, ideal
`J` of `R`, and degree `q : ℕ`, the `q`-th local cohomology functor `localCohomology J q` is
naturally isomorphic to the `q`-th right derived functor of `J.primaryComponentFunctor` (`Γ_J`). -/
@[stacks 0954]
def isoRightDerivedPrimaryComponent (q : ℕ) :
    localCohomology J q ≅ J.primaryComponentFunctor.{u}.rightDerived q := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} (ModuleCat.{u} R)
  have := Functor.comp_obj_additive (ringModIdeals (idealPowersDiagram J)).op
    (linearCoyoneda R (ModuleCat.{u} R))
  exact ofDiagramIsoRightDerivedColimitLinearCoyoneda (idealPowersDiagram J) q ≪≫
    NatIso.rightDerived (colimitLinearCoyonedaIsoPrimaryComponentFunctor J) q

/-- For any `R`-module `M`, the `q`-th local cohomology module `H^q_J(M)` is `R`-linearly
equivalent to `(R^q Γ_J)(M)`. -/
@[stacks 0954]
def linearEquivRightDerivedPrimaryComponent (M : ModuleCat.{u} R) (q : ℕ) :
    (localCohomology J q).obj M ≃ₗ[R] (J.primaryComponentFunctor.{u}.rightDerived q).obj M :=
  ((isoRightDerivedPrimaryComponent J q).app M).toLinearEquiv

/-- `linearEquivRightDerivedPrimaryComponent` commutes with induced maps of `R`-modules. -/
lemma linearEquivRightDerivedPrimaryComponent_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (q : ℕ) (x : (localCohomology J q).obj M) :
    (J.primaryComponentFunctor.{u}.rightDerived q).map f
        (linearEquivRightDerivedPrimaryComponent J M q x) =
      linearEquivRightDerivedPrimaryComponent J N q ((localCohomology J q).map f x) :=
  (ConcreteCategory.congr_hom ((isoRightDerivedPrimaryComponent J q).hom.naturality f) x).symm

/-- Local cohomology functors are additive in every degree. -/
instance additive (q : ℕ) : (localCohomology J q).Additive :=
  Functor.additive_of_iso (isoRightDerivedPrimaryComponent J q).symm

end Comparison

end localCohomology
