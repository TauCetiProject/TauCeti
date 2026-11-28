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
public import TauCeti.Algebra.Homology.Ext.Balance
public import TauCeti.Algebra.Homology.LocalCohomology.DegreeZero
public import TauCeti.CategoryTheory.Abelian.GrothendieckAxioms.RightDerived

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

/-- On each object `t`, `diagramIsoRightDerivedLinearCoyoneda` is
`extObjIsoRightDerivedLinearCoyoneda`. -/
@[simp]
lemma diagramIsoRightDerivedLinearCoyoneda_hom_app (q : ℕ) (t : Dᵒᵖ) :
    (diagramIsoRightDerivedLinearCoyoneda I q).hom.app t =
      (extObjIsoRightDerivedLinearCoyoneda R ((ringModIdeals I).obj t.unop) q).hom :=
  (rfl)

/-- When `ModuleCat.{u} R` has exact colimits of shape `Dᵒᵖ`, `localCohomology.ofDiagram I q` is
naturally isomorphic to the `q`-th right derived functor of `colimit_t Hom_R(R ⧸ I(t), -)`. -/
def ofDiagramIsoRightDerivedColimitLinearCoyoneda (q : ℕ)
    [HasColimitsOfShape Dᵒᵖ (ModuleCat.{u} R)]
    [HasExactColimitsOfShape Dᵒᵖ (ModuleCat.{u} R)] :
    ofDiagram I q ≅
      (colimit ((ringModIdeals I).op ⋙ linearCoyoneda R (ModuleCat.{u} R))).rightDerived q :=
  HasColimit.isoOfNatIso (diagramIsoRightDerivedLinearCoyoneda I q) ≪≫
    colimitRightDerivedIso ((ringModIdeals I).op ⋙ linearCoyoneda R (ModuleCat.{u} R)) q

/-- `ofDiagramIsoRightDerivedColimitLinearCoyoneda` is the composite of `HasColimit.isoOfNatIso`
and `colimitRightDerivedIso`. -/
@[simp]
lemma ofDiagramIsoRightDerivedColimitLinearCoyoneda_hom (q : ℕ)
    [HasColimitsOfShape Dᵒᵖ (ModuleCat.{u} R)]
    [HasExactColimitsOfShape Dᵒᵖ (ModuleCat.{u} R)] :
    (ofDiagramIsoRightDerivedColimitLinearCoyoneda I q).hom =
      (HasColimit.isoOfNatIso (diagramIsoRightDerivedLinearCoyoneda I q)).hom ≫
        (colimitRightDerivedIso
          ((ringModIdeals I).op ⋙ linearCoyoneda R (ModuleCat.{u} R)) q).hom :=
  (rfl)

end DiagramComparison

/-- **Local cohomology as right derived `J`-power torsion.** For any commutative ring `R`, ideal
`J` of `R`, and degree `q : ℕ`, the `q`-th local cohomology functor `localCohomology J q` is
naturally isomorphic to the `q`-th right derived functor of `J.primaryComponentFunctor` (`Γ_J`). -/
@[stacks 0954]
def isoRightDerivedPrimaryComponent (q : ℕ) :
    localCohomology J q ≅ J.primaryComponentFunctor.{u}.rightDerived q :=
  letI : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} (ModuleCat.{u} R)
  letI := Functor.additive_comp_obj (ringModIdeals (idealPowersDiagram J)).op
    (linearCoyoneda R (ModuleCat.{u} R))
  ofDiagramIsoRightDerivedColimitLinearCoyoneda (idealPowersDiagram J) q ≪≫
    NatIso.rightDerived (colimitLinearCoyonedaIsoPrimaryComponentFunctor J) q

/-- `isoRightDerivedPrimaryComponent` is the composite of
`ofDiagramIsoRightDerivedColimitLinearCoyoneda` and `NatIso.rightDerived` of
`colimitLinearCoyonedaIsoPrimaryComponentFunctor`. -/
lemma isoRightDerivedPrimaryComponent_hom (q : ℕ) :
    letI : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} (ModuleCat.{u} R)
    letI := Functor.additive_comp_obj (ringModIdeals (idealPowersDiagram J)).op
      (linearCoyoneda R (ModuleCat.{u} R))
    (isoRightDerivedPrimaryComponent J q).hom =
      (ofDiagramIsoRightDerivedColimitLinearCoyoneda (idealPowersDiagram J) q).hom ≫
        (NatIso.rightDerived (colimitLinearCoyonedaIsoPrimaryComponentFunctor J) q).hom :=
  (rfl)

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

/-- In degree zero, `isoRightDerivedPrimaryComponent` identifies the degree-zero isomorphism
`localCohomology J 0 ≅ Γ_J` with the canonical comparison `Γ_J ⟶ R⁰Γ_J`. -/
@[reassoc]
lemma degreeZeroIsoPrimaryComponentFunctor_hom_comp_toRightDerivedZero :
    (degreeZeroIsoPrimaryComponentFunctor J).hom ≫
        J.primaryComponentFunctor.{u}.toRightDerivedZero =
      (isoRightDerivedPrimaryComponent J 0).hom := by
  let : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} (ModuleCat.{u} R)
  let := Functor.additive_comp_obj (ringModIdeals (idealPowersDiagram J)).op
    (linearCoyoneda R (ModuleCat.{u} R))
  let G := (ringModIdeals (idealPowersDiagram J)).op ⋙ linearCoyoneda R (ModuleCat.{u} R)
  let α : colimit (diagram (idealPowersDiagram J) 0) ⟶ J.primaryComponentFunctor :=
    (degreeZeroIsoPrimaryComponentFunctor J).hom
  change α ≫ J.primaryComponentFunctor.{u}.toRightDerivedZero =
    (HasColimit.isoOfNatIso (diagramIsoRightDerivedLinearCoyoneda (idealPowersDiagram J) 0)).hom ≫
      (colimitRightDerivedIso G 0).hom ≫
      (NatIso.rightDerived (colimitLinearCoyonedaIsoPrimaryComponentFunctor J) 0).hom
  refine (colimit.hom_ext fun t ↦ ?_).symm
  rw [HasColimit.ι_isoOfNatIso_hom_assoc,
    colimitRightDerivedIso_hom, ι_colimitRightDerivedComparison_assoc, NatIso.rightDerived_hom,
    ← NatTrans.rightDerived_comp]
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, diagramIsoRightDerivedLinearCoyoneda_hom_app]
  have h0 : (extObjIsoRightDerivedLinearCoyoneda R
        ((ringModIdeals (idealPowersDiagram J)).obj t.unop) 0).hom.app M =
      (extZeroIso ((ringModIdeals (idealPowersDiagram J)).obj t.unop) M).hom ≫
        (G.obj t).toRightDerivedZero.app M := by
    erw [← extZeroIso_inv_comp_extObjIsoRightDerivedLinearCoyoneda_hom_app, Iso.hom_inv_id_assoc]
  erw [h0, Category.assoc]
  have hnat := NatTrans.congr_app (NatTrans.toRightDerivedZero_comp_rightDerived_zero
    (colimit.ι G t ≫ (colimitLinearCoyonedaIsoPrimaryComponentFunctor J).hom)) M
  simp only [NatTrans.comp_app] at hnat
  erw [hnat]
  have hcomp : (extZeroIso ((ringModIdeals (idealPowersDiagram J)).obj t.unop) M).hom ≫
      (colimit.ι G t).app M ≫ (colimitLinearCoyonedaIsoPrimaryComponentFunctor J).hom.app M =
      (colimit.ι (diagram (idealPowersDiagram J) 0) t).app M ≫ α.app M := by
    erw [ι_app_colimitLinearCoyonedaIsoPrimaryComponentFunctor_hom, Iso.hom_inv_id_assoc]
  erw [← Category.assoc, hcomp, Category.assoc]

/-- In degree zero, `isoRightDerivedPrimaryComponent` is compatible with
`Functor.rightDerivedZeroIsoSelf` and `degreeZeroIsoPrimaryComponentFunctor`. -/
@[reassoc]
lemma isoRightDerivedPrimaryComponent_hom_comp_rightDerivedZeroIsoSelf :
    (isoRightDerivedPrimaryComponent J 0).hom ≫
        J.primaryComponentFunctor.{u}.rightDerivedZeroIsoSelf.hom =
      (degreeZeroIsoPrimaryComponentFunctor J).hom := by
  rw [← degreeZeroIsoPrimaryComponentFunctor_hom_comp_toRightDerivedZero, Category.assoc,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id, Category.comp_id]

/-- Objectwise in degree zero, `isoRightDerivedPrimaryComponent` followed by
`Functor.rightDerivedZeroIsoSelf` agrees with `degreeZeroIsoPrimaryComponentFunctor`. -/
@[reassoc]
lemma isoRightDerivedPrimaryComponent_hom_app_comp_rightDerivedZeroIsoSelf_hom_app
    (M : ModuleCat.{u} R) :
    (isoRightDerivedPrimaryComponent J 0).hom.app M ≫
        J.primaryComponentFunctor.{u}.rightDerivedZeroIsoSelf.hom.app M =
      (degreeZeroIsoPrimaryComponentFunctor J).hom.app M :=
  NatTrans.congr_app (isoRightDerivedPrimaryComponent_hom_comp_rightDerivedZeroIsoSelf J) M

end Comparison

end localCohomology
