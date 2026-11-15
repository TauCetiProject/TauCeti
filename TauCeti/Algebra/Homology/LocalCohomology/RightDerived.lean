/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.CrossRefAttribute
public import TauCeti.Algebra.Category.ModuleCat.PrimaryComponent
public import TauCeti.Algebra.Homology.LocalCohomology.DegreeZero
public import TauCeti.CategoryTheory.Abelian.GrothendieckAxioms.RightDerived
public import TauCeti.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
import TauCeti.Algebra.Module.Torsion.PrimaryComponent

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

As applications, `localCohomology J q` is an additive functor (so `H^q_J(0) = 0`), and for a
discrete valuation ring `(R, 𝔪)` with fraction field `K`, the two-term injective resolution
`0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0` yields `H^0_𝔪(R) = 0`, `H^1_𝔪(R) ≅ K ⧸ R`, and
`H^{n+2}_𝔪(R) = 0`.

## Main definitions

* `localCohomology.degreeZeroEquivPrimaryComponent J M`: the `R`-linear equivalence
  `H^0_J(M) ≃ₗ[R] J.primaryComponent M`.
* `localCohomology.degreeZeroIsoPrimaryComponentFunctor J`: the natural isomorphism
  `localCohomology J 0 ≅ J.primaryComponentFunctor`.
* `localCohomology.isoRightDerivedPrimaryComponent J q`: the natural isomorphism
  `localCohomology J q ≅ J.primaryComponentFunctor.rightDerived q` (Stacks 0954).
* `localCohomology.dvrDegreeOneIso`: for a discrete valuation ring `(R, 𝔪)` with fraction field
  `K`, the isomorphism `(localCohomology 𝔪 1).obj (.of R R) ≅ .of R (K ⧸ R)`.

## Main results

* `localCohomology.isZero_obj_zero`: `H^q_J(0) = 0` in every degree `q`.
* `localCohomology.isZero_dvr_zero` and `localCohomology.isZero_dvr_add_two`: for a discrete
  valuation ring `(R, 𝔪)`, `H^0_𝔪(R) = 0` and `H^{n+2}_𝔪(R) = 0`.

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

/-- In degree zero, `degreeZeroToModule` restricts on its image to an `R`-linear equivalence
`H⁰_J(M) ≃ₗ[R] Γ_J(M)`. -/
def degreeZeroEquivPrimaryComponent (M : ModuleCat.{u} R) :
    (localCohomology J 0).obj M ≃ₗ[R] J.primaryComponent M :=
  (LinearEquiv.ofInjective (degreeZeroToModule J M).hom (degreeZeroToModule_injective J M)).trans
    (LinearEquiv.ofEq _ _ (range_hom_degreeZeroToModule J M))

@[simp]
lemma coe_degreeZeroEquivPrimaryComponent_apply (M : ModuleCat.{u} R)
    (x : (localCohomology J 0).obj M) :
    (degreeZeroEquivPrimaryComponent J M x : M) = degreeZeroToModule J M x :=
  (rfl)

/-- The natural isomorphism `localCohomology J 0 ≅ J.primaryComponentFunctor` in degree zero. -/
def degreeZeroIsoPrimaryComponentFunctor :
    localCohomology J 0 ≅ J.primaryComponentFunctor :=
  NatIso.ofComponents
    (fun M ↦ (degreeZeroEquivPrimaryComponent J M).toModuleIso ≪≫
      (J.primaryComponentFunctorObjIso M).symm)
    fun {M N} f ↦ by
      rw [← cancel_mono (J.primaryComponentFunctorι.app N)]
      simp only [Category.assoc, Iso.trans_hom, Iso.symm_hom,
        Ideal.primaryComponentFunctorObjIso_inv_comp_ι_app,
        J.primaryComponentFunctorι.naturality, Functor.id_map,
        Ideal.primaryComponentFunctorObjIso_inv_comp_ι_app_assoc]
      ext x
      exact ConcreteCategory.congr_hom (degreeZeroToModule_naturality J f) x

/-- Composing `degreeZeroIsoPrimaryComponentFunctor` with the submodule inclusion `Γ_J ↪ 𝟭`
recovers `degreeZeroToModule`. -/
@[reassoc (attr := simp)]
lemma degreeZeroIsoPrimaryComponentFunctor_hom_comp_ι :
    (degreeZeroIsoPrimaryComponentFunctor J).hom ≫ J.primaryComponentFunctorι =
      { app M := degreeZeroToModule J M
        naturality _ _ f := degreeZeroToModule_naturality J f } := by
  ext M x
  simp [degreeZeroIsoPrimaryComponentFunctor]

/-- In degree zero, the diagram `t ↦ Ext⁰_R(R ⧸ J^t, -)` is naturally isomorphic to
`t ↦ Hom_R(R ⧸ J^t, -)` via `CategoryTheory.extZeroIso`. -/
private def diagramZeroIsoLinearCoyoneda :
    diagram (idealPowersDiagram J) 0 ≅
      (ringModIdeals (idealPowersDiagram J)).op ⋙ linearCoyoneda R (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun M ↦ extZeroIso _ M)
      fun g ↦ extZeroIso_hom_naturality_right _ g)
    fun w ↦ by
      ext M x
      exact ConcreteCategory.congr_hom (extZeroIso_hom_naturality_left
        ((ringModIdeals (idealPowersDiagram J)).map w.unop) M) x

/-- The filtered colimit of `Hom_R(R ⧸ J^n, -)` is naturally isomorphic to the `J`-power torsion
functor `Γ_J`. -/
def colimitLinearCoyonedaIsoPrimaryComponentFunctor :
    colimit ((ringModIdeals (idealPowersDiagram J)).op ⋙ linearCoyoneda R (ModuleCat.{u} R)) ≅
      J.primaryComponentFunctor :=
  (HasColimit.isoOfNatIso (diagramZeroIsoLinearCoyoneda J)).symm ≪≫
    degreeZeroIsoPrimaryComponentFunctor J

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

/-- Local cohomology vanishes on a zero module in every degree. -/
theorem isZero_obj_zero {M : ModuleCat.{u} R} (hM : IsZero M) (q : ℕ) :
    IsZero ((localCohomology J q).obj M) :=
  (localCohomology J q).map_isZero hM

end Comparison

section DiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Over a discrete valuation ring `(R, 𝔪)`, `R` itself has no nonzero `𝔪`-power torsion. -/
lemma primaryComponent_maximalIdeal_self :
    (IsLocalRing.maximalIdeal R).primaryComponent R = ⊥ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.primaryComponent_span_singleton_eq_bot_iff]
  exact fun _ _ hxy ↦ mul_left_cancel₀ hϖ.ne_zero hxy

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`, `K` has no nonzero `𝔪`-power
torsion because any uniformizer acts invertibly on `K`. -/
lemma primaryComponent_maximalIdeal_fractionRing :
    (IsLocalRing.maximalIdeal R).primaryComponent K = ⊥ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.primaryComponent_span_singleton_eq_bot_iff]
  intro x y hxy
  have hϖK : algebraMap R K ϖ ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne hϖ.ne_zero
  simpa only [Algebra.smul_def, mul_eq_mul_left_iff, hϖK, or_false] using hxy

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`, the quotient `K ⧸ R` is
entirely `𝔪`-power torsion: every fraction has denominator a unit times a power of a
uniformizer. -/
lemma primaryComponent_maximalIdeal_quotient_fractionRing :
    (IsLocalRing.maximalIdeal R).primaryComponent
      (K ⧸ LinearMap.range (Algebra.linearMap R K)) = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Submodule.eq_top_iff']
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨⟨a, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (mem_nonZeroDivisors_iff_ne_zero.mp hs) hϖ
  rw [Ideal.mem_primaryComponent_span_singleton_iff]
  refine ⟨k, ?_⟩
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨↑u⁻¹ * a, ?_⟩
  have hspec := IsLocalization.mk'_spec' K a ⟨↑u * ϖ ^ k, hs⟩
  -- Multiply by `u⁻¹` in `R`: `(u * ϖ^k) • mk' K a _ = algebraMap R K a`.
  calc Algebra.linearMap R K (↑u⁻¹ * a)
    _ = (↑u⁻¹ : R) • algebraMap R K a := by
      rw [Algebra.linearMap_apply, map_mul, ← Algebra.smul_def]
    _ = (↑u⁻¹ : R) • ((↑u * ϖ ^ k) • IsLocalization.mk' K a ⟨↑u * ϖ ^ k, hs⟩) := by
      rw [← hspec, ← Algebra.smul_def]
    _ = ϖ ^ k • IsLocalization.mk' K a ⟨↑u * ϖ ^ k, hs⟩ := by
      rw [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul]

/-- The short exact sequence `0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0` in `ModuleCat.{u} R`. -/
private def dvrShortComplex : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (Algebra.linearMap R K))
    (ModuleCat.ofHom (LinearMap.range (Algebra.linearMap R K)).mkQ)
    (ModuleCat.hom_ext (LinearMap.ext fun r ↦ (Submodule.Quotient.mk_eq_zero _).mpr ⟨r, rfl⟩))

omit [IsDomain R] [IsDiscreteValuationRing R] in
private lemma dvrShortComplex_shortExact : (dvrShortComplex R K).ShortExact :=
  ModuleCat.shortComplex_shortExact (dvrShortComplex R K)
    (fun _ ↦ (Submodule.Quotient.mk_eq_zero _).trans LinearMap.mem_range)
    (FaithfulSMul.algebraMap_injective R K)
    (Submodule.mkQ_surjective _)

private instance injective_fractionRing_obj : Injective (ModuleCat.of R K) := by
  have : Module.Injective R K :=
    Module.Injective.of_ringEquiv (RingEquiv.refl R)
      (Submodule.quotEquivOfEqBot (⊥ : Submodule R K) rfl)
  exact Module.injective_object_of_injective_module R K

private instance injective_quotient_fractionRing_obj :
    Injective (ModuleCat.of R (K ⧸ LinearMap.range (Algebra.linearMap R K))) :=
  Module.injective_object_of_injective_module R _

/-- Over a discrete valuation ring `(R, 𝔪)`, `H⁰_𝔪(R) = 0`. -/
theorem isZero_dvr_zero :
    IsZero ((localCohomology (IsLocalRing.maximalIdeal R) 0).obj (.of R R)) := by
  have : Subsingleton ((IsLocalRing.maximalIdeal R).primaryComponent R) :=
    primaryComponent_maximalIdeal_self R ▸ inferInstance
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (degreeZeroEquivPrimaryComponent (IsLocalRing.maximalIdeal R) (.of R R)).toModuleIso

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`, `H¹_𝔪(R) ≅ K ⧸ R`,
computed from the two-term injective resolution `0 ⟶ R ⟶ K ⟶ K ⧸ R ⟶ 0`. -/
def dvrDegreeOneIso :
    ((localCohomology (IsLocalRing.maximalIdeal R) 1).obj (.of R R)) ≅
      .of R (K ⧸ LinearMap.range (Algebra.linearMap R K)) := by
  let 𝔪 := IsLocalRing.maximalIdeal R
  let S := dvrShortComplex R K
  have hS : S.ShortExact := dvrShortComplex_shortExact R K
  have : Injective S.X₂ := injective_fractionRing_obj R K
  have : Injective S.X₃ := injective_quotient_fractionRing_obj R K
  let I : InjectiveResolution S.X₁ := (InjectiveResolution.self S.X₃).ofShortExact hS
  let C := (𝔪.primaryComponentFunctor.{u}.mapHomologicalComplex _).obj I.cocomplex
  let T := C.sc' 0 1 2
  have : Subsingleton (𝔪.primaryComponent K) :=
    primaryComponent_maximalIdeal_fractionRing R K ▸ inferInstance
  have hX₁ : IsZero T.X₁ :=
    IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
      (𝔪.primaryComponentFunctorObjIso (.of R K))
  have hX₃ : IsZero T.X₃ :=
    𝔪.primaryComponentFunctor.{u}.map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 S.X₃ 1 (by decide))
  exact ((isoRightDerivedPrimaryComponent 𝔪 1).app S.X₁) ≪≫
    I.isoRightDerivedObj 𝔪.primaryComponentFunctor.{u} 1 ≪≫
    C.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    (ShortComplex.HomologyData.ofZeros T (hX₁.eq_of_src _ _)
      (hX₃.eq_of_tgt _ _)).left.homologyIso ≪≫
    𝔪.primaryComponentFunctorObjIso S.X₃ ≪≫
    (LinearEquiv.ofTop _ (primaryComponent_maximalIdeal_quotient_fractionRing R K)).toModuleIso

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`, `H¹_𝔪(R)` is `R`-linearly
equivalent to `K ⧸ R`. -/
def dvrDegreeOneLinearEquiv :
    ((localCohomology (IsLocalRing.maximalIdeal R) 1).obj (.of R R)) ≃ₗ[R]
      K ⧸ LinearMap.range (Algebra.linearMap R K) :=
  (dvrDegreeOneIso R K).toLinearEquiv

/-- Over a discrete valuation ring `(R, 𝔪)`, `H^{n+2}_𝔪(R) = 0` for every `n : ℕ`. -/
theorem isZero_dvr_add_two (n : ℕ) :
    IsZero ((localCohomology (IsLocalRing.maximalIdeal R) (n + 2)).obj (.of R R)) := by
  let 𝔪 := IsLocalRing.maximalIdeal R
  let S := dvrShortComplex R (FractionRing R)
  have hS : S.ShortExact := dvrShortComplex_shortExact R (FractionRing R)
  have : Injective S.X₂ := injective_fractionRing_obj R (FractionRing R)
  have : Injective S.X₃ := injective_quotient_fractionRing_obj R (FractionRing R)
  refine IsZero.of_iso ?_ ((isoRightDerivedPrimaryComponent 𝔪 (n + 2)).app S.X₁ ≪≫
    𝔪.primaryComponentFunctor.{u}.rightDerivedObjX₁IsoOfShortExact hS n)
  exact Functor.isZero_rightDerived_obj_injective_succ 𝔪.primaryComponentFunctor.{u} n S.X₃

end DiscreteValuationRing

end localCohomology
