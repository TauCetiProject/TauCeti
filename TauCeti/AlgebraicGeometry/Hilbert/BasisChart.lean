/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.MvPolynomial.QuotientBasis
public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Over
public import TauCeti.AlgebraicGeometry.AffineScheme.RelativeHom
import TauCeti.AlgebraicGeometry.BaseChangeSection

/-!
# Affine charts for polynomial quotients with a prescribed basis

The spectrum of the universal quotient-basis ring classifies polynomial ideals
whose quotients have a specified basis. The classification holds over every test
scheme and commutes with pullback. These spectra are the affine basis charts of
the Hilbert functor of points of affine space.
-/

public section

noncomputable section


universe schemeUniverse

open CategoryTheory Limits Opposite TauCeti.PolynomialQuotient

namespace AlgebraicGeometry.Hilbert

variable {indeterminates : Type schemeUniverse} {base : Scheme.{schemeUniverse}} [IsAffine base]
  {rank : ℕ}

/-- The affine scheme parametrizing polynomial quotients with the prescribed basis. -/
def basisChart (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)) : Over base :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(base, ⊤) (QuotientBasisRing family))) ≫ base.isoSpec.inv)

/-- The underlying scheme of a basis chart is the spectrum of its quotient-basis ring. -/
@[simp]
lemma basisChart_left (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)) :
    (basisChart family).left = Spec (CommRingCat.of (QuotientBasisRing family)) := (rfl)

/-- The structure morphism of a basis chart is induced by its coefficient algebra. -/
lemma basisChart_hom (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)) :
    eqToHom (basisChart_left family).symm ≫ (basisChart family).hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(base, ⊤) (QuotientBasisRing family))) ≫ base.isoSpec.inv := (rfl)

instance (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)) :
    IsAffine (basisChart family).left :=
  inferInstanceAs (IsAffine (Spec _))

/-- The coordinate-ring map of a morphism to a basis chart. -/
def basisChartRingHom {family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)}
    {test : Over base} :
    (test ⟶ basisChart family) → (QuotientBasisRing family →+* Γ(test.left, ⊤)) := by
  unfold basisChart
  exact fun chartMap ↦
    ((Scheme.ΓSpecIso (CommRingCat.of (QuotientBasisRing family))).inv ≫
      chartMap.left.appTop).hom

/-- A chart morphism induces a map of algebras over the base ring. -/
lemma basisChartRingHom_comp_algebraMap
    {family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)} {test : Over base}
    (chartMap : test ⟶ basisChart family) :
    (basisChartRingHom chartMap).comp
        (algebraMap Γ(base, ⊤) (QuotientBasisRing family)) =
      test.hom.appTop.hom := by
  unfold basisChart at chartMap
  have compatibility : CommRingCat.ofHom
      (algebraMap Γ(base, ⊤) (QuotientBasisRing family)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (QuotientBasisRing family))).inv ≫
        chartMap.left.appTop = (chartMap.left ≫ (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(base, ⊤) (QuotientBasisRing family))) ≫ base.isoSpec.inv)).hom).appTop := by
    simp only [Over.mk_hom]
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.comp_appTop,
      Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_appTop, Category.assoc]
    -- The coefficient algebra map and the composite appTop map have the same ring function.
    rfl
  rw [← Over.w chartMap, ← compatibility]
  -- RingHom.comp is the underlying hom of composition in CommRingCat.
  rfl

/-- The coordinate-ring classification commutes with changing the test scheme. -/
@[simp]
lemma basisChartRingHom_comp
    {family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)} {test smallerTest : Over base}
    (restriction : smallerTest ⟶ test) (chartMap : test ⟶ basisChart family) :
    basisChartRingHom (restriction ≫ chartMap) =
      restriction.left.appTop.hom.comp (basisChartRingHom chartMap) := by
  unfold basisChart at chartMap
  simp only [basisChartRingHom, basisChart, id_eq, Over.comp_left, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  exact RingHom.comp_assoc _ _ _

/-- Morphisms to a basis chart are algebra maps from its coordinate ring. -/
def basisChartAlgHomEquiv (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    (test : Over base) :
    letI := test.hom.appTop.hom.toAlgebra
    (test ⟶ basisChart family) ≃
      (QuotientBasisRing family →ₐ[Γ(base, ⊤)] Γ(test.left, ⊤)) := by
  letI := test.hom.appTop.hom.toAlgebra
  unfold basisChart
  exact Scheme.overAffineHomEquivAlgHom test
    (CommAlgCat.of Γ(base, ⊤) (QuotientBasisRing family))

/-- The chart algebra map has the prescribed coordinate-ring map. -/
@[simp]
lemma basisChartAlgHomEquiv_toRingHom
    (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    (test : Over base) (chartMap : test ⟶ basisChart family) :
    letI := test.hom.appTop.hom.toAlgebra
    (basisChartAlgHomEquiv family test chartMap : _ →+* _) = basisChartRingHom chartMap :=
  by
    unfold basisChartAlgHomEquiv basisChartRingHom basisChart
    exact Scheme.overAffineHomEquivAlgHom_toRingHom test
      (CommAlgCat.of Γ(base, ⊤) (QuotientBasisRing family)) chartMap

/-- The universal ideal classifies all polynomial quotients with the given basis. -/
def basisChartEquiv (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    (test : Over base) :
    letI := test.hom.appTop.hom.toAlgebra
    (test ⟶ basisChart family) ≃
      {ideal : Ideal (MvPolynomial indeterminates Γ(test.left, ⊤)) //
        IsQuotientBasis family ideal} := by
  letI := test.hom.appTop.hom.toAlgebra
  exact (basisChartAlgHomEquiv family test).trans
    (quotientBasisEquiv family Γ(test.left, ⊤))

/-- A chart morphism pulls back the universal ideal by its coordinate-ring map. -/
@[simp]
lemma basisChartEquiv_apply (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    {test : Over base} (chartMap : test ⟶ basisChart family) :
    (basisChartEquiv family test chartMap).val =
      (quotientBasisIdeal family).map
        (MvPolynomial.map (basisChartRingHom chartMap)) := by
  let := test.hom.appTop.hom.toAlgebra
  have h := coe_quotientBasisEquiv_apply family ((basisChartAlgHomEquiv family test) chartMap)
  rw [AlgHom.toRingHom_eq_coe, basisChartAlgHomEquiv_toRingHom] at h
  exact h

/-- The universal family is compatible with pullback of chart morphisms. -/
lemma basisChartEquiv_comp (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    {test smallerTest : Over base} (restriction : smallerTest ⟶ test)
    (chartMap : test ⟶ basisChart family) :
    (basisChartEquiv family smallerTest (restriction ≫ chartMap)).val =
      ((basisChartEquiv family test chartMap).val).map
        (MvPolynomial.map restriction.left.appTop.hom) := by
  let := test.hom.appTop.hom.toAlgebra
  let := smallerTest.hom.appTop.hom.toAlgebra
  let scalarMap : Γ(test.left, ⊤) →ₐ[Γ(base, ⊤)] Γ(smallerTest.left, ⊤) :=
    restriction.left.appTopAlgHom (Over.w restriction)
  have scalarMap_eq : scalarMap.toRingHom = restriction.left.appTop.hom :=
    restriction.left.toRingHom_appTopAlgHom (Over.w restriction)
  have scalarMap_coe : (scalarMap : Γ(test.left, ⊤) →+* Γ(smallerTest.left, ⊤)) =
      restriction.left.appTop.hom :=
    restriction.left.toRingHom_appTopAlgHom (Over.w restriction)
  have heq : basisChartAlgHomEquiv family smallerTest (restriction ≫ chartMap) =
      scalarMap.comp (basisChartAlgHomEquiv family test chartMap) := by
    apply AlgHom.toRingHom_injective
    simp only [basisChartAlgHomEquiv_toRingHom, AlgHom.comp_toRingHom, scalarMap_coe]
    exact basisChartRingHom_comp restriction chartMap
  simpa only [basisChartEquiv, Equiv.trans_apply, heq, scalarMap_eq] using
    quotientBasisEquiv_comp family scalarMap (basisChartAlgHomEquiv family test chartMap)

end AlgebraicGeometry.Hilbert
