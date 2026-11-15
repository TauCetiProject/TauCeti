/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.FiniteEtale
public import TauCeti.RingTheory.Henselization.Henselian
public import TauCeti.RingTheory.Henselization.Local

import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.RingTheory.Etale.NoetherianDescent

/-!
# Finite étale algebras over a henselization

For a commutative ring `R` and an ideal `I`, the henselization `(algebra I, extended I)` is a
Henselian pair (`TauCeti.Henselization.henselian`) whose quotient `algebra I ⧸ extended I` is
canonically isomorphic to `R ⧸ I` (`TauCeti.Henselization.quotient_bijective`). Combining this
identification with `CommAlgCat.FiniteEtale.isEquivalence_baseChange_quotient` yields an equivalence
between the categories of finite étale `(algebra I)`-algebras and finite étale `(R ⧸ I)`-algebras,
and in particular between finite étale algebras over the henselization of a local ring and finite
étale algebras over its residue field.

Because `algebra I` is the filtered colimit of the étale neighbourhoods of `(R, I)`, every finite
étale `(algebra I)`-algebra descends to a finite étale algebra over some étale neighbourhood
`N : Neighbourhood I`. Together with the Henselian lifting theorem over `(algebra I, extended I)`,
every finite étale `(R ⧸ I)`-algebra lifts to a finite étale algebra over an étale neighbourhood of
`(R, I)` (Stacks Project, Lemma 15.13.1, Tag 0D4A).

## Main results

* `TauCeti.Henselization.exists_neighbourhood_ringHom_comp_eq_of_finitePresentation`: every ring
  homomorphism from a finitely presented `ℤ`-algebra into `algebra I` factors through some étale
  neighbourhood of `(R, I)`.
* `TauCeti.Henselization.exists_neighbourhood_etale_and_finite_and_algEquiv`: every finite étale
  `(algebra I)`-algebra is the base change of a finite étale algebra over some étale neighbourhood
  of `(R, I)`.
* `TauCeti.Henselization.exists_neighbourhood_etale_and_finite_and_tensorProduct_algEquiv`: every
  finite étale `(R ⧸ I)`-algebra lifts to a finite étale algebra over some étale neighbourhood of
  `(R, I)`.
* `TauCeti.Henselization.finiteEtaleEquivQuotient`: the equivalence of categories
  `CommAlgCat.FiniteEtale (algebra I) ≌ CommAlgCat.FiniteEtale (R ⧸ I)`.
* `TauCeti.Henselization.finiteEtaleEquivResidueField`: for a local ring `R`, the equivalence of
  categories between finite étale algebras over the henselization `algebra (maximalIdeal R)` and
  finite étale algebras over `IsLocalRing.ResidueField R`.

## References

* [Stacks Project, Lemma 15.13.1](https://stacks.math.columbia.edu/tag/0D4A)
* [Stacks Project, Lemma 15.13.2](https://stacks.math.columbia.edu/tag/09ZL)
-/

public section

open CategoryTheory Limits TensorProduct

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R]

/-- The forgetful functor to `CommRingCat` carries the colimit cocone of `diagram I` to a colimit
cocone of commutative rings. -/
private noncomputable def diagramForget₂IsColimit (I : Ideal R) :
    IsColimit ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone
      (colimit.cocone (diagram I))) := by
  let J := SmallModel.{u} (Neighbourhood.{u, u} I)
  let : IsFiltered J := IsFiltered.of_equivalence (equivSmallModel.{u} (Neighbourhood.{u, u} I))
  have : PreservesColimitsOfShape J
      (forget₂ (CommAlgCat.{u} R) CommRingCat.{u} ⋙ forget CommRingCat.{u}) :=
    preservesColimitsOfShape_of_natIso (eqToIso HasForget₂.forget_comp).symm
  have : PreservesColimitsOfShape J (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) :=
    preservesColimitsOfShape_of_reflects_of_preserves _ (forget CommRingCat.{u})
  exact isColimitOfPreserves _ (colimit.isColimit (diagram I))

/-- Every ring homomorphism from a finitely presented `ℤ`-algebra into the henselization `algebra I`
factors through some étale neighbourhood of `(R, I)`. -/
theorem exists_neighbourhood_ringHom_comp_eq_of_finitePresentation (I : Ideal R)
    {A : Type*} [CommRing A] [Algebra.FinitePresentation ℤ A] (g : A →+* algebra I) :
    ∃ (N : Neighbourhood.{u, u} I) (g' : A →+* N.obj),
      (stage I N : N.obj →+* algebra I).comp g' = g := by
  have : Small.{u} A := Algebra.FiniteType.small.{u} (R := ℤ) (S := A)
  let eA : Shrink.{u} A ≃ₐ[ℤ] A := Shrink.algEquiv ℤ A
  have : Algebra.FinitePresentation ℤ (Shrink.{u} A) := .equiv eA.symm
  let J := SmallModel.{u} (Neighbourhood.{u, u} I)
  let : IsFiltered J := IsFiltered.of_equivalence (equivSmallModel.{u} (Neighbourhood.{u, u} I))
  let F : J ⥤ CommRingCat.{u} := diagram I ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}
  let Z : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)
  let α : (Functor.const J).obj Z ⟶ F :=
    { app j := CommRingCat.ofHom
        ((Int.castRingHom ((diagram I).obj j)).comp ULift.ringEquiv.toRingHom)
      naturality _ _ _ := by ext ⟨n⟩; simp }
  let f : Z ⟶ CommRingCat.of (Shrink.{u} A) :=
    CommRingCat.ofHom ((algebraMap ℤ (Shrink.{u} A)).comp ULift.ringEquiv.toRingHom)
  have hf : f.hom.FinitePresentation :=
    (RingHom.finitePresentation_algebraMap.mpr inferInstance).comp
      (.of_bijective ULift.ringEquiv.bijective)
  let c := (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone (colimit.cocone (diagram I))
  let g_cat : CommRingCat.of (Shrink.{u} A) ⟶ c.pt :=
    CommRingCat.ofHom
      (((algebraIsoColimitDiagram I).hom.hom.toRingHom.comp g).comp eA.toAlgHom.toRingHom)
  obtain ⟨j, g', -, hg'⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    Z F α f c (diagramForget₂IsColimit I) hf g_cat (fun _ ↦ by ext ⟨n⟩; simp [f, g_cat, α])
  let N := (equivSmallModel.{u} (Neighbourhood.{u, u} I)).inverse.obj j
  refine ⟨N, g'.hom.comp eA.symm.toAlgHom.toRingHom, RingHom.ext fun a ↦ ?_⟩
  have hstage : (algebraIsoColimitDiagram I).inv.hom
      ((c.ι.app j).hom (g'.hom (eA.symm a))) = stage I N (g'.hom (eA.symm a)) :=
    DFunLike.congr_fun (algebraIsoColimitDiagram_inv_comp_ι I j) (g'.hom (eA.symm a))
  have hcomp : (algebraIsoColimitDiagram I).inv.hom ((c.ι.app j).hom (g'.hom (eA.symm a))) =
      (algebraIsoColimitDiagram I).inv.hom (g_cat.hom (eA.symm a)) :=
    congrArg (fun k : CommRingCat.of (Shrink.{u} A) ⟶ c.pt ↦
      (algebraIsoColimitDiagram I).inv.hom (k.hom (eA.symm a))) hg'.symm
  have hiso : (algebraIsoColimitDiagram I).inv.hom (g_cat.hom (eA.symm a)) = g a := by
    have h := DFunLike.congr_fun
      (congrArg CommAlgCat.Hom.hom (algebraIsoColimitDiagram I).hom_inv_id) (g a)
    simpa only [g_cat, CommRingCat.hom_ofHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_toAlgHom, eA.apply_symm_apply, CommAlgCat.hom_comp,
      AlgHom.comp_apply, CommAlgCat.hom_id, AlgHom.id_apply] using h
  simpa using hstage.symm.trans (hcomp.trans hiso)

/-- Every finite étale algebra over the henselization `algebra I` is the base change of a finite
étale algebra over some étale neighbourhood of `(R, I)`. -/
theorem exists_neighbourhood_etale_and_finite_and_algEquiv (I : Ideal R)
    (S : Type*) [CommRing S] [Algebra (algebra I) S]
    [Algebra.Etale (algebra I) S] [Module.Finite (algebra I) S] :
    ∃ (N : Neighbourhood.{u, u} I) (B' : Type u) (_ : CommRing B') (_ : Algebra N.obj B'),
      Algebra.Etale N.obj B' ∧ Module.Finite N.obj B' ∧
      letI : Algebra N.obj (algebra I) := (stage I N).toRingHom.toAlgebra
      Nonempty (S ≃ₐ[algebra I] algebra I ⊗[N.obj] B') := by
  obtain ⟨R₀, S₀, _, _, hR₀, _, _, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg_of_finite ℤ (algebra I) S
  have : Algebra.FinitePresentation ℤ R₀ :=
    Algebra.FinitePresentation.of_finiteType.1 (Subalgebra.fg_iff_finiteType R₀ |>.1 hR₀)
  obtain ⟨N, φ, hφ⟩ :=
    exists_neighbourhood_ringHom_comp_eq_of_finitePresentation I (algebraMap R₀ (algebra I))
  let : Algebra N.obj (algebra I) := (stage I N).toRingHom.toAlgebra
  let : Algebra R₀ N.obj := φ.toAlgebra
  have : IsScalarTower R₀ N.obj (algebra I) := .of_algebraMap_eq fun x ↦ congr($hφ x).symm
  have : Small.{u} (N.obj ⊗[R₀] S₀) := Module.Finite.small N.obj _
  let e' := Shrink.algEquiv N.obj (N.obj ⊗[R₀] S₀)
  exact ⟨N, Shrink.{u} (N.obj ⊗[R₀] S₀), inferInstance, inferInstance, .of_equiv e'.symm,
    .equiv e'.symm.toLinearEquiv,
    ⟨e.trans <| (Algebra.TensorProduct.cancelBaseChange R₀ N.obj _ _ S₀).symm.trans <|
      Algebra.TensorProduct.congr .refl e'.symm⟩⟩

private theorem algebraMap_quotient_extended_bijective (I : Ideal R) :
    Function.Bijective (algebraMap (R ⧸ I) (algebra I ⧸ extended I)) := by
  have he : algebraMap (R ⧸ I) (algebra I ⧸ extended I) = reducedMap I (algebra I) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ by
      simp [reducedMap_mk, Ideal.Quotient.algebraMap_quotient_map_quotient])
  exact he ▸ quotient_bijective I

/-- Assemble the `(R ⧸ I)`-algebra equivalence `(R ⧸ I) ⊗[R] B' ≃ₐ[R ⧸ I] B₀` for a stage model
`B'` over `A` of an `H`-algebra `S` lifting `(H ⧸ IH) ⊗[R ⧸ I] B₀` in a scalar tower `R → A → H`. -/
private noncomputable def stageFiberAlgEquiv (I : Ideal R) {B₀ : Type*} [CommRing B₀]
    [Algebra (R ⧸ I) B₀] {A H B' S : Type u} [CommRing A] [Algebra R A]
    [CommRing H] [Algebra R H] [Algebra A H] [IsScalarTower R A H]
    [CommRing B'] [Algebra R B'] [Algebra A B'] [IsScalarTower R A B']
    [CommRing S] [Algebra H S]
    (hAQ : I.map (algebraMap R A) ≤ (I.map (algebraMap R H)).comap (algebraMap A H))
    (hQA : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R H)) (algebraMap A H) hAQ))
    (hQH : Function.Bijective (algebraMap (R ⧸ I) (H ⧸ I.map (algebraMap R H))))
    (eN : S ≃ₐ[H] H ⊗[A] B')
    (eS : (H ⧸ I.map (algebraMap R H)) ⊗[H] S ≃ₐ[H ⧸ I.map (algebraMap R H)]
      (H ⧸ I.map (algebraMap R H)) ⊗[R ⧸ I] B₀) :
    (R ⧸ I) ⊗[R] B' ≃ₐ[R ⧸ I] B₀ := by
  let J_H := I.map (algebraMap R H)
  let Q := H ⧸ J_H
  let J_A := I.map (algebraMap R A)
  let Q_A := A ⧸ J_A
  haveI : IsScalarTower R A Q := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R H Q, IsScalarTower.algebraMap_apply R A H,
      ← IsScalarTower.algebraMap_apply A H Q]
  have hmap : I.map (algebraMap R B') = J_A.map (algebraMap A B') := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let eQAQ : Q_A ≃ₐ[A] Q :=
    AlgEquiv.ofBijective (Ideal.quotientMapₐ J_H (Algebra.ofId A H) hAQ) hQA
  let eQuot : (R ⧸ I) ⊗[R] B' ≃ₐ[R] Q ⊗[A] B' :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B' I).symm.restrictScalars R).trans <|
    (Ideal.quotientEquivAlgOfEq R hmap).trans <|
    (((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B' J_A).restrictScalars A
      ).restrictScalars R).trans <|
    (Algebra.TensorProduct.congr eQAQ (AlgEquiv.refl : B' ≃ₐ[A] B')).restrictScalars R
  let eStage : Q ⊗[A] B' ≃ₐ[Q] Q ⊗[R ⧸ I] B₀ :=
    (Algebra.TensorProduct.cancelBaseChange A H Q Q B').symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : Q ≃ₐ[Q] Q) eN.symm).trans eS
  let eQ : (R ⧸ I) ≃ₐ[R ⧸ I] Q := AlgEquiv.ofBijective (Algebra.ofId (R ⧸ I) Q) hQH
  let eB₀ : Q ⊗[R ⧸ I] B₀ ≃ₐ[R ⧸ I] B₀ :=
    (Algebra.TensorProduct.congr eQ.symm (AlgEquiv.refl : B₀ ≃ₐ[R ⧸ I] B₀)).trans
      (Algebra.TensorProduct.lid (R ⧸ I) B₀)
  exact ((eQuot.trans (eStage.restrictScalars R)).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective).trans eB₀

/-- **Lifting finite étale algebras to an étale neighbourhood.** Given a commutative ring `R`, an
ideal `I`, and a finite étale `(R ⧸ I)`-algebra `B₀`, there exist an étale neighbourhood `N` of
`(R, I)` and a finite étale `N.obj`-algebra `B'` (equipped with the composite `R`-algebra structure
`IsScalarTower R N.obj B'`, hence étale over `R`) whose base change to `R ⧸ I` is `(R ⧸ I)`-algebra
isomorphic to `B₀`. -/
@[stacks 0D4A]
theorem exists_neighbourhood_etale_and_finite_and_tensorProduct_algEquiv (I : Ideal R)
    (B₀ : Type*) [CommRing B₀] [Algebra (R ⧸ I) B₀]
    [Algebra.Etale (R ⧸ I) B₀] [Module.Finite (R ⧸ I) B₀] :
    ∃ (N : Neighbourhood.{u, u} I) (B' : Type u) (_ : CommRing B')
      (_ : Algebra R B') (_ : Algebra N.obj B'),
      IsScalarTower R N.obj B' ∧ Algebra.Etale N.obj B' ∧ Module.Finite N.obj B' ∧
      Nonempty ((R ⧸ I) ⊗[R] B' ≃ₐ[R ⧸ I] B₀) := by
  let Q := algebra I ⧸ extended I
  obtain ⟨S, _, _, _, _, ⟨eS⟩⟩ :=
    TauCeti.HenselianRing.exists_etale_and_finite_and_tensorProduct_algEquiv
      (extended I) (Q ⊗[R ⧸ I] B₀)
  obtain ⟨N, B', _, _, _, _, ⟨eN⟩⟩ :=
    exists_neighbourhood_etale_and_finite_and_algEquiv I S
  let : Algebra N.obj (algebra I) := (stage I N).toRingHom.toAlgebra
  have : IsScalarTower R N.obj (algebra I) :=
    .of_algebraMap_eq fun r ↦ ((stage I N).commutes r).symm
  let : Algebra R B' := ((algebraMap N.obj B').comp (algebraMap R N.obj)).toAlgebra
  have : IsScalarTower R N.obj B' := .of_algebraMap_eq' rfl
  exact ⟨N, B', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨stageFiberAlgEquiv I (map_le_comap_stage_extended I N)
      (quotientMap_stage_bijective I N) (algebraMap_quotient_extended_bijective I) eN eS⟩⟩

/-- Base change of finite étale algebras along `R ⧸ I → algebra I ⧸ extended I` is an equivalence
of categories. -/
instance isEquivalence_baseChange_reducedMap (I : Ideal R) :
    (CommAlgCat.FiniteEtale.baseChange.{u} (R ⧸ I) (algebra I ⧸ extended I)).IsEquivalence :=
  CommAlgCat.FiniteEtale.isEquivalence_baseChange_of_bijective
    (algebraMap_quotient_extended_bijective I)

/-- **Equivalence of finite étale algebras over a henselization.** For any pair `(R, I)`, the
category of finite étale algebras over the henselization `algebra I` is equivalent to the category
of finite étale algebras over `R ⧸ I`. -/
@[stacks 0D4A]
noncomputable def finiteEtaleEquivQuotient (I : Ideal R) :
    CommAlgCat.FiniteEtale.{u} (algebra I) ≌ CommAlgCat.FiniteEtale.{u} (R ⧸ I) :=
  (CommAlgCat.FiniteEtale.baseChange.{u} (algebra I) (algebra I ⧸ extended I)).asEquivalence.trans
    (CommAlgCat.FiniteEtale.baseChange.{u} (R ⧸ I) (algebra I ⧸ extended I)).asEquivalence.symm

/-- Composing `(finiteEtaleEquivQuotient I).functor` with base change along
`R ⧸ I → algebra I ⧸ extended I` is naturally isomorphic to base change along
`algebra I → algebra I ⧸ extended I`. -/
noncomputable def finiteEtaleEquivQuotientFunctorIso (I : Ideal R) :
    (finiteEtaleEquivQuotient I).functor ⋙
        CommAlgCat.FiniteEtale.baseChange.{u} (R ⧸ I) (algebra I ⧸ extended I) ≅
      CommAlgCat.FiniteEtale.baseChange.{u} (algebra I) (algebra I ⧸ extended I) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (CommAlgCat.FiniteEtale.baseChange.{u} (R ⧸ I)
        (algebra I ⧸ extended I)).asEquivalence.counitIso ≪≫
    Functor.rightUnitor _

/-- Composing `(finiteEtaleEquivQuotient I).inverse` with base change along
`algebra I → algebra I ⧸ extended I` is naturally isomorphic to base change along
`R ⧸ I → algebra I ⧸ extended I`. -/
noncomputable def finiteEtaleEquivQuotientInverseIso (I : Ideal R) :
    (finiteEtaleEquivQuotient I).inverse ⋙
        CommAlgCat.FiniteEtale.baseChange.{u} (algebra I) (algebra I ⧸ extended I) ≅
      CommAlgCat.FiniteEtale.baseChange.{u} (R ⧸ I) (algebra I ⧸ extended I) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (CommAlgCat.FiniteEtale.baseChange.{u} (algebra I)
        (algebra I ⧸ extended I)).asEquivalence.counitIso ≪≫
    Functor.rightUnitor _

section IsLocalRing

variable (R) [IsLocalRing R]

/-- Base change of finite étale algebras along the residue-field map
`ResidueField R → ResidueField (algebra (maximalIdeal R))` is an equivalence of categories. -/
instance isEquivalence_baseChange_residueField :
    (CommAlgCat.FiniteEtale.baseChange.{u} (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (algebra (IsLocalRing.maximalIdeal R)))).IsEquivalence :=
  CommAlgCat.FiniteEtale.isEquivalence_baseChange_of_bijective (residueField_map_bijective R)

/-- **Equivalence of finite étale algebras over the henselization of a local ring.** Finite étale
algebras over the henselization `algebra (maximalIdeal R)` of a local ring `R` are equivalent to
finite étale algebras over `IsLocalRing.ResidueField R`. -/
noncomputable def finiteEtaleEquivResidueField :
    CommAlgCat.FiniteEtale.{u} (algebra (IsLocalRing.maximalIdeal R)) ≌
      CommAlgCat.FiniteEtale.{u} (IsLocalRing.ResidueField R) :=
  (CommAlgCat.FiniteEtale.baseChange.{u} (algebra (IsLocalRing.maximalIdeal R))
    (IsLocalRing.ResidueField (algebra (IsLocalRing.maximalIdeal R)))).asEquivalence.trans
    (CommAlgCat.FiniteEtale.baseChange.{u} (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (algebra (IsLocalRing.maximalIdeal R)))).asEquivalence.symm

end IsLocalRing

-- Finite étale algebras over the henselization of `(ℤ, (5))` are equivalent to finite étale
-- algebras over `ℤ ⧸ (5)`.
example : Nonempty (CommAlgCat.FiniteEtale.{0} (algebra (Ideal.span {(5 : ℤ)})) ≌
    CommAlgCat.FiniteEtale.{0} (ℤ ⧸ Ideal.span {(5 : ℤ)})) :=
  ⟨finiteEtaleEquivQuotient (Ideal.span {(5 : ℤ)})⟩

end TauCeti.Henselization
