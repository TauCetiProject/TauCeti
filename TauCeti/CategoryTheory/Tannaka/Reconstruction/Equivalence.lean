/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Tannaka.Hull.Equivalence
public import TauCeti.CategoryTheory.Tannaka.Reconstruction.Coalgebra

/-!
# Reconstruction of an abelian category with a fibre functor as finite comodules

Let `K` be a field, `C` an essentially small abelian `K`-linear category and
`ω : C ⥤ ModuleCat K` a `K`-linear, exact and faithful functor with finite-dimensional values.
This file proves that the lift `ω.toReconstructionComodule : C ⥤ FGComoduleCat K B` of `ω` to
finite comodules over its coalgebra `B = ω.reconstructionCoalgebra` is an equivalence of
categories (`CategoryTheory.Functor.reconstructionEquivalence`). Its composite with the
forgetful functor to vector spaces is `ω`
(`CategoryTheory.Functor.toReconstructionComoduleCompForget₂Iso`).
No tensor structure on `C`, and no semisimplicity, is used.

The proof combines the finite case with filtered descent. On the hull `⟨X_s⟩` of a stage, `ω`
identifies `⟨X_s⟩` with finite modules over `A_s = ω.hullAlgebra X_s`
(`CategoryTheory.Functor.hullEquivalence`), and `A_s`-modules are `A_s^∨`-comodules. A finite
`B`-comodule descends to a comodule over some `A_s^∨`
(`TauCeti.Comodule.exists_comoduleFactor_ofCoalgHom`), hence comes from an object of `⟨X_s⟩`;
a morphism of `B`-comodules between objects of `⟨X_s⟩` is a morphism of `A_t^∨`-comodules for a
larger stage `t` (`TauCeti.Comodule.Hom.exists_map_lTensor_comp_coact_eq`), hence comes from a
morphism of `⟨X_t⟩`.

For a fibre functor `w : C ⥤ FGModuleCat K`, apply this to
`w ⋙ forget₂ (FGModuleCat K) (ModuleCat K)`.

## Main results

* `CategoryTheory.Functor.reconstructionEquivalence`: the equivalence
  `C ≌ FGComoduleCat K ω.reconstructionCoalgebra`, whose functor is
  `CategoryTheory.Functor.toReconstructionComodule`.

## References

* P. Deligne, J. S. Milne, *Tannakian categories*, Proposition 2.14 and its proof.
* A. Huber, S. Müller-Stach, *Periods and Nori motives*, Propositions 7.4.1–7.4.2.
-/

public section

open CategoryTheory Limits TauCeti TauCeti.Tannaka
open scoped TensorProduct

universe w v u

namespace CategoryTheory.Functor

attribute [local instance] Abelian.hasFiniteBiproducts natEndModule

variable {K : Type u} [Field K] {C : Type v} [Category.{w} C] [EssentiallySmall.{u} C]
  [Abelian C] (ω : C ⥤ ModuleCat.{u} K) [ω.Additive] [PreservesFiniteLimits ω]
  [ω.PreservesEpimorphisms] [∀ X, Module.Finite K (ω.obj X)]

/-- A finite comodule over the coalgebra of `ω` descends to the dual coalgebra of a stage. -/
private theorem exists_reconstructionStage_comodule (M : Type u) [AddCommGroup M] [Module K M]
    [σ : Comodule K ω.reconstructionCoalgebra M] [Module.Finite K M] :
    ∃ s, ∃ σ' : Comodule K (ω.ReconstructionStage s) M,
      (ω.toReconstructionCoalgebra s).toLinearMap.lTensor M ∘ₗ σ'.coact = σ.coact := by
  classical
  have := Module.finitePresentation_of_finite K M
  exact @Comodule.exists_comoduleFactor_ofCoalgHom K _ _ _ _ _ ω.ReconstructionStage _ _
    (fun _ ↦ inferInstance) (fun s t h ↦ ω.reconstructionTransition s t h) _ M _ _ σ _ _

/-- A morphism of comodules over the coalgebra of `ω` between the fibres of two members of the
hull of `X_s` is a morphism of the comodules of some larger stage. -/
private theorem exists_le_map_comp_coact_eq {s : Finset (SmallModel.{u} C)} {Y Y' : C}
    (h : subquotientHull (smallModelBiproduct C s) Y)
    (h' : subquotientHull (smallModelBiproduct C s) Y') (φ : ω.obj Y →ₗ[K] ω.obj Y')
    (hφ : TensorProduct.map φ LinearMap.id ∘ₗ (ω.reconstructionComodule Y).coact =
      (ω.reconstructionComodule Y').coact ∘ₗ φ) :
    ∃ t, ∃ hst : s ≤ t, TensorProduct.map φ LinearMap.id ∘ₗ (ω.reconstructionStageComodule
        (subquotientHull_le_of_mem (subquotientHull_smallModelBiproduct_of_le hst) _ h)).coact =
      (ω.reconstructionStageComodule (subquotientHull_le_of_mem
        (subquotientHull_smallModelBiproduct_of_le hst) _ h')).coact ∘ₗ φ := by
  classical
  let := ω.reconstructionComodule Y
  let := ω.reconstructionComodule Y'
  let g : Comodule.Hom K ω.reconstructionCoalgebra (ω.obj Y) (ω.obj Y') := ⟨φ, hφ⟩
  obtain ⟨t, hst, ht⟩ := @Comodule.Hom.exists_map_lTensor_comp_coact_eq K _ _ _ _ _
    ω.ReconstructionStage _ _ (fun _ ↦ inferInstance)
    (fun s t h ↦ ω.reconstructionTransition s t h) _ (ω.obj Y) _ _ (ω.reconstructionComodule Y)
    (ω.obj Y') _ _ (ω.reconstructionComodule Y') _ g s (ω.reconstructionStageComodule h)
    (ω.reconstructionStageComodule h') (ω.reconstructionComodule_coact h).symm
    (ω.reconstructionComodule_coact h').symm
  refine ⟨t, hst, ?_⟩
  rw [← ω.lTensor_reconstructionTransition_comp_coact hst h,
    ← ω.lTensor_reconstructionTransition_comp_coact hst h', LinearMap.comp_assoc]
  exact ht

/-- The lift of `ω` to comodules is faithful. -/
instance [ω.Faithful] : ω.toReconstructionComodule.Faithful :=
  Functor.Faithful.of_comp_iso ω.toReconstructionComoduleCompForget₂Iso

variable [CategoryTheory.Linear K C] [ω.Linear K] [ω.Faithful]

/-- The lift of `ω` to comodules is full. -/
instance : ω.toReconstructionComodule.Full where
  map_surjective {Y Y'} φ := by
    obtain ⟨s, h, h'⟩ := exists_subquotientHull_smallModelBiproduct Y Y'
    obtain ⟨t, hst, ht⟩ := ω.exists_le_map_comp_coact_eq h h' φ.hom.toLinearMap φ.hom.map_coact
    have hφ := (ω.map_comp_reconstructionStageComodule_coact_iff _ _ _).1 ht
    let φ' : (ω.hullModuleFunctor (smallModelBiproduct C t)).obj ⟨Y, _⟩ ⟶
        (ω.hullModuleFunctor (smallModelBiproduct C t)).obj ⟨Y', _⟩ :=
      ObjectProperty.homMk (ModuleCat.ofHom
        { toFun := φ.hom.toLinearMap
          map_add' := φ.hom.toLinearMap.map_add
          map_smul' η y := by
            have := LinearMap.congr_fun (hφ (ω.hullEndAlgEquiv _ η)) y
            rw [hullAction_hullEndAlgEquiv, hullAction_hullEndAlgEquiv] at this
            -- `η` acts on the fibres through its components (`natEndModule_smul`).
            exact this })
    obtain ⟨g, hg⟩ := (ω.hullModuleFunctor (smallModelBiproduct C t)).map_surjective φ'
    refine ⟨g.hom, ?_⟩
    ext y
    exact (ω.hullModuleFunctor_map_hom_hom_apply g y).symm.trans
      (congrArg (fun ψ ↦ ψ.hom.hom y) hg)

/-- Every finite comodule over the coalgebra of `ω` is isomorphic to the comodule of an object
of `C`. -/
instance : ω.toReconstructionComodule.EssSurj where
  mem_essImage M := by
    let := Module.addCommMonoidToAddCommGroup K (M := M)
    obtain ⟨s, σ, hσ⟩ := ω.exists_reconstructionStage_comodule M
    let : Comodule K (ConvolutionDual K (ω.hullAlgebra (smallModelBiproduct C s))) M := σ
    let ρ := (Comodule.algebraAction (R := K) (A := ω.hullAlgebra (smallModelBiproduct C s))
      (M := M)).comp (ω.hullEndAlgEquiv (smallModelBiproduct C s)).toAlgHom
    let : Module (End ((subquotientHull (smallModelBiproduct C s)).ι ⋙ ω)) M :=
      Module.compHom M ρ.toRingHom
    have : IsScalarTower K (End ((subquotientHull (smallModelBiproduct C s)).ι ⋙ ω)) M :=
      IsScalarTower.of_algebraMap_smul fun c m ↦ by
        -- The natural endomorphisms act on `M` through `ρ`, by the definition of
        -- `Module.compHom`.
        change ρ (algebraMap K _ c) m = c • m
        rw [AlgHom.commutes, Module.algebraMap_end_apply]
    have : Module.Finite (End ((subquotientHull (smallModelBiproduct C s)).ι ⋙ ω)) M :=
      Module.Finite.of_restrictScalars_finite K _ M
    obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (F := ω.hullModuleFunctor (smallModelBiproduct C s)) (FGModuleCat.of _ M)
    let e' : ((subquotientHull (smallModelBiproduct C s)).ι ⋙ ω).obj Y ≃ₗ[
        End ((subquotientHull (smallModelBiproduct C s)).ι ⋙ ω)] M :=
      ((ModuleCat.isFG _).ι.mapIso e).toLinearEquiv
    let ℓ : ((subquotientHull (smallModelBiproduct C s)).ι ⋙ ω).obj Y ≃ₗ[K] M :=
      e'.restrictScalars K
    refine ⟨Y.obj, ⟨FGComoduleCat.isoOfLinearEquiv ℓ ?_⟩⟩
    have key : TensorProduct.map ℓ.toLinearMap LinearMap.id ∘ₗ
        (ω.reconstructionStageComodule Y.property).coact = σ.coact ∘ₗ ℓ.toLinearMap := by
      have := (Comodule.map_coact_ofAlgebraAction_iff (ω.hullAction Y.property)
        (Comodule.algebraAction (R := K) (A := ω.hullAlgebra (smallModelBiproduct C s)) (M := M))
        ℓ.toLinearMap).2 fun a ↦ LinearMap.ext fun y ↦ by
          obtain ⟨η, rfl⟩ := (ω.hullEndAlgEquiv (smallModelBiproduct C s)).surjective a
          rw [LinearMap.comp_apply, hullAction_hullEndAlgEquiv]
          -- On both sides `η` acts by `natEndModule` and through `ρ`: this is the
          -- `End`-linearity of `e'`.
          exact e'.map_smul η y
      rwa [Comodule.ofAlgebraAction_algebraAction] at this
    have hcomm : (ω.toReconstructionCoalgebra s).toLinearMap.lTensor M ∘ₗ
        TensorProduct.map ℓ.toLinearMap LinearMap.id =
          TensorProduct.map ℓ.toLinearMap LinearMap.id ∘ₗ
            (ω.toReconstructionCoalgebra s).toLinearMap.lTensor (ω.obj Y.obj) :=
      TensorProduct.ext' fun _ _ ↦ rfl
    rw [coact_toReconstructionComodule_obj, ω.reconstructionComodule_coact Y.property, ← hσ]
    refine LinearMap.ext fun y ↦ ?_
    have h₁ := LinearMap.congr_fun hcomm ((ω.reconstructionStageComodule Y.property).coact y)
    have h₂ := LinearMap.congr_fun key y
    simp only [LinearMap.comp_apply] at h₁ h₂
    exact h₁.symm.trans (congrArg _ h₂)

/-- The lift of `ω` to comodules is an equivalence of categories. -/
instance : ω.toReconstructionComodule.IsEquivalence where

/-- **Reconstruction of an abelian category from a fibre functor.** For a field `K`, an
essentially small abelian `K`-linear category `C` and a `K`-linear, exact and faithful functor
`ω` from `C` to finite-dimensional vector spaces, `C` is equivalent to the category of finite
comodules over the coalgebra `ω.reconstructionCoalgebra`. The functor of the equivalence is
`ω.toReconstructionComodule`, whose underlying vector spaces are the values of `ω`
(`CategoryTheory.Functor.toReconstructionComoduleCompForget₂Iso`). -/
noncomputable def reconstructionEquivalence :
    C ≌ FGComoduleCat.{u, u, u} K ω.reconstructionCoalgebra :=
  ω.toReconstructionComodule.asEquivalence

/-- The functor of `reconstructionEquivalence` is the lift of `ω` to comodules. -/
@[simp]
theorem reconstructionEquivalence_functor :
    ω.reconstructionEquivalence.functor = ω.toReconstructionComodule :=
  (rfl)

end CategoryTheory.Functor
