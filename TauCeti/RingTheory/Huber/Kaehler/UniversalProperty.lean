/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.Topology
public import TauCeti.RingTheory.Huber.Kaehler.FiniteTarget
public import TauCeti.RingTheory.Huber.Kaehler.FiniteType

/-!
# Universal property of continuous differentials

When `B ⊗̂_A B` is of noetherian type, combining `Derivation.liftContinuousKaehlerDifferential` and
`Derivation.liftContinuousKaehlerDifferentialOfFinite` with `hom_ext` and `linearMap_ext` yields
uniqueness (`Derivation.existsUnique_liftContinuousKaehlerDifferential`,
`ContinuousLinearMap.liftContinuousKaehlerDifferential_compDer_D`,
`LinearMap.liftContinuousKaehlerDifferentialOfFinite_compDer_D`). When `A → B` is topologically
of finite type into complete Hausdorff Huber `B` of noetherian type, `continuous_D` gives the
`B`-linear equivalence
`continuousLinearMapEquivDerivation : (Ωᶜ[B⁄A] →L[B] M) ≃ₗ[B]`
`TauCeti.continuousDerivationSubmodule A B M`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Definition 1.6.1 and (1.6.2)(ii).
-/

public section

namespace Derivation

open TauCeti.Huber CompletedTensor ContinuousKaehlerDifferential

section NoetherianDiagonal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace A]
  [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]
  [IsNoetherianType (CompletedTensor A B B)]
  {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]

/-- **Universal property of `Ωᶜ[B⁄A]`** (Huber 1996, §1.6, Definition 1.6.1 and (1.6.2)(ii)):
when `B ⊗̂_A B` is of noetherian type, every continuous `A`-derivation `δ : B → M` factors
through a unique `Ωᶜ[B⁄A] →L[B] M`. -/
theorem existsUnique_liftContinuousKaehlerDifferential (δ : Derivation A B M) (hδ : Continuous δ) :
    ∃! f : ContinuousKaehlerDifferential A B →L[B] M, ∀ b, f (D A B b) = δ b :=
  ⟨δ.liftContinuousKaehlerDifferential hδ, δ.liftContinuousKaehlerDifferential_comp_D hδ,
    fun _ hf ↦ hom_ext fun b ↦
      (hf b).trans (δ.liftContinuousKaehlerDifferential_comp_D hδ b).symm⟩

end NoetherianDiagonal

end Derivation

namespace ContinuousLinearMap

open TauCeti.Huber CompletedTensor ContinuousKaehlerDifferential

section NoetherianDiagonal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace A]
  [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]
  [IsNoetherianType (CompletedTensor A B B)]
  {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]

/-- Lifting the derivation `f ∘ d` recovers the continuous `B`-linear map `f`. -/
@[simp] theorem liftContinuousKaehlerDifferential_compDer_D
    (f : ContinuousKaehlerDifferential A B →L[B] M)
    (hf : Continuous (f.toLinearMap.compDer (D A B))) :
    (f.toLinearMap.compDer (D A B)).liftContinuousKaehlerDifferential hf = f :=
  hom_ext fun b ↦ Derivation.liftContinuousKaehlerDifferential_comp_D _ _ b

end NoetherianDiagonal

end ContinuousLinearMap

namespace LinearMap

open TauCeti.Huber CompletedTensor ContinuousKaehlerDifferential

section NoetherianDiagonal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace A]
  [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]
  [IsNoetherianType (CompletedTensor A B B)]

/-- Lifting `f ∘ d` into a finite `B`-module carrying its natural topology recovers `f`, when
`B` and `B ⊗̂_A B` are of noetherian type. -/
@[simp] theorem liftContinuousKaehlerDifferentialOfFinite_compDer_D
    [IsHuberRing B] [IsNoetherianType B]
    {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module.Finite B N] [TopologicalSpace N] [IsModuleTopology B N]
    (f : ContinuousKaehlerDifferential A B →ₗ[B] N) (hf : Continuous (f.compDer (D A B))) :
    (f.compDer (D A B)).liftContinuousKaehlerDifferentialOfFinite hf = f :=
  linearMap_ext fun b ↦ Derivation.liftContinuousKaehlerDifferentialOfFinite_comp_D _ _ b

end NoetherianDiagonal

end LinearMap

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

section UniversalEquiv

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]
  {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [IsScalarTower A B M] [ContinuousSMul B M]

/-- **`B`-linear equivalence between continuous `B`-linear maps `Ωᶜ[B⁄A] →L[B] M` and
continuous `A`-derivations `B → M`** (Huber 1996, §1.6, Definition 1.6.1 and (1.6.2)(ii)). -/
noncomputable def continuousLinearMapEquivDerivation
    (h : IsTopologicallyFiniteType (algebraMap A B)) :
    (ContinuousKaehlerDifferential A B →L[B] M) ≃ₗ[B]
      continuousDerivationSubmodule A B M where
  toFun f := ⟨f.toLinearMap.compDer (D A B),
    mem_continuousDerivationSubmodule.mpr (f.continuous.comp (continuous_D h))⟩
  map_add' _ _ := Subtype.ext <| by ext b; simp
  map_smul' _ _ := Subtype.ext <| by ext b; simp
  invFun δ := δ.val.liftContinuousKaehlerDifferential
    (mem_continuousDerivationSubmodule.mp δ.property)
  left_inv _ :=
    have := isNoetherianType_of_isTopologicallyFiniteType (B := B) h
    hom_ext fun b ↦ Derivation.liftContinuousKaehlerDifferential_comp_D _ _ b
  right_inv δ :=
    Subtype.ext (δ.val.liftContinuousKaehlerDifferential_comp
      (mem_continuousDerivationSubmodule.mp δ.property))

/-- The underlying derivation of `continuousLinearMapEquivDerivation h f` is `f ∘ d`. -/
@[simp] theorem continuousLinearMapEquivDerivation_apply_coe
    (h : IsTopologicallyFiniteType (algebraMap A B))
    (f : ContinuousKaehlerDifferential A B →L[B] M) :
    ((continuousLinearMapEquivDerivation h f : continuousDerivationSubmodule A B M) :
      Derivation A B M) = f.toLinearMap.compDer (D A B) := (rfl)

/-- The inverse of `continuousLinearMapEquivDerivation` is
`Derivation.liftContinuousKaehlerDifferential`. -/
@[simp] theorem continuousLinearMapEquivDerivation_symm_apply
    (h : IsTopologicallyFiniteType (algebraMap A B))
    (δ : continuousDerivationSubmodule A B M) :
    (continuousLinearMapEquivDerivation h).symm δ =
      δ.val.liftContinuousKaehlerDifferential
        (mem_continuousDerivationSubmodule.mp δ.property) := (rfl)

/-- `continuousLinearMapEquivDerivation` sends `δ.liftContinuousKaehlerDifferential hδ` back to
`⟨δ, hδ⟩`. -/
@[simp] theorem continuousLinearMapEquivDerivation_lift
    (h : IsTopologicallyFiniteType (algebraMap A B)) (δ : Derivation A B M) (hδ : Continuous δ) :
    continuousLinearMapEquivDerivation h (δ.liftContinuousKaehlerDifferential hδ) =
      ⟨δ, mem_continuousDerivationSubmodule.mpr hδ⟩ :=
  Subtype.ext (δ.liftContinuousKaehlerDifferential_comp hδ)

end UniversalEquiv

end TauCeti.Huber.ContinuousKaehlerDifferential
