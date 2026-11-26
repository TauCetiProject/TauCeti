/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.ConormalMap
public import TauCeti.RingTheory.Huber.Kaehler.FiniteType

import TauCeti.RingTheory.Derivation.Quotient
import TauCeti.RingTheory.Huber.Kaehler.FiniteTarget

/-!
# Exact sequences for continuous differentials

This file proves Huber (1996), Proposition 1.6.3(i)–(ii), mirroring Mathlib's
`KaehlerDifferential.exact_mapBaseChange_map` and
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`:

* First fundamental sequence (Proposition 1.6.3(i)): `exact_mapBaseChange_mapTower` (via
  `exact_mapBaseChange_mapTower_of_isTopologicallyFiniteType_comp`).
* Conormal sequence (Proposition 1.6.3(ii)): `exact_kerCotangentToTensor_mapBaseChange` and
  `mapBaseChange_surjective`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Proposition 1.6.3(i)–(ii).
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

/-! ### First fundamental exact sequence (Huber 1996, Proposition 1.6.3(i)) -/

section FirstFundamentalSequenceOfComp

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C] [IsNoetherianType C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)]

/-- **First fundamental exact sequence from topological finite type of the composite**: when `A, C`
are Huber, `B, C` are complete Hausdorff nonarchimedean with `C` of noetherian type, `A → B` and
`B → C` are adic, and `A → C` is topologically of finite type,
`C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is exact. -/
theorem exact_mapBaseChange_mapTower_of_isTopologicallyFiniteType_comp
    (hAC : IsTopologicallyFiniteType (algebraMap A C)) :
    haveI : IsAdicHom (algebraMap A C) :=
      IsScalarTower.algebraMap_eq A B C ▸
        (inferInstance : IsAdicHom (algebraMap B C)).comp inferInstance
    Function.Exact (mapBaseChange A B C (IsAdicHom.continuous (inferInstance :
      IsAdicHom (algebraMap B C)))) (mapTower A B C) := by
  have : IsAdicHom (algebraMap A C) := IsScalarTower.algebraMap_eq A B C ▸
    (inferInstance : IsAdicHom (algebraMap B C)).comp inferInstance
  have hc := IsAdicHom.continuous (inferInstance : IsAdicHom (algebraMap B C))
  refine LinearMap.exact_iff.mpr (le_antisymm ?_
    (LinearMap.range_le_ker_iff.mpr (LinearMap.ext (mapTower_mapBaseChange A B C hc))))
  have : Module.Finite C (ContinuousKaehlerDifferential A C) := finite hAC
  let R := LinearMap.range (mapBaseChange A B C hc)
  let Q := ContinuousKaehlerDifferential A C ⧸ R
  let : TopologicalSpace Q := moduleTopology C Q; have : IsModuleTopology C Q := ⟨rfl⟩
  let : IsTopologicalAddGroup Q := IsModuleTopology.isTopologicalAddGroup C Q
  let : Module B Q := Module.compHom Q (algebraMap B C)
  have : IsScalarTower B C Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let δB : Derivation B C Q :=
    { toFun c := R.mkQ (D A C c), map_add' _ _ := by simp
      map_smul' b c := by
        rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz, map_add, map_smul, map_smul]
        have h0 : R.mkQ (D A C (algebraMap B C b)) = 0 :=
          (Submodule.Quotient.mk_eq_zero R).mpr ⟨1 ⊗ₜ[B] D A B b, by simp⟩
        rw [h0, smul_zero, add_zero, ← algebraMap_smul C b]
      map_one_eq_zero' := by simp, leibniz' _ _ := by simp [Derivation.leibniz] }
  have hδB : Continuous δB :=
    (IsModuleTopology.continuous_of_linearMap R.mkQ).comp (continuous_D hAC)
  have := isNoetherianType_of_isTopologicallyFiniteType (B := C) hAC
  have hs : (δB.liftContinuousKaehlerDifferentialOfFinite hδB).comp (mapTower A B C) = R.mkQ :=
    linearMap_ext fun c ↦ by simp; rfl
  intro ω hω
  have hq := (LinearMap.congr_fun hs ω).symm
  simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp hω, map_zero] at hq
  exact (Submodule.Quotient.mk_eq_zero R).mp hq

end FirstFundamentalSequenceOfComp

section FirstFundamentalSequence

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)]

/-- **Huber Proposition 1.6.3(i) (First fundamental exact sequence)**: for topologically finite
type homomorphisms `A → B` and `B → C` between Huber rings with `B, C` complete Hausdorff and `B`
of noetherian type, `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is exact. -/
theorem exact_mapBaseChange_mapTower
    (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (hBC : IsTopologicallyFiniteType (algebraMap B C)) :
    haveI : IsAdicHom (algebraMap A C) := IsScalarTower.algebraMap_eq A B C ▸
      (inferInstance : IsAdicHom (algebraMap B C)).comp inferInstance
    Function.Exact (mapBaseChange A B C (IsAdicHom.continuous (inferInstance :
      IsAdicHom (algebraMap B C)))) (mapTower A B C) :=
  haveI : IsAdicHom (algebraMap A C) := IsScalarTower.algebraMap_eq A B C ▸
    (inferInstance : IsAdicHom (algebraMap B C)).comp inferInstance
  haveI : IsNoetherianType C := .of_isTopologicallyFiniteType hBC
  exact_mapBaseChange_mapTower_of_isTopologicallyFiniteType_comp
    (IsScalarTower.algebraMap_eq A B C ▸ hBC.comp hAB)

end FirstFundamentalSequence

/-! ### Conormal exact sequence (Huber 1996, Proposition 1.6.3(ii)) -/

section MapBaseChangeSurjective

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- **Surjectivity in the conormal sequence** (Huber 1996, Proposition 1.6.3(ii)): when
`C ⊗̂_A C` is of noetherian type and the image of `B` topologically generates `C` over `A`,
`C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is surjective. -/
theorem mapBaseChange_surjective [IsNoetherianType (CompletedTensor A C C)]
    (hc : Continuous (algebraMap B C))
    (hdense : Dense (Algebra.adjoin A (Set.range (algebraMap B C)) : Set C)) :
    Function.Surjective (mapBaseChange A B C hc) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_image_D_eq_top hdense, Submodule.span_le]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  exact ⟨1 ⊗ₜ[B] D A B b, by simp⟩

end MapBaseChangeSurjective

section ConormalSequence

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
  [IsAdicHom (algebraMap A B)]

omit [IsHuberRing A] [IsHuberRing B] [UniformSpace C] [IsUniformAddGroup C]
  [NonarchimedeanRing C] [CompleteSpace C] [T0Space C] in
/-- Algebraic quotient derivation `C → (C ⊗[B] Ωᶜ[B⁄A]) ⧸ L` along a surjection `B → C`. -/
private noncomputable def conormalQuotientDerivation
    (hsurj : Function.Surjective (algebraMap B C))
    (L : Submodule C (C ⊗[B] ContinuousKaehlerDifferential A B))
    (hL : ∀ x ∈ RingHom.ker (algebraMap B C), (1 : C) ⊗ₜ[B] D A B x ∈ L) :
    {δ : Derivation A C ((C ⊗[B] ContinuousKaehlerDifferential A B) ⧸ L) //
      ∀ b : B, δ (algebraMap B C b) = L.mkQ (1 ⊗ₜ[B] D A B b)} := by
  let Q := (C ⊗[B] ContinuousKaehlerDifferential A B) ⧸ L
  let f : B →ₐ[A] C := IsScalarTower.toAlgHom A B C; let J : Ideal B := RingHom.ker f
  let e : (B ⧸ J) ≃ₐ[A] C := Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj
  letI : Module (B ⧸ J) Q := Module.compHom Q e.toRingHom
  have hsmul_e (x : B ⧸ J) (q : Q) : x • q = e x • q := rfl
  haveI : IsScalarTower B (B ⧸ J) Q := IsScalarTower.of_algebraMap_smul fun b q ↦ by
    rw [hsmul_e, Ideal.Quotient.algebraMap_eq,
      Ideal.quotientKerAlgEquivOfSurjective_mk (f := f) hsurj b]
    exact algebraMap_smul C b q
  let lB : ContinuousKaehlerDifferential A B →ₗ[B] Q :=
    (L.mkQ.restrictScalars B).comp (TensorProduct.mk B C (ContinuousKaehlerDifferential A B) 1)
  let dB := lB.compDer (D A B)
  let dQ := dB.liftQuotient J fun b hb ↦ (Submodule.Quotient.mk_eq_zero L).mpr (hL b hb)
  letI : Algebra C (B ⧸ J) := e.symm.toRingHom.toAlgebra
  haveI : IsScalarTower A C (B ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (e.symm.commutes a).symm
  haveI : IsScalarTower C (B ⧸ J) Q := IsScalarTower.of_algebraMap_smul fun c q ↦ by
    simp only [hsmul_e, RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, e.apply_symm_apply]
  have halg (c : C) : algebraMap C (B ⧸ J) c = e.symm c := rfl
  refine ⟨dQ.compAlgebraMap C, fun b ↦ ?_⟩
  have hfb : algebraMap B C b = f b := rfl
  rw [Derivation.compAlgebraMap_apply, hfb, halg,
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply (f := f) hsurj b]
  exact Derivation.liftQuotient_mk J dB _ b

/-- **Huber Proposition 1.6.3(ii) (Conormal exact sequence)**: when `A, B` are Huber with `B`
complete Hausdorff of noetherian type, `A → B` topologically of finite type, and `B → C` an open
quotient map into complete Hausdorff nonarchimedean `C`, the sequence
`J / J² → C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is exact for `J = ker(B → C)`. -/
theorem exact_kerCotangentToTensor_mapBaseChange [IsNoetherianType B]
    (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (hBC : IsOpenQuotientMap (algebraMap B C)) :
    haveI : IsAdicHom (algebraMap A C) :=
      IsScalarTower.algebraMap_eq A B C ▸ (IsAdicHom.of_isOpenQuotientMap hBC).comp inferInstance
    Function.Exact (kerCotangentToTensor A B C) (mapBaseChange A B C hBC.continuous) := by
  have : IsAdicHom (algebraMap A C) :=
    IsScalarTower.algebraMap_eq A B C ▸ (IsAdicHom.of_isOpenQuotientMap hBC).comp inferInstance
  intro z
  refine ⟨fun hz ↦ ?_,
    fun ⟨u, hu⟩ ↦ hu ▸ mapBaseChange_kerCotangentToTensor A B C hBC.continuous u⟩
  have : IsHuberRing C := .of_isOpenQuotientMap hBC
  have : IsNoetherianType C := .of_isOpenQuotientMap hBC
  have : Module.Finite B (ContinuousKaehlerDifferential A B) := finite hAB
  let L := (Submodule.orderIsoOfAlgebraMapSurjective hBC.surjective).symm
    (LinearMap.range (kerCotangentToTensor A B C))
  let Q := (C ⊗[B] ContinuousKaehlerDifferential A B) ⧸ L
  let : TopologicalSpace Q := moduleTopology C Q; have : IsModuleTopology C Q := ⟨rfl⟩
  let : IsTopologicalAddGroup Q := IsModuleTopology.isTopologicalAddGroup C Q
  have : ContinuousSMul B C := continuousSMul_of_algebraMap B C hBC.continuous
  have : ContinuousSMul B Q := IsScalarTower.continuousSMul C
  obtain ⟨δC, hδC_eq⟩ := conormalQuotientDerivation hBC.surjective L fun x hx ↦
    ⟨(RingHom.ker (algebraMap B C)).toCotangent ⟨x, hx⟩,
      kerCotangentToTensor_toCotangent A B C ⟨x, hx⟩⟩
  let lB : ContinuousKaehlerDifferential A B →ₗ[B] Q :=
    (L.mkQ.restrictScalars B).comp (TensorProduct.mk B C (ContinuousKaehlerDifferential A B) 1)
  have hδC : Continuous δC := hBC.isQuotientMap.continuous_iff.mpr <|
    ((IsModuleTopology.continuous_of_linearMap lB).comp (continuous_D hAB)).congr
      fun b ↦ (hδC_eq b).symm
  have := CompletedTensor.isNoetherianType_of_isTopologicallyFiniteType (B := B) hAB
  have hs : (δC.liftContinuousKaehlerDifferentialOfFinite hδC).comp
      (mapBaseChange A B C hBC.continuous) = L.mkQ :=
    linearMap_tensor_ext fun b ↦ by simp [hδC_eq]
  have hq := (LinearMap.congr_fun hs z).symm
  simp only [LinearMap.comp_apply, hz, map_zero] at hq
  exact (Submodule.Quotient.mk_eq_zero L).mp hq

end ConormalSequence

end TauCeti.Huber.ContinuousKaehlerDifferential
