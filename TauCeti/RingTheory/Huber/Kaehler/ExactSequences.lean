/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Map
public import TauCeti.RingTheory.Huber.Kaehler.UniversalProperty

import TauCeti.RingTheory.Derivation.Quotient
import TauCeti.RingTheory.Huber.NoetherianType.Quotient
import TauCeti.RingTheory.Huber.TensorProduct.Quotient.Basic
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Exact sequences for continuous differentials

This file establishes the first fundamental exact sequence and the conormal exact sequence for
continuous differentials `Ωᶜ[B⁄A]` (Huber 1996, Proposition 1.6.3(i)–(ii)), mirroring Mathlib's
`KaehlerDifferential.exact_mapBaseChange_map` and
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`:

* **First fundamental sequence (Proposition 1.6.3(i))**: `exact_mapBaseChange_mapTower` (via
  `exact_mapBaseChange_mapTower_of_isTopologicallyFiniteType_comp`) and `mapTower_surjective`.
* **Conormal sequence (Proposition 1.6.3(ii))**: `kerToTensor`, `kerCotangentToTensor`,
  `exact_kerCotangentToTensor_mapBaseChange`, `mapBaseChange_surjective_of_isOpenQuotientMap`
  (without finite-type or noetherian hypotheses), and `mapBaseChange_surjective`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Proposition 1.6.3(i)–(ii).
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

section ConormalMap

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [IsAdicHom (algebraMap A B)]

/-- The `B`-linear map `J →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` for `J = ker(B → C)`, sending `x ↦ 1 ⊗ₜ d x`,
adapted from Mathlib's `KaehlerDifferential.kerToTensor`. -/
noncomputable def kerToTensor :
    RingHom.ker (algebraMap B C) →ₗ[B] C ⊗[B] ContinuousKaehlerDifferential A B where
  toFun x := 1 ⊗ₜ[B] D A B x.1
  map_add' x y := by simp [tmul_add]
  map_smul' b x := by
    simp only [SetLike.val_smul, smul_eq_mul, Derivation.leibniz, tmul_add, tmul_smul, smul_tmul',
      ← Algebra.algebraMap_eq_smul_one, RingHom.mem_ker.mp x.2, zero_tmul, add_zero,
      RingHom.id_apply]

/-- Evaluating `kerToTensor` on `x ∈ ker(B → C)` yields `1 ⊗ₜ d x`. -/
@[simp]
theorem kerToTensor_apply (x : RingHom.ker (algebraMap B C)) :
    kerToTensor A B C x = 1 ⊗ₜ[B] D A B x.1 := (rfl)

/-- The conormal map `J / J² →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` for `J = ker(B → C)` (Huber 1996,
Proposition 1.6.3(ii)), adapted from Mathlib's `KaehlerDifferential.kerCotangentToTensor`. -/
noncomputable def kerCotangentToTensor :
    (RingHom.ker (algebraMap B C)).Cotangent →ₗ[B] C ⊗[B] ContinuousKaehlerDifferential A B :=
  Ideal.Cotangent.lift (kerToTensor A B C) fun x y ↦ by
    simp only [kerToTensor_apply, MulMemClass.coe_mul, Derivation.leibniz, tmul_add, ← smul_tmul,
      ← Algebra.algebraMap_eq_smul_one, RingHom.mem_ker.mp x.2, RingHom.mem_ker.mp y.2, zero_tmul,
      add_zero]

/-- Evaluating `kerCotangentToTensor` on the cotangent class of `x ∈ ker(B → C)` gives
`1 ⊗ₜ d x`. -/
@[simp]
theorem kerCotangentToTensor_toCotangent (x : RingHom.ker (algebraMap B C)) :
    kerCotangentToTensor A B C ((RingHom.ker (algebraMap B C)).toCotangent x) =
      1 ⊗ₜ[B] D A B x.1 := by
  rw [kerCotangentToTensor, Ideal.Cotangent.lift_toCotangent, kerToTensor_apply]

/-- The composite `J / J² → C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` vanishes identically. -/
@[simp]
theorem mapBaseChange_kerCotangentToTensor [Algebra A C] [IsScalarTower A B C]
    [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
    [IsAdicHom (algebraMap A C)]
    (hc : Continuous (algebraMap B C)) (u : (RingHom.ker (algebraMap B C)).Cotangent) :
    mapBaseChange A B C hc (kerCotangentToTensor A B C u) = 0 := by
  obtain ⟨x, rfl⟩ := (RingHom.ker (algebraMap B C)).toCotangent_surjective u
  rw [kerCotangentToTensor_toCotangent, mapBaseChange_tmul_D, RingHom.mem_ker.mp x.2,
    map_zero, smul_zero]

end ConormalMap

/-! ### First fundamental exact sequence (Huber 1996, Proposition 1.6.3(i)) -/

section MapTowerSurjective

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C] [IsNoetherianType C]
  [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap B C)]

/-- **Surjectivity in the first fundamental sequence** (Huber 1996, Proposition 1.6.3(i)): when
`B, C` are Huber with `C` complete Hausdorff of noetherian type and `B → C` is topologically of
finite type, `Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is surjective. -/
theorem mapTower_surjective (hBC : IsTopologicallyFiniteType (algebraMap B C)) :
    Function.Surjective (mapTower A B C) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_derivation hBC, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  exact ⟨D A C c, mapTower_D A B C c⟩

end MapTowerSurjective

section FirstFundamentalSequenceOfComp

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C] [IsNoetherianType C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)] [IsAdicHom (algebraMap A C)]

/-- **First fundamental exact sequence from topological finite type of the composite**: when `A, C`
are Huber, `B, C` are complete Hausdorff nonarchimedean with `C` of noetherian type, `B → C` is
continuous, and `A → C` is topologically of finite type, `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is
exact. -/
theorem exact_mapBaseChange_mapTower_of_isTopologicallyFiniteType_comp
    (hc : Continuous (algebraMap B C)) (hAC : IsTopologicallyFiniteType (algebraMap A C)) :
    Function.Exact (mapBaseChange A B C hc) (mapTower A B C) := by
  refine LinearMap.exact_iff.mpr (le_antisymm ?_
    (LinearMap.range_le_ker_iff.mpr (LinearMap.ext (mapTower_mapBaseChange A B C hc))))
  have : Module.Finite C (ContinuousKaehlerDifferential A C) := finite hAC
  let R : Submodule C (ContinuousKaehlerDifferential A C) :=
    LinearMap.range (mapBaseChange A B C hc)
  let Q := ContinuousKaehlerDifferential A C ⧸ R
  let : TopologicalSpace Q := moduleTopology C Q
  have : IsModuleTopology C Q := ⟨rfl⟩
  let : IsTopologicalAddGroup Q := IsModuleTopology.isTopologicalAddGroup C Q
  let : Module B Q := Module.compHom Q (algebraMap B C)
  have : IsScalarTower B C Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let δB : Derivation B C Q :=
    { toFun c := R.mkQ (D A C c)
      map_add' _ _ := by simp
      map_smul' b c := by
        rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz, map_add, map_smul, map_smul]
        have h0 : R.mkQ (D A C (algebraMap B C b)) = 0 :=
          (Submodule.Quotient.mk_eq_zero R).mpr ⟨1 ⊗ₜ[B] D A B b, by simp⟩
        rw [h0, smul_zero, add_zero, ← algebraMap_smul C b]
      map_one_eq_zero' := by simp
      leibniz' _ _ := by simp [Derivation.leibniz] }
  have hδB : Continuous δB :=
    (IsModuleTopology.continuous_of_linearMap R.mkQ).comp (continuous_D hAC)
  let s : ContinuousKaehlerDifferential B C →ₗ[C] Q := liftOfFinite δB hδB
  have hs : s.comp (mapTower A B C) = R.mkQ := linearMap_ext hAC fun c ↦ by
    simp only [LinearMap.comp_apply, mapTower_D, s, liftOfFinite_D]; rfl
  intro ω hω
  have h0 : R.mkQ ω = 0 := by rw [← hs, LinearMap.comp_apply, LinearMap.mem_ker.mp hω, map_zero]
  exact (Submodule.Quotient.mk_eq_zero R).mp h0

end FirstFundamentalSequenceOfComp

section FirstFundamentalSequence

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)] [IsAdicHom (algebraMap A C)]

/-- **Huber Proposition 1.6.3(i) (First fundamental exact sequence)**: for topologically finite
type homomorphisms `A → B` and `B → C` between Huber rings with `B, C` complete Hausdorff and `B`
of noetherian type, `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is exact. -/
theorem exact_mapBaseChange_mapTower
    (hc : Continuous (algebraMap B C))
    (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (hBC : IsTopologicallyFiniteType (algebraMap B C)) :
    Function.Exact (mapBaseChange A B C hc) (mapTower A B C) := by
  have : IsNoetherianType C := .of_isTopologicallyFiniteType hBC
  have hAC : IsTopologicallyFiniteType (algebraMap A C) :=
    IsScalarTower.algebraMap_eq A B C ▸ hBC.comp hAB
  exact exact_mapBaseChange_mapTower_of_isTopologicallyFiniteType_comp hc hAC

end FirstFundamentalSequence

/-! ### Conormal exact sequence (Huber 1996, Proposition 1.6.3(ii)) -/

section MapBaseChangeOpenQuotient

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
  [IsAdicHom (algebraMap A B)]

/-- **Surjectivity in the conormal sequence for open quotients** (Huber 1996,
Proposition 1.6.3(ii)): when `B → C` is an open quotient map between complete Hausdorff
nonarchimedean rings with `A → B` adic, `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is surjective, with no
finite-type or noetherian hypotheses. -/
theorem mapBaseChange_surjective_of_isOpenQuotientMap
    (hBC : IsOpenQuotientMap (algebraMap B C)) :
    haveI : IsAdicHom (algebraMap A C) := by
      obtain ⟨_, Q, _, _⟩ := (inferInstance : IsAdicHom (algebraMap A B)).exists_pairOfDefinition
      have : IsHuberRing B := ⟨⟨Q⟩⟩
      exact IsScalarTower.algebraMap_eq A B C ▸
        (IsAdicHom.of_isOpenQuotientMap hBC).comp inferInstance
    Function.Surjective (mapBaseChange A B C hBC.continuous) := by
  have : IsAdicHom (algebraMap A C) := by
    obtain ⟨_, Q, _, _⟩ := (inferInstance : IsAdicHom (algebraMap A B)).exists_pairOfDefinition
    have : IsHuberRing B := ⟨⟨Q⟩⟩
    exact IsScalarTower.algebraMap_eq A B C ▸
      (IsAdicHom.of_isOpenQuotientMap hBC).comp inferInstance
  have hBC_comp : (algebraMap B C).comp (algebraMap A B) = algebraMap A C := by
    ext a; exact (IsScalarTower.algebraMap_apply A B C a).symm
  let F := CompletedTensor.map (RingHom.id A) (algebraMap B C) (algebraMap B C)
    hBC_comp hBC_comp hBC.continuous hBC.continuous
  have hF : Function.Surjective F :=
    (CompletedTensor.isOpenQuotientMap_map hBC_comp hBC_comp hBC hBC).surjective
  have hmul : (algebraMap B C).comp (mulRingHom A B) = (mulRingHom A C).comp F :=
    CompletedTensor.hom_ext (hBC.continuous.comp (continuous_mulRingHom A B))
      ((continuous_mulRingHom A C).comp (CompletedTensor.continuous_map ..))
      (by ext r; simp [F]) (by ext r; simp [F])
  intro ω
  obtain ⟨⟨y, hy⟩, rfl⟩ := fromIdeal_surjective A C ω
  obtain ⟨x, hxF⟩ := hF y
  let b := mulRingHom A B x
  have hb : algebraMap B C b = 0 := by
    rw [← RingHom.comp_apply, RingHom.congr_fun hmul x, RingHom.comp_apply, hxF,
      mem_ideal_iff.mp hy]
  refine ⟨1 ⊗ₜ[B] fromIdeal A B ⟨x - inl A B B b, mem_ideal_iff.mpr (by simp [b])⟩, ?_⟩
  simp only [mapBaseChange_tmul, one_smul, mapSemilinear_fromIdeal]
  congr 1; ext; change F (x - inl A B B b) = y; simp [F, hxF, hb]

end MapBaseChangeOpenQuotient

section MapBaseChangeSurjective

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C] [IsNoetherianType C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- **Surjectivity in the conormal sequence** (Huber 1996, Proposition 1.6.3(ii)): when `A, C` are
Huber, `B, C` complete Hausdorff nonarchimedean with `C` of noetherian type, `B → C` continuously
surjective, and `A → C` topologically of finite type, `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is surjective. -/
theorem mapBaseChange_surjective
    (hc : Continuous (algebraMap B C)) (hsurj : Function.Surjective (algebraMap B C))
    (hAC : IsTopologicallyFiniteType (algebraMap A C)) :
    Function.Surjective (mapBaseChange A B C hc) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_derivation hAC, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  obtain ⟨b, rfl⟩ := hsurj c
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
/-- Algebraic quotient derivation `C → (C ⊗[B] Ωᶜ[B⁄A]) ⧸ L` along a surjection `B → C`, sending
the image of `b` to the class of `1 ⊗ₜ d b`. -/
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
  let dB : Derivation A B Q := lB.compDer (D A B)
  let dQ : Derivation A (B ⧸ J) Q :=
    dB.liftQuotient J fun b hb ↦ (Submodule.Quotient.mk_eq_zero L).mpr (hL b hb)
  letI : Algebra C (B ⧸ J) := e.symm.toRingHom.toAlgebra
  haveI : IsScalarTower A C (B ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (e.symm.commutes a).symm
  haveI : IsScalarTower C (B ⧸ J) Q := IsScalarTower.of_algebraMap_smul fun c q ↦ by
    simp only [hsmul_e, RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, e.apply_symm_apply]
  refine ⟨dQ.compAlgebraMap C, fun b ↦ ?_⟩
  change dQ (e.symm (f b)) = _
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply (f := f) hsurj b]
  exact Derivation.liftQuotient_mk J dB _ b

/-- **Huber Proposition 1.6.3(ii) (Conormal exact sequence)**: when `A, B` are Huber with `B`
complete Hausdorff of noetherian type, `A → B` topologically of finite type, and `B → C` an open
quotient map into complete Hausdorff nonarchimedean `C`, `J / J² → C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is
exact for `J = ker(B → C)`. -/
theorem exact_kerCotangentToTensor_mapBaseChange [IsNoetherianType B]
    (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (hBC : IsOpenQuotientMap (algebraMap B C)) :
    haveI : IsAdicHom (algebraMap A C) :=
      IsScalarTower.algebraMap_eq A B C ▸ (IsAdicHom.of_isOpenQuotientMap hBC).comp inferInstance
    Function.Exact (kerCotangentToTensor A B C) (mapBaseChange A B C hBC.continuous) := by
  have : IsAdicHom (algebraMap A C) :=
    IsScalarTower.algebraMap_eq A B C ▸ (IsAdicHom.of_isOpenQuotientMap hBC).comp inferInstance
  intro z
  refine ⟨fun hz ↦ ?_, fun ⟨u, hu⟩ ↦ hu ▸ mapBaseChange_kerCotangentToTensor A B C hBC.continuous u⟩
  have : IsHuberRing C := .of_isOpenQuotientMap hBC
  have : IsNoetherianType C := .of_isOpenQuotientMap hBC
  have : Module.Finite B (ContinuousKaehlerDifferential A B) := finite hAB
  let L : Submodule C (C ⊗[B] ContinuousKaehlerDifferential A B) :=
    (Submodule.orderIsoOfAlgebraMapSurjective hBC.surjective).symm
      (LinearMap.range (kerCotangentToTensor A B C))
  let Q := (C ⊗[B] ContinuousKaehlerDifferential A B) ⧸ L
  let : TopologicalSpace Q := moduleTopology C Q
  have : IsModuleTopology C Q := ⟨rfl⟩
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
  let s : ContinuousKaehlerDifferential A C →ₗ[C] Q := liftOfFinite δC hδC
  have hs : s.comp (mapBaseChange A B C hBC.continuous) = L.mkQ :=
    linearMap_tensor_ext hAB fun b ↦ by
      simp only [LinearMap.comp_apply, mapBaseChange_tmul_D, one_smul, s, liftOfFinite_D, hδC_eq]
  have h0 : L.mkQ z = 0 := by rw [← hs, LinearMap.comp_apply, hz, map_zero]
  exact (Submodule.Quotient.mk_eq_zero L).mp h0

end ConormalSequence

end TauCeti.Huber.ContinuousKaehlerDifferential
