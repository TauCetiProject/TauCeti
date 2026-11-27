/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Map

import TauCeti.RingTheory.Huber.TensorProduct.Quotient.Basic

/-!
# Conormal map for continuous differentials

For a continuous homomorphism `B → C` of complete Hausdorff nonarchimedean `A`-algebras with
`A → B` adic and `J = ker(B → C)`, this file constructs the conormal map
`kerCotangentToTensor : J / J² →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` (adapted from Mathlib's
`KaehlerDifferential.kerCotangentToTensor`), proves that its composition with
`mapBaseChange : C ⊗[B] Ωᶜ[B⁄A] →ₗ[C] Ωᶜ[C⁄A]` vanishes identically
(`mapBaseChange_kerCotangentToTensor`), and shows that `mapBaseChange` is surjective when `B → C`
is an open quotient map (`mapBaseChange_surjective_of_isOpenQuotientMap`), without any finite-type
or noetherian hypotheses.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Proposition 1.6.3(ii).
-/

public section

open TensorProduct

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

section ConormalMap

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [IsAdicHom (algebraMap A B)]

/-- The `B`-linear map `J →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` for `J = ker(B → C)`, sending `x ↦ 1 ⊗ₜ d x`
(adapted from Mathlib's `KaehlerDifferential.kerToTensor`). -/
noncomputable def kerToTensor :
    RingHom.ker (algebraMap B C) →ₗ[B] C ⊗[B] ContinuousKaehlerDifferential A B where
  toFun x := 1 ⊗ₜ[B] D A B x.val
  map_add' x y := by simp [tmul_add]
  map_smul' b x := by
    simp only [SetLike.val_smul, smul_eq_mul, Derivation.leibniz, tmul_add, tmul_smul, smul_tmul',
      ← Algebra.algebraMap_eq_smul_one, RingHom.mem_ker.mp x.property, zero_tmul, add_zero,
      RingHom.id_apply]

/-- Evaluating `kerToTensor` on `x ∈ ker(B → C)` yields `1 ⊗ₜ d x`. -/
@[simp] theorem kerToTensor_apply (x : RingHom.ker (algebraMap B C)) :
    kerToTensor A B C x = 1 ⊗ₜ[B] D A B x.val := (rfl)

/-- The conormal map `J / J² →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` for `J = ker(B → C)` (Huber 1996,
Proposition 1.6.3(ii)), adapted from Mathlib's `KaehlerDifferential.kerCotangentToTensor`. -/
noncomputable def kerCotangentToTensor :
    (RingHom.ker (algebraMap B C)).Cotangent →ₗ[B] C ⊗[B] ContinuousKaehlerDifferential A B :=
  Ideal.Cotangent.lift (kerToTensor A B C) fun x y ↦ by
    simp only [kerToTensor_apply, MulMemClass.coe_mul, Derivation.leibniz, tmul_add, ← smul_tmul,
      ← Algebra.algebraMap_eq_smul_one, RingHom.mem_ker.mp x.property,
      RingHom.mem_ker.mp y.property, zero_tmul, add_zero]

/-- Evaluating `kerCotangentToTensor` on the cotangent class of `x ∈ ker(B → C)` gives
`1 ⊗ₜ d x`. -/
@[simp] theorem kerCotangentToTensor_toCotangent (x : RingHom.ker (algebraMap B C)) :
    kerCotangentToTensor A B C ((RingHom.ker (algebraMap B C)).toCotangent x) =
      1 ⊗ₜ[B] D A B x.val := by
  rw [kerCotangentToTensor, Ideal.Cotangent.lift_toCotangent, kerToTensor_apply]

/-- The composite `J / J² → C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` vanishes identically. -/
@[simp] theorem mapBaseChange_kerCotangentToTensor [Algebra A C] [IsScalarTower A B C]
    [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
    [IsAdicHom (algebraMap A C)]
    (hc : Continuous (algebraMap B C)) (u : (RingHom.ker (algebraMap B C)).Cotangent) :
    mapBaseChange A B C hc (kerCotangentToTensor A B C u) = 0 := by
  obtain ⟨x, rfl⟩ := (RingHom.ker (algebraMap B C)).toCotangent_surjective u
  rw [kerCotangentToTensor_toCotangent, mapBaseChange_tmul_D, RingHom.mem_ker.mp x.property,
    map_zero, smul_zero]

end ConormalMap

/-- **Surjectivity in the conormal sequence for open quotients** (Huber 1996,
Proposition 1.6.3(ii)): when `B → C` is an open quotient map between complete Hausdorff
nonarchimedean rings with `A → B` adic, `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is surjective, with no
finite-type or noetherian hypotheses. -/
theorem mapBaseChange_surjective_of_isOpenQuotientMap
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [TopologicalSpace A] [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B]
    [NonarchimedeanRing B] [CompleteSpace B] [T0Space B] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C] [T0Space C] [IsAdicHom (algebraMap A B)]
    (hBC : IsOpenQuotientMap (algebraMap B C)) :
    haveI : IsAdicHom (algebraMap A C) :=
      haveI : IsHuberRing B :=
        ⟨⟨(inferInstance : IsAdicHom (algebraMap A B)).exists_pairOfDefinition.choose_spec.choose⟩⟩
      IsScalarTower.algebraMap_eq A B C ▸ (IsAdicHom.of_isOpenQuotientMap hBC).comp inferInstance
    Function.Surjective (mapBaseChange A B C hBC.continuous) := by
  have : IsAdicHom (algebraMap A C) :=
    haveI : IsHuberRing B :=
      ⟨⟨(inferInstance : IsAdicHom (algebraMap A B)).exists_pairOfDefinition.choose_spec.choose⟩⟩
    IsScalarTower.algebraMap_eq A B C ▸ (IsAdicHom.of_isOpenQuotientMap hBC).comp inferInstance
  have hBC_comp : (algebraMap B C).comp (algebraMap A B) = algebraMap A C := by
    ext a; exact (IsScalarTower.algebraMap_apply A B C a).symm
  have hF := (CompletedTensor.isOpenQuotientMap_map hBC_comp hBC_comp hBC hBC).surjective
  intro ω
  obtain ⟨⟨y, hy⟩, rfl⟩ := fromIdeal_surjective A C ω
  obtain ⟨x, hxF⟩ := hF y
  let b := mulRingHom A B x
  have hb : algebraMap B C b = 0 := by
    rw [← CompletedTensor.mulRingHom_map (RingHom.id A) (algebraMap B C) hBC_comp hBC.continuous x,
      hxF, mem_ideal_iff.mp hy]
  refine ⟨1 ⊗ₜ[B] fromIdeal A B ⟨x - inl A B B b, mem_ideal_iff.mpr (by simp [b])⟩, ?_⟩
  simp only [mapBaseChange_tmul, one_smul, mapSemilinear_fromIdeal]
  have hval : CompletedTensor.map (RingHom.id A) (algebraMap B C) (algebraMap B C)
      hBC_comp hBC_comp hBC.continuous hBC.continuous (x - inl A B B b) = y := by
    rw [map_sub, CompletedTensor.map_inl, hb, map_zero, sub_zero, hxF]
  exact congrArg (fromIdeal A C) (Subtype.ext hval)

end TauCeti.Huber.ContinuousKaehlerDifferential
