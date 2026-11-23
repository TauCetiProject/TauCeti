/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Map

/-!
# Conormal map for continuous differentials

For a continuous homomorphism `B → C` of complete Hausdorff nonarchimedean `A`-algebras with
`A → B` adic and `J = ker(B → C)`, this file constructs the conormal map
`kerCotangentToTensor : J / J² →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` (adapted from Mathlib's
`KaehlerDifferential.kerCotangentToTensor`) and proves that its composition with
`mapBaseChange : C ⊗[B] Ωᶜ[B⁄A] →ₗ[C] Ωᶜ[C⁄A]` vanishes identically
(`mapBaseChange_kerCotangentToTensor`), without any finite-type or noetherian hypotheses.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Proposition 1.6.3(ii).
-/

public section

open TensorProduct

namespace TauCeti.Huber.ContinuousKaehlerDifferential

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

end TauCeti.Huber.ContinuousKaehlerDifferential
