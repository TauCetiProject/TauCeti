/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FixedField.FiberCount

/-!
# The fixed-field fibre of a cyclic generator

When `σ` generates the Galois group of `L/K`, its fixed field is `K`. At a prime with arithmetic
Frobenius `σ`, the relative Frobenius fibre over that fixed field consists of exactly one prime.
This is the generator case of the general fixed-field fibre count, including its specification of
the relative Frobenius as `σ` itself.

The calculation follows the cyclic fixed-field argument in J. Neukirch, *Algebraic Number
Theory*, Chapter VII, §13.
-/

public section

open IntermediateField
open scoped NumberField
open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Over a prime with Frobenius class `[σ]`, a cyclic generator `σ` gives exactly one prime of
its fixed field whose relative Frobenius in `L` is `σ`. -/
theorem fixedField_frobenius_fiber_card_of_generator (σ : L ≃ₐ[K] L)
    (hσ : Subgroup.zpowers σ = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ frobeniusPrimeSet K L (ConjClasses.mk σ)) :
    Nat.card {P : HeightOneSpectrum (𝓞 ↥(fixedField (Subgroup.zpowers σ))) //
      P.under (𝓞 K) = p ∧
        P ∈ frobeniusPrimeSet ↥(fixedField (Subgroup.zpowers σ)) L
          (ConjClasses.mk σ.toFixedFieldAlgEquiv)} = 1 := by
  have : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩
  have hcenter : σ ∈ Subgroup.center (L ≃ₐ[K] L) :=
    Subgroup.mem_center_iff.mpr fun τ ↦ IsCyclic.commGroup.mul_comm τ σ
  have hcard : Nat.card (ConjClasses.mk σ).carrier = 1 :=
    ConjClasses.ncard_carrier_mk_of_mem_center hcenter
  rw [fixedField_frobenius_fiber_card (ConjClasses.mk σ) σ
    ConjClasses.mem_carrier_mk p hp, hcard, one_mul,
    orderOf_eq_card_of_zpowers_eq_top hσ, Nat.div_self Nat.card_pos]

end NumberField.Chebotarev
