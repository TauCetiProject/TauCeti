/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Krull dimension of a principal quotient

For a Noetherian ring, quotienting by an element in the Jacobson radical that lies outside every
minimal prime gives `dim (R ⧸ (x)) + 1 = dim R`. This is the ring form of Mathlib's
`Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson`.
-/

public section

namespace TauCeti

open Ideal Pointwise

/-- In a Noetherian ring, for `x` in the Jacobson radical outside every minimal prime,
`dim R ⧸ (x) + 1 = dim R`. -/
@[stacks 0B52 "the equality case"]
theorem
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes_of_mem_jacobson
    {R : Type*} [CommRing R] [IsNoetherianRing R] {x : R}
    (hmin : ∀ p ∈ minimalPrimes R, x ∉ p) (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h : span {x} = x • (⊤ : Ideal R) := by simp [← Submodule.ideal_span_singleton_smul]
  have hann : Module.annihilator R R = ⊥ :=
    Module.annihilator_eq_bot.mpr ((faithfulSMul_iff_algebraMap_injective R R).mpr fun _ _ h ↦ h)
  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R h).toRingEquiv,
    ← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  exact Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson
    (by rwa [hann]) ((Module.annihilator R R).ringJacobson_le_jacobson hx)

end TauCeti
