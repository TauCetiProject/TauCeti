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
`Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson`. Applied to a
two-dimensional Noetherian local domain, where the only minimal prime is `0`, it says that
dividing out an element of `𝔪 \ 𝔪²` leaves a curve, a ring of dimension one.
-/

public section

namespace TauCeti

open Ideal Pointwise _root_.IsLocalRing

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

/-- **A general hyperplane section of a two-dimensional local domain is a curve of dimension one.**
In a Noetherian local domain `(R, 𝔪)` of Krull dimension two, an element `f ∈ 𝔪 \ 𝔪²` is
nonzero, hence outside the only minimal prime of `R`, and lies in the Jacobson radical `𝔪`, so
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes_of_mem_jacobson`
drops the dimension by one. For a regular local ring this is the local form of the fact that a
Cartier divisor on a regular surface is cut out by a single equation. -/
theorem ringKrullDim_quot_span_singleton_eq_one {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsDomain R] (hd : ringKrullDim R = 2) {f : R} (hf : f ∈ maximalIdeal R)
    (hf2 : f ∉ maximalIdeal R ^ 2) : ringKrullDim (R ⧸ span {f}) = 1 := by
  -- a nonzero divisor lowers the dimension by one, and the element `f` in particular lies in
  -- the Jacobson radical of the local ring `R`, being in its maximal ideal by `hf`
  have hkey :=
   ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes_of_mem_jacobson
      (x := f)
      (by
        -- the only minimal prime of the domain `R` is `0`, and `f ≠ 0` as `f ∉ 𝔪²`
        rw [IsDomain.minimalPrimes_eq_singleton_bot R]
        intro p hp
        simp only [Set.mem_singleton_iff] at hp
        rw [hp]
        intro hf0
        have hf1 : f = 0 := (Submodule.mem_bot R).mp hf0
        subst hf1
        exact hf2 (zero_mem _))
      (by rwa [IsLocalRing.ringJacobson_eq_maximalIdeal R])
  rw [hd, ← Nat.cast_two, Nat.cast_succ, ENat.WithBot.add_one_cancel] at hkey
  exact hkey

end TauCeti
