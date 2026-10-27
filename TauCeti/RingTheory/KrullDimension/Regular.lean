/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Krull dimension of a principal quotient

For a Noetherian ring, quotienting by an element in the Jacobson radical that lies outside every
minimal prime gives `dim (R ⧸ (x)) + 1 = dim R`. This is the ring form of Mathlib's
`Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson`. Applied to a
two-dimensional Noetherian local ring, it says that dividing out a non-zero-divisor of `𝔪`
leaves a curve, a ring of dimension one, and in a local domain, where the only minimal prime is
`0`, that applies to every nonzero element of `𝔪`.

Over a Noetherian ring, each element of the Jacobson radical of the annihilator of a finite
module lowers the dimension of its support by at most one, so `dim M ≤ dim M ⧸ (r₁, …, rₙ) M + n`
for such `r₁, …, rₙ` (`Module.supportDim_le_supportDim_quotient_add_length_of_mem_jacobson`), in
particular for `r₁, …, rₙ ∈ 𝔪` over a local ring
(`Module.supportDim_le_supportDim_quotient_add_length`). This is the inequality
that the regular case `Module.supportDim_add_length_eq_supportDim_of_isRegular` turns into an
equality.
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

/-- **A general hyperplane section of a two-dimensional local ring is a curve of dimension one.**
In a Noetherian local ring `(R, 𝔪)` of Krull dimension two, the quotient by an element
`f ∈ 𝔪` that is a non-zero-divisor has dimension one:
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` drops the dimension by one along such
an `f`. A nonzero element of a local domain is a non-zero-divisor, so in a local domain a nonzero
`f ∈ 𝔪` does so; in particular a parameter `f ∈ 𝔪 \ 𝔪²` of a regular local ring, which is nonzero,
does so, and for a regular local ring this is the local form of the fact that a Cartier divisor on
a regular surface is cut out by a single equation. -/
theorem ringKrullDim_quotient_span_singleton_eq_one {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (hd : ringKrullDim R = 2) {f : R} (hf : f ∈ maximalIdeal R)
    (hfnd : f ∈ nonZeroDivisors R) : ringKrullDim (R ⧸ span {f}) = 1 := by
  -- a nonzero divisor lowers the dimension by one, `hf` placing it in the maximal ideal of the
  -- local ring `R`
  have hkey : ringKrullDim (R ⧸ span {f}) + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hfnd) hf
  rw [hd, ← Nat.cast_two, Nat.cast_succ, ENat.WithBot.add_one_cancel] at hkey
  exact hkey

end TauCeti

namespace Module

open Ideal Pointwise _root_.IsLocalRing

/-- Over a Noetherian ring, dividing a finite module `M` by elements `r₁, …, rₙ` of the Jacobson
radical of its annihilator lowers the dimension of its support by at most `n`:
`dim M ≤ dim M ⧸ (r₁, …, rₙ) M + n`. -/
@[stacks 0B52 "the second inequality, iterated"]
theorem supportDim_le_supportDim_quotient_add_length_of_mem_jacobson {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hrs : ∀ r ∈ rs, r ∈ (annihilator R M).jacobson) :
    supportDim R M ≤ supportDim R (M ⧸ ofList rs • (⊤ : Submodule R M)) + rs.length := by
  induction rs generalizing M with
  | nil =>
    rw [ofList_nil, Submodule.bot_smul]
    simpa using (supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)).ge
  | cons x rs ih =>
    rw [supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs),
      List.length_cons, Nat.cast_add_one, ← add_assoc]
    refine (supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson
      (hrs x List.mem_cons_self)).trans ?_
    gcongr
    -- The annihilator only grows on passing to the quotient `M ⧸ x M`.
    have hann : annihilator R M ≤ annihilator R (QuotSMulTop x M) :=
      LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)
    exact ih fun r hr ↦ jacobson_mono hann (hrs r (List.mem_cons_of_mem x hr))

/-- Over a Noetherian local ring, dividing a finite module by `r₁, …, rₙ ∈ 𝔪` lowers the dimension
of its support by at most `n`: `dim M ≤ dim M ⧸ (r₁, …, rₙ) M + n`. -/
@[stacks 0B52 "the second inequality, iterated"]
theorem supportDim_le_supportDim_quotient_add_length {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    supportDim R M ≤ supportDim R (M ⧸ ofList rs • (⊤ : Submodule R M)) + rs.length :=
  supportDim_le_supportDim_quotient_add_length_of_mem_jacobson rs
    fun r hr ↦ maximalIdeal_le_jacobson _ (hrs r hr)

end Module
