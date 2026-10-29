/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Associated primes, dimension, and quotients by a regular element

Facts about the associated primes of a module `M` over a commutative ring `R`. The first two are
used to bound the depth of `M` by the dimensions `dim (R ⧸ p)` of its associated primes `p`:

* `IsAssociatedPrime.ringKrullDim_quotient_le_supportDim`: for an associated prime `p` of `M`, the
  dimension of `R ⧸ p` is at most the dimension of the support of `M`.
* `IsAssociatedPrime.exists_le_isAssociatedPrime_quotSMulTop`: if `R` is Noetherian, `M` is
  finite, and `x` is `M`-regular and lies in the Jacobson radical of the annihilator of `M`, then
  every associated prime of `M` lies in an associated prime of `M ⧸ x M`. This comes from
  Nakayama's lemma applied to the elements of `M` killed by `p`.

A separate fact describes the associated primes of a reduced ring:

* `IsAssociatedPrime.mem_minimalPrimes_of_isReduced`: every associated prime of a reduced ring is
  a minimal prime.

## References

* H. Matsumura, *Commutative Ring Theory*, proof of Theorem 17.2.
-/

public section

open Pointwise

section CommSemiring

variable {R : Type*} [CommSemiring R] {p : Ideal R}

/-- Every associated prime of a reduced ring is a minimal prime: an associated prime is the
radical of the annihilator of some `x ≠ 0`, so it lies in a minimal prime that does not contain
`x`. -/
theorem IsAssociatedPrime.mem_minimalPrimes_of_isReduced [IsReduced R]
    (hp : IsAssociatedPrime p R) : p ∈ minimalPrimes R := by
  obtain ⟨hp, x, rfl⟩ := hp
  have hx0 : x ≠ 0 := fun h ↦ hp.ne_top (by simp [h])
  obtain ⟨q, hq, hxq⟩ : ∃ q ∈ minimalPrimes R, x ∉ q := by
    by_contra! h
    have hx : x ∈ nilradical R := by
      rw [nilradical, ← Ideal.sInf_minimalPrimes]
      exact Submodule.mem_sInf.2 h
    simp [nilradical_eq_zero, hx0] at hx
  have hle : (⊥ : Submodule R R).colon {x} ≤ q := fun r hr ↦ by
    refine (hq.1.1.mem_or_mem ?_).resolve_right hxq
    rw [← smul_eq_mul, (Submodule.mem_bot R).1 (Submodule.mem_colon_singleton.1 hr)]
    exact q.zero_mem
  have hle' := hq.1.1.radical_le_iff.2 hle
  rw [le_antisymm hle' (hq.2 ⟨hp, bot_le⟩ hle')]
  exact hq

end CommSemiring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Ideal R}

namespace IsAssociatedPrime

/-- The quotient by an associated prime of `M` has dimension at most the dimension of the support
of `M`: every prime containing an associated prime lies in the support. -/
theorem ringKrullDim_quotient_le_supportDim (hp : IsAssociatedPrime p M) :
    ringKrullDim (R ⧸ p) ≤ Module.supportDim R M := by
  obtain ⟨-, z, rfl⟩ := hp
  rw [ringKrullDim_quotient, Module.supportDim]
  refine Order.krullDim_le_of_strictMono (fun q ↦ ⟨q.1,
    Module.mem_support_iff_exists_annihilator.2 ⟨z, ?_⟩⟩) fun _ _ h ↦ h
  rw [← Submodule.bot_colon']
  exact Ideal.le_radical.trans (SetLike.coe_subset_coe.1 ((PrimeSpectrum.mem_zeroLocus _ _).1 q.2))

/-- Let `M` be a finite module over a Noetherian ring and `x` an `M`-regular element of the
Jacobson radical of the annihilator of `M`. Every associated prime of `M` is contained in an
associated prime of `M ⧸ x M`. -/
theorem exists_le_isAssociatedPrime_quotSMulTop [IsNoetherianRing R] [Module.Finite R M] {x : R}
    (hp : IsAssociatedPrime p M) (reg : IsSMulRegular M x)
    (hx : x ∈ (Module.annihilator R M).jacobson) :
    ∃ q, IsAssociatedPrime q (QuotSMulTop x M) ∧ p ≤ q := by
  let N := Submodule.torsionBySet R M p
  -- Some element of `M` killed by `p` does not lie in `x M`: otherwise `N ≤ x N`, since `x` is
  -- `M`-regular, and Nakayama's lemma would force `N = 0`.
  obtain ⟨w, hwN, hw⟩ : ∃ w ∈ N, w ∉ x • (⊤ : Submodule R M) := by
    by_contra! h
    have hle : N ≤ Ideal.span {x} • N := by
      intro w hwN
      obtain ⟨w', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (h w hwN)
      refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) ?_
      rw [Submodule.mem_torsionBySet_iff] at hwN ⊢
      exact fun a ↦ reg <| by simp only [smul_comm x (a : R) w', hwN a, smul_zero]
    have hN : N = ⊥ := by
      rw [Submodule.eq_smul_of_le_smul_of_le_jacobson (IsNoetherian.noetherian N) hle
        ((Ideal.span_singleton_le_iff_mem _).2 hx), eq_bot_iff, ← Submodule.annihilator_top,
        ← Submodule.annihilator_smul (⊤ : Submodule R M)]
      exact Submodule.smul_mono le_rfl le_top
    obtain ⟨z, rfl⟩ := (isAssociatedPrime_iff.1 hp).2
    have hz : z ≠ 0 := by
      rintro rfl
      exact hp.isPrime.ne_top (by simp)
    refine hz <| (Submodule.mem_bot R).1 <| hN ▸ (Submodule.mem_torsionBySet_iff _ _).2 ?_
    exact fun a ↦ Submodule.mem_colon_singleton.1 a.2
  have hw' : (Submodule.Quotient.mk w : QuotSMulTop x M) ≠ 0 :=
    (Submodule.Quotient.mk_eq_zero _).not.2 hw
  obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hw'
  refine ⟨q, hq, fun a ha ↦ hle <| Submodule.mem_colon_singleton.2 ?_⟩
  rw [← Submodule.Quotient.mk_smul, (Submodule.mem_torsionBySet_iff _ _).1 hwN ⟨a, ha⟩,
    Submodule.Quotient.mk_zero]
  exact Submodule.zero_mem _

end IsAssociatedPrime
