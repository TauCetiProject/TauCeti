/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.LinearMap
import Mathlib.Algebra.GroupWithZero.Action.Regular

/-!
# Ideals together with their annihilators

In a reduced Noetherian ring, an ideal `J` and its annihilator together contain a nonzerodivisor.
An element killing `J.annihilator ⊔ J` lies in `J.annihilator` and kills itself, so it is
nilpotent, hence zero; Mathlib's `IsSMulRegular.subsingleton_linearMap_iff` turns this into a
regular element of `J.annihilator ⊔ J`.

This is the input that splits an idempotent off the total ring of fractions of a reduced
Noetherian ring with two minimal primes, as in `IsLocalRing.isDomain_of_isIntegrallyClosed`.

## Main results

* `Ideal.exists_mem_annihilator_sup_isSMulRegular`: in a reduced Noetherian ring, every ideal
  together with its annihilator contains a nonzerodivisor.
-/

public section

/-- In a reduced Noetherian ring, every ideal `J` together with its annihilator contains a
nonzerodivisor: some element of `J.annihilator ⊔ J` is regular on `R`. -/
theorem Ideal.exists_mem_annihilator_sup_isSMulRegular {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsReduced R] (J : Ideal R) :
    ∃ b ∈ J.annihilator ⊔ J, IsSMulRegular R b := by
  -- an element killing `J.annihilator ⊔ J` lies in and kills `J.annihilator`, so its square is zero
  have hann (m : R) (hm : ∀ k ∈ J.annihilator ⊔ J, k * m = 0) : m = 0 := by
    have hmI : m ∈ J.annihilator := Submodule.mem_annihilator.2 fun j hj ↦ by
      rw [smul_eq_mul, mul_comm]
      exact hm j (Ideal.mem_sup_right hj)
    exact IsReduced.eq_zero m ⟨2, by rw [pow_two]; exact hm m (Ideal.mem_sup_left hmI)⟩
  -- so every linear map `R ⧸ (J.annihilator ⊔ J) → R` vanishes
  rw [← Ideal.annihilator_quotient (I := J.annihilator ⊔ J)]
  refine IsSMulRegular.subsingleton_linearMap_iff.1 (subsingleton_of_forall_eq 0 fun f ↦ ?_)
  have hmk (r : R) : Ideal.Quotient.mk (J.annihilator ⊔ J) r = r • Ideal.Quotient.mk _ 1 := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one]
  have h0 : f (Ideal.Quotient.mk _ 1) = 0 := hann _ fun k hk ↦ by
    rw [← smul_eq_mul, ← map_smul, ← hmk, Ideal.Quotient.eq_zero_iff_mem.2 hk, map_zero]
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [hmk, map_smul, h0, smul_zero, LinearMap.zero_apply]
