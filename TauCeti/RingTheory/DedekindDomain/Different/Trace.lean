/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Different.Basic
import TauCeti.RingTheory.IntegralClosure.IntegralRestrict

/-!
# The trace of the powers of a prime, through the different

Let `B` be a Dedekind domain, module-finite over a Dedekind domain `A` with `Frac B / Frac A`
separable, and let `P` be a nonzero prime of `B` which is the only prime above an ideal `p` of
`A`, so that `p · B = P ^ e`. Write `d` for the multiplicity of `P` in the different ideal
`𝔡(B/A)`. The trace dual of `B` is `𝔡⁻¹`, so the integral trace carries `P ^ m` into `p ^ r`
exactly when `P ^ m` lies in the fractional ideal `p ^ r 𝔡⁻¹`. Its `P`-adic valuation is
`e r - d`, and its valuation at every other prime of `B` is nonpositive, since `P` is the only
prime above `p`; so the condition is exactly `e r ≤ m + d`. When `A` is a discrete valuation
ring with maximal ideal `p`, every ideal of `A` is a power of `p` and the criterion determines the
image completely:

`Tr(P ^ m) = p ^ ((m + d) / e)`,

with the division of natural numbers. This is the trace side of the theory of the different, in
the form used to compute the norm on the unit filtration of an extension of local fields: the
expansion `N(1 + x) = 1 + Tr(x) + ⋯ + N(x)` has trace terms whose valuations the formula reads
off (Serre, *Local Fields*, Chapter V, §3).

The proof rests on the trace criterion `TauCeti.dvd_differentIdeal_iff_forall_intTrace_mem`,
applied to the factorization `P ^ (e r - m) * P ^ m = p ^ r · B` when `m ≤ e r`; when `m > e r`
the inclusion `Tr(P ^ m) ⊆ Tr(p ^ r · B) ⊆ p ^ r` holds for free.

## Main results

* `TauCeti.map_intTrace_pow_le_pow_iff`: `Tr(P ^ m) ⊆ p ^ r ↔ e r ≤ m + d`.
* `TauCeti.map_intTrace_pow_eq_maximalIdeal_pow`: for `A` a discrete valuation ring,
  `Tr(P ^ m) = 𝓂_A ^ ((m + d) / e)`.

## References

* J.-P. Serre, *Local Fields*, Chapter III (the different) and Chapter V, §3.
-/

public section

open Module IsLocalRing

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]

section DedekindDomain

variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
variable {p : Ideal A} {P : Ideal B} [P.IsPrime] {e : ℕ}

/-- **The trace of a power of the prime above `p`.** If `p · B = P ^ e` for an ideal `p` of `A`
and a nonzero prime `P` of `B`, the integral trace carries `P ^ m` into `p ^ r` exactly when
`e * r ≤ m + d`, where `d` is the multiplicity of `P` in the different ideal. -/
theorem map_intTrace_pow_le_pow_iff (hP : P ≠ ⊥) (hPe : p.map (algebraMap A B) = P ^ e)
    (m r : ℕ) :
    ((P ^ m).restrictScalars A).map (Algebra.intTrace A B) ≤ p ^ r ↔
      e * r ≤ m + multiplicity P (differentIdeal A B) := by
  have hp : p ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot] at hPe
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp at hPe
    · exact hP ((Ideal.pow_eq_bot he.ne').mp hPe.symm)
  rw [Submodule.map_le_iff_le_comap, IsConcreteLE.le_iff]
  simp only [Submodule.restrictScalars_mem, Submodule.mem_comap]
  rcases le_or_gt m (e * r) with hm | hm
  · have hIQ : P ^ (e * r - m) * P ^ m = (p ^ r).map (algebraMap A B) := by
      rw [Ideal.map_pow, hPe, ← pow_mul, ← pow_add, Nat.sub_add_cancel hm]
    rw [← dvd_differentIdeal_iff_forall_intTrace_mem A (pow_ne_zero r hp) _ _ hIQ,
      pow_dvd_differentIdeal_iff_le_multiplicity A hP]
    omega
  · refine iff_of_true (fun x hx ↦ Algebra.intTrace_mem_of_mem_map ?_) (by omega)
    rw [Ideal.map_pow, hPe, ← pow_mul]
    exact Ideal.pow_le_pow_right hm.le hx

end DedekindDomain

section DiscreteValuationRing

variable [IsDomain A] [IsDiscreteValuationRing A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
variable {P : Ideal B} [P.IsPrime] {e : ℕ}

/-- **The trace of a power of the prime above the maximal ideal of a discrete valuation ring.**
If `A` is a discrete valuation ring with maximal ideal `𝓂_A` and `𝓂_A · B = P ^ e` for a nonzero
prime `P` of `B`, the image of `P ^ m` under the integral trace is `𝓂_A ^ ((m + d) / e)`, where
`d` is the multiplicity of `P` in the different ideal and the division is that of natural
numbers. -/
theorem map_intTrace_pow_eq_maximalIdeal_pow (hP : P ≠ ⊥)
    (hPe : (maximalIdeal A).map (algebraMap A B) = P ^ e) (m : ℕ) :
    ((P ^ m).restrictScalars A).map (Algebra.intTrace A B) =
      maximalIdeal A ^ ((m + multiplicity P (differentIdeal A B)) / e) := by
  set d := multiplicity P (differentIdeal A B)
  have hp : maximalIdeal A ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  have hp' : maximalIdeal A ≠ ⊤ := (maximalIdeal.isMaximal A).ne_top
  have he : 0 < e := by
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_eq_top_iff _ (FaithfulSMul.algebraMap_injective A B)
      fun x ↦ Algebra.IsIntegral.isIntegral x] at hPe
    exact hp' hPe
  -- Every step of the filtration of `A` compares with the image through the trace criterion.
  have key : ∀ r, ((P ^ m).restrictScalars A).map (Algebra.intTrace A B) ≤ maximalIdeal A ^ r ↔
      r ≤ (m + d) / e := fun r ↦ by
    rw [map_intTrace_pow_le_pow_iff A hP hPe, Nat.le_div_iff_mul_le he, mul_comm]
  have hJ : ((P ^ m).restrictScalars A).map (Algebra.intTrace A B) ≠ ⊥ := fun h ↦ by
    have := (key ((m + d) / e + 1)).mp (h.le.trans bot_le)
    omega
  obtain ⟨s, hs⟩ :=
    exists_maximalIdeal_pow_eq_of_principal A (IsPrincipalIdealRing.principal _) _ hJ
  have hanti := Ideal.pow_right_strictAnti (maximalIdeal A) hp hp'
  rw [hs] at key ⊢
  congr 1
  exact le_antisymm ((key s).mp le_rfl) (hanti.le_iff_ge.mp ((key _).mpr le_rfl))

end DiscreteValuationRing

end TauCeti
