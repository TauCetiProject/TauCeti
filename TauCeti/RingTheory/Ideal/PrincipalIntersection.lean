/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Powers of principal-ideal intersections

In a commutative domain, `(p) ∩ (q) = (pq)` implies the corresponding equality for every
pair of powers. This hypothesis does not assert that `(p) + (q)` is the whole ring.

The nonzero case is an application of the existing power-regularity theorem for a weakly
regular pair: the intersection hypothesis makes `q` regular modulo `(p)`. The zero-scalar
and zero-power cases are included.

## References

* The Stacks Project, [Regular sequences](https://stacks.math.columbia.edu/tag/0AUH), for the
  regular-sequence interpretation of the divisibility argument.
-/

public section

open scoped Pointwise

namespace Ideal

variable {R : Type*} [CommRing R] [IsDomain R] {p q : R}

/-- An intersection equal to the product of two principal ideals remains so for every pair
of powers. No Bézout, factorization, or comaximality assumption is needed. -/
theorem inf_span_singleton_pow_eq_span_singleton_mul
    (h : span {p} ⊓ span {q} = span {p * q}) (r s : ℕ) :
    span {p ^ r} ⊓ span {q ^ s} = span {p ^ r * q ^ s} := by
  by_cases hp : p = 0
  · subst p
    cases r <;> simp
  by_cases hq : q = 0
  · subst q
    cases s <;> simp
  have hreg : RingTheory.Sequence.IsWeaklyRegular R [p, q] := by
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
      RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    refine ⟨(IsRegular.of_ne_zero' hp).left.isSMulRegular, ?_⟩
    apply TauCeti.isSMulRegular_quotSMulTop_iff.mpr
    intro m c hcm
    have hmem : q * m ∈ span {p} ⊓ span {q} :=
      ⟨mem_span_singleton.mpr ⟨c, hcm.symm⟩, mem_span_singleton.mpr ⟨m, rfl⟩⟩
    rw [h, mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    have hm : m = p * a := mul_left_cancel₀ hq (by
      simpa only [mul_comm p q, mul_assoc] using ha)
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨a, Submodule.mem_top, hm.symm⟩
  have hpow := hreg.isSMulRegular_quotSMulTop_pow r s
  apply le_antisymm
  · intro z hz
    obtain ⟨m, hm⟩ := mem_span_singleton.mp hz.1
    obtain ⟨n, hn⟩ := mem_span_singleton.mp hz.2
    have hnmem : n ∈ p ^ r • (⊤ : Submodule R R) :=
      TauCeti.isSMulRegular_quotSMulTop_iff.mp hpow n m (hm.symm.trans hn)
    obtain ⟨t, -, ht⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hnmem
    refine mem_span_singleton.mpr ⟨t, ?_⟩
    calc
      z = q ^ s * n := hn
      _ = q ^ s * (p ^ r * t) := by rw [← ht, smul_eq_mul]
      _ = (p ^ r * q ^ s) * t := by simp only [mul_assoc, mul_left_comm]
  · intro z hz
    obtain ⟨t, rfl⟩ := mem_span_singleton.mp hz
    exact ⟨mem_span_singleton.mpr ⟨q ^ s * t, by rw [mul_assoc]⟩,
      mem_span_singleton.mpr ⟨p ^ r * t, by simp only [mul_assoc, mul_left_comm]⟩⟩

end Ideal
