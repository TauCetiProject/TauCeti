/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Valuation rings separated for a principal adic topology

Let `R` be a valuation ring and `ϖ ∈ R`. If `R` is separated for the `ϖ`-adic topology, then `ϖ`
behaves like a uniformiser for divisibility: every nonzero element divides a power of `ϖ`.
Consequently a module on which `ϖ` acts injectively has no torsion at all. Over the valuation ring
of a complete rank-one valued field, this is what identifies flatness with the absence of
`ϖ`-torsion for the admissible algebras of Bosch–Lütkebohmert.

## Main results

* `TauCeti.PreValuationRing.exists_dvd_pow_of_isHausdorff`: in a valuation ring that is separated
  for the `ϖ`-adic topology, every nonzero element divides a power of `ϖ`.
* `IsSMulRegular.of_isHausdorff`: over such a ring, a module on which `ϖ` is regular is
  torsion-free.

## References

* S. Bosch and W. Lütkebohmert, *Formal and rigid geometry. I. Rigid spaces*, Math. Ann. 295
  (1993), §1.
-/

public section

/-- In a valuation ring that is separated for the `ϖ`-adic topology, every nonzero element
divides some power of `ϖ`: otherwise it would lie in every `ϖⁿ R`. -/
theorem TauCeti.PreValuationRing.exists_dvd_pow_of_isHausdorff {R : Type*} [CommRing R]
    [PreValuationRing R] {ϖ : R} [IsHausdorff (Ideal.span {ϖ}) R] {a : R} (ha : a ≠ 0) :
    ∃ n : ℕ, a ∣ ϖ ^ n := by
  by_contra! h
  refine ha (IsHausdorff.haus (I := Ideal.span {ϖ}) inferInstance a fun n ↦ ?_)
  rcases ValuationRing.dvd_total a (ϖ ^ n) with hdvd | hdvd
  · exact absurd hdvd (h n)
  · rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr hdvd

/-- Over a valuation ring that is separated for the `ϖ`-adic topology, a module on which `ϖ`
acts injectively has no torsion: multiplication by every nonzero scalar is injective. -/
theorem IsSMulRegular.of_isHausdorff {R M : Type*} [CommRing R] [PreValuationRing R]
    [AddCommGroup M] [Module R M] {ϖ : R} [IsHausdorff (Ideal.span {ϖ}) R]
    (hϖ : IsSMulRegular M ϖ) {a : R} (ha : a ≠ 0) : IsSMulRegular M a := by
  obtain ⟨n, b, hb⟩ := TauCeti.PreValuationRing.exists_dvd_pow_of_isHausdorff (ϖ := ϖ) ha
  have h := hϖ.pow n
  rw [hb, mul_comm] at h
  exact h.of_mul
