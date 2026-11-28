/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.WittVector.Complete

import TauCeti.RingTheory.QuotSMulTop
import TauCeti.RingTheory.Regular.RegularSequence
import TauCeti.RingTheory.WittVector.Teichmuller.Coeff
import TauCeti.RingTheory.WittVector.Units

/-!
# Regular elements and regular pairs in Witt vectors of a perfect ring

Let `R` be a perfect ring of characteristic `p` and `𝕎 R = WittVector p R` its ring of `p`-typical
Witt vectors. Since `𝕎 R` is `p`-torsion-free and `p`-adically separated with
`𝕎 R ⧸ (p) ≃+* R` through the zeroth Witt coordinate, regularity of multiplication by `x` on
`𝕎 R ⧸ (p)` is equivalent to `x.coeff 0 ∈ R⁰`, and this gives a sufficient criterion for
regularity of `x` on `𝕎 R`, of `p` on `𝕎 R ⧸ (x)`, and of the pairs `[p, x]` and `[x, p]`:

* `p` is a nonzerodivisor of `𝕎 R`.
* Multiplication by `x` on `𝕎 R ⧸ (p)` is regular iff `x.coeff 0 ∈ R⁰`.
* If `x.coeff 0 ∈ R⁰`, then `x ∈ (𝕎 R)⁰`, `p` is regular on `𝕎 R ⧸ (x)`, and both `[p, x]` and
  `[x, p]` are weakly regular sequences on `𝕎 R` (and regular when `¬ IsUnit (x.coeff 0)`).

This is the regular-sequence input for the regularity of the cyclotomic periods of `A_inf`
(Bhatt–Morrow–Scholze, *Integral p-adic Hodge theory*, Lemma 3.23 and Proposition 3.17).

## Main results

* `WittVector.isSMulRegular_natCast`: `p` is `𝕎 R`-regular.
* `WittVector.isSMulRegular_quotientP_iff`: multiplication by `x` on `𝕎 R ⧸ (p)` is regular iff
  `x.coeff 0 ∈ R⁰`.
* `WittVector.mem_nonZeroDivisors_of_coeff_zero`: if `x.coeff 0 ∈ R⁰`, then `x ∈ (𝕎 R)⁰`.
* `WittVector.mk_natCast_mem_nonZeroDivisors`: if `x.coeff 0 ∈ R⁰`, then `p` is a nonzerodivisor
  on `𝕎 R ⧸ (x)`.
* `WittVector.isSMulRegular_quotient_natCast_of_coeff_zero`: if `x.coeff 0 ∈ R⁰`, then `p` is
  regular on `𝕎 R ⧸ (x)`.
* `WittVector.isWeaklyRegular_pair_natCast_of_coeff_zero` and
  `WittVector.isWeaklyRegular_pair_of_coeff_zero`: `[p, x]` and `[x, p]` are weakly regular.
* `WittVector.span_pair_natCast_ne_top_iff`: `(p, x) ≠ ⊤ ↔ ¬ IsUnit (x.coeff 0)`.
* `WittVector.isRegular_natCast_cons_singleton`,
  `WittVector.isRegular_natCast_cons_singleton_of_map_eq_zero`, and
  `WittVector.isRegular_pair_of_coeff_zero`: `[p, x]` and `[x, p]` are regular when
  `x.coeff 0 ∈ R⁰` and `¬ IsUnit (x.coeff 0)`.
-/

public section

namespace WittVector

open Ideal RingTheory.Sequence
open scoped nonZeroDivisors

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

local notation "𝕎" => WittVector p

/-- Over a perfect ring of characteristic `p`, `p` is a regular element of `𝕎 R`. -/
theorem isSMulRegular_natCast : IsSMulRegular (𝕎 R) (p : 𝕎 R) :=
  (isRegular_iff_mem_nonZeroDivisors.mpr p_mem_nonZeroDivisors).left.isSMulRegular

/-- Multiplication by `x` on `𝕎 R ⧸ (p)` is regular iff `x.coeff 0` is a nonzerodivisor of `R`. -/
theorem isSMulRegular_quotientP_iff (x : 𝕎 R) :
    IsSMulRegular (𝕎 R ⧸ span {(p : 𝕎 R)}) x ↔ x.coeff 0 ∈ R⁰ := by
  let e : 𝕎 R ⧸ span {(p : 𝕎 R)} ≃+* R := quotientPEquiv
  have he (y : 𝕎 R ⧸ span {(p : 𝕎 R)}) : e (x • y) = x.coeff 0 * e y := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    exact congrArg (· * e y) ((quotientPEquiv_mk x).trans (constantCoeff_apply x))
  have hcongr : IsSMulRegular (𝕎 R ⧸ span {(p : 𝕎 R)}) x ↔ IsSMulRegular R (x.coeff 0) := by
    refine ⟨fun h y z hyz ↦ ?_, fun h y z hyz ↦ ?_⟩
    · obtain ⟨y, rfl⟩ := e.surjective y
      obtain ⟨z, rfl⟩ := e.surjective z
      exact congrArg e (h (e.injective (by simpa only [he, smul_eq_mul] using hyz)))
    · exact e.injective (h (by simpa only [← he, smul_eq_mul] using congrArg e hyz))
  exact hcongr.trans (isLeftRegular_iff.symm.trans
    ((Commute.isRegular_iff (Commute.all _)).symm.trans isRegular_iff_mem_nonZeroDivisors))

/-- Multiplication by `x` on `𝕎 R ⧸ p 𝕎 R` is regular iff `x.coeff 0 ∈ R⁰`. -/
theorem isSMulRegular_quotSMulTop_natCast_iff (x : 𝕎 R) :
    IsSMulRegular (QuotSMulTop (p : 𝕎 R) (𝕎 R)) x ↔ x.coeff 0 ∈ R⁰ :=
  ((QuotSMulTop.equivQuotSpanSingleton (p : 𝕎 R)).isSMulRegular_congr x).trans
    (isSMulRegular_quotientP_iff x)

/-- If the zeroth Witt coordinate of `x` is a nonzerodivisor of `R`, then `x` is a nonzerodivisor
of `𝕎 R`. -/
theorem mem_nonZeroDivisors_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰) : x ∈ (𝕎 R)⁰ := by
  refine mem_nonZeroDivisors_iff_right.mpr fun y hy ↦ ext fun n ↦ ?_
  -- Show `(p : 𝕎 R) ^ m ∣ y` for all `m` by induction, then take `m = n + 1`.
  have hdvd : ∀ m : ℕ, (p : 𝕎 R) ^ m ∣ y := by
    intro m
    induction m generalizing y with
    | zero => simp
    | succ m ih =>
      have hy0 : y.coeff 0 * x.coeff 0 = 0 := by
        simpa [mul_coeff_zero] using congrArg (coeff · 0) hy
      obtain ⟨y', rfl⟩ := mem_span_singleton.mp
        ((mem_span_p_iff_coeff_zero_eq_zero y).mpr (hx.2 _ hy0))
      have hy' : y' * x = 0 :=
        (mul_cancel_left_mem_nonZeroDivisors p_mem_nonZeroDivisors).mp (by linear_combination hy)
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih y' hy')
  rw [zero_coeff]
  exact (mem_span_p_pow_iff_le_coeff_eq_zero y (n + 1)).mp (mem_span_singleton.mpr (hdvd (n + 1)))
    n (Nat.lt_succ_self n)

/-- If `x.coeff 0 ∈ R⁰`, then `x` is `𝕎 R`-regular. -/
theorem isSMulRegular_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰) : IsSMulRegular (𝕎 R) x :=
  ((Commute.isRegular_iff (Commute.all x)).mp
    (isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_coeff_zero hx))).isSMulRegular

/-- If the zeroth Witt coordinate of `x : 𝕎 R` is a nonzerodivisor, then `p` is a nonzerodivisor on
`𝕎 R ⧸ (x)`. -/
theorem mk_natCast_mem_nonZeroDivisors (x : 𝕎 R) (hx : x.coeff 0 ∈ R⁰) :
    Ideal.Quotient.mk (span {x}) (p : 𝕎 R) ∈ (𝕎 R ⧸ span {x})⁰ := by
  refine mem_nonZeroDivisors_iff_left.mpr fun y hy ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton'] at hy
  obtain ⟨z, hz⟩ := hy
  -- comparing zeroth coordinates of `z * x = p * y` gives `z₀ = 0`, so `z = p * w`
  have hz0 : z.coeff 0 = 0 := by
    have h0 := congrArg (fun v : 𝕎 R ↦ v.coeff 0) (hz.trans (mul_comm _ _))
    rw [mul_charP_coeff_zero, mul_coeff_zero] at h0
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hx).mp h0
  obtain ⟨w, rfl⟩ := mem_span_singleton.mp ((mem_span_p_iff_coeff_zero_eq_zero z).mpr hz0)
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton']
  refine ⟨w, sub_eq_zero.mp (eq_zero_of_p_mul_eq_zero _ ?_)⟩
  linear_combination hz

/-- If `x.coeff 0 ∈ R⁰`, then `p` is regular on `𝕎 R ⧸ (x)`. -/
theorem isSMulRegular_quotient_natCast_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰) :
    IsSMulRegular (𝕎 R ⧸ span {x}) (p : 𝕎 R) := by
  have hp := (isRegular_iff_mem_nonZeroDivisors.mpr (mk_natCast_mem_nonZeroDivisors x hx)).left
  intro y z hyz
  exact hp (by simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hyz)

/-- If `x.coeff 0 ∈ R⁰`, then `p` is regular on `𝕎 R ⧸ x 𝕎 R`. -/
theorem isSMulRegular_quotSMulTop_natCast_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰) :
    IsSMulRegular (QuotSMulTop x (𝕎 R)) (p : 𝕎 R) :=
  ((QuotSMulTop.equivQuotSpanSingleton x).isSMulRegular_congr (p : 𝕎 R)).mpr
    (isSMulRegular_quotient_natCast_of_coeff_zero hx)

/-- If `x.coeff 0 ∈ R⁰`, then `[p, x]` is a weakly regular sequence on `𝕎 R`. -/
theorem isWeaklyRegular_pair_natCast_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰) :
    IsWeaklyRegular (𝕎 R) [(p : 𝕎 R), x] :=
  IsWeaklyRegular.cons isSMulRegular_natCast
    ((isWeaklyRegular_singleton_iff _ x).mpr ((isSMulRegular_quotSMulTop_natCast_iff x).mpr hx))

/-- If `x.coeff 0 ∈ R⁰`, then `[x, p]` is a weakly regular sequence on `𝕎 R`. -/
theorem isWeaklyRegular_pair_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰) :
    IsWeaklyRegular (𝕎 R) [x, (p : 𝕎 R)] :=
  IsWeaklyRegular.cons (isSMulRegular_of_coeff_zero hx)
    ((isWeaklyRegular_singleton_iff _ (p : 𝕎 R)).mpr
      (isSMulRegular_quotSMulTop_natCast_of_coeff_zero hx))

omit [PerfectRing R p] in
/-- The ideal `(p, x)` of `𝕎 R` is proper iff `x.coeff 0` is not a unit of `R`. -/
theorem span_pair_natCast_ne_top_iff (x : 𝕎 R) :
    span {(p : 𝕎 R), x} ≠ ⊤ ↔ ¬ IsUnit (x.coeff 0) := by
  have hmap : (span {(p : 𝕎 R), x}).map constantCoeff = span {x.coeff 0} := by
    simp [Ideal.map_span]
  refine ⟨fun h hu ↦ h ?_, fun h htop ↦ h ?_⟩
  · exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp))
      (isUnit_iff_isUnit_coeff_zero.mpr hu)
  · have : span {x.coeff 0} = ⊤ := by rw [← hmap, htop, Ideal.map_top]
    exact Ideal.span_singleton_eq_top.mp this

/-- **Regular pairs `(p, x)`.** Over a perfect ring `R` of characteristic `p`, if the zeroth Witt
coordinate of `x : 𝕎 R` is a nonzerodivisor and not a unit, then `p, x` is a regular sequence in
`𝕎 R`. -/
theorem isRegular_natCast_cons_singleton (x : 𝕎 R) (hx : x.coeff 0 ∈ R⁰)
    (hu : ¬IsUnit (x.coeff 0)) : IsRegular (𝕎 R) [(p : 𝕎 R), x] :=
  (isRegular_pair_iff_isWeaklyRegular_of_span_ne_top
    ((span_pair_natCast_ne_top_iff x).mpr hu)).mpr
      (isWeaklyRegular_pair_natCast_of_coeff_zero hx)

/-- If the zeroth Witt coordinate of `x : 𝕎 R` is a nonzerodivisor and `x` is killed by a ring
homomorphism to a nontrivial ring, then `p, x` is a regular sequence in `𝕎 R`. -/
theorem isRegular_natCast_cons_singleton_of_map_eq_zero (x : 𝕎 R) (hx : x.coeff 0 ∈ R⁰)
    {B : Type*} [CommRing B] [Nontrivial B] (f : 𝕎 R →+* B) (hf : f x = 0) :
    IsRegular (𝕎 R) [(p : 𝕎 R), x] := by
  refine isRegular_natCast_cons_singleton x hx fun hu ↦ ?_
  have := (isUnit_iff_isUnit_coeff_zero.mpr hu).map f
  rw [hf] at this
  exact not_isUnit_zero this

/-- If `x.coeff 0 ∈ R⁰` and `¬ IsUnit (x.coeff 0)`, then `[x, p]` is a regular sequence on `𝕎 R`.
-/
theorem isRegular_pair_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰)
    (hnu : ¬ IsUnit (x.coeff 0)) : IsRegular (𝕎 R) [x, (p : 𝕎 R)] :=
  (isRegular_pair_iff_isWeaklyRegular_of_span_ne_top
    (by rw [Set.pair_comm]; exact (span_pair_natCast_ne_top_iff x).mpr hnu)).mpr
      (isWeaklyRegular_pair_of_coeff_zero hx)

end WittVector
