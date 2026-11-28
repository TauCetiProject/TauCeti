/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.WittVector.Complete

import TauCeti.RingTheory.QuotSMulTop
import TauCeti.RingTheory.WittVector.Teichmuller.Coeff
import TauCeti.RingTheory.WittVector.Units

/-!
# Regular elements in Witt vectors

Let `R` be a ring of characteristic `p` and `𝕎 R = WittVector p R` its ring of `p`-typical Witt
vectors. If `x.coeff 0 ∈ R⁰`, then multiplication by `x` on `𝕎 R` is regular (`x ∈ (𝕎 R)⁰`),
without requiring `R` to be perfect. When `R` is perfect of characteristic `p`, `p` is
`𝕎 R`-regular, regularity of multiplication by `x` on `𝕎 R ⧸ (p)` holds iff `x.coeff 0 ∈ R⁰`,
and `x.coeff 0 ∈ R⁰` also makes `p` regular on `𝕎 R ⧸ (x)`. Finally,
`(p, x) ≠ ⊤ ↔ ¬ IsUnit (x.coeff 0)`.

For weakly regular and regular pairs `[p, x]` and `[x, p]`, see
`TauCeti.RingTheory.WittVector.Regular.Sequence`.

## Main results

* `WittVector.isSMulRegular_natCast`: over a perfect ring of characteristic `p`, `p` is
  `𝕎 R`-regular.
* `WittVector.isSMulRegular_quotientP_iff`: over a perfect ring of characteristic `p`,
  multiplication by `x` on `𝕎 R ⧸ (p)` is regular iff `x.coeff 0 ∈ R⁰`.
* `WittVector.isSMulRegular_quotSMulTop_natCast_iff`: the same for `QuotSMulTop (p : 𝕎 R) (𝕎 R)`.
* `WittVector.mem_nonZeroDivisors_of_coeff_zero`: over any ring of characteristic `p`, if
  `x.coeff 0 ∈ R⁰`, then `x ∈ (𝕎 R)⁰`.
* `WittVector.isSMulRegular_of_coeff_zero`: over any ring of characteristic `p`, if
  `x.coeff 0 ∈ R⁰`, then `x` is `𝕎 R`-regular.
* `WittVector.mk_natCast_mem_nonZeroDivisors`: over a perfect ring of characteristic `p`, if
  `x.coeff 0 ∈ R⁰`, then `p` is a nonzerodivisor on `𝕎 R ⧸ (x)`.
* `WittVector.isSMulRegular_quotient_natCast_of_coeff_zero` and
  `WittVector.isSMulRegular_quotSMulTop_natCast_of_coeff_zero`: over a perfect ring of
  characteristic `p`, if `x.coeff 0 ∈ R⁰`, then `p` is regular on `𝕎 R ⧸ (x)` and
  `QuotSMulTop x (𝕎 R)`.
* `WittVector.span_pair_natCast_ne_top_iff`: `(p, x) ≠ ⊤ ↔ ¬ IsUnit (x.coeff 0)`.
-/

public section

namespace WittVector

open Ideal
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

omit [PerfectRing R p] in
/-- If the zeroth Witt coordinate of `x` is a nonzerodivisor of `R`, then `x` is a nonzerodivisor
of `𝕎 R`. -/
theorem mem_nonZeroDivisors_of_coeff_zero {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰) : x ∈ (𝕎 R)⁰ := by
  refine mem_nonZeroDivisors_iff_right.mpr fun y hy ↦ by_contra fun hy0 ↦ ?_
  obtain ⟨n, w, hw0, rfl⟩ := verschiebung_nonzero hy0
  have h0 : ((verschiebung^[n] w * verschiebung^[0] x).coeff (n + 0)) = 0 := by
    simpa only [Function.iterate_zero_apply, add_zero, hy] using zero_coeff (p := p) (R := R) n
  rw [iterate_verschiebung_mul_coeff, pow_zero, pow_one] at h0
  exact hw0 ((pow_mem hx (p ^ n)).2 _ h0)

omit [PerfectRing R p] in
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

end WittVector
