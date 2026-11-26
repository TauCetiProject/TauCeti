/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.WittVector.Complete

import TauCeti.RingTheory.WittVector.Teichmuller.Coeff
import TauCeti.RingTheory.WittVector.Units

/-!
# Regular pairs `(p, x)` in Witt vectors of a perfect ring

Let `R` be a perfect ring of characteristic `p`. Then `𝕎 R` is `p`-torsion free with
`𝕎 R ⧸ (p) ≅ R` through the zeroth Witt coordinate. Hence `p, x` is a regular sequence in `𝕎 R`
as soon as the zeroth coordinate `x₀` of `x` is a nonzerodivisor and a nonunit of `R`: `x` acts
on `𝕎 R ⧸ (p)` as multiplication by `x₀`, and `1 ∈ (p, x)` would make `x₀` a unit. In the other
order, `p` is a nonzerodivisor on `𝕎 R ⧸ (x)` whenever `x₀` is a nonzerodivisor.

This is the regular-sequence input for the regularity of the cyclotomic periods of `A_inf`
(Bhatt–Morrow–Scholze, *Integral p-adic Hodge theory*, Lemma 3.23 and Proposition 3.17).

## Main results

* `WittVector.isRegular_natCast_cons_singleton`: if `x₀ ∈ R⁰` is not a unit, then `p, x` is a
  regular sequence in `𝕎 R`.
* `WittVector.isRegular_natCast_cons_singleton_of_map_eq_zero`: the same when `x₀ ∈ R⁰` and `x`
  is killed by a ring homomorphism to a nontrivial ring.
* `WittVector.mk_natCast_mem_nonZeroDivisors`: if `x₀ ∈ R⁰`, then `p` is a nonzerodivisor on
  `𝕎 R ⧸ (x)`.
-/

public section

namespace WittVector

open RingTheory.Sequence Ideal
open scoped nonZeroDivisors Pointwise

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

local notation "𝕎" => WittVector p

/-- **Regular pairs `(p, x)`.** Over a perfect ring `R` of characteristic `p`, if the zeroth Witt
coordinate of `x : 𝕎 R` is a nonzerodivisor and not a unit, then `p, x` is a regular sequence in
`𝕎 R`. -/
theorem isRegular_natCast_cons_singleton (x : 𝕎 R) (hx : x.coeff 0 ∈ R⁰)
    (hu : ¬IsUnit (x.coeff 0)) : IsRegular (𝕎 R) [(p : 𝕎 R), x] := by
  rw [isRegular_iff, isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  refine ⟨⟨(isRegular_iff_mem_nonZeroDivisors.mpr p_mem_nonZeroDivisors).left.isSMulRegular,
    ?_⟩, fun htop ↦ hu ?_⟩
  · rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro y hy
    obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    -- the zeroth coordinate of `x * y` vanishes, hence so does that of `y`
    have h0 : x.coeff 0 * y.coeff 0 = 0 := by
      rw [← mul_coeff_zero, ← smul_eq_mul, ← hz, smul_eq_mul, mul_comm, mul_charP_coeff_zero]
    have hy0 : y.coeff 0 = 0 := (mul_left_mem_nonZeroDivisors_eq_zero_iff hx).mp h0
    obtain ⟨w, hw⟩ := mem_span_singleton.mp ((mem_span_p_iff_coeff_zero_eq_zero y).mpr hy0)
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨w, trivial, hw.symm⟩
  · -- reducing `1 = a * p + b * x` to zeroth coordinates gives `1 = b₀ * x₀`
    have h1 : (1 : 𝕎 R) ∈ ofList [(p : 𝕎 R), x] • (⊤ : Ideal (𝕎 R)) := htop ▸ trivial
    rw [smul_eq_mul, mul_top, ofList_cons, ofList_singleton, ← span_insert] at h1
    obtain ⟨a, b, hab⟩ := mem_span_pair.mp h1
    refine IsUnit.of_mul_eq_one (b.coeff 0) ?_
    have := congrArg (fun z : 𝕎 R ↦ z.coeff 0) hab
    simpa [add_coeff_zero, mul_coeff_zero, mul_charP_coeff_zero, mul_comm] using this

/-- If the zeroth Witt coordinate of `x : 𝕎 R` is a nonzerodivisor and `x` is killed by a ring
homomorphism to a nontrivial ring, then `p, x` is a regular sequence in `𝕎 R`. -/
theorem isRegular_natCast_cons_singleton_of_map_eq_zero (x : 𝕎 R) (hx : x.coeff 0 ∈ R⁰)
    {B : Type*} [CommRing B] [Nontrivial B] (f : 𝕎 R →+* B) (hf : f x = 0) :
    IsRegular (𝕎 R) [(p : 𝕎 R), x] := by
  refine isRegular_natCast_cons_singleton x hx fun hu ↦ ?_
  have := (isUnit_iff_isUnit_coeff_zero.mpr hu).map f
  rw [hf] at this
  exact not_isUnit_zero this

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

end WittVector
