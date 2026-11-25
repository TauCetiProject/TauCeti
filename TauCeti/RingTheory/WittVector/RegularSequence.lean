/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.WittVector.Complete

/-!
# Regular pairs `(p, x)` in Witt vectors of a perfect ring

Let `R` be a perfect ring of characteristic `p`. Then `𝕎 R` is `p`-torsion free with
`𝕎 R ⧸ (p) ≅ R` through the zeroth Witt coordinate. Hence `p, x` is a regular sequence in `𝕎 R`
as soon as the zeroth coordinate `x₀` of `x` is a nonzerodivisor and a nonunit of `R`: `x` acts
on `𝕎 R ⧸ (p)` as multiplication by `x₀`, and `1 ∈ (p, x)` would make `x₀` a unit.

This is the regular-sequence input for the regularity of the cyclotomic periods of `A_inf`
(Bhatt–Morrow–Scholze, *Integral p-adic Hodge theory*, Lemma 3.23 and Proposition 3.17).

## Main results

* `WittVector.isRegular_natCast_cons_singleton`: if `x₀ ∈ R⁰` is not a unit, then `p, x` is a
  regular sequence in `𝕎 R`.
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
theorem isRegular_natCast_cons_singleton {x : 𝕎 R} (hx : x.coeff 0 ∈ R⁰)
    (hu : ¬IsUnit (x.coeff 0)) : IsRegular (𝕎 R) [(p : 𝕎 R), x] := by
  rw [isRegular_iff, isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  refine ⟨⟨fun a b h ↦ ?_, ?_⟩, fun htop ↦ hu ?_⟩
  · -- `𝕎 R` is `p`-torsion free
    rw [← sub_eq_zero]
    refine eq_zero_of_p_mul_eq_zero _ ?_
    simp only [smul_eq_mul] at h
    rw [sub_mul, mul_comm a, mul_comm b, h, sub_self]
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
    rw [smul_eq_mul, mul_top] at h1
    have hspan : ofList [(p : 𝕎 R), x] = span {(p : 𝕎 R), x} := by
      rw [ofList]
      congr 1
      ext
      simp
    obtain ⟨a, b, hab⟩ := mem_span_pair.mp (hspan ▸ h1)
    refine IsUnit.of_mul_eq_one (b.coeff 0) ?_
    have := congrArg (fun z : 𝕎 R ↦ z.coeff 0) hab
    simpa [add_coeff_zero, mul_coeff_zero, mul_charP_coeff_zero, mul_comm] using this

end WittVector
