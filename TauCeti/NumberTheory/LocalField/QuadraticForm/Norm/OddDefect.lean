/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Valuation

/-!
# Norm valuations from a radicand of odd quadratic defect

An optimal square approximation to a nonsquare `a` gives a norm from `K(√a)` whose valuation is
the defect exponent of `a`: if `a - ξ² = x`, then `ξ² - a = -x` is the norm of `ξ + √a`.
If the defect exponent is odd, multiplying this norm by a square gives valuation one; its
integer powers then give norms of every integer valuation. This identifies the valuation part
of the norm group in the ramified unit case of the local Hilbert symbol.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- An odd quadratic defect yields a norm of valuation one. -/
private theorem exists_norm_valuation_one_of_odd_defectExponent
    {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) (hodd : Odd d) :
    ∃ b : Kˣ, b ∈ quadraticNormSubgroup (a : K) ∧
      (normalizedValuation K b).toAdd = 1 := by
  obtain ⟨b, hb, hbval⟩ :=
    exists_mem_quadraticNormSubgroup_toAdd_normalizedValuation_eq_defectExponent hd
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨c, hc⟩ := normalizedValuation_surjective (K := K) (Multiplicative.ofAdd (-k))
  refine ⟨b * c ^ 2, (quadraticNormSubgroup _).mul_mem hb
    (square_le_quadraticNormSubgroup _ (Subgroup.mem_square.mpr ⟨c, pow_two c⟩)), ?_⟩
  simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul, hc, toAdd_ofAdd,
    hbval]
  omega

/-- If the defect exponent is odd, every integer is the valuation of a quadratic norm. -/
theorem exists_mem_quadraticNormSubgroup_toAdd_normalizedValuation_eq_of_odd_defectExponent
    {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) (hodd : Odd d) (n : ℤ) :
    ∃ b : Kˣ, b ∈ quadraticNormSubgroup (a : K) ∧
      (normalizedValuation K b).toAdd = n := by
  obtain ⟨b, hb, hbval⟩ :=
    exists_norm_valuation_one_of_odd_defectExponent hd hodd
  refine ⟨b ^ n, (quadraticNormSubgroup _).zpow_mem hb n, ?_⟩
  simp [map_zpow, toAdd_zpow, hbval]

end TauCeti
