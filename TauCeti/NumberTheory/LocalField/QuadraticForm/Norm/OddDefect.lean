/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect
public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup

/-!
# A norm with valuation equal to the quadratic defect

An optimal square approximation to a nonsquare `a` gives a norm from `K(√a)` whose valuation is
the defect exponent of `a`: if `a - ξ² = x`, then `ξ² - a = -x` is the norm of `ξ + √a`.
In particular, a radicand with odd defect has a norm of odd valuation. This identifies the
valuation part of the norm group in the ramified unit case of the local Hilbert symbol.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- If the quadratic defect of `a` has finite exponent `d`, then a norm from `K(√a)` has
normalized valuation exactly `d`. -/
theorem exists_quadraticNormSubgroup_val_eq_defectExponent {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) :
    ∃ b : Kˣ, b ∈ quadraticNormSubgroup (a : K) ∧
      (normalizedValuation K b).toAdd = d := by
  have ha : ¬IsSquare a := by
    intro h
    have htop := defectExponent_eq_top_iff.mpr h
    rw [hd] at htop
    exact WithTop.coe_ne_top htop
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq ha
  refine ⟨-x, ?_, ?_⟩
  · apply (mem_quadraticNormSubgroup_iff_exists_norm_eq (a : K) (-x)).mpr
    refine ⟨⟨ξ, 1⟩, ?_⟩
    simp only [QuadraticAlgebra.norm_def, mul_one]
    push_cast
    rw [hx]
    ring
  · rw [hd] at hxd
    simpa only [normalizedValuation_neg] using (WithTop.coe_inj.mp hxd)

/-- An odd quadratic defect yields a norm of valuation one. Thus the norm group reaches every
valuation after taking powers. -/
theorem exists_quadraticNormSubgroup_val_one_of_odd_defectExponent {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) (hodd : Odd d) :
    ∃ b : Kˣ, b ∈ quadraticNormSubgroup (a : K) ∧
      (normalizedValuation K b).toAdd = 1 := by
  obtain ⟨b, hb, hbval⟩ := exists_quadraticNormSubgroup_val_eq_defectExponent hd
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨c, hc⟩ := normalizedValuation_surjective (K := K) (Multiplicative.ofAdd (-k))
  refine ⟨b * c ^ 2, (quadraticNormSubgroup _).mul_mem hb
    (square_le_quadraticNormSubgroup _ (Subgroup.mem_square.mpr ⟨c, pow_two c⟩)), ?_⟩
  simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul, hc, toAdd_ofAdd,
    hbval]
  omega

/-- If the defect exponent is odd, every integer is the valuation of a quadratic norm. -/
theorem exists_quadraticNormSubgroup_val_of_odd_defectExponent {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) (hodd : Odd d) (n : ℤ) :
    ∃ b : Kˣ, b ∈ quadraticNormSubgroup (a : K) ∧
      (normalizedValuation K b).toAdd = n := by
  obtain ⟨b, hb, hbval⟩ := exists_quadraticNormSubgroup_val_one_of_odd_defectExponent hd hodd
  refine ⟨b ^ n, (quadraticNormSubgroup _).zpow_mem hb n, ?_⟩
  simp [map_zpow, toAdd_zpow, hbval]

end TauCeti
