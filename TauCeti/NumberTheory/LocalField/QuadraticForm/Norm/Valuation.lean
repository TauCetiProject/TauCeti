/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect
public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup

/-!
# Norm valuation at a finite quadratic defect

An optimal square approximation to a nonsquare `a` gives a norm from `K(√a)` whose normalized
valuation is the defect exponent: if `a - ξ² = x`, then `ξ² - a = -x` is the norm of `ξ + √a`.
This supplies a norm witness for any finite quadratic defect exponent.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- If the quadratic defect of `a` has finite exponent `d`, then some norm from `K(√a)` has
normalized valuation exactly `d`. -/
theorem exists_mem_quadraticNormSubgroup_toAdd_normalizedValuation_eq_defectExponent
    {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) :
    ∃ b : Kˣ, b ∈ quadraticNormSubgroup (a : K) ∧
      (normalizedValuation K b).toAdd = d := by
  have ha : ¬IsSquare a := not_isSquare_of_defectExponent_eq hd
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq ha
  refine ⟨-x, ?_, ?_⟩
  · apply sq_sub_mem_quadraticNormSubgroup (a : K) ξ
    rw [Units.val_neg, hx]
    ring
  · rw [hd] at hxd
    simpa only [normalizedValuation_neg] using (WithTop.coe_inj.mp hxd)

end TauCeti
