/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup

/-!
# Norm valuation and uniformizer-norm scaling

An optimal square approximation to a nonsquare `a` gives a norm from `K(√a)` whose normalized
valuation is the defect exponent: if `a - ξ² = x`, then `ξ² - a = -x` is the norm of `ξ + √a`
(`TauCeti.exists_mem_quadraticNormSubgroup_toAdd_normalizedValuation_eq_defectExponent`). Moreover,
given any norm `w ∈ quadraticNormSubgroup a` of normalized valuation `1`, scaling by `w ^ (-v_K(b))`
expresses every element of `quadraticNormSubgroup a` as `w ^ n * c` with `c` a norm of valuation one
(`TauCeti.mem_quadraticNormSubgroup_iff_exists_zpow_mul_unit`).

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

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

/-- Given a norm `w ∈ quadraticNormSubgroup a` of normalized valuation `1`, every element of
`quadraticNormSubgroup a` is an integer power of `w` times a norm of valuation one. -/
theorem mem_quadraticNormSubgroup_iff_exists_zpow_mul_unit {a : K} {w : Kˣ}
    (hw : w ∈ quadraticNormSubgroup a) (hwv : (normalizedValuation K w).toAdd = 1) (b : Kˣ) :
    b ∈ quadraticNormSubgroup a ↔
      ∃ (n : ℤ) (c : Kˣ), c ∈ quadraticNormSubgroup a ∧ valuation K (c : K) = 1 ∧
        b = w ^ n * c := by
  constructor
  · intro hb
    let n : ℤ := (normalizedValuation K b).toAdd
    let c : Kˣ := b * w ^ (-n)
    have hc : c ∈ quadraticNormSubgroup a :=
      (quadraticNormSubgroup a).mul_mem hb ((quadraticNormSubgroup a).zpow_mem hw (-n))
    have hcv : valuation K (c : K) = 1 := by
      apply (normalizedValuation_eq_one_iff c).mp
      apply Multiplicative.toAdd.injective
      simp [c, n, map_zpow, hwv]
    exact ⟨n, c, hc, hcv, by simp [c, zpow_neg, mul_left_comm]⟩
  · rintro ⟨n, c, hc, -, rfl⟩
    exact (quadraticNormSubgroup a).mul_mem ((quadraticNormSubgroup a).zpow_mem hw n) hc

end TauCeti
