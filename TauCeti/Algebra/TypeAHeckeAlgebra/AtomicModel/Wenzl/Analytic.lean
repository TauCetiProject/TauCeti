/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.CycleWord
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Wenzl.Basic

/-!
# Cycle-trace generating products for Wenzl's continuous interval models

Over `ℂ`, the cycle-trace infinite products of the countable two-sided geometric models
`TauCeti.TypeAHeckeAlgebra.wenzlGtOneWeight` (`1 < Q`) and
`TauCeti.TypeAHeckeAlgebra.wenzlLtOneWeight` (`0 < Q < 1`) telescope to the rational function
`(1 + (Q - (1 + Q) * η) * x) / (1 - ((1 + Q) * η - 1) * x)`
(`TauCeti.TypeAHeckeAlgebra.wenzlGtOneWeight_cycleWord_hasProd`,
`TauCeti.TypeAHeckeAlgebra.wenzlLtOneWeight_cycleWord_hasProd`).
-/

public section

open OrderDual

namespace TauCeti.TypeAHeckeAlgebra

/-- **Telescoping infinite product for Wenzl's `1 < Q` countable model.** For `1 < Q`,
`η ∈ [1 / (1 + Q), Q / (1 + Q)]`, and `Q * ‖x‖ < 1`, the cycle-trace product converges to
`(1 + (Q - (1 + Q) * η) * x) / (1 - ((1 + Q) * η - 1) * x)`. -/
theorem wenzlGtOneWeight_cycleWord_hasProd {q : ℂˣ} {Q : ℝ} (hQ : 1 < Q) (hqQ : (q : ℂ) ^ 2 = Q)
    {η : ℝ} (hη : η ∈ Set.Icc (1 / (1 + Q)) (Q / (1 + Q))) {x : ℂ} (hx : Q * ‖x‖ < 1) :
    HasProd (fun a : ℕ ⊕ₗ ℕᵒᵈ ↦
        if wenzlGtOnePos a then (1 - (wenzlGtOneWeight Q η a : ℂ) * x) /
            (1 - (q : ℂ) ^ 2 * (wenzlGtOneWeight Q η a : ℂ) * x)
        else (1 + (q : ℂ) ^ 2 * (wenzlGtOneWeight Q η a : ℂ) * x) /
            (1 + (wenzlGtOneWeight Q η a : ℂ) * x))
      ((1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) / (1 - (((1 + Q) * η - 1 : ℝ) : ℂ) * x)) := by
  have hmax : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) = Q := by
    simp only [hqQ, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    grind
  have hsx : ‖(((1 + Q) * η - 1 : ℝ) : ℂ) * x‖ < 1 := by
    have h1Q : 0 < 1 + Q := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [(div_le_iff₀ h1Q).mp hη.1])]
    exact (mul_le_mul_of_nonneg_right (by linarith [(le_div_iff₀ h1Q).mp hη.2])
      (norm_nonneg x)).trans_lt hx
  exact hasProd_ofReal_cycleWord wenzlGtOnePos hqQ (summable_norm_wenzlGtOneWeight hQ η) (
    wenzlGtOneWeight_nonneg hQ hη) (tsum_wenzlGtOneWeight hQ η) η (wenzlGtOneWeight_leftSlice hQ η)
    (by rwa [hmax]) hsx

/-- **Telescoping infinite product for Wenzl's `0 < Q < 1` countable model.** For `0 < Q < 1`,
`η ∈ [Q / (1 + Q), 1 / (1 + Q)]`, and `‖x‖ < 1`, the cycle-trace product converges to
`(1 + (Q - (1 + Q) * η) * x) / (1 - ((1 + Q) * η - 1) * x)`. -/
theorem wenzlLtOneWeight_cycleWord_hasProd {q : ℂˣ} {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1)
    (hqQ : (q : ℂ) ^ 2 = Q) {η : ℝ} (hη : η ∈ Set.Icc (Q / (1 + Q)) (1 / (1 + Q)))
    {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun a : ℕ ⊕ₗ ℕᵒᵈ ↦
        if wenzlLtOnePos a then (1 - (wenzlLtOneWeight Q η a : ℂ) * x) /
            (1 - (q : ℂ) ^ 2 * (wenzlLtOneWeight Q η a : ℂ) * x)
        else (1 + (q : ℂ) ^ 2 * (wenzlLtOneWeight Q η a : ℂ) * x) /
            (1 + (wenzlLtOneWeight Q η a : ℂ) * x))
      ((1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) / (1 - (((1 + Q) * η - 1 : ℝ) : ℂ) * x)) := by
  have hmax : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) = 1 := by
    simp only [hqQ, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    grind
  have hsx : ‖(((1 + Q) * η - 1 : ℝ) : ℂ) * x‖ < 1 := by
    have h1Q : 0 < 1 + Q := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonpos (by linarith [(le_div_iff₀ h1Q).mp hη.2])]
    have h1 : -((1 + Q) * η - 1) ≤ 1 := by linarith [(div_le_iff₀ h1Q).mp hη.1]
    exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg x)).trans_lt (by simpa using hx)
  exact hasProd_ofReal_cycleWord wenzlLtOnePos hqQ (summable_norm_wenzlLtOneWeight hQ0 hQ1 η) (
    wenzlLtOneWeight_nonneg hQ0 hη) (tsum_wenzlLtOneWeight hQ0 hQ1 η) η (
      wenzlLtOneWeight_leftSlice hQ0 hQ1 η) (by rwa [hmax, one_mul]) hsx

end TauCeti.TypeAHeckeAlgebra
