/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.CycleWord
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.WenzlInterval.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Cycle-trace generating products for Wenzl's continuous interval models

Over `ℂ`, the cycle-trace infinite products of the countable two-sided geometric models
`TauCeti.TypeAHeckeAlgebra.wenzlGtOneWeight` (`1 < Q`) and
`TauCeti.TypeAHeckeAlgebra.wenzlLtOneWeight` (`0 < Q < 1`) telescope to the rational function
`(1 + (Q - (1 + Q) * η) * x) / (1 - ((1 + Q) * η - 1) * x)`
(`TauCeti.TypeAHeckeAlgebra.wenzlGtOneWeight_cycleWord_hasProd`,
`TauCeti.TypeAHeckeAlgebra.wenzlLtOneWeight_cycleWord_hasProd`).

## Main results

* `TauCeti.TypeAHeckeAlgebra.wenzlGtOneWeight_cycleWord_hasProd`: telescoping infinite product on
  `Q * ‖x‖ < 1` for `1 < Q`.
* `TauCeti.TypeAHeckeAlgebra.wenzlLtOneWeight_cycleWord_hasProd`: telescoping infinite product on
  `‖x‖ < 1` for `0 < Q < 1`.
-/

public section

open OrderDual

namespace TauCeti.TypeAHeckeAlgebra

private theorem hasProd_ofReal_cycleWord {ι : Type*} [LinearOrder ι] (pos : ι → Prop)
    [DecidablePred pos] {q : ℂˣ} {Q : ℝ} (hqQ : (q : ℂ) ^ 2 = Q) {w : ι → ℝ}
    (hw : Summable fun a ↦ ‖w a‖) (hw0 : ∀ a, 0 ≤ w a) (hsum : (∑' a, w a) = 1)
    (η : ℝ) (hslice : ∀ b, (if pos b then Q else -1) * w b +
      (Q - 1) * (∑' a, if a < b then w a else 0) = (1 + Q) * η - 1)
    {x : ℂ} (hxM : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ‖x‖ < 1)
    (hsx : ‖(((1 + Q) * η - 1 : ℝ) : ℂ) * x‖ < 1) :
    HasProd (fun a : ι ↦
        if pos a then (1 - (w a : ℂ) * x) / (1 - (q : ℂ) ^ 2 * (w a : ℂ) * x)
        else (1 + (q : ℂ) ^ 2 * (w a : ℂ) * x) / (1 + (w a : ℂ) * x))
      ((1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) /
        (1 - (((1 + Q) * η - 1 : ℝ) : ℂ) * x)) := by
  have hp : Summable fun a ↦ ‖(w a : ℂ)‖ := hw.congr fun _ ↦ (Complex.norm_real _).symm
  have hnorm_sum : (∑' a, ‖(w a : ℂ)‖) = 1 := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg (hw0 _)] using hsum
  have hprod := (countableAtomicTrace_cycleWord_hasProd pos q _ hp (by rwa [hnorm_sum, mul_one])).2
  set s : ℝ := (1 + Q) * η - 1
  have htr (m : ℕ) : countableAtomicTrace pos q (fun a ↦ (w a : ℂ))
      hp (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1) = x * ((s : ℂ) * x) ^ m := by
    rw [countableAtomicTrace_ofReal_eq_ocneanuTrace_of_leftSlice pos hqQ hw η hsum hslice,
      toInfinite_cycleWord,
      (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace _).map_cycleWord,
      Nat.add_sub_cancel, mul_markovParam_proj_eq hqQ η]
    ring
  have hne : 1 - (s : ℂ) * x ≠ 0 := fun h0 ↦ by
    have : ‖(s : ℂ) * x‖ = 1 := by simpa [sub_eq_zero.mp h0] using norm_one (α := ℂ)
    linarith
  convert hprod using 1
  simp_rw [htr]
  rw [(summable_geometric_of_norm_lt_one hsx).tsum_mul_left,
    tsum_geometric_of_norm_lt_one hsx, hqQ, eq_comm, eq_div_iff hne]
  have hmul : (1 - (s : ℂ) * x)⁻¹ * (1 - (s : ℂ) * x) = 1 := inv_mul_cancel₀ hne
  dsimp only [s] at hmul ⊢
  push_cast at hmul ⊢
  linear_combination ((Q : ℂ) - 1) * x * hmul

/-- **Telescoping infinite product for Wenzl's `1 < Q` countable model.** For `1 < Q`,
`η ∈ [1 / (1 + Q), Q / (1 + Q)]`, and `Q * ‖x‖ < 1`, the cycle-trace product converges to
`(1 + (Q - (1 + Q) * η) * x) / (1 - ((1 + Q) * η - 1) * x)`. -/
theorem wenzlGtOneWeight_cycleWord_hasProd {q : ℂˣ} {Q : ℝ} (hQ : 1 < Q) (hqQ : (q : ℂ) ^ 2 = Q)
    {η : ℝ} (hη : η ∈ Set.Icc (1 / (1 + Q)) (Q / (1 + Q))) {x : ℂ} (hx : Q * ‖x‖ < 1) :
    HasProd (fun a : ℕ ⊕ₗ ℕᵒᵈ ↦
        if wenzlGtOnePos a then
          (1 - (wenzlGtOneWeight Q η a : ℂ) * x) /
            (1 - (q : ℂ) ^ 2 * (wenzlGtOneWeight Q η a : ℂ) * x)
        else
          (1 + (q : ℂ) ^ 2 * (wenzlGtOneWeight Q η a : ℂ) * x) /
            (1 + (wenzlGtOneWeight Q η a : ℂ) * x))
      ((1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) /
        (1 - (((1 + Q) * η - 1 : ℝ) : ℂ) * x)) := by
  have hmax : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) = Q := by
    rw [hqQ, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (zero_lt_one.trans hQ).le, Real.norm_of_nonneg (sub_nonneg.mpr hQ.le),
      max_eq_left (a := Q) (b := Q - 1) (by linarith), max_eq_right hQ.le]
  have hs0 : 0 ≤ (1 + Q) * η - 1 := by linarith [(div_le_iff₀ (by linarith : 0 < 1 + Q)).mp hη.1]
  have hsx : ‖(((1 + Q) * η - 1 : ℝ) : ℂ) * x‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
    exact (mul_le_mul_of_nonneg_right
      (by linarith [(le_div_iff₀ (by linarith : 0 < 1 + Q)).mp hη.2])
      (norm_nonneg x)).trans_lt hx
  exact hasProd_ofReal_cycleWord wenzlGtOnePos hqQ (summable_norm_wenzlGtOneWeight hQ η)
    (wenzlGtOneWeight_nonneg hQ hη) (tsum_wenzlGtOneWeight hQ η) η
    (wenzlGtOneWeight_leftSlice hQ η) (by rwa [hmax]) hsx

/-- **Telescoping infinite product for Wenzl's `0 < Q < 1` countable model.** For `0 < Q < 1`,
`η ∈ [Q / (1 + Q), 1 / (1 + Q)]`, and `‖x‖ < 1`, the cycle-trace product converges to
`(1 + (Q - (1 + Q) * η) * x) / (1 - ((1 + Q) * η - 1) * x)`. -/
theorem wenzlLtOneWeight_cycleWord_hasProd {q : ℂˣ} {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1)
    (hqQ : (q : ℂ) ^ 2 = Q) {η : ℝ} (hη : η ∈ Set.Icc (Q / (1 + Q)) (1 / (1 + Q)))
    {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun a : ℕ ⊕ₗ ℕᵒᵈ ↦
        if wenzlLtOnePos a then
          (1 - (wenzlLtOneWeight Q η a : ℂ) * x) /
            (1 - (q : ℂ) ^ 2 * (wenzlLtOneWeight Q η a : ℂ) * x)
        else
          (1 + (q : ℂ) ^ 2 * (wenzlLtOneWeight Q η a : ℂ) * x) /
            (1 + (wenzlLtOneWeight Q η a : ℂ) * x))
      ((1 + ((Q - (1 + Q) * η : ℝ) : ℂ) * x) /
        (1 - (((1 + Q) * η - 1 : ℝ) : ℂ) * x)) := by
  have hmax : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) = 1 := by
    rw [hqQ, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hQ0.le, Real.norm_of_nonpos (sub_nonpos.mpr hQ1.le), neg_sub]
    exact max_eq_left (max_le hQ1.le (by linarith))
  have hs0 : (1 + Q) * η - 1 ≤ 0 := by linarith [(le_div_iff₀ (by linarith : 0 < 1 + Q)).mp hη.2]
  have hs1 : -(1 - Q) ≤ (1 + Q) * η - 1 := by
    linarith [(div_le_iff₀ (by linarith : 0 < 1 + Q)).mp hη.1]
  have hs_le : -((1 + Q) * η - 1) ≤ 1 := by linarith
  have hsx : ‖(((1 + Q) * η - 1 : ℝ) : ℂ) * x‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonpos hs0]
    exact (mul_le_mul_of_nonneg_right hs_le (norm_nonneg x)).trans_lt (by simpa using hx)
  exact hasProd_ofReal_cycleWord wenzlLtOnePos hqQ (summable_norm_wenzlLtOneWeight hQ0 hQ1 η)
    (wenzlLtOneWeight_nonneg hQ0 hη) (tsum_wenzlLtOneWeight hQ0 hQ1 η) η
    (wenzlLtOneWeight_leftSlice hQ0 hQ1 η) (by rwa [hmax, one_mul]) hsx

end TauCeti.TypeAHeckeAlgebra
