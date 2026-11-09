/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Exponential weighting of measures with a uniform interval bound

A family of measures on the real line with a common bound on the mass of every unit interval
becomes a uniformly bounded tight family after multiplication by `exp (-|x|)`. The estimate
uses the summable geometric bounds on the shells `n ≤ |x| ≤ n + 1`; no finiteness of the original
measures is required.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

private theorem exp_neg_abs_shell_bound (μ : Measure ℝ) (C : ℝ≥0)
    (hμ : ∀ a : ℝ, μ (Icc a (a + 1)) ≤ C) (n : ℕ) :
    ∫⁻ x in {x : ℝ | (n : ℝ) ≤ |x| ∧ |x| ≤ n + 1},
      ENNReal.ofReal (Real.exp (-|x|)) ∂μ ≤
      ENNReal.ofReal (Real.exp (-1)) ^ n * (C + C) := by
  let A := {x : ℝ | (n : ℝ) ≤ |x| ∧ |x| ≤ n + 1}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hm : μ A ≤ (C + C : ℝ≥0) := by
    have hs : A ⊆ Icc (n : ℝ) (n + 1) ∪ Icc (-(n : ℝ) - 1) (-(n : ℝ)) := by
      intro x hx
      dsimp [A] at hx
      rcases le_total 0 x with hx₀ | hx₀
      · left; simpa [abs_of_nonneg hx₀] using hx
      · right; rw [abs_of_nonpos hx₀] at hx; constructor <;> linarith
    exact (measure_mono hs).trans ((measure_union_le _ _).trans
      (by simpa only [ENNReal.coe_add, sub_add_cancel] using
        add_le_add (hμ n) (hμ (-(n : ℝ) - 1))))
  calc
    _ ≤ ∫⁻ _x in A, ENNReal.ofReal (Real.exp (-(n : ℝ))) ∂μ :=
      setLIntegral_mono' hA fun x hx ↦ ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (neg_le_neg hx.1))
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ))) * (C + C : ℝ≥0) := by
      simpa [mul_comm] using mul_le_mul_left hm (ENNReal.ofReal (Real.exp (-(n : ℝ))))
    _ = _ := by
      have hneg : -(n : ℝ) = n * (-1 : ℝ) := by ring
      rw [hneg, Real.exp_nat_mul,
        ENNReal.ofReal_pow (Real.exp_pos _).le, ENNReal.coe_add]

private theorem exp_neg_abs_tail_bound (μ : Measure ℝ) (C : ℝ≥0)
    (hμ : ∀ a : ℝ, μ (Icc a (a + 1)) ≤ C) (N : ℕ) :
    ∫⁻ x in {x : ℝ | (N : ℝ) ≤ |x|}, ENNReal.ofReal (Real.exp (-|x|)) ∂μ ≤
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-1)) ^ (n + N) * (C + C) := by
  let A (n : ℕ) := {x : ℝ | ((n + N : ℕ) : ℝ) ≤ |x| ∧ |x| ≤ (n + N : ℕ) + 1}
  have hs : {x : ℝ | (N : ℝ) ≤ |x|} ⊆ ⋃ n, A n := by
    intro x hx
    simp only [mem_ofPred_eq] at hx
    refine mem_iUnion.2 ⟨⌊|x| - N⌋₊, ?_⟩
    have h₁ := Nat.floor_le (by linarith : 0 ≤ |x| - N)
    have h₂ := Nat.lt_floor_add_one (|x| - N)
    dsimp [A]
    push_cast
    constructor <;> linarith
  exact (lintegral_mono_set hs).trans ((lintegral_iUnion_le A _).trans
    (tsum_le_tsum fun n ↦ exp_neg_abs_shell_bound μ C hμ (n + N)))

/-- A common bound on the mass of unit intervals gives uniformly bounded total mass and
tightness after weighting every measure by `exp (-|x|)`. -/
theorem exists_bound_isTightMeasureSet_withDensity_exp_neg_abs {ι : Type*}
    (μ : ι → Measure ℝ) (C : ℝ≥0) (hμ : ∀ i a, μ i (Icc a (a + 1)) ≤ C) :
    ∃ B : ℝ≥0,
      (∀ i, (μ i).withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-|x|))) univ ≤ B) ∧
      IsTightMeasureSet (range fun i ↦
        (μ i).withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-|x|)))) := by
  let b (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-1)) ^ n * (C + C)
  have hb : ∑' n, b n ≠ ∞ := by
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top ((tsum_geometric_lt_top.mpr
      (by simp)).ne)
      ENNReal.coe_ne_top
  refine ⟨(∑' n, b n).toNNReal, ?_, ?_⟩
  · intro i
    rw [ENNReal.coe_toNNReal hb, withDensity_apply _ MeasurableSet.univ]
    simpa [b] using exp_neg_abs_tail_bound (μ i) C (hμ i) 0
  · apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp
      (ENNReal.tendsto_sum_nat_add b hb)) ε hε
    refine ⟨Icc (-(N : ℝ)) N, isCompact_Icc, ?_⟩
    rintro ν ⟨i, rfl⟩
    rw [withDensity_apply _ measurableSet_Icc.compl]
    refine (lintegral_mono_set ?_).trans
      ((exp_neg_abs_tail_bound (μ i) C (hμ i) N).trans (hN N le_rfl))
    intro x hx
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact (neg_le_abs x).trans' (by linarith)
    · exact hx.le.trans (le_abs_self x)

end MeasureTheory
