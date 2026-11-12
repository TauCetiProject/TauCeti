/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Dyadic simple approximations to the square

`TauCeti.dyadicSquareApprox k` rounds the absolute value down to mesh `2⁻ᵏ`, squares
the result, and discards values outside `[0, 2ᵏ)`. It is a finite Borel simple
function. Its values increase to the square, are bounded by the square, and have
a deterministic bound. These particular approximations give finite-valued
predictable approximants to squared Brownian left-endpoint samples.

The expanding value window is essential: a fixed cutoff would not converge to
the square at every real input. The interval convention is `[j/2ᵏ, (j+1)/2ᵏ)`.
-/

public section

noncomputable section

open MeasureTheory Set Finset Filter
open scoped Topology ENNReal

namespace TauCeti

/-- The finite Borel simple function
`∑_{j < 2^(2k)} (j/2^k)² 1_{[j/2^k,(j+1)/2^k)}(|x|)`.
The value window grows with `k`, while the mesh tends to zero. -/
def dyadicSquareApprox (k : ℕ) : SimpleFunc ℝ ℝ :=
  ∑ j ∈ range (2 ^ (2 * k)),
    (SimpleFunc.const ℝ (((j : ℝ) / 2 ^ k) ^ 2)).restrict
      {x | |x| ∈ Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k)}

/-- Evaluation of the dyadic square approximation as a finite indicator sum. -/
theorem dyadicSquareApprox_apply (k : ℕ) (x : ℝ) :
    dyadicSquareApprox k x = ∑ j ∈ range (2 ^ (2 * k)),
      (Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k)).indicator
        (fun _ ↦ ((j : ℝ) / 2 ^ k) ^ 2) |x| := by
  simp only [dyadicSquareApprox, sum_apply]
  apply sum_congr rfl
  intro j _
  have hm : MeasurableSet {y : ℝ | |y| ∈
      Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k)} :=
    measurableSet_Ico.preimage continuous_abs.measurable
  rw [SimpleFunc.restrict_apply _ hm]
  by_cases hx : |x| ∈ Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k)
  all_goals simp only [indicator_apply, mem_ofPred_eq, SimpleFunc.const_apply, hx, ite_true,
    ite_false]

/-- On each dyadic cell, the approximation is the square of its left endpoint. -/
theorem dyadicSquareApprox_of_mem_Ico {k j : ℕ} (hj : j < 2 ^ (2 * k)) {x : ℝ}
    (hx : |x| ∈ Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k)) :
    dyadicSquareApprox k x = ((j : ℝ) / 2 ^ k) ^ 2 := by
  rw [dyadicSquareApprox_apply, sum_eq_single_of_mem j (mem_range.mpr hj),
    indicator_of_mem hx]
  intro i _ hij
  apply indicator_of_notMem
  intro hi
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hji : (j : ℝ) < i + 1 := by
    have := hx.1.trans_lt hi.2
    exact (div_lt_div_iff_of_pos_right hp).mp this
  have hij' : (i : ℝ) < j + 1 := by
    have := hi.1.trans_lt hx.2
    exact (div_lt_div_iff_of_pos_right hp).mp this
  have hji' : j < i + 1 := by exact_mod_cast hji
  have hij'' : i < j + 1 := by exact_mod_cast hij'
  exact hij (by omega)

/-- Outside the expanding value window the approximation vanishes. -/
@[simp]
theorem dyadicSquareApprox_of_le_abs {k : ℕ} {x : ℝ} (hx : (2 : ℝ) ^ k ≤ |x|) :
    dyadicSquareApprox k x = 0 := by
  rw [dyadicSquareApprox_apply]
  apply sum_eq_zero
  intro j hj
  apply indicator_of_notMem
  intro h
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hj' : (j + 1 : ℝ) ≤ (2 ^ k) ^ 2 := by
    have h := Nat.succ_le_of_lt (mem_range.mp hj)
    rw [Nat.mul_comm 2 k, pow_mul] at h
    exact_mod_cast h
  have : |x| < (2 : ℝ) ^ k := h.2.trans_le ((div_le_iff₀ hp).mpr (by nlinarith))
  exact this.not_ge hx

/-- Inside the window, evaluation is the squared dyadic floor. -/
theorem dyadicSquareApprox_of_abs_lt {k : ℕ} {x : ℝ} (hx : |x| < (2 : ℝ) ^ k) :
    dyadicSquareApprox k x = ((⌊|x| * (2 : ℝ) ^ k⌋₊ : ℝ) / 2 ^ k) ^ 2 := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  apply dyadicSquareApprox_of_mem_Ico
  · apply (Nat.floor_lt (by positivity)).mpr
    push_cast
    rw [Nat.mul_comm 2 k, pow_mul]
    nlinarith
  · constructor
    · exact (div_le_iff₀ hp).mpr (Nat.floor_le (by positivity))
    · exact (lt_div_iff₀ hp).mpr (Nat.lt_floor_add_one _)

/-- The approximations are nonnegative. -/
theorem dyadicSquareApprox_nonneg (k : ℕ) (x : ℝ) : 0 ≤ dyadicSquareApprox k x := by
  rw [dyadicSquareApprox_apply]
  exact sum_nonneg fun j _ ↦ indicator_nonneg (fun _ _ ↦ sq_nonneg _) _

/-- Each approximation is bounded above by the square being approximated. -/
theorem dyadicSquareApprox_le_sq (k : ℕ) (x : ℝ) : dyadicSquareApprox k x ≤ x ^ 2 := by
  by_cases hx : |x| < (2 : ℝ) ^ k
  · rw [dyadicSquareApprox_of_abs_lt hx, ← sq_abs x]
    apply pow_le_pow_left₀ (by positivity)
    exact (div_le_iff₀ (by positivity)).mpr (Nat.floor_le (by positivity))
  · rw [dyadicSquareApprox_of_le_abs (le_of_not_gt hx)]
    exact sq_nonneg _

/-- Every approximant vanishes at zero. -/
@[simp]
theorem dyadicSquareApprox_zero (k : ℕ) : dyadicSquareApprox k 0 = 0 := by
  exact le_antisymm (by simpa using dyadicSquareApprox_le_sq k 0)
    (dyadicSquareApprox_nonneg k 0)

/-- A deterministic bound on the range, independent of the input. -/
theorem dyadicSquareApprox_le (k : ℕ) (x : ℝ) :
    dyadicSquareApprox k x ≤ ((2 : ℝ) ^ k) ^ 2 := by
  by_cases hx : |x| < (2 : ℝ) ^ k
  · exact (dyadicSquareApprox_le_sq k x).trans (by
      rw [← sq_abs x]
      exact pow_le_pow_left₀ (abs_nonneg _) hx.le _)
  · rw [dyadicSquareApprox_of_le_abs (le_of_not_gt hx)]
    positivity

/-- Refining the mesh and expanding the window increases the approximation. -/
theorem monotone_dyadicSquareApprox (x : ℝ) : Monotone (fun k ↦ dyadicSquareApprox k x) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hx : |x| < (2 : ℝ) ^ k
  · have hy : |x| < (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      have : (0 : ℝ) < 2 ^ k := by positivity
      linarith
    rw [dyadicSquareApprox_of_abs_lt hx, dyadicSquareApprox_of_abs_lt hy]
    have hfloor : 2 * ⌊|x| * (2 : ℝ) ^ k⌋₊ ≤ ⌊|x| * (2 : ℝ) ^ (k + 1)⌋₊ := by
      apply Nat.le_floor
      push_cast
      have := Nat.floor_le (mul_nonneg (abs_nonneg x) (by positivity : 0 ≤ (2 : ℝ) ^ k))
      rw [pow_succ]
      nlinarith
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
    have hf : 2 * (⌊|x| * (2 : ℝ) ^ k⌋₊ : ℝ) ≤
        (⌊|x| * (2 : ℝ) ^ (k + 1)⌋₊ : ℝ) := by exact_mod_cast hfloor
    rw [pow_succ] at hf
    nlinarith [mul_le_mul_of_nonneg_right hf (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)]
  · rw [dyadicSquareApprox_of_le_abs (le_of_not_gt hx)]
    exact dyadicSquareApprox_nonneg _ _

/-- The finite-valued dyadic approximations converge pointwise to the square. -/
theorem tendsto_dyadicSquareApprox (x : ℝ) :
    Tendsto (fun k ↦ dyadicSquareApprox k x) atTop (𝓝 (x ^ 2)) := by
  have hpow : Tendsto (fun k : ℕ ↦ (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h := ((tendsto_nat_floor_mul_div_atTop (abs_nonneg x)).comp hpow).pow 2
  rw [sq_abs] at h
  apply h.congr'
  filter_upwards [hpow.eventually (eventually_gt_atTop |x|)] with k hk
  exact (dyadicSquareApprox_of_abs_lt hk).symm

/-- Composing the approximations with a random variable preserves every `Lᵖ`
membership possessed by its square. No finiteness of the measure is required. -/
theorem memLp_dyadicSquareApprox_comp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {X : α → ℝ} {p : ℝ≥0∞} (k : ℕ) (hX : AEStronglyMeasurable X μ)
    (hXsq : MemLp (fun a ↦ X a ^ 2) p μ) :
    MemLp (fun a ↦ dyadicSquareApprox k (X a)) p μ := by
  apply hXsq.mono' ((dyadicSquareApprox k).measurable.comp_aemeasurable
    hX.aemeasurable).aestronglyMeasurable
  exact .of_forall fun a ↦ by
    simp only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (dyadicSquareApprox_nonneg _ _)]
    exact dyadicSquareApprox_le_sq _ _

/-- If the square is in `L²`, its specified dyadic finite-value approximations
converge in native `L²`. Equivalently, the input has a finite fourth moment. -/
theorem tendsto_eLpNorm_dyadicSquareApprox_sub_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {X : α → ℝ} (hX : AEStronglyMeasurable X μ)
    (hXsq : MemLp (fun a ↦ X a ^ 2) 2 μ) :
    Tendsto (fun k ↦ eLpNorm (fun a ↦ dyadicSquareApprox k (X a) - X a ^ 2) 2 μ)
      atTop (𝓝 0) := by
  have hmem (k : ℕ) : MemLp (fun a ↦ dyadicSquareApprox k (X a) - X a ^ 2) 2 μ :=
    (memLp_dyadicSquareApprox_comp k hX hXsq).sub hXsq
  have hlim := tendsto_integral_of_dominated_convergence
    (f := fun _ : α ↦ (0 : ℝ)) (fun a ↦ (X a ^ 2) ^ 2)
    (fun k ↦ (hmem k).integrable_sq.aestronglyMeasurable) hXsq.integrable_sq ?_ ?_
  · have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim.sqrt
    simp only [integral_zero, Real.sqrt_zero, ENNReal.ofReal_zero] at h
    convert h using 1
    ext k
    rw [(hmem k).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs]
  · intro k
    exact .of_forall fun a ↦ by
      have h0 := dyadicSquareApprox_nonneg k (X a)
      have hle := dyadicSquareApprox_le_sq k (X a)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (X a)]
  · exact .of_forall fun a ↦ by
      have h := ((tendsto_dyadicSquareApprox (X a)).sub
        (tendsto_const_nhds (x := X a ^ 2))).pow 2
      rw [sub_self, zero_pow two_ne_zero] at h
      exact h

end TauCeti
