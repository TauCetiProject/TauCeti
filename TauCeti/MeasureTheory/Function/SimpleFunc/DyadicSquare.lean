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

/-!
# Bounded dyadic approximations of the square

`TauCeti.dyadicSquareApprox k` rounds the absolute value down on the mesh `2⁻ᵏ`,
squares it, and discards values outside `[0, 2ᵏ)`. These finite Borel simple functions
increase pointwise to the square. The expanding cutoff is essential: a fixed value
window would not approximate an unbounded random variable.

For an L⁴ random variable the approximations converge in L². This gives explicit bounded
simple heights for elementary stochastic integrands with squared random heights.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace TauCeti

/-- The dyadic square approximation with mesh `2⁻ᵏ` and absolute-value cutoff `2ᵏ`.
The half-open cells include their lower endpoint and exclude their upper endpoint. -/
def dyadicSquareApprox (k : ℕ) : SimpleFunc ℝ ℝ :=
  ∑ j ∈ Finset.range (2 ^ (2 * k)),
    (SimpleFunc.const ℝ (((j : ℝ) / 2 ^ k) ^ 2)).restrict
      {x | |x| ∈ Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k)}

/-- The explicit finite indicator-sum formula. -/
theorem dyadicSquareApprox_apply (k : ℕ) (x : ℝ) :
    dyadicSquareApprox k x = ∑ j ∈ Finset.range (2 ^ (2 * k)),
      (Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k)).indicator
        (fun _ ↦ ((j : ℝ) / 2 ^ k) ^ 2) |x| := by
  simp only [dyadicSquareApprox, sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hs : MeasurableSet {x : ℝ | |x| ∈
      Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k)} :=
    measurableSet_Ico.preimage continuous_abs.measurable
  rw [SimpleFunc.restrict_apply _ hs]
  by_cases h : |x| ∈ Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k) <;>
    simp_all [Set.indicator]

private theorem mem_dyadicCell_iff (k j : ℕ) (x : ℝ) :
    |x| ∈ Ico ((j : ℝ) / 2 ^ k) ((j + 1 : ℝ) / 2 ^ k) ↔
      ⌊|x| * 2 ^ k⌋₊ = j := by
  rw [Nat.floor_eq_iff (by positivity)]
  simp only [mem_Ico, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ k),
    lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)]

/-- Below the cutoff the approximation is the square of the lower dyadic rounding. -/
theorem dyadicSquareApprox_of_abs_lt {k : ℕ} {x : ℝ} (hx : |x| < 2 ^ k) :
    dyadicSquareApprox k x = ((⌊|x| * 2 ^ k⌋₊ : ℝ) / 2 ^ k) ^ 2 := by
  rw [dyadicSquareApprox_apply]
  have hfloor : ⌊|x| * 2 ^ k⌋₊ < 2 ^ (2 * k) := by
    rw [Nat.floor_lt (by positivity)]
    push_cast
    simpa [two_mul, pow_add] using mul_lt_mul_of_pos_right hx
      (by positivity : (0 : ℝ) < 2 ^ k)
  rw [Finset.sum_eq_single ⌊|x| * 2 ^ k⌋₊]
  · rw [indicator_of_mem ((mem_dyadicCell_iff _ _ _).mpr rfl)]
  · intro j _ hj
    rw [indicator_of_notMem]
    exact fun h ↦ hj ((mem_dyadicCell_iff _ _ _).mp h).symm
  · simp [hfloor]

/-- At and beyond the cutoff all cells vanish. In particular the cutoff is excluded. -/
theorem dyadicSquareApprox_of_le_abs {k : ℕ} {x : ℝ} (hx : 2 ^ k ≤ |x|) :
    dyadicSquareApprox k x = 0 := by
  rw [dyadicSquareApprox_apply]
  apply Finset.sum_eq_zero
  intro j hj
  apply indicator_of_notMem
  intro h
  have hj' : (j + 1 : ℝ) ≤ 2 ^ (2 * k) := by
    exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
  have hp : (2 : ℝ) ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
  have := h.2
  rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)] at this
  nlinarith [mul_le_mul_of_nonneg_right hx (by positivity : (0 : ℝ) ≤ 2 ^ k)]

/-- The approximation is nonnegative. -/
theorem dyadicSquareApprox_nonneg (k : ℕ) (x : ℝ) : 0 ≤ dyadicSquareApprox k x := by
  by_cases hx : |x| < 2 ^ k
  · rw [dyadicSquareApprox_of_abs_lt hx]
    positivity
  · rw [dyadicSquareApprox_of_le_abs (le_of_not_gt hx)]

/-- Dyadic square approximations never exceed the square. -/
theorem dyadicSquareApprox_le_sq (k : ℕ) (x : ℝ) : dyadicSquareApprox k x ≤ x ^ 2 := by
  by_cases hx : |x| < 2 ^ k
  · rw [dyadicSquareApprox_of_abs_lt hx, ← sq_abs x]
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)]
    exact Nat.floor_le (by positivity)
  · rw [dyadicSquareApprox_of_le_abs (le_of_not_gt hx)]
    positivity

/-- Both the refining mesh and the expanding cutoff preserve monotonicity. -/
theorem monotone_dyadicSquareApprox (x : ℝ) : Monotone (fun k ↦ dyadicSquareApprox k x) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hx : |x| < 2 ^ k
  · have hx' : |x| < 2 ^ (k + 1) := hx.trans_le (by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k])
    rw [dyadicSquareApprox_of_abs_lt hx, dyadicSquareApprox_of_abs_lt hx']
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)
      (by positivity : (0 : ℝ) < 2 ^ (k + 1)), pow_succ]
    have h : 2 * ⌊|x| * 2 ^ k⌋₊ ≤ ⌊|x| * 2 ^ (k + 1)⌋₊ := by
      apply Nat.le_floor
      push_cast
      rw [pow_succ]
      nlinarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ |x| * 2 ^ k)]
    have h' : (2 : ℝ) * ⌊|x| * 2 ^ k⌋₊ ≤ ⌊|x| * (2 ^ k * 2)⌋₊ := by
      exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ 2 ^ k)]
  · rw [dyadicSquareApprox_of_le_abs (le_of_not_gt hx)]
    exact dyadicSquareApprox_nonneg _ _

/-- The finite Borel simple functions converge pointwise to the square. -/
theorem tendsto_dyadicSquareApprox (x : ℝ) :
    Tendsto (fun k ↦ dyadicSquareApprox k x) atTop (𝓝 (x ^ 2)) := by
  have hp : Tendsto (fun k : ℕ ↦ (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h := (tendsto_nat_floor_mul_div_atTop (abs_nonneg x)).comp hp
  have hevent : ∀ᶠ k : ℕ in atTop, dyadicSquareApprox k x =
      ((⌊|x| * 2 ^ k⌋₊ : ℝ) / 2 ^ k) ^ 2 :=
    (hp.eventually (eventually_gt_atTop |x|)).mono fun _ hk ↦ dyadicSquareApprox_of_abs_lt hk
  exact Tendsto.congr' (hevent.mono fun _ hk ↦ hk.symm)
    (by simpa only [Function.comp_apply, sq_abs] using h.pow 2)

/-- A uniform bound on the values, independent of the argument. -/
theorem dyadicSquareApprox_lt_pow (k : ℕ) (x : ℝ) :
    dyadicSquareApprox k x < (2 : ℝ) ^ (2 * k) := by
  by_cases hx : |x| < 2 ^ k
  · have h := mul_self_lt_mul_self (abs_nonneg x) hx
    calc
      dyadicSquareApprox k x ≤ x ^ 2 := dyadicSquareApprox_le_sq k x
      _ < (2 : ℝ) ^ (2 * k) := by simpa [two_mul, pow_add, ← sq_abs x, pow_two] using h
  · rw [dyadicSquareApprox_of_le_abs (le_of_not_gt hx)]
    positivity

/-- The approximation vanishes at zero. -/
@[simp]
theorem dyadicSquareApprox_zero (k : ℕ) : dyadicSquareApprox k 0 = 0 := by
  exact le_antisymm (by simpa using dyadicSquareApprox_le_sq k 0)
    (dyadicSquareApprox_nonneg k 0)

end TauCeti

namespace MeasureTheory.MemLp

open TauCeti

/-- For an L⁴ random variable, the explicit bounded dyadic square approximations converge
in L². No finiteness assumption on the measure is needed. -/
theorem tendsto_eLpNorm_dyadicSquareApprox_sub_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 4 μ) :
    Tendsto (fun k ↦ eLpNorm (fun ω ↦ dyadicSquareApprox k (f ω) - f ω ^ 2) 2 μ)
      atTop (𝓝 0) := by
  let : ENNReal.HolderTriple 4 4 2 := .of_toReal (by norm_num [Real.holderTriple_iff])
  have hsq : MemLp (fun ω ↦ f ω ^ 2) 2 μ := by
    simpa only [pow_two, Pi.mul_def] using hf.mul hf
  have hbound (k : ℕ) (ω : Ω) :
      ‖dyadicSquareApprox k (f ω) - f ω ^ 2‖ ≤ f ω ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (dyadicSquareApprox_le_sq _ _))]
    linarith [dyadicSquareApprox_nonneg k (f ω)]
  have hmem (k : ℕ) : MemLp (fun ω ↦ dyadicSquareApprox k (f ω) - f ω ^ 2) 2 μ :=
    hsq.mono (((dyadicSquareApprox k).measurable.comp_aemeasurable
      hf.aestronglyMeasurable.aemeasurable).aestronglyMeasurable.sub
        hsq.aestronglyMeasurable) (Eventually.of_forall fun ω ↦ by
          simpa only [Real.norm_eq_abs, abs_sq] using hbound k ω)
  have hlim := tendsto_integral_of_dominated_convergence
    (f := fun _ : Ω ↦ (0 : ℝ)) (bound := fun ω ↦ (f ω ^ 2) ^ 2)
    (fun k ↦ (hmem k).integrable_sq.aestronglyMeasurable) hsq.integrable_sq
    (fun k ↦ Eventually.of_forall fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
        pow_le_pow_left₀ (norm_nonneg _) (hbound k ω) 2)
    (Eventually.of_forall fun ω ↦ by
      have h := ((tendsto_dyadicSquareApprox (f ω)).sub
        (tendsto_const_nhds (x := f ω ^ 2))).pow 2
      rw [sub_self, zero_pow two_ne_zero] at h
      exact h)
  have hnorm := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim.sqrt
  simp only [integral_zero, Real.sqrt_zero, ENNReal.ofReal_zero] at hnorm
  convert hnorm using 1
  ext k
  rw [(hmem k).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp [Real.sqrt_eq_rpow, Real.norm_eq_abs]

end MeasureTheory.MemLp
