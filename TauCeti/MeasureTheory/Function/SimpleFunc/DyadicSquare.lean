/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Bounded dyadic approximations of the square

For `|x| < 2ᵏ`, `TauCeti.dyadicSquareApprox k` rounds `|x|` down on the mesh `2⁻ᵏ`
and squares the result, taking values in `[0, 2^(2k))`. It vanishes when `|x| ≥ 2ᵏ`.
These finite Borel simple functions increase pointwise to the square. The expanding cutoff
is essential: a fixed value window would not approximate an unbounded random variable.

Whenever the square belongs to Lᵖ for finite `p`, the approximations converge in Lᵖ.
In particular, an L⁴ random variable gives L² convergence and explicit bounded simple
heights for elementary stochastic integrands with squared random heights.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace TauCeti

/-- The dyadic square approximation with mesh `2⁻ᵏ` and absolute-value cutoff `2ᵏ`.
It assigns `((j : ℝ) / 2 ^ k) ^ 2` when `|x| ∈ [j / 2^k, (j + 1) / 2^k)`
for `j < 2^(2*k)`, and zero when `|x| ≥ 2^k`. The half-open endpoint convention
applies to the magnitude `|x|`, not to the signed input `x`. -/
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
@[grind =]
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
@[grind =]
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
theorem dyadicSquareApprox_apply_zero (k : ℕ) : dyadicSquareApprox k 0 = 0 := by
  exact le_antisymm (by simpa using dyadicSquareApprox_le_sq k 0)
    (dyadicSquareApprox_nonneg k 0)

/-- The coarsest approximation is identically zero. -/
@[simp]
theorem dyadicSquareApprox_zero : dyadicSquareApprox 0 = 0 := by
  ext x
  simp [dyadicSquareApprox_apply]

/-- The approximation depends only on the magnitude of its argument. -/
@[simp]
theorem dyadicSquareApprox_abs (k : ℕ) (x : ℝ) :
    dyadicSquareApprox k |x| = dyadicSquareApprox k x := by
  simp only [dyadicSquareApprox_apply, abs_abs]

/-- Dyadic square approximation is even. -/
@[simp]
theorem dyadicSquareApprox_neg (k : ℕ) (x : ℝ) :
    dyadicSquareApprox k (-x) = dyadicSquareApprox k x := by
  simp only [dyadicSquareApprox_apply, abs_neg]

grind_pattern dyadicSquareApprox_nonneg => dyadicSquareApprox k x
grind_pattern dyadicSquareApprox_le_sq => dyadicSquareApprox k x
grind_pattern dyadicSquareApprox_lt_pow => dyadicSquareApprox k x

end TauCeti

namespace MeasureTheory.MemLp

open TauCeti

/-- Dyadic square approximation preserves Lᵖ membership of the square, even when only
the square, rather than the original function, is a.e. measurable. -/
theorem dyadicSquareApprox {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} {f : Ω → ℝ} (hf : MemLp (fun ω ↦ f ω ^ 2) p μ) (k : ℕ) :
    MemLp (fun ω ↦ TauCeti.dyadicSquareApprox k (f ω)) p μ := by
  have hm := (TauCeti.dyadicSquareApprox k).measurable.comp_aemeasurable
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable).aemeasurable
  refine hf.mono (by simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
    dyadicSquareApprox_abs] using hm.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun ω ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (dyadicSquareApprox_nonneg k (f ω)),
      abs_sq] using dyadicSquareApprox_le_sq k (f ω)

/-- If the square belongs to Lᵖ for a finite exponent, its explicit bounded dyadic
approximations converge in Lᵖ. No finiteness assumption on the measure is needed. -/
theorem tendsto_eLpNorm_dyadicSquareApprox_sub_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : ℝ≥0∞} {f : Ω → ℝ} (hf : MemLp (fun ω ↦ f ω ^ 2) p μ)
    (hp : p ≠ ∞) :
    Tendsto (fun k ↦ eLpNorm (fun ω ↦ TauCeti.dyadicSquareApprox k (f ω) - f ω ^ 2) p μ)
      atTop (𝓝 0) := by
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) hp
    (Eventually.of_forall fun k ↦ (hf.dyadicSquareApprox k).aestronglyMeasurable) hf
    (Eventually.of_forall fun k ↦ Eventually.of_forall fun ω ↦ ?_)
    (Eventually.of_forall fun ω ↦ tendsto_dyadicSquareApprox (f ω))
  simp only [ENNReal.coe_one, one_mul, enorm_le_iff_norm_le, Real.norm_eq_abs, abs_sq]
  rw [abs_of_nonpos (sub_nonpos.mpr (dyadicSquareApprox_le_sq _ _))]
  linarith [dyadicSquareApprox_nonneg k (f ω)]

end MeasureTheory.MemLp
