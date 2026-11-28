/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Slope-restricted activation functions

A function `σ : ℝ → ℝ` is *slope-restricted in `[α, β]`* when
`0 ≤ (σ a - σ b - α * (a - b)) * (β * (a - b) - (σ a - σ b))` for all `a` and `b`, that is,
when each increment `σ a - σ b` lies between `α * (a - b)` and `β * (a - b)`. For `a ≠ b` this
says that the slope of `σ` between `a` and `b` lies between `α` and `β`. This quadratic form of
the condition is the one that the semidefinite Lipschitz certificates of neural networks use:
summed over the neurons of a layer with nonnegative weights, it gives the incremental quadratic
constraint that these certificates add to the quadratic form of a network.

The condition does not need `α ≤ β`: it is symmetric in `α` and `β`.

## Main declarations

* `TauCeti.SlopeRestricted`: `σ` is slope-restricted in `[α, β]`.
* `TauCeti.slopeRestricted_iff_mem_uIcc` and `TauCeti.slopeRestricted_iff_slope_mem_uIcc`: the
  condition says that each increment `σ a - σ b` lies in `[[α * (a - b), β * (a - b)]]`, or that
  each slope `slope σ a b` with `a ≠ b` lies in `[[α, β]]`.
* `TauCeti.slopeRestricted_of_monotone_of_lipschitzWith`: a monotone `K`-Lipschitz function is
  slope-restricted in `[0, K]`.
* `TauCeti.SlopeRestricted.abs_sub_le` and `TauCeti.SlopeRestricted.lipschitzWith`: a function
  that is slope-restricted in `[α, β]` is `max |α| |β|`-Lipschitz.
* `TauCeti.slopeRestricted_max_mul`: `t ↦ max (p * t) (q * t)` is slope-restricted in `[p, q]`.
  Special cases are the ReLU `t ↦ max 0 t` in `[0, 1]` (`TauCeti.slopeRestricted_relu`) and the
  leaky ReLU `t ↦ max t (c * t)` in `[c, 1]` for every real `c`
  (`TauCeti.slopeRestricted_leakyRelu`).
* `TauCeti.slopeRestricted_tanh`: `Real.tanh` is slope-restricted in `[0, 1]`.
* `TauCeti.SlopeRestricted.sum_nonneg`: the incremental quadratic constraint
  `0 ≤ ∑ p, 2 * t p * (Δy p - α * Δu p) * (β * Δu p - Δy p)` for weights `t ≥ 0`, where
  `Δu p = u p - u' p` and `Δy p = σ (u p) - σ (u' p)`.

## References

* M. Fazlyab, A. Robey, H. Hassani, M. Morari and G. J. Pappas, *Efficient and accurate
  estimation of Lipschitz constants for deep neural networks*, NeurIPS 2019, arXiv:1906.04893,
  Definition 1 and Lemma 1. The source assumes `0 ≤ α < β`; the statements here hold for all
  real `α` and `β`.
-/

public section

namespace TauCeti

variable {α β : ℝ} {σ : ℝ → ℝ}

/-- The function `σ : ℝ → ℝ` is *slope-restricted in `[α, β]`*: for all `a` and `b`, the
increment `σ a - σ b` satisfies
`0 ≤ (σ a - σ b - α * (a - b)) * (β * (a - b) - (σ a - σ b))`, so it lies between `α * (a - b)`
and `β * (a - b)`. -/
def SlopeRestricted (α β : ℝ) (σ : ℝ → ℝ) : Prop :=
  ∀ a b, 0 ≤ (σ a - σ b - α * (a - b)) * (β * (a - b) - (σ a - σ b))

/-- The defining inequality of `TauCeti.SlopeRestricted`. -/
theorem slopeRestricted_iff :
    SlopeRestricted α β σ ↔
      ∀ a b, 0 ≤ (σ a - σ b - α * (a - b)) * (β * (a - b) - (σ a - σ b)) :=
  Iff.rfl

/-- A function is slope-restricted in `[α, β]` if and only if each increment `σ a - σ b` lies
in the unordered interval `[[α * (a - b), β * (a - b)]]`. -/
theorem slopeRestricted_iff_mem_uIcc :
    SlopeRestricted α β σ ↔ ∀ a b, σ a - σ b ∈ Set.uIcc (α * (a - b)) (β * (a - b)) := by
  refine forall₂_congr fun a b ↦ ?_
  rw [mul_nonneg_iff, Set.mem_uIcc, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos]
  exact or_congr_right and_comm

/-- Slope restriction is symmetric in the two bounds. -/
theorem SlopeRestricted.symm (h : SlopeRestricted α β σ) : SlopeRestricted β α σ :=
  slopeRestricted_iff.2 fun a b ↦ (slopeRestricted_iff.1 h a b).trans_eq (by ring)

/-- Slope restriction is symmetric in the two bounds. -/
theorem slopeRestricted_comm : SlopeRestricted α β σ ↔ SlopeRestricted β α σ :=
  ⟨.symm, .symm⟩

/-- A function is slope-restricted in `[α, β]` if and only if its slope between any two distinct
points lies in the unordered interval `[[α, β]]`. -/
theorem slopeRestricted_iff_slope_mem_uIcc :
    SlopeRestricted α β σ ↔ ∀ a b, a ≠ b → slope σ a b ∈ Set.uIcc α β := by
  have key : ∀ a b, a ≠ b → (slope σ b a ∈ Set.uIcc α β ↔
      σ a - σ b ∈ Set.uIcc (α * (a - b)) (β * (a - b))) := by
    intro a b hab
    have hd := sub_ne_zero.2 hab
    rw [← div_mul_cancel₀ (σ a - σ b) hd, ← Set.mem_preimage (f := (· * (a - b))),
      Set.preimage_mul_const_uIcc hd, mul_div_cancel_right₀ _ hd, mul_div_cancel_right₀ _ hd,
      slope_def_field]
  rw [slopeRestricted_iff_mem_uIcc]
  refine ⟨fun h a b hab ↦ (key b a hab.symm).2 (h b a), fun h a b ↦ ?_⟩
  rcases eq_or_ne a b with rfl | hab
  · simp
  · exact (key a b hab).1 (h b a hab.symm)

/-- **Monotone Lipschitz functions are slope-restricted.** A monotone `K`-Lipschitz function is
slope-restricted in `[0, K]`. -/
theorem slopeRestricted_of_monotone_of_lipschitzWith {K : NNReal} (hm : Monotone σ)
    (hl : LipschitzWith K σ) : SlopeRestricted 0 K σ := by
  rw [slopeRestricted_iff_slope_mem_uIcc]
  intro a b hab
  rw [Set.uIcc_of_le K.coe_nonneg]
  refine ⟨(hm.monotoneOn Set.univ).slope_nonneg trivial trivial,
    (le_abs_self _).trans ?_⟩
  rw [slope_def_field, abs_div, div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 hab.symm))]
  simpa [Real.dist_eq] using hl.dist_le_mul b a

/-- A function that is slope-restricted in `[α, β]` changes by at most `max |α| |β|` times the
change of its argument. -/
theorem SlopeRestricted.abs_sub_le (h : SlopeRestricted α β σ) (a b : ℝ) :
    |σ a - σ b| ≤ max |α| |β| * |a - b| := by
  have hab := Set.mem_uIcc.1 (slopeRestricted_iff_mem_uIcc.1 h a b)
  rw [max_mul_of_nonneg _ _ (abs_nonneg _), ← abs_mul, ← abs_mul]
  rcases hab with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact abs_le_max_abs_abs h₁ h₂
  · exact (abs_le_max_abs_abs h₁ h₂).trans_eq (max_comm _ _)

/-- **Slope-restricted functions are Lipschitz.** A function that is slope-restricted in
`[α, β]` is `max |α| |β|`-Lipschitz. -/
theorem SlopeRestricted.lipschitzWith (h : SlopeRestricted α β σ) :
    LipschitzWith (max ‖α‖₊ ‖β‖₊) σ :=
  LipschitzWith.of_dist_le_mul fun a b ↦ by simpa [Real.dist_eq] using h.abs_sub_le a b

/-- The maximum `t ↦ max (p * t) (q * t)` of two linear functions is slope-restricted in
`[p, q]`. -/
theorem slopeRestricted_max_mul (p q : ℝ) : SlopeRestricted p q fun t ↦ max (p * t) (q * t) := by
  refine slopeRestricted_iff.2 fun a b ↦ ?_
  rcases le_total (p * a) (q * a) with ha | ha <;> rcases le_total (p * b) (q * b) with hb | hb <;>
    simp only [max_eq_left, max_eq_right, ha, hb] <;>
    nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

/-- The ReLU `t ↦ max 0 t` is slope-restricted in `[0, 1]`. -/
theorem slopeRestricted_relu : SlopeRestricted 0 1 fun t ↦ max 0 t := by
  simpa using slopeRestricted_max_mul 0 1

/-- The leaky ReLU `t ↦ max t (c * t)` is slope-restricted in `[c, 1]`, for every real `c`. -/
theorem slopeRestricted_leakyRelu (c : ℝ) : SlopeRestricted c 1 fun t ↦ max t (c * t) := by
  simpa using (slopeRestricted_max_mul 1 c).symm

/-- The hyperbolic tangent is slope-restricted in `[0, 1]`: it is monotone and `1`-Lipschitz. -/
theorem slopeRestricted_tanh : SlopeRestricted 0 1 Real.tanh := by
  simpa using slopeRestricted_of_monotone_of_lipschitzWith Real.tanh_strictMono.monotone
    Real.lipschitzWith_tanh

/-- **Incremental quadratic constraint.** If `σ` is slope-restricted in `[α, β]` and the weights
`t p` are nonnegative, then for all `u` and `u'`, with `Δu p = u p - u' p` and
`Δy p = σ (u p) - σ (u' p)`, the sum `∑ p, 2 * t p * (Δy p - α * Δu p) * (β * Δu p - Δy p)` is
nonnegative. -/
theorem SlopeRestricted.sum_nonneg {ι : Type*} [Fintype ι] (h : SlopeRestricted α β σ)
    {t : ι → ℝ} (ht : 0 ≤ t) (u u' : ι → ℝ) :
    0 ≤ ∑ p, 2 * t p * (σ (u p) - σ (u' p) - α * (u p - u' p)) *
      (β * (u p - u' p) - (σ (u p) - σ (u' p))) :=
  Finset.sum_nonneg fun p _ ↦ by
    rw [mul_assoc]
    exact mul_nonneg (mul_nonneg zero_le_two (ht p)) (slopeRestricted_iff.1 h _ _)

/-! ### Examples -/

/-- `t ↦ -t` is not slope-restricted in `[0, 1]`: at `a = 1`, `b = 0` the product is
`(-1) * 2 < 0`. -/
example : ¬ SlopeRestricted 0 1 fun t ↦ -t := fun h ↦ by
  have := h 1 0
  norm_num at this

/-- The ReLU is not slope-restricted in `[0, 1 / 2]`: at `a = 1`, `b = 0` the product is
`1 * (1 / 2 - 1) < 0`. -/
example : ¬ SlopeRestricted 0 (1 / 2) fun t ↦ max 0 t := fun h ↦ by
  have := h 1 0
  norm_num at this

/-- The leaky ReLU with `c = 1 / 2` is not slope-restricted in `[3 / 5, 1]`: at `a = -1`, `b = 0`
the product is `(1 / 10) * (-1 / 2) < 0`. -/
example : ¬ SlopeRestricted (3 / 5) 1 fun t ↦ max t (1 / 2 * t) := fun h ↦ by
  have := h (-1) 0
  norm_num at this

/-- `t ↦ 2 * t` is slope-restricted in `[2, 2]`, hence `2`-Lipschitz. -/
example : LipschitzWith 2 fun t : ℝ ↦ 2 * t := by
  have h : SlopeRestricted 2 2 fun t ↦ 2 * t := by simpa using slopeRestricted_max_mul 2 2
  simpa using h.lipschitzWith

end TauCeti
