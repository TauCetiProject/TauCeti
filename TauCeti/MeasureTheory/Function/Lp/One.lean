/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.Normed.Order.PositiveLinearMap
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The constant one in `L∞`

This file equips `L∞(μ)` with the class `1` of the constant function one, for any normed group
with a distinguished element `1` and on an arbitrary measure space. Unlike
`MeasureTheory.Lp.const`, the construction needs no finite-measure hypothesis because the
essential supremum of a constant is always finite. Its norm is that of `1` unless `μ = 0`. In a
real Banach space its integral is `μ.real univ • 1`, the total mass times `1`, which is zero when
the mass is infinite.

Every real `L∞` class `f` satisfies `f ≤ ‖f‖ • 1` (`MeasureTheory.Lp.le_norm_smul_one`), so the
constant one is an order unit, and a positive linear functional on `L∞` is controlled by its value
at one; in particular it is continuous (`PositiveLinearMap.continuous_lpTop`). Conversely, a
nonnegative class `f` satisfies `‖‖f‖ • 1 - f‖ ≤ ‖f‖`
(`MeasureTheory.Lp.norm_norm_smul_one_sub_le_of_nonneg`), which tests positivity of a functional
bounded by its value at one.
-/

public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E] [One E]

/-- The class of the constant function one, as an element of `L∞(μ)`. -/
instance inftyOne : One (Lp E ∞ μ) where
  one := (memLp_top_const (1 : E)).toLp fun _ => 1

/-- The constant one of `L∞(μ)` is the class of the constant function one. -/
theorem one_def : (1 : Lp E ∞ μ) = (memLp_top_const (1 : E)).toLp fun _ => 1 :=
  rfl

/-- The representative of `1 : L∞(μ)` is almost everywhere the constant function one. -/
theorem coeFn_one : ((1 : Lp E ∞ μ) : α → E) =ᵐ[μ] 1 :=
  MemLp.coeFn_toLp (memLp_top_const (1 : E))

/-- On a nonzero measure, the norm of `1 : L∞(μ)` is that of `1`. -/
theorem norm_one_of_ne_zero (hμ : μ ≠ 0) : ‖(1 : Lp E ∞ μ)‖ = ‖(1 : E)‖ := by
  rw [one_def, norm_toLp, eLpNorm_exponent_top aestronglyMeasurable_const,
    eLpNormEssSup_const _ hμ, toReal_eNorm]

/-- The integral of the constant one of `L∞(μ)` is the total mass `μ.real univ` times `1`; like
`MeasureTheory.integral_const`, it vanishes when the mass is infinite. -/
@[simp]
theorem integral_one [NormedSpace ℝ E] [CompleteSpace E] :
    ∫ x, (1 : Lp E ∞ μ) x ∂μ = μ.real Set.univ • (1 : E) := by
  simp [integral_congr_ae coeFn_one]

/-- Every real `L∞` class lies below its norm times the constant one. With the lemmas of
`TauCeti/Analysis/Normed/Order/PositiveLinearMap.lean`, this bounds and makes continuous every
positive linear functional on `L∞`. -/
theorem le_norm_smul_one (f : Lp ℝ ∞ μ) : f ≤ ‖f‖ • 1 := by
  rw [← Lp.coeFn_le]
  filter_upwards [Lp.ae_norm_le_norm_top f, Lp.coeFn_smul ‖f‖ (1 : Lp ℝ ∞ μ),
    coeFn_one (E := ℝ) (μ := μ)] with x hx hs h1
  rw [hs, Pi.smul_apply, h1, Pi.one_apply, smul_eq_mul, mul_one]
  exact (Real.le_norm_self _).trans hx

/-- A nonnegative real `L∞` class `f` lies within `‖f‖` of `‖f‖` times the constant one. -/
theorem norm_norm_smul_one_sub_le_of_nonneg {f : Lp ℝ ∞ μ} (hf : 0 ≤ f) :
    ‖‖f‖ • 1 - f‖ ≤ ‖f‖ := by
  refine Lp.norm_top_le_of_ae_bound (norm_nonneg f) ?_
  filter_upwards [Lp.coeFn_sub (‖f‖ • 1) f, Lp.coeFn_smul ‖f‖ (1 : Lp ℝ ∞ μ),
    coeFn_one (E := ℝ) (μ := μ), (Lp.coeFn_nonneg f).2 hf, Lp.ae_norm_le_norm_top f]
    with x hsub hsmul h1 h0 hx
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, h1, Pi.one_apply, smul_eq_mul, mul_one]
  rw [Pi.zero_apply] at h0
  exact (Real.norm_eq_abs _).trans_le <|
    abs_sub_le_of_nonneg_of_le (norm_nonneg f) le_rfl h0 ((Real.le_norm_self _).trans hx)

end MeasureTheory.Lp

namespace PositiveLinearMap

variable {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

/-- A positive linear functional on real `L∞` is continuous. -/
theorem continuous_lpTop (M : MeasureTheory.Lp ℝ ∞ μ →ₚ[ℝ] ℝ) : Continuous M :=
  continuous_of_forall_le_norm_smul M MeasureTheory.Lp.le_norm_smul_one

end PositiveLinearMap
