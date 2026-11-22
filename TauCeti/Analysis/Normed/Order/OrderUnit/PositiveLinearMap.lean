/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Analysis.Normed.Order.OrderUnit.Basic
import TauCeti.Analysis.Normed.Order.PositiveLinearMap

/-!
# Positive linear maps between order-unit spaces

This file develops automatic continuity and operator-norm formulas for positive linear maps
and functionals on order-unit spaces, without requiring weak-star topology or state spaces.

Every positive linear map `T : E → F` between order-unit spaces is automatically Lipschitz with
constant `‖T e‖`, and when `T` is continuous its operator norm equals `‖T e‖`; in particular,
unital positive linear maps are contractive (`‖T‖ = 1`). For real-valued continuous linear
functionals, positivity is equivalent to `‖φ‖ = φ e`.

## Main definitions and results

* `TauCeti.IsOrderUnitNorm.norm_map_le`, `lipschitzWith_of_positive`,
  `continuous_of_positive`, `toPositiveContinuousLinearMap`,
  `opNorm_eq_norm_apply_unit`, `opNorm_eq_one_of_monotone_of_map_unit`,
  `norm_apply_le_of_monotone_of_map_unit`: automatic boundedness and operator-norm formulas for
  positive linear maps between order-unit spaces.
* `TauCeti.IsOrderUnitNorm.opNorm_eq_apply_unit_of_monotone`,
  `monotone_iff_opNorm_eq_apply_unit`, `monotone_and_apply_unit_eq_one_iff`: operator-norm
  characterization of positive continuous real-linear functionals.

## References

* Marc A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, Section 1.
* Richard V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open scoped NNReal

namespace TauCeti

/-! ### Positive linear maps between order-unit spaces -/

section PositiveMaps

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
  [IsOrderedAddMonoid F] {e : E} {f : F}

/-- A positive linear map between order-unit spaces satisfies `‖T a‖ ≤ ‖T e‖ * ‖a‖`, with no
continuity hypothesis. -/
theorem IsOrderUnitNorm.norm_map_le {M : Type*} [FunLike M E F] [LinearMapClass M ℝ E F]
    [OrderHomClass M E F] (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : M) (a : E) :
    ‖T a‖ ≤ ‖T e‖ * ‖a‖ := by
  have hlo : -(‖a‖ • T e) ≤ T a := by
    have h := OrderHomClass.mono T (he.neg_norm_smul_le a)
    rwa [map_neg, map_smul] at h
  have hhi : T a ≤ ‖a‖ • T e := by
    have h := OrderHomClass.mono T (he.le_norm_smul a)
    rwa [map_smul] at h
  calc
    ‖T a‖ ≤ ‖‖a‖ • T e‖ := hf.norm_le_norm_of_le hlo hhi
    _ = ‖T e‖ * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a), mul_comm]

/-- A positive linear map between order-unit spaces is `‖T e‖`-Lipschitz. -/
theorem IsOrderUnitNorm.lipschitzWith_of_positive {M : Type*} [FunLike M E F]
    [LinearMapClass M ℝ E F] [OrderHomClass M E F] (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : M) : LipschitzWith ‖T e‖₊ T := by
  have h := AddMonoidHomClass.lipschitz_of_bound T ‖T e‖ fun a => he.norm_map_le hf T a
  have hnn : ‖T e‖.toNNReal = ‖T e‖₊ := NNReal.eq (by simp)
  rwa [hnn] at h

/-- Every positive linear map between order-unit spaces is automatically continuous. -/
theorem IsOrderUnitNorm.continuous_of_positive {M : Type*} [FunLike M E F]
    [LinearMapClass M ℝ E F] [OrderHomClass M E F] (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : M) : Continuous T :=
  (he.lipschitzWith_of_positive hf T).continuous

/-- Upgrade a positive linear map `E →ₚ[ℝ] F` between order-unit spaces to a positive continuous
linear map `E →P[ℝ] F`. -/
def IsOrderUnitNorm.toPositiveContinuousLinearMap (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →ₚ[ℝ] F) : E →P[ℝ] F :=
  PositiveContinuousLinearMap.mk T (he.continuous_of_positive hf T)

/-- Evaluating `toPositiveContinuousLinearMap` agrees with the underlying positive linear map. -/
@[simp]
theorem IsOrderUnitNorm.toPositiveContinuousLinearMap_apply (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →ₚ[ℝ] F) (a : E) :
    he.toPositiveContinuousLinearMap hf T a = T a :=
  (rfl)

/-- A monotone continuous linear map between order-unit spaces has operator norm `‖T e‖`. -/
theorem IsOrderUnitNorm.opNorm_eq_norm_apply_unit (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →L[ℝ] F) (hT : Monotone T) : ‖T‖ = ‖T e‖ := by
  let Tpos : E →ₚ[ℝ] F := { toLinearMap := T.toLinearMap, monotone' := hT }
  refine le_antisymm (T.opNorm_le_bound (norm_nonneg _) fun a => he.norm_map_le hf Tpos a) ?_
  calc
    ‖T e‖ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = ‖T‖ := by rw [he.norm_eq_one, mul_one]

/-- A unital monotone continuous linear map between order-unit spaces has operator norm `1`. -/
theorem IsOrderUnitNorm.opNorm_eq_one_of_monotone_of_map_unit (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →L[ℝ] F) (hT : Monotone T) (hTe : T e = f) : ‖T‖ = 1 := by
  rw [he.opNorm_eq_norm_apply_unit hf T hT, hTe, hf.norm_eq_one]

/-- Every unital positive continuous linear map between order-unit spaces is contractive. -/
theorem IsOrderUnitNorm.norm_apply_le_of_monotone_of_map_unit (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E →L[ℝ] F) (hT : Monotone T) (hTe : T e = f) (a : E) :
    ‖T a‖ ≤ ‖a‖ := by
  simpa [he.opNorm_eq_one_of_monotone_of_map_unit hf T hT hTe] using T.le_opNorm a

end PositiveMaps

/-! ### Positive real-linear functionals -/

section Functionals

/-- A monotone continuous real-linear functional on an order-unit space has operator norm `φ e`. -/
theorem IsOrderUnitNorm.opNorm_eq_apply_unit_of_monotone {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PartialOrder E] {e : E} (he : IsOrderUnitNorm e)
    (φ : E →L[ℝ] ℝ) (hφ : Monotone φ) : ‖φ‖ = φ e :=
  ContinuousLinearMap.opNorm_eq_apply_of_monotone φ hφ he.le_norm_smul he.norm_eq_one.le

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- A continuous real-linear functional on an order-unit space is monotone iff `‖φ‖ = φ e`. -/
theorem IsOrderUnitNorm.monotone_iff_opNorm_eq_apply_unit (φ : E →L[ℝ] ℝ) :
    Monotone φ ↔ ‖φ‖ = φ e := by
  refine ⟨he.opNorm_eq_apply_unit_of_monotone φ, fun h => ?_⟩
  refine (monotone_iff_map_nonneg φ).mpr fun a ha =>
    LinearMapClass.apply_nonneg_of_abs_apply_le_mul_norm φ
      (fun g => by simpa [Real.norm_eq_abs, h] using φ.le_opNorm g)
      (he.nonneg_iff_norm_smul_sub_le.mp ha)

/-- A continuous real-linear functional is positive and normalized at `e` iff `‖φ‖ = 1` and
`φ e = 1`. -/
theorem IsOrderUnitNorm.monotone_and_apply_unit_eq_one_iff (φ : E →L[ℝ] ℝ) :
    (Monotone φ ∧ φ e = 1) ↔ ‖φ‖ = 1 ∧ φ e = 1 := by
  refine ⟨fun ⟨hmono, h1⟩ => ⟨by rw [he.opNorm_eq_apply_unit_of_monotone φ hmono, h1], h1⟩,
    fun ⟨hnorm, h1⟩ => ⟨(he.monotone_iff_opNorm_eq_apply_unit φ).mpr (by rw [hnorm, h1]), h1⟩⟩

end Functionals

end TauCeti
