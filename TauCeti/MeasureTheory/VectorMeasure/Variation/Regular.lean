/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import TauCeti.MeasureTheory.Measure.Regular

/-!
# Finiteness and regularity of the variation of sums and scalar multiples

The variation `|μ|` of a vector measure is subadditive, `|μ + ν| ≤ |μ| + |ν|` and
`|μ - ν| ≤ |μ| + |ν|`, and homogeneous, `|c • μ| = ‖c‖ • |μ|`. Finiteness of the variation
therefore passes to sums and differences.

Regularity passes too, on an `R₁` space with its Borel σ-algebra, for example a compact Hausdorff
space. If `|μ|` and `|ν|` are finite and regular, then so is `|μ| + |ν|`. The variation of
`μ + ν` or `μ - ν` is dominated by it, hence absolutely continuous with respect to it, and is
therefore regular by `MeasureTheory.Measure.AbsolutelyContinuous.regular`. Regularity of
`|c • μ|` needs no hypothesis on the space. These are the closure properties used for scalar
measures of finite regular variation, which are the dual of the space of continuous functions on a
compact Hausdorff space and arise by polarizing positive measures.

## Main results

* `MeasureTheory.VectorMeasure.isFiniteMeasure_variation_add`,
  `MeasureTheory.VectorMeasure.isFiniteMeasure_variation_sub`: finite variation is closed under
  sums and differences.
* `MeasureTheory.VectorMeasure.regular_variation_smul`: regular variation is closed under scalar
  multiplication.
* `MeasureTheory.VectorMeasure.regular_variation_add`,
  `MeasureTheory.VectorMeasure.regular_variation_sub`: finite regular variation is closed under
  sums and differences.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill (1987), §6.1 and §6.19.
-/

public section

open MeasureTheory

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} [MeasurableSpace X]

section Add

variable [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V] [ContinuousAdd V]
  {μ ν : VectorMeasure X V}

/-- The sum of two vector measures of finite variation has finite variation. -/
instance isFiniteMeasure_variation_add [IsFiniteMeasure μ.variation]
    [IsFiniteMeasure ν.variation] : IsFiniteMeasure (μ + ν).variation :=
  isFiniteMeasure_of_le _ variation_add_le

/-- On an `R₁` space with its Borel σ-algebra, the sum of two vector measures of finite regular
variation has regular variation. -/
instance regular_variation_add [TopologicalSpace X] [BorelSpace X] [R1Space X]
    [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation] [μ.variation.Regular]
    [ν.variation.Regular] : (μ + ν).variation.Regular :=
  (Measure.absolutelyContinuous_of_le variation_add_le).regular

end Add

section NormedAddCommGroup

variable [NormedAddCommGroup V] {μ ν : VectorMeasure X V}

/-- The difference of two vector measures of finite variation has finite variation. -/
instance isFiniteMeasure_variation_sub [IsFiniteMeasure μ.variation]
    [IsFiniteMeasure ν.variation] : IsFiniteMeasure (μ - ν).variation :=
  isFiniteMeasure_of_le _ variation_sub_le

variable [TopologicalSpace X]

/-- A scalar multiple of a vector measure of regular variation has regular variation. -/
instance regular_variation_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜}
    [μ.variation.Regular] : (c • μ).variation.Regular := by
  rw [variation_smul]
  infer_instance

/-- On an `R₁` space with its Borel σ-algebra, the difference of two vector measures of finite
regular variation has regular variation. -/
instance regular_variation_sub [BorelSpace X] [R1Space X] [IsFiniteMeasure μ.variation]
    [IsFiniteMeasure ν.variation] [μ.variation.Regular] [ν.variation.Regular] :
    (μ - ν).variation.Regular :=
  (Measure.absolutelyContinuous_of_le variation_sub_le).regular

end NormedAddCommGroup

end MeasureTheory.VectorMeasure
