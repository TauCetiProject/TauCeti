/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Measure.Haar.Unique

/-!
# Comparing `Lᵖ` seminorms across Haar measures

On a second-countable locally compact group, any two Haar measures `μ` and `ν` differ by the
positive finite scalar factor `Measure.haarScalarFactor μ ν`. Consequently the `Lᵖ` seminorms of
any function (on the whole group or restricted to an arbitrary set `s`) scale by
`(Measure.haarScalarFactor μ ν) ^ (1 / p)`, and membership in `Lᵖ` is independent of the choice of
Haar measure. Multiplicative and additive versions are provided.

## Main declarations

* `MeasureTheory.eLpNorm_eq_haarScalarFactor_rpow_mul` and
  `MeasureTheory.eLpNorm_restrict_eq_haarScalarFactor_rpow_mul`: scaling of `eLpNorm` between two
  Haar measures, globally and on a subset.
* `MeasureTheory.toReal_eLpNorm_eq_haarScalarFactor_rpow_mul` and
  `MeasureTheory.toReal_eLpNorm_restrict_eq_haarScalarFactor_rpow_mul`: the real-valued `toReal`
  forms.
* `MeasureTheory.MemLp.of_isHaarMeasure` and `MeasureTheory.MemLp.restrict_of_isHaarMeasure`:
  `MemLp` invariance across Haar measures, globally and on a subset.

All six declarations have additive counterparts (`addHaarScalarFactor`, `of_isAddHaarMeasure`).
-/

public section

open scoped ENNReal NNReal

namespace MeasureTheory

variable {G ε : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace ε] [ContinuousENorm ε]

/-- Two Haar measures on a second-countable locally compact group give `Lᵖ` seminorms differing by
the `p.toReal⁻¹`-th power of `Measure.haarScalarFactor μ ν`. -/
@[to_additive eLpNorm_eq_addHaarScalarFactor_rpow_mul /-- Two additive Haar measures on a
second-countable locally compact group give `Lᵖ` seminorms differing by the `p.toReal⁻¹`-th power
of `Measure.addHaarScalarFactor μ ν`. -/]
theorem eLpNorm_eq_haarScalarFactor_rpow_mul (f : G → ε) (p : ℝ≥0∞) (μ ν : Measure G)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    eLpNorm f p μ = (Measure.haarScalarFactor μ ν : ℝ≥0∞) ^ p.toReal⁻¹ * eLpNorm f p ν := by
  have hα : Measure.haarScalarFactor μ ν ≠ 0 :=
    (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne'
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  rw [eLpNorm_smul_measure_of_ne_zero' hα, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_rpow_of_ne_zero hα]

/-- On any subset `s`, two Haar measures on a second-countable locally compact group give
restricted `Lᵖ` seminorms differing by the `p.toReal⁻¹`-th power of
`Measure.haarScalarFactor μ ν`. -/
@[to_additive eLpNorm_restrict_eq_addHaarScalarFactor_rpow_mul /-- On any subset `s`, two additive
Haar measures on a second-countable locally compact group give restricted `Lᵖ` seminorms differing
by the `p.toReal⁻¹`-th power of `Measure.addHaarScalarFactor μ ν`. -/]
theorem eLpNorm_restrict_eq_haarScalarFactor_rpow_mul (f : G → ε) (p : ℝ≥0∞) (μ ν : Measure G)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] (s : Set G) :
    eLpNorm f p (μ.restrict s) =
      (Measure.haarScalarFactor μ ν : ℝ≥0∞) ^ p.toReal⁻¹ * eLpNorm f p (ν.restrict s) := by
  have hα : Measure.haarScalarFactor μ ν ≠ 0 :=
    (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne'
  rw [Measure.restrict_eq_haarScalarFactor_smul μ ν s, eLpNorm_smul_measure_of_ne_zero' hα,
    ENNReal.smul_def, smul_eq_mul, ENNReal.coe_rpow_of_ne_zero hα]

/-- Real-valued scaling of `eLpNorm` between two Haar measures on a second-countable locally
compact group. -/
@[to_additive toReal_eLpNorm_eq_addHaarScalarFactor_rpow_mul /-- Real-valued scaling of `eLpNorm`
between two additive Haar measures on a second-countable locally compact group. -/]
theorem toReal_eLpNorm_eq_haarScalarFactor_rpow_mul (f : G → ε) (p : ℝ≥0∞) (μ ν : Measure G)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    (eLpNorm f p μ).toReal =
      (Measure.haarScalarFactor μ ν : ℝ) ^ p.toReal⁻¹ * (eLpNorm f p ν).toReal := by
  rw [eLpNorm_eq_haarScalarFactor_rpow_mul f p μ ν, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.coe_toReal]

/-- Real-valued scaling of restricted `eLpNorm` between two Haar measures on a second-countable
locally compact group. -/
@[to_additive toReal_eLpNorm_restrict_eq_addHaarScalarFactor_rpow_mul /-- Real-valued scaling of
restricted `eLpNorm` between two additive Haar measures on a second-countable locally compact
group. -/]
theorem toReal_eLpNorm_restrict_eq_haarScalarFactor_rpow_mul (f : G → ε) (p : ℝ≥0∞)
    (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] (s : Set G) :
    (eLpNorm f p (μ.restrict s)).toReal =
      (Measure.haarScalarFactor μ ν : ℝ) ^ p.toReal⁻¹ * (eLpNorm f p (ν.restrict s)).toReal := by
  rw [eLpNorm_restrict_eq_haarScalarFactor_rpow_mul f p μ ν s, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.coe_toReal]

/-- Membership in `Lᵖ` on a second-countable locally compact group does not depend on the choice
of Haar measure. -/
@[to_additive /-- Membership in `Lᵖ` on a second-countable locally compact group does not depend on
the choice of additive Haar measure. -/]
theorem MemLp.of_isHaarMeasure {f : G → ε} {p : ℝ≥0∞} {μ : Measure G} [μ.IsHaarMeasure]
    (hf : MemLp f p μ) (ν : Measure G) [ν.IsHaarMeasure] : MemLp f p ν := by
  rw [Measure.isMulLeftInvariant_eq_smul ν μ]
  exact hf.smul_measure_nnreal

/-- Membership in `Lᵖ` on a subset of a second-countable locally compact group does not depend on
the choice of Haar measure. -/
@[to_additive /-- Membership in `Lᵖ` on a subset of a second-countable locally compact group does
not depend on the choice of additive Haar measure. -/]
theorem MemLp.restrict_of_isHaarMeasure {f : G → ε} {p : ℝ≥0∞} {μ : Measure G} [μ.IsHaarMeasure]
    {s : Set G} (hf : MemLp f p (μ.restrict s)) (ν : Measure G) [ν.IsHaarMeasure] :
    MemLp f p (ν.restrict s) := by
  rw [Measure.restrict_eq_haarScalarFactor_smul ν μ s]
  exact hf.smul_measure_nnreal

end MeasureTheory
