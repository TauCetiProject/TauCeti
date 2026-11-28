/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Comparing `Lᵖ` seminorms across Haar measures

On a second-countable locally compact group, any two Haar measures `μ` and `ν` differ by the
positive finite scalar factor `Measure.haarScalarFactor μ ν`. Consequently the `Lᵖ` seminorms of
any function restricted to an arbitrary set `s` scale by
`(Measure.haarScalarFactor μ ν) ^ p.toReal⁻¹` (at the endpoints `p = 0` and `p = ∞`,
`p.toReal⁻¹ = 0` so the scaling factor is `1`), and membership in `Lᵖ` on `s` is independent of
the choice of Haar measure. Multiplicative and additive versions are provided.

## Main declarations

* `MeasureTheory.eLpNorm_restrict_eq_haarScalarFactor_rpow_mul`: scaling of restricted `eLpNorm`
  between two Haar measures.
* `MeasureTheory.toReal_eLpNorm_restrict_eq_haarScalarFactor_rpow_mul`: the real-valued `toReal`
  form.
* `MeasureTheory.MemLp.restrict_of_isHaarMeasure`: `MemLp` invariance on a subset across Haar
  measures.
* `MeasureTheory.eLpNorm_restrict_le_haarScalarFactor_rpow_mul_add`,
  `MeasureTheory.MemLp.restrict_of_isHaarMeasure_of_eLpNorm_le_add`,
  `MeasureTheory.toReal_eLpNorm_restrict_le_haarScalarFactor_rpow_mul_add`: transferring a
  restricted `eLpNorm` domination `‖g‖_{Lᵖ(s)} ≤ ‖f‖_{Lᵖ(s)} + c` on `s ⊆ u` from one Haar measure
  to another.

All declarations have additive counterparts (`addHaarScalarFactor`, `isAddHaarMeasure`).
-/

public section

open scoped ENNReal NNReal

namespace MeasureTheory

variable {G ε ε' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace ε] [ENorm ε] [TopologicalSpace ε'] [ENorm ε']

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
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ ν, Measure.restrict_smul]
  rw [eLpNorm_smul_measure_of_ne_zero' hα, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_rpow_of_ne_zero hα]

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

/-- Membership in `Lᵖ` on a subset of a second-countable locally compact group does not depend on
the choice of Haar measure. -/
@[to_additive /-- Membership in `Lᵖ` on a subset of a second-countable locally compact group does
not depend on the choice of additive Haar measure. -/]
theorem MemLp.restrict_of_isHaarMeasure {f : G → ε} {p : ℝ≥0∞} {μ : Measure G} [μ.IsHaarMeasure]
    {s : Set G} (hf : MemLp f p (μ.restrict s)) (ν : Measure G) [ν.IsHaarMeasure] :
    MemLp f p (ν.restrict s) := by
  rw [Measure.isMulLeftInvariant_eq_smul ν μ, Measure.restrict_smul]
  exact hf.smul_measure_nnreal

/-- Transfer a restricted `eLpNorm` bound `‖g‖_{Lᵖ(s)} ≤ ‖f‖_{Lᵖ(s)} + c` on nested sets
`s ⊆ u` between two Haar measures on a second-countable locally compact group. -/
@[to_additive eLpNorm_restrict_le_addHaarScalarFactor_rpow_mul_add /-- Transfer a restricted
`eLpNorm` bound `‖g‖_{Lᵖ(s)} ≤ ‖f‖_{Lᵖ(s)} + c` on nested sets `s ⊆ u` between two additive Haar
measures on a second-countable locally compact group. -/]
theorem eLpNorm_restrict_le_haarScalarFactor_rpow_mul_add {f : G → ε} {g : G → ε'} (p : ℝ≥0∞)
    (ν μ : Measure G) [ν.IsHaarMeasure] [μ.IsHaarMeasure] {s u : Set G} (hsu : s ⊆ u) {c : ℝ≥0∞}
    (hg : eLpNorm g p (μ.restrict s) ≤ eLpNorm f p (μ.restrict s) + c) :
    eLpNorm g p (ν.restrict s) ≤
      (Measure.haarScalarFactor ν μ : ℝ≥0∞) ^ p.toReal⁻¹ * (eLpNorm f p (μ.restrict u) + c) := by
  rw [eLpNorm_restrict_eq_haarScalarFactor_rpow_mul g p ν μ s]
  gcongr
  exact hg.trans (add_le_add (eLpNorm_mono_measure f (Measure.restrict_mono_set μ hsu)) le_rfl)

/-- If `f ∈ Lᵖ(u)` for a Haar measure `μ` and `‖g‖_{Lᵖ(s)} ≤ ‖f‖_{Lᵖ(s)} + c` on `s ⊆ u` with
`c < ∞`, then `g ∈ Lᵖ(s)` for any Haar measure `ν`. -/
@[to_additive /-- If `f ∈ Lᵖ(u)` for an additive Haar measure `μ` and
`‖g‖_{Lᵖ(s)} ≤ ‖f‖_{Lᵖ(s)} + c` on `s ⊆ u` with `c < ∞`, then `g ∈ Lᵖ(s)` for any additive Haar
measure `ν`. -/]
theorem MemLp.restrict_of_isHaarMeasure_of_eLpNorm_le_add {f : G → ε} {g : G → ε'} {p : ℝ≥0∞}
    {μ : Measure G} [μ.IsHaarMeasure] {s u : Set G} (hsu : s ⊆ u)
    (hf : MemLp f p (μ.restrict u)) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hg : eLpNorm g p (μ.restrict s) ≤ eLpNorm f p (μ.restrict s) + c)
    (ν : Measure G) [ν.IsHaarMeasure] :
    MemLp g p (ν.restrict s) := by
  have hle : eLpNorm g p (μ.restrict s) ≤ eLpNorm f p (μ.restrict u) + c :=
    hg.trans (add_le_add (eLpNorm_mono_measure f (Measure.restrict_mono_set μ hsu)) le_rfl)
  have hfin : eLpNorm f p (μ.restrict u) + c < ∞ :=
    ENNReal.add_lt_top.2 ⟨hf.eLpNorm_lt_top, hc.lt_top⟩
  exact (memLp_iff.2 (hle.trans_lt hfin)).restrict_of_isHaarMeasure ν

/-- Real-valued transfer of a restricted `eLpNorm` bound `‖g‖_{Lᵖ(s)} ≤ ‖f‖_{Lᵖ(s)} + η` on
nested sets `s ⊆ u` between two Haar measures on a second-countable locally compact group. -/
@[to_additive toReal_eLpNorm_restrict_le_addHaarScalarFactor_rpow_mul_add /-- Real-valued transfer
of a restricted `eLpNorm` bound `‖g‖_{Lᵖ(s)} ≤ ‖f‖_{Lᵖ(s)} + η` on nested sets `s ⊆ u` between
two additive Haar measures on a second-countable locally compact group. -/]
theorem toReal_eLpNorm_restrict_le_haarScalarFactor_rpow_mul_add {f : G → ε} {g : G → ε'}
    (p : ℝ≥0∞) (ν μ : Measure G) [ν.IsHaarMeasure] [μ.IsHaarMeasure] {s u : Set G} (hsu : s ⊆ u)
    (hf : MemLp f p (μ.restrict u)) {η : ℝ} (hη : 0 ≤ η)
    (hg : eLpNorm g p (μ.restrict s) ≤ eLpNorm f p (μ.restrict s) + ENNReal.ofReal η) :
    (eLpNorm g p (ν.restrict s)).toReal ≤
      (Measure.haarScalarFactor ν μ : ℝ) ^ p.toReal⁻¹ *
        ((eLpNorm f p (μ.restrict u)).toReal + η) := by
  have hfin : eLpNorm f p (μ.restrict u) + ENNReal.ofReal η ≠ ∞ :=
    (ENNReal.add_lt_top.2 ⟨hf.eLpNorm_lt_top, ENNReal.ofReal_lt_top⟩).ne
  have hle := eLpNorm_restrict_le_haarScalarFactor_rpow_mul_add p ν μ hsu hg
  calc (eLpNorm g p (ν.restrict s)).toReal
      ≤ ((Measure.haarScalarFactor ν μ : ℝ≥0∞) ^ p.toReal⁻¹ *
            (eLpNorm f p (μ.restrict u) + ENNReal.ofReal η)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg
          (by positivity) ENNReal.coe_ne_top) hfin) hle
    _ = (Measure.haarScalarFactor ν μ : ℝ) ^ p.toReal⁻¹ *
          ((eLpNorm f p (μ.restrict u)).toReal + η) := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal,
          ENNReal.toReal_add hf.eLpNorm_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hη]

end MeasureTheory
