/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Conditional entropy of standard-Borel labels

For labels with possibly uncountably many values, such as the subordinate partitions of a
homogeneous flow, the conditional entropy of a label `a : X → Y` given a label `b : X → Z` is
defined through the conditional distribution `ProbabilityTheory.condDistrib a b μ`, a kernel from
`Z` to `Y` (`Y` standard Borel): the information of the atom of `a` containing `x` under the
conditional probability given `b x` is integrated over `x`.

* `TauCeti.atomInformation p` is the information `-log p` of an event of probability `p`, with
  value `∞` at `p = 0`: a zero-probability atom is not assigned zero information.
* `TauCeti.conditionalLabelEntropy μ a b` is
  `∫⁻ x, atomInformation (condDistrib a b μ (b x) {a x}) ∂μ`, in `[0, ∞]`.

## Main results

* `TauCeti.atomInformation_zero`, `TauCeti.atomInformation_one`, `TauCeti.atomInformation_half`:
  the values `∞`, `0` and `log 2`.
* `TauCeti.conditionalLabelEntropy_eq_of_ae_eq`: the value is unchanged when the conditional
  distribution is replaced by a kernel agreeing with it almost everywhere for the law of `b`.
* `TauCeti.conditionalLabelEntropy_self`: conditioning a measurable label on itself gives zero.
* `TauCeti.conditionalLabelEntropy_const`: conditioning on a constant label integrates the
  information of the atoms of `a` under `μ`.

## References

* G. A. Margulis and G. M. Tomanov, Invariant measures for actions of unipotent groups over local
  fields on homogeneous spaces, Invent. Math. 116 (1994), 347–392, §9.3, pp. 381–383,
  doi:10.1007/BF01231565.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace TauCeti

/-- The information `-log p` of an event of probability `p`, with value `∞` at `p = 0`. -/
noncomputable def atomInformation (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 0 then ∞ else ENNReal.ofReal (-log p.toReal)

theorem atomInformation_def (p : ℝ≥0∞) :
    atomInformation p = if p = 0 then ∞ else ENNReal.ofReal (-log p.toReal) :=
  (rfl)

/-- A zero-probability event has infinite information. -/
@[simp]
theorem atomInformation_zero : atomInformation 0 = ∞ := by
  simp [atomInformation_def]

/-- A sure event has zero information. -/
@[simp]
theorem atomInformation_one : atomInformation 1 = 0 := by
  simp [atomInformation_def]

/-- An event of probability `1/2` has information `log 2`. -/
theorem atomInformation_half : atomInformation 2⁻¹ = ENNReal.ofReal (log 2) := by
  simp [atomInformation_def, log_inv]

/-- An event of positive probability has information `-log p`. -/
theorem atomInformation_of_ne_zero {p : ℝ≥0∞} (hp : p ≠ 0) :
    atomInformation p = ENNReal.ofReal (-log p.toReal) := by
  simp [atomInformation_def, hp]

/-- The information is infinite exactly at probability zero. -/
theorem atomInformation_eq_top_iff {p : ℝ≥0∞} : atomInformation p = ∞ ↔ p = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ atomInformation_zero⟩
  by_contra h0
  simp [atomInformation_of_ne_zero h0] at h

variable {X Y Z : Type*} {mX : MeasurableSpace X} [MeasurableSpace Y] [StandardBorelSpace Y]
  [Nonempty Y] [MeasurableSpace Z] {μ : Measure X} [IsFiniteMeasure μ]

/-- The conditional entropy of the label `a` given the label `b`: the integral over `x` of the
information of the atom `{a x}` under the conditional distribution of `a` given `b = b x`. A
zero-probability atom contributes `∞`. -/
noncomputable def conditionalLabelEntropy (μ : Measure X) [IsFiniteMeasure μ] (a : X → Y)
    (b : X → Z) : ℝ≥0∞ :=
  ∫⁻ x, atomInformation (condDistrib a b μ (b x) {a x}) ∂μ

theorem conditionalLabelEntropy_def (a : X → Y) (b : X → Z) :
    conditionalLabelEntropy μ a b = ∫⁻ x, atomInformation (condDistrib a b μ (b x) {a x}) ∂μ :=
  (rfl)

/-- **Independence of the kernel.** Replacing the conditional distribution by a kernel that agrees
with it almost everywhere for the law of `b` does not change the conditional entropy. -/
theorem conditionalLabelEntropy_eq_of_ae_eq {a : X → Y} {b : X → Z} (hb : AEMeasurable b μ)
    {κ : Kernel Z Y} (hκ : κ =ᵐ[μ.map b] condDistrib a b μ) :
    conditionalLabelEntropy μ a b = ∫⁻ x, atomInformation (κ (b x) {a x}) ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_of_ae_map hb hκ] with x hx
  rw [hx]

/-- **Conditioning on itself.** A measurable label conditioned on itself has conditional entropy
zero: given `a x`, the atom `{a x}` is sure. -/
theorem conditionalLabelEntropy_self {a : X → Y} (ha : AEMeasurable a μ) :
    conditionalLabelEntropy μ a a = 0 := by
  rw [conditionalLabelEntropy_eq_of_ae_eq ha (condDistrib_self ha).symm]
  simp [Kernel.id_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _)]

/-- **Conditioning on a constant.** Under a probability measure, conditioning a measurable label
on a constant label integrates the information of its atoms under `μ`. -/
theorem conditionalLabelEntropy_const [IsProbabilityMeasure μ] [MeasurableSingletonClass Z]
    {a : X → Y} (ha : Measurable a) (z : Z) :
    conditionalLabelEntropy μ a (fun _ ↦ z) = ∫⁻ x, atomInformation (μ (a ⁻¹' {a x})) ∂μ := by
  refine lintegral_congr fun x ↦ ?_
  have hz : μ.map (fun _ : X ↦ z) {z} ≠ 0 := by
    simp [Measure.map_const]
  rw [condDistrib_apply_of_ne_zero measurable_const ha z hz,
    Measure.map_apply (measurable_const.prodMk ha) ((measurableSet_singleton z).prod
      (measurableSet_singleton (a x)))]
  simp only [Measure.map_const, measure_univ, smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_singleton z), smul_eq_mul, mul_one, inv_one, one_mul]
  congr 2
  ext y
  simp

end TauCeti
