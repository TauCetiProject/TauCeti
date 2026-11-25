/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
-- Proof-only: continuity of a parametric integral under a uniform bound.
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The group elements preserving a measure

For an action of a group `G` on a measurable space `X` and a measure `ν` on `X`, the elements
`g` with `ν.map (g • ·) = ν` form a subgroup of `G`. For a continuous action of a first-countable
topological group on a space in which bounded continuous integrals determine finite measures
(`HasOuterApproxClosed`, for instance a pseudometrizable space), this subgroup is closed when `ν`
is finite: `g ↦ ∫ x, f (g • x) ∂ν` is continuous for every bounded continuous `f`. Consequently a
finite measure preserved by the action of an element `a` whose integer powers `a ^ n` are dense
is invariant under the whole group. For left translation of a group on itself, this says that
the measure is left-invariant.

## Main results

* `MeasureTheory.Measure.isClosed_setOf_map_smul_eq_self`,
  `MeasureTheory.Measure.isClosed_setOf_map_vadd_eq_self`: the elements whose action preserves a
  finite measure form a closed set.
* `MeasureTheory.Measure.smulInvariantMeasure_of_denseRange_zpow`,
  `MeasureTheory.Measure.vaddInvariantMeasure_of_denseRange_zsmul`: a finite measure preserved by
  the action of an element with dense powers (or multiples) is invariant under the whole group.
* `MeasureTheory.Measure.isMulLeftInvariant_of_denseRange_zpow`,
  `MeasureTheory.Measure.isAddLeftInvariant_of_denseRange_zsmul`: a finite measure preserved by a
  translation with dense powers (or multiples) is left-invariant.
-/

public section

open Set Topology
open scoped BoundedContinuousFunction

namespace MeasureTheory.Measure

variable {M G X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [HasOuterApproxClosed X]

/-- The elements of `M` whose action preserves a finite measure on `X` form a closed set. -/
@[to_additive /-- The elements of `M` whose action preserves a finite measure on `X` form a closed
set. -/]
theorem isClosed_setOf_map_smul_eq_self [TopologicalSpace M] [FirstCountableTopology M] [SMul M X]
    [ContinuousSMul M X] (ν : Measure X) [IsFiniteMeasure ν] :
    IsClosed {g : M | ν.map (g • ·) = ν} := by
  have key : {g : M | ν.map (g • ·) = ν} =
      ⋂ f : X →ᵇ ℝ, {g | ∫ x, f (g • x) ∂ν = ∫ x, f x ∂ν} := by
    ext g
    simp only [mem_ofPred_eq, mem_iInter]
    have hm : Measurable (g • · : X → X) := (continuous_const_smul g).measurable
    constructor
    · intro h f
      conv_rhs => rw [← h]
      rw [integral_map hm.aemeasurable f.continuous.aestronglyMeasurable]
    · intro h
      refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_
      rw [integral_map hm.aemeasurable f.continuous.aestronglyMeasurable, h f]
  rw [key]
  refine isClosed_iInter fun f ↦ isClosed_eq ?_ continuous_const
  refine continuous_of_dominated (bound := fun _ ↦ ‖f‖) (fun g ↦ ?_) (fun g ↦ ?_)
    (integrable_const _) ?_
  · exact (f.continuous.comp (continuous_const_smul g)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm _
  · exact Filter.Eventually.of_forall fun x ↦
      f.continuous.comp (continuous_id.smul continuous_const)

/-- **Actions with dense powers.** A finite measure preserved by the action of `a`, where the
integer powers of `a` are dense, is invariant under the action of the whole group. -/
@[to_additive /-- **Actions with dense multiples.** A finite measure preserved by the action of
`a`, where the integer multiples of `a` are dense, is invariant under the action of the whole
group. -/]
theorem smulInvariantMeasure_of_denseRange_zpow [Group G] [TopologicalSpace G]
    [FirstCountableTopology G] [MulAction G X] [ContinuousSMul G X] {a : G}
    (ha : DenseRange (fun n : ℤ ↦ a ^ n)) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : ν.map (a • ·) = ν) : SMulInvariantMeasure G X ν := by
  -- The preserving elements form a subgroup. Mathlib's stabilizer for the action of `Gᵈᵐᵃ` on
  -- measures has no additive counterpart, so the closure properties are checked directly.
  have hmul {g h : G} (hg : ν.map (g • ·) = ν) (hh : ν.map (h • ·) = ν) :
      ν.map ((g * h) • ·) = ν := by
    rw [show ((g * h) • · : X → X) = (g • ·) ∘ (h • ·) from funext fun x ↦ mul_smul g h x,
      ← map_map (measurable_const_smul g) (measurable_const_smul h), hh, hg]
  have hinv : ν.map (a⁻¹ • ·) = ν := by
    conv_lhs => rw [← hν]
    rw [map_map (measurable_const_smul _) (measurable_const_smul a)]
    simp [Function.comp_def]
  have hpow : ∀ n : ℤ, ν.map (a ^ n • ·) = ν := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one]; exact hmul ih hν
    | pred n ih => rw [zpow_sub_one]; exact hmul ih hinv
  have hall : {g : G | ν.map (g • ·) = ν} = univ :=
    eq_univ_of_univ_subset <| ha.closure_range ▸ closure_minimal (range_subset_iff.mpr hpow)
      (isClosed_setOf_map_smul_eq_self ν)
  refine ⟨fun g s hs ↦ ?_⟩
  rw [← map_apply (measurable_const_smul g) hs, (hall ▸ mem_univ g :)]

/-- **Translations with dense powers.** A finite measure preserved by the left translation by
`a`, where the integer powers of `a` are dense, is preserved by every left translation. -/
@[to_additive /-- **Translations with dense multiples.** A finite measure preserved by the left
translation by `a`, where the integer multiples of `a` are dense, is preserved by every left
translation. -/]
theorem isMulLeftInvariant_of_denseRange_zpow [Group G] [TopologicalSpace G]
    [FirstCountableTopology G] [MeasurableSpace G] [BorelSpace G] [HasOuterApproxClosed G]
    [ContinuousMul G] {a : G} (ha : DenseRange (fun n : ℤ ↦ a ^ n)) {ν : Measure G}
    [IsFiniteMeasure ν] (hν : ν.map (a * ·) = ν) : IsMulLeftInvariant ν :=
  have := smulInvariantMeasure_of_denseRange_zpow ha hν
  ⟨fun g ↦ (measurePreserving_smul g ν).map_eq⟩

end MeasureTheory.Measure
