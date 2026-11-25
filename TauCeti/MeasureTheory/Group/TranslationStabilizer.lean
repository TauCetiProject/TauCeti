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
# The translations preserving a measure

For a measure `ν` on a group `G`, the left translations `x ↦ g * x` that preserve `ν` form a
subgroup of `G`. For a finite measure on a first-countable topological group in which bounded
continuous integrals determine finite measures (`HasOuterApproxClosed`, for instance a
pseudometrizable group), this subgroup is closed: `g ↦ ∫ x, f (g * x) ∂ν` is continuous for every
bounded continuous `f`. Consequently a finite measure preserved by a translation `x ↦ a * x`
whose integer powers `a ^ n` are dense is preserved by every left translation.

## Main results

* `MeasureTheory.Measure.isClosed_setOf_map_mul_left_eq_self`,
  `MeasureTheory.Measure.isClosed_setOf_map_add_left_eq_self`: the translations preserving a
  finite measure form a closed set.
* `MeasureTheory.Measure.map_mul_mul_left_eq_self`, `MeasureTheory.Measure.map_inv_mul_left_eq_self`
  and their additive versions: the translations preserving a measure are closed under products and
  inverses.
* `MeasureTheory.Measure.isMulLeftInvariant_of_denseRange_zpow`,
  `MeasureTheory.Measure.isAddLeftInvariant_of_denseRange_zsmul`: a finite measure preserved by a
  translation with dense powers (or multiples) is left-invariant.
-/

public section

open Set Topology
open scoped BoundedContinuousFunction

namespace MeasureTheory.Measure

variable {G : Type*} [MeasurableSpace G]

/-- If a measure is preserved by the left translations by `g` and `h`, it is preserved by the
left translation by `g * h`. -/
@[to_additive /-- If a measure is preserved by the left translations by `g` and `h`, it is
preserved by the left translation by `g + h`. -/]
theorem map_mul_mul_left_eq_self [Semigroup G] [MeasurableMul G] {ν : Measure G} {g h : G}
    (hg : ν.map (g * ·) = ν) (hh : ν.map (h * ·) = ν) : ν.map (g * h * ·) = ν := by
  rw [show (g * h * · : G → G) = (g * ·) ∘ (h * ·) from funext fun x ↦ mul_assoc g h x,
    ← map_map (measurable_const_mul g) (measurable_const_mul h), hh, hg]

/-- If a measure is preserved by the left translation by `g`, it is preserved by the left
translation by `g⁻¹`. -/
@[to_additive /-- If a measure is preserved by the left translation by `g`, it is preserved by
the left translation by `-g`. -/]
theorem map_inv_mul_left_eq_self [Group G] [MeasurableMul G] {ν : Measure G} {g : G}
    (hg : ν.map (g * ·) = ν) : ν.map (g⁻¹ * ·) = ν := by
  conv_lhs => rw [← hg]
  rw [map_map (measurable_const_mul _) (measurable_const_mul g)]
  simp [Function.comp_def]

variable [TopologicalSpace G] [BorelSpace G] [FirstCountableTopology G] [HasOuterApproxClosed G]

/-- The left translations preserving a finite measure form a closed set. -/
@[to_additive /-- The left translations preserving a finite measure form a closed set. -/]
theorem isClosed_setOf_map_mul_left_eq_self [Monoid G] [ContinuousMul G] (ν : Measure G)
    [IsFiniteMeasure ν] : IsClosed {g : G | ν.map (g * ·) = ν} := by
  have key : {g : G | ν.map (g * ·) = ν} =
      ⋂ f : G →ᵇ ℝ, {g | ∫ x, f (g * x) ∂ν = ∫ x, f x ∂ν} := by
    ext g
    simp only [mem_ofPred_eq, mem_iInter]
    have hm : Measurable (g * · : G → G) := (continuous_const_mul g).measurable
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
  · exact (f.continuous.comp (continuous_const_mul g)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm _
  · exact Filter.Eventually.of_forall fun x ↦ f.continuous.comp (continuous_id.mul continuous_const)

/-- **Translations with dense powers.** A finite measure preserved by the left translation by
`a`, where the integer powers of `a` are dense, is preserved by every left translation. -/
@[to_additive /-- **Translations with dense multiples.** A finite measure preserved by the left
translation by `a`, where the integer multiples of `a` are dense, is preserved by every left
translation. -/]
theorem isMulLeftInvariant_of_denseRange_zpow [Group G] [ContinuousMul G] {a : G}
    (ha : DenseRange (fun n : ℤ ↦ a ^ n)) {ν : Measure G} [IsFiniteMeasure ν]
    (hν : ν.map (a * ·) = ν) : IsMulLeftInvariant ν := by
  have hpow : ∀ n : ℤ, ν.map (a ^ n * ·) = ν := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one]; exact map_mul_mul_left_eq_self ih hν
    | pred n ih =>
      rw [zpow_sub_one]
      exact map_mul_mul_left_eq_self ih (map_inv_mul_left_eq_self hν)
  have hall : {g : G | ν.map (g * ·) = ν} = univ :=
    eq_univ_of_univ_subset <| ha.closure_range ▸ closure_minimal (range_subset_iff.mpr hpow)
      (isClosed_setOf_map_mul_left_eq_self ν)
  exact ⟨fun g ↦ (hall ▸ mem_univ g :)⟩

end MeasureTheory.Measure
