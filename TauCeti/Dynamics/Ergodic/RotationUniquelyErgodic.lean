/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.InvariantProbabilities
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Metrizable.Basic

/-!
# Rotations with dense powers are uniquely ergodic

Let `G` be a compact metrizable additive topological group, not necessarily abelian, and `a : G`
an element whose integer multiples are dense. A finite Borel measure invariant under the rotation
`x ↦ a + x` is invariant under every translation: the translations preserving it form a closed
subgroup (closed because `g ↦ ∫ x, f (g + x) ∂ν` is continuous for bounded continuous `f`, and
such integrals determine finite measures on metrizable spaces), and this subgroup contains the
dense set of multiples of `a`. By uniqueness of Haar measure the rotation has exactly one
invariant probability.

## Main results

* `TauCeti.isClosed_setOf_map_add_left_eq`: the translations preserving a finite measure form a
  closed set.
* `TauCeti.isAddLeftInvariant_of_map_add_left_eq`: a finite measure invariant under a rotation
  with dense multiples is invariant under all translations.
* `TauCeti.uniquelyErgodic_add_left`: a rotation of a compact metrizable group with dense
  multiples is uniquely ergodic.
-/

public section

open MeasureTheory Measure Topology Set TopologicalSpace
open scoped BoundedContinuousFunction

namespace TauCeti

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- The translations preserving a finite measure on a pseudometrizable additive group form a
closed set. -/
theorem isClosed_setOf_map_add_left_eq [PseudoMetrizableSpace G] (ν : Measure G)
    [IsFiniteMeasure ν] : IsClosed {g : G | ν.map (g + ·) = ν} := by
  have key : {g : G | ν.map (g + ·) = ν} =
      ⋂ f : G →ᵇ ℝ, {g | ∫ x, f (g + x) ∂ν = ∫ x, f x ∂ν} := by
    ext g
    simp only [mem_ofPred_eq, mem_iInter]
    have hm : Measurable (g + · : G → G) := (continuous_const_add g).measurable
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
  · exact (f.continuous.comp (continuous_const_add g)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm _
  · exact Filter.Eventually.of_forall fun x ↦ f.continuous.comp (continuous_id.add continuous_const)

/-- If a measure is preserved by the translations by `g` and `h`, it is preserved by the
translation by `g + h`. -/
theorem map_add_left_eq_of_add {ν : Measure G} {g h : G} (hg : ν.map (g + ·) = ν)
    (hh : ν.map (h + ·) = ν) : ν.map (g + h + ·) = ν := by
  rw [show (g + h + · : G → G) = (g + ·) ∘ (h + ·) from funext fun x ↦ add_assoc g h x,
    ← map_map (continuous_const_add g).measurable (continuous_const_add h).measurable, hh, hg]

/-- If a measure is preserved by the translation by `g`, it is preserved by the translation by
`-g`. -/
theorem map_add_left_eq_of_neg {ν : Measure G} {g : G} (hg : ν.map (g + ·) = ν) :
    ν.map (-g + ·) = ν := by
  conv_lhs => rw [← hg]
  rw [map_map (continuous_const_add _).measurable (continuous_const_add g).measurable]
  simp [Function.comp_def]

/-- **Rotations with dense multiples.** On a pseudometrizable additive group, a finite measure
preserved by the translation by `a`, where the integer multiples of `a` are dense, is preserved
by every translation. -/
theorem isAddLeftInvariant_of_map_add_left_eq [PseudoMetrizableSpace G] {a : G}
    (ha : DenseRange (fun n : ℤ ↦ n • a)) {ν : Measure G} [IsFiniteMeasure ν]
    (hν : ν.map (a + ·) = ν) : IsAddLeftInvariant ν := by
  have hmul : ∀ n : ℤ, ν.map (n • a + ·) = ν := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [add_zsmul, one_zsmul]; exact map_add_left_eq_of_add ih hν
    | pred n ih =>
      rw [sub_zsmul, one_zsmul]
      exact map_add_left_eq_of_add ih (map_add_left_eq_of_neg hν)
  have hall : {g : G | ν.map (g + ·) = ν} = univ :=
    eq_univ_of_univ_subset <| ha.closure_range ▸ closure_minimal (range_subset_iff.mpr hmul)
      (isClosed_setOf_map_add_left_eq ν)
  exact ⟨fun g ↦ (hall ▸ mem_univ g :)⟩

/-- **Unique ergodicity of rotations.** A rotation `x ↦ a + x` of a compact metrizable additive
group whose integer multiples are dense is uniquely ergodic: its only invariant probability is the
normalised Haar measure. -/
theorem uniquelyErgodic_add_left [CompactSpace G] [MetrizableSpace G] {a : G}
    (ha : DenseRange (fun n : ℤ ↦ n • a)) : UniquelyErgodic (a + · : G → G) := by
  have : SecondCountableTopology G := by
    let := metrizableSpaceMetric G
    infer_instance
  refine uniquelyErgodic_iff.mpr ⟨invariantProbabilities_nonempty (continuous_const_add a),
    fun ν₁ h₁ ν₂ h₂ ↦ ProbabilityMeasure.toMeasure_injective ?_⟩
  have hinv : ∀ ν : ProbabilityMeasure G, ν ∈ invariantProbabilities (a + · : G → G) →
      IsAddLeftInvariant (ν : Measure G) := fun ν hν ↦
    isAddLeftInvariant_of_map_add_left_eq ha (mem_invariantProbabilities.mp hν).map_eq
  have := hinv ν₁ h₁
  have := hinv ν₂ h₂
  have := isAddHaarMeasure_of_isCompact_nonempty_interior (ν₁ : Measure G) univ isCompact_univ
    (by simp) (by simp) (by simp)
  have := isAddHaarMeasure_of_isCompact_nonempty_interior (ν₂ : Measure G) univ isCompact_univ
    (by simp) (by simp) (by simp)
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

end TauCeti
