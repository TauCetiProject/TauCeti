/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.InvariantProbabilities
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Group.TranslationStabilizer
import Mathlib.Topology.Metrizable.Basic

/-!
# Rotations with dense powers are uniquely ergodic

Let `G` be a compact metrizable topological group, not necessarily commutative, and `a : G` an
element whose integer powers are dense. A Borel probability measure invariant under the rotation
`x ↦ a * x` is invariant under every left translation
(`MeasureTheory.Measure.isMulLeftInvariant_of_denseRange_zpow`: the translations preserving it
form a closed subgroup containing the dense set of powers of `a`). By uniqueness of Haar measure
the rotation has exactly one invariant probability.

## Main results

* `TauCeti.uniquelyErgodic_mul_left_of_denseRange_zpow`,
  `TauCeti.uniquelyErgodic_add_left_of_denseRange_zsmul`: a rotation of a compact metrizable group
  with dense powers (or multiples) is uniquely ergodic.

## References

* P. Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer
  (1982), Theorem 6.20. There `G` is commutative and invariance under all powers of `a` extends to
  all translations by continuity; here the closedness of the set of measure-preserving
  translations extends the argument to noncommutative groups.
-/

public section

open MeasureTheory Measure Set TopologicalSpace

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

/-- **Unique ergodicity of rotations.** A rotation `x ↦ a * x` of a compact metrizable group whose
integer powers are dense is uniquely ergodic: it has exactly one invariant probability. -/
@[to_additive /-- **Unique ergodicity of rotations.** A rotation `x ↦ a + x` of a compact
metrizable additive group whose integer multiples are dense is uniquely ergodic: it has exactly
one invariant probability. -/]
theorem uniquelyErgodic_mul_left_of_denseRange_zpow [CompactSpace G] [MetrizableSpace G] {a : G}
    (ha : DenseRange (fun n : ℤ ↦ a ^ n)) : UniquelyErgodic (a * · : G → G) := by
  have : SecondCountableTopology G := by
    let := metrizableSpaceMetric G
    infer_instance
  refine uniquelyErgodic_iff.mpr ⟨invariantProbabilities_nonempty (continuous_const_mul a),
    fun ν₁ h₁ ν₂ h₂ ↦ ProbabilityMeasure.toMeasure_injective ?_⟩
  have hHaar : ∀ ν : ProbabilityMeasure G, ν ∈ invariantProbabilities (a * · : G → G) →
      IsHaarMeasure (ν : Measure G) := fun ν hν ↦
    have := isMulLeftInvariant_of_denseRange_zpow ha (mem_invariantProbabilities.mp hν).map_eq
    isHaarMeasure_of_isCompact_nonempty_interior _ univ isCompact_univ (by simp) (by simp)
      (by simp)
  have := hHaar ν₁ h₁
  have := hHaar ν₂ h₂
  exact isHaarMeasure_eq_of_isProbabilityMeasure _ _

end TauCeti
