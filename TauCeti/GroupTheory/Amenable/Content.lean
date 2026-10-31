/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Discrete
public import TauCeti.Topology.ContinuousMap.Bounded.AddContent

/-!
# Finitely additive probabilities from discrete means

A mean on a discrete group gives a finitely additive probability on all subsets by evaluating
characteristic functions. `TauCeti.Mean.toContent` bundles this probability as an `AddContent`,
not as a countably additive measure. Its values are finite, and their real parts recover the
mean on characteristic functions. More generally, the mean of a finite linear combination of
characteristic functions is the corresponding linear combination of content values.

The construction commutes with pushforward along arbitrary maps between discrete groups.
A left-invariant mean gives a left-invariant probability, so every amenable discrete group
admits such a probability. No converse construction of a mean from a content is asserted here.

## References

* A. Garrido, *An introduction to amenable groups*, Theorem 1.15, in discrete scope.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped BoundedContinuousFunction ENNReal Pointwise

namespace TauCeti

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [DiscreteTopology H]

namespace Mean

/-- The finitely additive probability on all subsets associated to a discrete mean. -/
def toContent (m : Mean G) : AddContent ℝ≥0∞ (univ : Set (Set G)) :=
  ((boundedContinuousFunctionEquiv G m).1.toLinearMap.toAddContent).ofReal
    (fun s _ => PositiveLinearMap.toAddContent_nonneg _ s)

/-- A content value is the mean of the characteristic function, converted to `ℝ≥0∞`. -/
theorem toContent_apply (m : Mean G) (s : Set G) :
    m.toContent s = ENNReal.ofReal
      (m ((UCB.discreteAlgEquiv G).symm
        (BoundedContinuousFunction.indicator s (isClopen_discrete s)))) := by
  simp only [toContent, AddContent.ofReal_apply, LinearMap.toAddContent_apply,
    PositiveLinearMap.coe_toLinearMap, boundedContinuousFunctionEquiv_apply]

/-- The content associated to a mean has total mass one. -/
@[simp]
theorem toContent_univ (m : Mean G) : m.toContent univ = 1 := by
  simp [toContent_apply]

/-- Every value of the content associated to a mean is at most one. -/
theorem toContent_le_one (m : Mean G) (s : Set G) : m.toContent s ≤ 1 := by
  simpa using addContent_le_univ m.toContent s

/-- The content associated to a mean is finite on every subset. -/
theorem toContent_ne_top (m : Mean G) (s : Set G) : m.toContent s ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (m.toContent_le_one s)

/-- Taking real values recovers the mean on characteristic functions. -/
@[simp]
theorem toReal_toContent (m : Mean G) (s : Set G) :
    (m.toContent s).toReal = m ((UCB.discreteAlgEquiv G).symm
      (BoundedContinuousFunction.indicator s (isClopen_discrete s))) := by
  rw [toContent_apply, ENNReal.toReal_ofReal]
  simpa only [LinearMap.toAddContent_apply, PositiveLinearMap.coe_toLinearMap,
    boundedContinuousFunctionEquiv_apply] using
    PositiveLinearMap.toAddContent_nonneg (boundedContinuousFunctionEquiv G m).1 s

/-- The original real content is recovered by taking real values of `toContent`. -/
theorem toContent_toReal (m : Mean G) :
    m.toContent.toReal (fun s _ => m.toContent_ne_top s) =
      (boundedContinuousFunctionEquiv G m).1.toLinearMap.toAddContent := by
  simp only [toContent, AddContent.toReal_ofReal]

/-- A mean evaluates finite linear combinations of characteristic functions by its content.
The sets need not be disjoint. -/
theorem apply_sum_smul_indicator (m : Mean G) {ι : Type*} (I : Finset ι)
    (c : ι → ℝ) (A : ι → Set G) :
    m ((UCB.discreteAlgEquiv G).symm
      (∑ i ∈ I, c i • BoundedContinuousFunction.indicator (A i) (isClopen_discrete _))) =
      ∑ i ∈ I, c i * (m.toContent (A i)).toReal := by
  simp only [map_sum, map_smul, toReal_toContent, smul_eq_mul]

/-- Contents commute with pushforward along arbitrary maps between discrete groups. -/
theorem toContent_mapOfDiscrete (m : Mean G) (r : G → H) :
    (m.mapOfDiscrete r).toContent = m.toContent.map r (fun _ _ => mem_univ _) := by
  ext s
  rw [AddContent.map_apply, toContent_apply, toContent_apply, mapOfDiscrete_apply]
  congr 2
  apply (UCB.discreteAlgEquiv G).injective
  simp only [UCB.discreteAlgEquiv_apply, UCB.coe_compRightAlgHomOfDiscrete,
    UCB.coe_discreteAlgEquiv_symm, BoundedContinuousFunction.indicator_compContinuous,
    ContinuousMap.coe_mk]

/-- In particular, contents commute with pushforward by continuous homomorphisms. -/
theorem toContent_map (m : Mean G) (φ : G →ₜ* H) :
    (m.map φ).toContent = m.toContent.map φ (fun _ _ => mem_univ _) := by
  rw [← mapOfDiscrete_coe, toContent_mapOfDiscrete]

/-- A left-invariant mean assigns equal content to a set and each of its left translates. -/
theorem IsLeftInvariant.toContent_smul {m : Mean G} (hm : m.IsLeftInvariant)
    (g : G) (s : Set G) : m.toContent (g • s) = m.toContent s := by
  have h : (UCB.discreteAlgEquiv G).symm
      (BoundedContinuousFunction.indicator (g • s) (isClopen_discrete _)) =
      UCB.leftTranslation g ((UCB.discreteAlgEquiv G).symm
        (BoundedContinuousFunction.indicator s (isClopen_discrete _))) := by
    apply UCB.ext
    intro x
    simp only [UCB.leftTranslation_apply, UCB.coe_discreteAlgEquiv_symm,
      BoundedContinuousFunction.indicator_apply]
    by_cases hx : x ∈ g • s <;> simp_all [mem_smul_set_iff_inv_smul_mem]
  simp only [toContent_apply, h, hm.apply_leftTranslation]

end Mean

/-- An amenable discrete group admits an invariant finitely additive probability on all subsets. -/
theorem Amenable.exists_invariantContent [Amenable G] :
    ∃ ν : AddContent ℝ≥0∞ (univ : Set (Set G)),
      ν univ = 1 ∧ ∀ (g : G) (s : Set G), ν (g • s) = ν s := by
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  exact ⟨m.toContent, m.toContent_univ, hm.toContent_smul⟩

end TauCeti
