/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Discrete
public import TauCeti.Topology.ContinuousMap.Bounded.AddContent

/-!
# Means and finitely additive probabilities on discrete groups

A mean on a discrete group gives a finitely additive probability on all subsets by evaluating
characteristic functions. `TauCeti.Mean.toContent` bundles this probability as an `AddContent`,
not as a countably additive measure. Its values are finite, and their real parts recover the
mean on characteristic functions. More generally, the mean of a finite linear combination of
characteristic functions is the corresponding linear combination of content values.

Every finitely additive probability on all subsets arises from exactly one mean
(`TauCeti.Mean.contentEquiv`), by integrating bounded functions against it. The construction
commutes with pushforward along arbitrary maps between discrete groups, and a mean is left
invariant exactly when its probability is. Hence a discrete group is amenable exactly when it
admits a left-invariant finitely additive probability on all subsets
(`TauCeti.amenable_iff_exists_invariantContent`).

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

variable (G) in
/-- Means on a discrete group correspond to finitely additive probabilities on all subsets, by
evaluating at characteristic functions. The inverse integrates a bounded function against the
probability. -/
def contentEquiv : Mean G ≃ {ν : AddContent ℝ≥0∞ (univ : Set (Set G)) // ν univ = 1} where
  toFun m := ⟨m.toContent, m.toContent_univ⟩
  invFun ν := (boundedContinuousFunctionEquiv G).symm
    ⟨(PositiveLinearMap.addContentEquiv G).symm
      ⟨ν.1.toReal fun s _ => addContent_ne_top_of_univ_ne_top (ν.2.trans_ne ENNReal.one_ne_top) s,
        AddContent.toReal_nonneg _ _⟩,
      by simp [AddContent.toReal_apply, ν.2]⟩
  left_inv m := by
    refine (boundedContinuousFunctionEquiv G).symm_apply_eq.2 (Subtype.ext ?_)
    refine (PositiveLinearMap.addContentEquiv G).symm_apply_eq.2 (Subtype.ext ?_)
    rw [PositiveLinearMap.coe_addContentEquiv_apply]
    exact toContent_toReal m
  right_inv ν := by
    refine Subtype.ext (AddContent.ext fun s => ?_)
    rw [toContent_apply, boundedContinuousFunctionEquiv_symm_apply,
      UCB.coe_discreteAlgEquiv_symm, PositiveLinearMap.addContentEquiv_symm_apply_indicator,
      AddContent.toReal_apply,
      ENNReal.ofReal_toReal (addContent_ne_top_of_univ_ne_top (ν.2.trans_ne ENNReal.one_ne_top) s)]

@[simp]
theorem coe_contentEquiv_apply (m : Mean G) :
    (contentEquiv G m : AddContent ℝ≥0∞ (univ : Set (Set G))) = m.toContent :=
  (rfl)

/-- The mean associated to a finitely additive probability has that probability as its
content. -/
@[simp]
theorem toContent_contentEquiv_symm
    (ν : {ν : AddContent ℝ≥0∞ (univ : Set (Set G)) // ν univ = 1}) :
    ((contentEquiv G).symm ν).toContent = ν.1 :=
  congrArg Subtype.val ((contentEquiv G).apply_symm_apply ν)

/-- A mean on a discrete group is determined by its content. -/
theorem toContent_injective : Function.Injective (toContent : Mean G → _) :=
  fun _ _ h => (contentEquiv G).injective (Subtype.ext h)

/-- A mean on a discrete group is left invariant exactly when its content is invariant under
left translation of sets. -/
theorem isLeftInvariant_iff_toContent_smul (m : Mean G) :
    m.IsLeftInvariant ↔ ∀ (g : G) (s : Set G), m.toContent (g • s) = m.toContent s := by
  refine ⟨fun hm => hm.toContent_smul, fun h => isLeftInvariant_iff.2 fun g f => ?_⟩
  -- Pushing `m` forward along `x ↦ g⁻¹ * x` translates its content by `g`, so fixes it.
  have hmap : m.mapOfDiscrete (g⁻¹ * ·) = m := by
    refine toContent_injective (AddContent.ext fun s => ?_)
    -- The left regular action `g⁻¹ • x` is multiplication `g⁻¹ * x`.
    have hs : (g⁻¹ * ·) ⁻¹' s = g • s := preimage_smul_inv g s
    rw [toContent_mapOfDiscrete, AddContent.map_apply, hs, h]
  have hf : UCB.compRightAlgHomOfDiscrete (g⁻¹ * ·) f = UCB.leftTranslation g f :=
    UCB.ext fun x => by simp [UCB.compRightAlgHomOfDiscrete_apply, UCB.leftTranslation_apply]
  rw [← hf, ← mapOfDiscrete_apply, hmap]

end Mean

/-- An amenable discrete group admits an invariant finitely additive probability on all subsets. -/
theorem Amenable.exists_invariantContent [Amenable G] :
    ∃ ν : AddContent ℝ≥0∞ (univ : Set (Set G)),
      ν univ = 1 ∧ ∀ (g : G) (s : Set G), ν (g • s) = ν s := by
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  exact ⟨m.toContent, m.toContent_univ, hm.toContent_smul⟩

variable (G) in
/-- **Discrete amenability by finitely additive probabilities.** A discrete group is amenable
exactly when it admits a left-invariant finitely additive probability on all subsets. -/
theorem amenable_iff_exists_invariantContent :
    Amenable G ↔ ∃ ν : AddContent ℝ≥0∞ (univ : Set (Set G)),
      ν univ = 1 ∧ ∀ (g : G) (s : Set G), ν (g • s) = ν s := by
  refine ⟨fun _ => Amenable.exists_invariantContent, fun ⟨ν, h₁, hν⟩ => ?_⟩
  refine (amenable_iff G).2 ⟨(Mean.contentEquiv G).symm ⟨ν, h₁⟩, ?_⟩
  rw [Mean.isLeftInvariant_iff_toContent_smul, Mean.toContent_contentEquiv_symm]
  exact hν

end TauCeti
