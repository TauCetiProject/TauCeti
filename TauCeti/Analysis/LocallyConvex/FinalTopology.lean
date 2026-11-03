/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Final locally convex topologies

Given linear maps from a family of topological real vector spaces into a real vector space,
`finalLocallyConvexTopology` is the finest locally convex vector topology making them continuous.
The source topologies need not themselves be vector topologies. No separation or injectivity
assumption is imposed; in particular, this construction does not assert Hausdorffness.

A linear map out of this topology into a locally convex space is continuous exactly when its
composites with the generating maps are continuous. The comparison criterion permits replacing
the generating family by another family through finite sums of continuous factorizations. This
allows partition-of-unity decompositions when comparing chart-generated test-section topologies
with fixed-support inductive limits.

The construction and universal-property proof generalize Mathlib's
`TestFunction.topologicalSpace` and `TestFunction.continuous_iff_continuous_comp` from a particular
family of fixed-support inclusions to an arbitrary family of linear maps. They use the same
infimum of locally convex vector topologies, not the final topology of topological spaces.
-/

public section

noncomputable section

open TopologicalSpace

namespace TauCeti

variable {ι : Type*} {E : ι → Type*} {F : Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
  [AddCommGroup F] [Module ℝ F]

/-- The finest locally convex real vector topology making all the linear maps `f i` continuous.
This need not be the final topology in the category of topological spaces. -/
@[instance_reducible]
def finalLocallyConvexTopology (f : ∀ i, E i →ₗ[ℝ] F) : TopologicalSpace F :=
  sInf {t : TopologicalSpace F |
    (⨆ i, coinduced (f i) inferInstance) ≤ t ∧
    @IsTopologicalAddGroup F t _ ∧ @ContinuousSMul ℝ F _ _ t ∧
    @LocallyConvexSpace ℝ F _ _ _ _ t}

namespace FinalLocallyConvexTopology

variable (f : ∀ i, E i →ₗ[ℝ] F)

instance : @IsTopologicalAddGroup F (finalLocallyConvexTopology f) _ :=
  isTopologicalAddGroup_sInf fun _ ⟨_, ht, _, _⟩ ↦ ht

instance : @ContinuousSMul ℝ F _ _ (finalLocallyConvexTopology f) :=
  continuousSMul_sInf fun _ ⟨_, _, ht, _⟩ ↦ ht

instance : @LocallyConvexSpace ℝ F _ _ _ _ (finalLocallyConvexTopology f) :=
  .sInf fun _ ⟨_, _, _, ht⟩ ↦ ht

/-- Every generating map is continuous for the final locally convex topology. -/
@[fun_prop]
theorem continuous (i : ι) :
    @Continuous (E i) F inferInstance (finalLocallyConvexTopology f) (f i) := by
  apply continuous_iff_coinduced_le.2
  exact le_trans (le_iSup (fun j ↦ coinduced (f j) inferInstance) i)
    (le_sInf fun _ ⟨ht, _⟩ ↦ ht)

/-- A locally convex real vector topology is coarser than the final topology exactly when it
makes every generating map continuous. Topologies are ordered in Lean by reverse fineness. -/
theorem le_iff (t : TopologicalSpace F) [@IsTopologicalAddGroup F t _]
    [@ContinuousSMul ℝ F _ _ t] [@LocallyConvexSpace ℝ F _ _ _ _ t] :
    finalLocallyConvexTopology f ≤ t ↔ ∀ i, @Continuous (E i) F inferInstance t (f i) := by
  constructor
  · intro h i
    exact continuous_iff_coinduced_le.2
      ((continuous_iff_coinduced_le.1 (continuous f i)).trans h)
  · intro h
    exact sInf_le ⟨iSup_le fun i ↦ continuous_iff_coinduced_le.1 (h i),
      inferInstance, inferInstance, inferInstance⟩

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G]

variable {𝕜 : Type*} [Semiring 𝕜] [Algebra ℝ 𝕜]
  [Module 𝕜 F] [IsScalarTower ℝ 𝕜 F] [Module 𝕜 G] [IsScalarTower ℝ 𝕜 G]

/-- The universal property of the final locally convex topology, for linear maps over an
ℝ-algebra into locally convex real topological vector spaces. -/
theorem continuous_iff_continuous_comp (g : F →ₗ[𝕜] G) :
    @Continuous F G (finalLocallyConvexTopology f) inferInstance g ↔
      ∀ i, Continuous (g ∘ f i) := by
  simp_rw [← g.coe_restrictScalars ℝ]
  have : @IsTopologicalAddGroup F (induced (g.restrictScalars ℝ) inferInstance) _ :=
    isTopologicalAddGroup_induced (g.restrictScalars ℝ)
  have : @ContinuousSMul ℝ F _ _ (induced (g.restrictScalars ℝ) inferInstance) :=
    continuousSMul_induced (g.restrictScalars ℝ)
  have : @LocallyConvexSpace ℝ F _ _ _ _ (induced (g.restrictScalars ℝ) inferInstance) :=
    .induced (g.restrictScalars ℝ)
  rw [continuous_iff_le_induced, le_iff]
  simp only [continuous_induced_rng]

/-- Construct a continuous linear map by checking continuity on each generating space. -/
def lift (g : F →ₗ[𝕜] G) (hg : ∀ i, Continuous (g ∘ f i)) :
    letI := finalLocallyConvexTopology f
    F →L[𝕜] G :=
  letI := finalLocallyConvexTopology f
  { g with cont := (continuous_iff_continuous_comp f g).2 hg }

@[simp]
theorem lift_apply (g : F →ₗ[𝕜] G) (hg : ∀ i, Continuous (g ∘ f i)) (x : F) :
    lift f g hg x = g x := (rfl)

variable {κ : Type*} {H : κ → Type*} [∀ j, AddCommGroup (H j)]
  [∀ j, Module ℝ (H j)] [∀ j, TopologicalSpace (H j)]

/-- A finite continuous decomposition of each generator into generators of another family
compares their final locally convex topologies. The finite sets may depend on the source stage,
as happens for a partition of unity on each fixed compact support. -/
theorem le_of_sum_factor (g : ∀ j, H j →ₗ[ℝ] F)
    (h : ∀ i, ∃ (s : Finset κ) (a : ∀ j, E i →ₗ[ℝ] H j),
      (∀ j ∈ s, Continuous (a j)) ∧ ∑ j ∈ s, g j ∘ₗ a j = f i) :
    finalLocallyConvexTopology f ≤ finalLocallyConvexTopology g := by
  let := finalLocallyConvexTopology g
  apply (le_iff f _).2
  intro i
  obtain ⟨s, a, ha, hfa⟩ := h i
  rw [← hfa]
  convert continuous_finsetSum s (fun j hj ↦ (continuous g j).comp (ha j hj)) using 1
  ext x
  simp

/-- Mutual finite continuous stage decompositions identify two presentations of the same
locally convex inductive-limit topology. Neither family needs to be directed. -/
theorem eq_of_sum_factor (g : ∀ j, H j →ₗ[ℝ] F)
    (hfg : ∀ i, ∃ (s : Finset κ) (a : ∀ j, E i →ₗ[ℝ] H j),
      (∀ j ∈ s, Continuous (a j)) ∧ ∑ j ∈ s, g j ∘ₗ a j = f i)
    (hgf : ∀ j, ∃ (s : Finset ι) (a : ∀ i, H j →ₗ[ℝ] E i),
      (∀ i ∈ s, Continuous (a i)) ∧ ∑ i ∈ s, f i ∘ₗ a i = g j) :
    finalLocallyConvexTopology f = finalLocallyConvexTopology g :=
  le_antisymm (le_of_sum_factor f g hfg) (le_of_sum_factor g f hgf)

/-- If all generators are continuous for an existing locally convex topology and one of them
has a continuous linear right inverse, the final topology recovers that existing topology. -/
theorem eq_of_rightInverse [t : TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    (hf : ∀ i, Continuous (f i)) (i : ι) (s : F →L[ℝ] E i)
    (hs : Function.RightInverse s (f i)) : finalLocallyConvexTopology f = t := by
  apply le_antisymm ((le_iff f t).2 hf)
  have h : @Continuous F F t (finalLocallyConvexTopology f) id := by
    have hc := @Continuous.comp F (E i) F t inferInstance (finalLocallyConvexTopology f)
      s (f i) (continuous f i) s.continuous
    rwa [Function.comp_def, funext hs] at hc
  exact (@continuous_id_iff_le F t (finalLocallyConvexTopology f)).1 h

end FinalLocallyConvexTopology

end TauCeti
