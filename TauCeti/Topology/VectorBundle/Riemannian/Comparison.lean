/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Riemannian.Basic
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Uniform comparison of bundle metrics

A continuous metric on a finite-rank real vector bundle is uniformly comparable to a fixed
continuous reference metric over every compact subset of the base. The comparison is on all
vectors, not just on a local frame, and uses strictly positive constants. This lets estimates
made using different metrics be transferred without changing the topology of the fibres.

The proof takes the minimum and maximum of the new metric on the reference unit sphere bundle,
then uses quadratic homogeneity. Adjoining the value one to the compact set of values handles
empty compact sets and rank-zero bundles without a nonemptiness assumption.
-/

public section

open Bundle Set
open scoped Topology

namespace Bundle.ContinuousRiemannianMetric

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)]
  [FiberBundle F E]

section Evaluation

variable [∀ x, NormedSpace ℝ (E x)] [VectorBundle ℝ F E]

/-- The diagonal value of a continuous metric is continuous on the total space, independently
of the reference norms on the fibres. -/
theorem continuous_inner_self (g : ContinuousRiemannianMetric F E) :
    Continuous (fun z : TotalSpace F E ↦ g.inner z.proj z.2 z.2) := by
  have hv : Continuous (fun z : TotalSpace F E ↦ TotalSpace.mk' F z.proj z.2) :=
    continuous_id.congr fun z ↦ (TotalSpace.eta z).symm
  have h : Continuous (fun z : TotalSpace F E ↦
      TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) z.proj (g.inner z.proj z.2 z.2)) :=
    (g.continuous.comp (FiberBundle.continuous_proj F E)).clm_bundle_apply₂ hv hv
  exact continuous_snd.comp ((Bundle.Trivial.homeomorphProd B ℝ).continuous.comp h)

end Evaluation

variable [∀ x, InnerProductSpace ℝ (E x)] [VectorBundle ℝ F E]
  [FiniteDimensional ℝ F] [IsContinuousRiemannianBundle F E]

/-- On a compact set, a continuous metric has positive uniform lower and upper bounds against
the squared norm of a continuous reference metric. No nonemptiness or positive rank is required. -/
theorem exists_uniform_bounds (g : ContinuousRiemannianMetric F E)
    {K : Set B} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : E x,
      c * ‖v‖ ^ 2 ≤ g.inner x v v ∧ g.inner x v v ≤ C * ‖v‖ ^ 2 := by
  let S : Set (TotalSpace F E) := {z | z.proj ∈ K ∧ ‖z.2‖ = 1}
  have hS : IsCompact S := by
    convert (hK.norm_le_bundle (F := F) 1).inter_right
      (isClosed_eq (TauCeti.continuous_norm_bundle F E) (continuous_const (y := (1 : ℝ))))
      using 1
    ext z
    simp only [S, mem_inter_iff, mem_ofPred_eq]
    grind
  let q : TotalSpace F E → ℝ := fun z ↦ g.inner z.proj z.2 z.2
  have hvalues : IsCompact (insert 1 (q '' S)) :=
    (hS.image g.continuous_inner_self).insert 1
  have hpos : ∀ a ∈ insert 1 (q '' S), 0 < a := by
    rintro a (rfl | ⟨z, hz, rfl⟩)
    · exact zero_lt_one
    · exact g.pos _ _ (fun h ↦ by simpa [h] using hz.2)
  obtain ⟨c, hc⟩ := hvalues.exists_isLeast (by simp)
  obtain ⟨C, hC⟩ := hvalues.exists_isGreatest (by simp)
  refine ⟨c, C, hpos _ hc.1, hpos _ hC.1, fun x hx v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · have hu : (⟨x, NormedSpace.normalize v⟩ : TotalSpace F E) ∈ S :=
      ⟨hx, NormedSpace.norm_normalize hv⟩
    have hmem : g.inner x (NormedSpace.normalize v) (NormedSpace.normalize v) ∈
        insert 1 (q '' S) := Or.inr ⟨_, hu, rfl⟩
    have heq : g.inner x v v = ‖v‖ ^ 2 *
        g.inner x (NormedSpace.normalize v) (NormedSpace.normalize v) := by
      conv_lhs => rw [← NormedSpace.norm_smul_normalize v]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [heq]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left (hc.2 hmem) (sq_nonneg ‖v‖)]
    · nlinarith [mul_le_mul_of_nonneg_left (hC.2 hmem) (sq_nonneg ‖v‖)]

end Bundle.ContinuousRiemannianMetric
