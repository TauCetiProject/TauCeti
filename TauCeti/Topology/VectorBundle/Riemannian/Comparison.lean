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

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]

section Evaluation

variable [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace Bundle.ContinuousRiemannianMetric

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

end Bundle.ContinuousRiemannianMetric

end Evaluation

section NormedReference

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [FiniteDimensional ℝ F] [IsContinuousRiemannianBundle F E]

/-- A bilinear field continuous and positive on a compact set has positive uniform two-sided
bounds against a continuous reference squared norm. Neither symmetry nor positivity outside the
compact set is required, and the compact set and unit sphere fibres may be empty. -/
theorem IsCompact.exists_pos_mul_norm_sq_le_bilin_self_and_le {K : Set B} (hK : IsCompact K)
    {b : ∀ x, E x →L[ℝ] E x →L[ℝ] ℝ}
    (hb : ContinuousOn (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (b x)) K)
    (hpos : ∀ x ∈ K, ∀ v : E x, v ≠ 0 → 0 < b x v v) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : E x,
      c * ‖v‖ ^ 2 ≤ b x v v ∧ b x v v ≤ C * ‖v‖ ^ 2 := by
  let S : Set (TotalSpace F E) := {z | z.proj ∈ K ∧ ‖z.2‖ = 1}
  have hS : IsCompact S := by
    convert (hK.norm_le_bundle (F := F) 1).inter_right
      (isClosed_eq (TauCeti.continuous_norm_bundle F E) (continuous_const (y := (1 : ℝ))))
      using 1
    ext z
    simp only [S, mem_inter_iff, mem_ofPred_eq]
    grind
  let q : TotalSpace F E → ℝ := fun z ↦ b z.proj z.2 z.2
  have hv : ContinuousOn (fun z : TotalSpace F E ↦ TotalSpace.mk' F z.proj z.2) S :=
    (continuous_id.congr fun z ↦ (TotalSpace.eta z).symm).continuousOn
  have hq : ContinuousOn q S := by
    have h : ContinuousOn (fun z : TotalSpace F E ↦
        TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) z.proj (b z.proj z.2 z.2)) S :=
      (hb.comp (FiberBundle.continuous_proj F E).continuousOn
        (fun z (hz : z ∈ S) ↦ hz.1)).clm_bundle_apply₂ hv hv
    exact continuous_snd.comp_continuousOn
      ((Bundle.Trivial.homeomorphProd B ℝ).continuous.comp_continuousOn h)
  have hvalues : IsCompact (insert 1 (q '' S)) :=
    (hS.image_of_continuousOn hq).insert 1
  have hvalues_pos : ∀ a ∈ insert 1 (q '' S), 0 < a := by
    rintro a (rfl | ⟨z, hz, rfl⟩)
    · exact zero_lt_one
    · exact hpos _ hz.1 _ (fun h ↦ by simpa [h] using hz.2)
  obtain ⟨c, hc⟩ := hvalues.exists_isLeast (by simp)
  obtain ⟨C, hC⟩ := hvalues.exists_isGreatest (by simp)
  refine ⟨c, C, hvalues_pos _ hc.1, hvalues_pos _ hC.1, fun x hx v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · have hu : (⟨x, NormedSpace.normalize v⟩ : TotalSpace F E) ∈ S :=
      ⟨hx, NormedSpace.norm_normalize hv⟩
    have hmem : b x (NormedSpace.normalize v) (NormedSpace.normalize v) ∈
        insert 1 (q '' S) := Or.inr ⟨_, hu, rfl⟩
    have heq : b x v v = ‖v‖ ^ 2 *
        b x (NormedSpace.normalize v) (NormedSpace.normalize v) := by
      conv_lhs => rw [← NormedSpace.norm_smul_normalize v]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [heq]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left (hc.2 hmem) (sq_nonneg ‖v‖)]
    · nlinarith [mul_le_mul_of_nonneg_left (hC.2 hmem) (sq_nonneg ‖v‖)]

/-- On a compact set, a continuous metric has positive uniform lower and upper bounds against
the squared norm of a continuous reference metric. No nonemptiness or positive rank is required. -/
theorem Bundle.ContinuousRiemannianMetric.exists_pos_mul_norm_sq_le_inner_self_and_le_of_isCompact
    (g : ContinuousRiemannianMetric F E) {K : Set B} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : E x,
      c * ‖v‖ ^ 2 ≤ g.inner x v v ∧ g.inner x v v ≤ C * ‖v‖ ^ 2 :=
  hK.exists_pos_mul_norm_sq_le_bilin_self_and_le g.continuous.continuousOn (fun x _ ↦ g.pos x)

end NormedReference

namespace Bundle.ContinuousRiemannianMetric

variable [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, IsTopologicalAddGroup (E x)]
  [∀ x, ContinuousConstSMul ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [FiniteDimensional ℝ F]

/-- Two continuous metrics are uniformly comparable on a compact subset, with strictly positive
constants valid for every fibre vector. No fibre norm instances are required. -/
theorem exists_pos_mul_inner_self_le_and_le_of_isCompact (g g₀ : ContinuousRiemannianMetric F E)
    {K : Set B} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : E x,
      c * g₀.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ C * g₀.inner x v v := by
  let : RiemannianBundle E := ⟨g₀.toRiemannianMetric⟩
  have h := g.exists_pos_mul_norm_sq_le_inner_self_and_le_of_isCompact hK
  have hnorm (x : B) (v : E x) : ‖v‖ ^ 2 = g₀.inner x v v :=
    norm_sq_eq_re_inner (𝕜 := ℝ) v
  simpa only [hnorm] using h

/-- On a compact base, any two continuous metrics have global positive two-sided comparison
constants. -/
theorem exists_pos_mul_inner_self_le_and_le_of_compactSpace [CompactSpace B]
    (g g₀ : ContinuousRiemannianMetric F E) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, ∀ v : E x,
      c * g₀.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ C * g₀.inner x v v := by
  simpa only [mem_univ, forall_const] using
    g.exists_pos_mul_inner_self_le_and_le_of_isCompact g₀ isCompact_univ

end Bundle.ContinuousRiemannianMetric
