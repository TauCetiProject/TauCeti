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

A continuous metric on a real vector bundle is uniformly comparable to a fixed continuous
reference metric over every compact subset of the base, with no finite-rank assumption. The
comparison is on all vectors and uses strictly positive constants. This lets estimates made
using different metrics be transferred without changing the topology of the fibres.

The metric comparison proof bounds each metric locally against the squared coordinate norm,
then combines these bounds by compact induction. For a positive bilinear field on a finite-rank
bundle, a separate result takes extrema on the reference unit sphere bundle and uses quadratic
homogeneity. Adjoining the value one handles empty compact sets and rank-zero bundles.
-/

public section

open Bundle Set
open scoped Topology

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]

section NormedReference

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [FiniteDimensional ℝ F] [IsContinuousRiemannianBundle F E]

/-- A bilinear field continuous and positive on a compact set has positive uniform two-sided
bounds against the squared fibre norm of a continuous Riemannian bundle. Neither symmetry nor
positivity outside the compact set is required, and the compact set and unit sphere fibres may
be empty. -/
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
  have hq : ContinuousOn q S := hb.bilin_bundle_self.mono fun _ hz ↦ hz.1
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

end NormedReference

namespace Bundle.ContinuousRiemannianMetric

variable [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- Local comparison with the squared coordinate norm. The metric supplies a compatible fibre
norm, so Mathlib's local bounds on a trivialization and its inverse apply in arbitrary rank. -/
private theorem eventually_inner_self_bounds (g : ContinuousRiemannianMetric F E) (x : B) :
    ∃ A > 0, ∃ D > 0, ∀ᶠ y in 𝓝 x, ∀ v : E y,
      ‖(trivializationAt F E x).continuousLinearMapAt ℝ y v‖ ^ 2 ≤ A * g.inner y v v ∧
      g.inner y v v ≤ D * ‖(trivializationAt F E x).continuousLinearMapAt ℝ y v‖ ^ 2 := by
  have (y : B) : IsTopologicalAddGroup (E y) :=
    (VectorBundle.continuousLinearEquivAt ℝ F E y).toHomeomorph.isInducing.isTopologicalAddGroup
      (VectorBundle.continuousLinearEquivAt ℝ F E y).toLinearEquiv.toAddEquiv
  have (y : B) : ContinuousSMul ℝ (E y) :=
    (VectorBundle.continuousLinearEquivAt ℝ F E y).toHomeomorph.isInducing.continuousSMul
      continuous_id (fun {c v} ↦ map_smul (VectorBundle.continuousLinearEquivAt ℝ F E y) c v)
  let : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA, hA'⟩ := eventually_norm_trivializationAt_lt F E x
  obtain ⟨D, hD, hD'⟩ := eventually_norm_symmL_trivializationAt_lt F E x
  refine ⟨A ^ 2, sq_pos_of_pos hA, D ^ 2, sq_pos_of_pos hD, ?_⟩
  filter_upwards [hA', hD', (trivializationAt F E x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hyA hyD hy
  intro v
  have hnorm : ‖v‖ ^ 2 = g.inner y v v := norm_sq_eq_re_inner (𝕜 := ℝ) v
  constructor
  · calc
      _ ≤ (A * ‖v‖) ^ 2 := by
        gcongr
        exact ContinuousLinearMap.le_of_opNorm_le _ hyA.le v
      _ = _ := by rw [mul_pow, hnorm]
  · have hv : ‖v‖ ≤ D * ‖(trivializationAt F E x).continuousLinearMapAt ℝ y v‖ := by
      calc
        _ = ‖(trivializationAt F E x).symmL ℝ y
            ((trivializationAt F E x).continuousLinearMapAt ℝ y v)‖ := by
          rw [Trivialization.symmL_continuousLinearMapAt _ hy]
        _ ≤ _ := ContinuousLinearMap.le_of_opNorm_le _ hyD.le _
    rw [← hnorm, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hv 2

/-- Two continuous metrics are uniformly comparable on a compact subset, with strictly positive
constants valid for every fibre vector. No fibre norm instances are required. -/
theorem exists_pos_mul_inner_self_le_and_le_of_isCompact (g g₀ : ContinuousRiemannianMetric F E)
    {K : Set B} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : E x,
      c * g₀.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ C * g₀.inner x v v := by
  have hnonneg (h : ContinuousRiemannianMetric F E) (x : B) (v : E x) :
      0 ≤ h.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (h.pos x v hv).le
  refine hK.induction_on ⟨1, 1, zero_lt_one, zero_lt_one, by simp⟩
    (fun s t hst ⟨c, C, hc, hC, h⟩ ↦ ⟨c, C, hc, hC, fun x hx ↦ h x (hst hx)⟩)
    (fun s t ⟨c, C, hc, hC, h⟩ ⟨c', C', hc', _, h'⟩ ↦ ?_) (fun x _ ↦ ?_)
  · refine ⟨min c c', max C C', lt_min hc hc', lt_max_of_lt_left hC, fun x hx v ↦ ?_⟩
    rcases hx with hx | hx
    · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (hnonneg g₀ x v)).trans
        (h x hx v).1, (h x hx v).2.trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnonneg g₀ x v))⟩
    · exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (hnonneg g₀ x v)).trans
        (h' x hx v).1, (h' x hx v).2.trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (hnonneg g₀ x v))⟩
  · obtain ⟨A, hA, D, hD, hg⟩ := g.eventually_inner_self_bounds x
    obtain ⟨A₀, hA₀, D₀, hD₀, hg₀⟩ := g₀.eventually_inner_self_bounds x
    refine ⟨{y | ∀ v : E y, (D₀ * A)⁻¹ * g₀.inner y v v ≤ g.inner y v v ∧
      g.inner y v v ≤ (D * A₀) * g₀.inner y v v}, ?_,
      (D₀ * A)⁻¹, D * A₀, by positivity, by positivity, fun _ hy ↦ hy⟩
    apply mem_nhdsWithin_of_mem_nhds
    filter_upwards [hg, hg₀] with y hy hy₀
    intro v
    constructor
    · rw [inv_mul_le_iff₀ (mul_pos hD₀ hA)]
      exact (hy₀ v).2.trans (by nlinarith [(hy v).1])
    · exact (hy v).2.trans (by nlinarith [(hy₀ v).1])

/-- On a compact base, any two continuous metrics have global positive two-sided comparison
constants. -/
theorem exists_pos_mul_inner_self_le_and_le_of_compactSpace [CompactSpace B]
    (g g₀ : ContinuousRiemannianMetric F E) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, ∀ v : E x,
      c * g₀.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ C * g₀.inner x v v := by
  simpa only [mem_univ, forall_const] using
    g.exists_pos_mul_inner_self_le_and_le_of_isCompact g₀ isCompact_univ

end Bundle.ContinuousRiemannianMetric

section NormedReference

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

/-- On a compact set, a continuous metric has positive uniform lower and upper bounds against
the squared fibre norm of a continuous Riemannian bundle, with no finite-rank assumption. -/
theorem Bundle.ContinuousRiemannianMetric.exists_pos_mul_norm_sq_le_inner_self_and_le_of_isCompact
    (g : ContinuousRiemannianMetric F E) {K : Set B} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : E x,
      c * ‖v‖ ^ 2 ≤ g.inner x v v ∧ g.inner x v v ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨b, hb, hinner⟩ := IsContinuousRiemannianBundle.exists_continuous (F := F) (E := E)
  let g₀ : ContinuousRiemannianMetric F E :=
    { inner := b
      symm := fun x v w ↦ by simpa only [← hinner] using (real_inner_comm v w).symm
      pos := fun x v hv ↦ by simpa only [← hinner] using (real_inner_self_pos.mpr hv)
      isVonNBounded := fun x ↦ (NormedSpace.isVonNBounded_iff' ℝ).mpr ⟨1, fun v hv ↦ by
        have : ‖v‖ ^ 2 < 1 := by
          simpa only [mem_ofPred_eq, ← hinner, real_inner_self_eq_norm_sq] using hv
        nlinarith [norm_nonneg v]⟩
      continuous := hb }
  simpa only [g₀, ← hinner, real_inner_self_eq_norm_sq] using
    g.exists_pos_mul_inner_self_le_and_le_of_isCompact g₀ hK

end NormedReference
