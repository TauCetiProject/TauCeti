/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import TauCeti.GroupTheory.Amenable.Basic

/-!
# The weak-* compact space of means

Every mean `m` on `TauCeti.UCB G` is a continuous linear functional of norm one, so the means sit
inside the closed unit ball of the dual of `UCB G`. Positivity and normalization are conditions on
finitely many values at a time, hence closed for the weak-* topology, and by the Banach–Alaoglu
theorem the means form a weak-* compact set. We give `TauCeti.Mean G` the weak-* topology, induced
from `WeakDual ℝ (UCB G)`, so that it becomes a compact Hausdorff space in which a net of means
converges exactly when it converges at every function.

Each invariance equation `m (L_g f) = m f` also defines a closed set of means, so the left-invariant
means form a compact set. Compactness yields the two standard criteria for amenability:

* a finite-intersection criterion: `G` is amenable as soon as every finite family of invariance
  equations is satisfied by some mean;
* a cluster-point criterion: if means `m_i` are approximately left invariant along a nontrivial
  filter, in the sense that `m_i (L_g f) - m_i f → 0` for all `g` and `f`, then every weak-* cluster
  point of `m_i` is a left-invariant mean, and such a cluster point exists.

These criteria are how amenability is proved for directed unions of subgroups and for groups with
Følner sets.

## Main definitions

* `TauCeti.Mean.toWeakDual`: a mean as an element of the weak-* dual of `UCB G`.
* `TauCeti.Mean.instTopologicalSpace`: the weak-* topology on means.

## Main results

* `TauCeti.Mean.mem_range_toWeakDual_iff`: the weak-* functionals coming from means are the positive
  ones taking the value `1` at `1`.
* `TauCeti.Mean.isCompact_range_toWeakDual`: the means form a weak-* compact subset of the dual
  unit ball; hence `Mean G` is a compact Hausdorff space.
* `TauCeti.Mean.tendsto_iff_forall_apply_tendsto`: weak-* convergence of means is convergence at
  every function.
* `TauCeti.Mean.isCompact_setOf_isLeftInvariant`: the left-invariant means form a compact set.
* `TauCeti.amenable_iff_forall_finset_exists`: the finite-intersection criterion for amenability.
* `TauCeti.Mean.IsLeftInvariant.of_mapClusterPt`, `TauCeti.Amenable.of_tendsto`: the cluster-point
  criterion for amenability.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1 and the proof of
  Proposition G.2.2.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace Mean

/-! ### Means in the weak-* dual -/

/-- A mean on `UCB G`, as an element of the weak-* dual of `UCB G`. -/
def toWeakDual (m : Mean G) : WeakDual ℝ (UCB G) :=
  StrongDual.toWeakDual m.toContinuousLinearMap

@[simp]
theorem toWeakDual_apply (m : Mean G) (f : UCB G) : m.toWeakDual f = m f := by
  simp [toWeakDual, StrongDual.toWeakDual_apply]

@[simp]
theorem toStrongDual_toWeakDual (m : Mean G) :
    WeakDual.toStrongDual m.toWeakDual = m.toContinuousLinearMap :=
  StrongDual.toStrongDual_toWeakDual _

theorem toWeakDual_injective : Function.Injective (toWeakDual : Mean G → WeakDual ℝ (UCB G)) :=
  StrongDual.toWeakDual.injective.comp toContinuousLinearMap_injective

/-- An element of the weak-* dual of `UCB G` comes from a mean exactly when it is nonnegative on
nonnegative functions and takes the value `1` at `1`. -/
theorem mem_range_toWeakDual_iff {φ : WeakDual ℝ (UCB G)} :
    φ ∈ Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G)) ↔
      (∀ f, 0 ≤ f → 0 ≤ φ f) ∧ φ 1 = 1 := by
  have : φ ∈ Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G)) ↔
      WeakDual.toStrongDual φ ∈ Set.range (toContinuousLinearMap : Mean G → UCB G →L[ℝ] ℝ) := by
    refine exists_congr fun m => ?_
    rw [← toStrongDual_toWeakDual, WeakDual.toStrongDual_inj]
  rw [this, mem_range_toContinuousLinearMap_iff]
  simp [WeakDual.toStrongDual_apply]

/-- The means lie in the closed unit ball of the dual of `UCB G`. -/
theorem range_toWeakDual_subset_closedBall :
    Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G)) ⊆
      WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1 := by
  rintro _ ⟨m, rfl⟩
  simp

/-- The means form a weak-* closed set: positivity and normalization are closed conditions. -/
theorem isClosed_range_toWeakDual :
    IsClosed (Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G))) := by
  have h : Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G)) =
      (⋂ (f : UCB G) (_ : 0 ≤ f), {φ | 0 ≤ φ f}) ∩ {φ | φ 1 = 1} := by
    ext φ
    rw [mem_range_toWeakDual_iff]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  exact (isClosed_iInter fun f => isClosed_iInter fun _ =>
    isClosed_le continuous_const (WeakDual.eval_continuous (𝕜 := ℝ) f)).inter
      (isClosed_eq (WeakDual.eval_continuous (𝕜 := ℝ) (1 : UCB G)) continuous_const)

/-- The means form a weak-* compact set, by the Banach–Alaoglu theorem. -/
theorem isCompact_range_toWeakDual :
    IsCompact (Set.range (toWeakDual : Mean G → WeakDual ℝ (UCB G))) :=
  (WeakDual.isCompact_closedBall 0 1).of_isClosed_subset isClosed_range_toWeakDual
    range_toWeakDual_subset_closedBall

/-! ### The weak-* topology on means -/

/-- The weak-* topology on means, induced from the weak-* dual of `UCB G`. A net of means
converges exactly when it converges at every function, see `tendsto_iff_forall_apply_tendsto`. -/
instance instTopologicalSpace : TopologicalSpace (Mean G) :=
  .induced toWeakDual inferInstance

theorem isEmbedding_toWeakDual : IsEmbedding (toWeakDual : Mean G → WeakDual ℝ (UCB G)) :=
  ⟨⟨rfl⟩, toWeakDual_injective⟩

@[fun_prop]
theorem continuous_toWeakDual : Continuous (toWeakDual : Mean G → WeakDual ℝ (UCB G)) :=
  isEmbedding_toWeakDual.continuous

/-- Evaluation of means at a fixed function is weak-* continuous. -/
instance : ContinuousEvalConst (Mean G) (UCB G) ℝ where
  continuous_eval_const f := by
    simpa only [Function.comp_def, toWeakDual_apply] using
      (WeakDual.eval_continuous f).comp continuous_toWeakDual

instance : T2Space (Mean G) :=
  isEmbedding_toWeakDual.t2Space

/-- The space of means is weak-* compact. -/
instance : CompactSpace (Mean G) :=
  isCompact_univ_iff.1 <| isEmbedding_toWeakDual.isCompact_iff.2 <| by
    simpa [Set.image_univ] using isCompact_range_toWeakDual

/-- A family of means converges weak-* exactly when it converges at every function. -/
theorem tendsto_iff_forall_apply_tendsto {ι : Type*} {l : Filter ι} {ms : ι → Mean G}
    {m : Mean G} : Tendsto ms l (𝓝 m) ↔ ∀ f, Tendsto (fun i => ms i f) l (𝓝 (m f)) := by
  rw [isEmbedding_toWeakDual.isInducing.tendsto_nhds_iff,
    tendsto_iff_forall_eval_tendsto_topDualPairing]
  -- `topDualPairing ℝ (UCB G) φ f` is `φ f` by definition of the canonical pairing.
  exact forall_congr' fun f => by simp only [← toWeakDual_apply]; rfl

/-! ### Invariant means -/

/-- Each invariance equation `m (L_g f) = m f` defines a weak-* closed set of means. -/
theorem isClosed_setOf_apply_leftTranslation_eq (g : G) (f : UCB G) :
    IsClosed {m : Mean G | m (UCB.leftTranslation g f) = m f} :=
  isClosed_eq (continuous_eval_const _) (continuous_eval_const _)

/-- The left-invariant means form a weak-* closed set. -/
theorem isClosed_setOf_isLeftInvariant : IsClosed {m : Mean G | m.IsLeftInvariant} := by
  simp only [isLeftInvariant_iff, Set.ofPred_forall]
  exact isClosed_iInter fun g => isClosed_iInter fun f =>
    isClosed_setOf_apply_leftTranslation_eq g f

/-- The left-invariant means form a weak-* compact set. -/
theorem isCompact_setOf_isLeftInvariant : IsCompact {m : Mean G | m.IsLeftInvariant} :=
  isClosed_setOf_isLeftInvariant.isCompact

/-- A weak-* cluster point of means `ms i` which are approximately left invariant along `l`, in the
sense that `ms i (L_g f) - ms i f → 0` for every `g` and `f`, is a left-invariant mean. -/
theorem IsLeftInvariant.of_mapClusterPt {ι : Type*} {l : Filter ι} {ms : ι → Mean G} {m : Mean G}
    (hm : MapClusterPt m l ms)
    (h : ∀ g f, Tendsto (fun i => ms i (UCB.leftTranslation g f) - ms i f) l (𝓝 0)) :
    m.IsLeftInvariant := by
  refine isLeftInvariant_iff.2 fun g f => ?_
  have hc : Continuous fun n : Mean G => n (UCB.leftTranslation g f) - n f :=
    (continuous_eval_const _).sub (continuous_eval_const _)
  have hcl := MapClusterPt.continuousAt_comp hc.continuousAt hm
  exact sub_eq_zero.1 (eq_of_nhds_neBot (ClusterPt.mono hcl (h g f)).neBot)

/-- Means which are approximately left invariant along a nontrivial filter have a weak-* cluster
point, and every such cluster point is a left-invariant mean. -/
theorem exists_mapClusterPt_isLeftInvariant {ι : Type*} {l : Filter ι} [l.NeBot]
    {ms : ι → Mean G}
    (h : ∀ g f, Tendsto (fun i => ms i (UCB.leftTranslation g f) - ms i f) l (𝓝 0)) :
    ∃ m : Mean G, MapClusterPt m l ms ∧ m.IsLeftInvariant :=
  have ⟨m, _, hm⟩ := isCompact_univ.exists_mapClusterPt (f := l) (u := ms) (by simp)
  ⟨m, hm, .of_mapClusterPt hm h⟩

end Mean

/-- Cluster-point criterion: a topological group is amenable when it carries means `ms i` which
are approximately left invariant along a nontrivial filter, that is, `ms i (L_g f) - ms i f → 0`
for every `g` and `f`. -/
theorem Amenable.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {ms : ι → Mean G}
    (h : ∀ g f, Tendsto (fun i => ms i (UCB.leftTranslation g f) - ms i f) l (𝓝 0)) :
    Amenable G :=
  have ⟨m, _, hm⟩ := Mean.exists_mapClusterPt_isLeftInvariant h
  ⟨⟨m, hm⟩⟩

/-- Finite-intersection criterion: a topological group is amenable exactly when every finite
family of invariance equations `m (L_g f) = m f` is satisfied by some mean. -/
theorem amenable_iff_forall_finset_exists :
    Amenable G ↔ ∀ s : Finset (G × UCB G),
      ∃ m : Mean G, ∀ p ∈ s, m (UCB.leftTranslation p.1 p.2) = m p.2 := by
  refine ⟨fun ⟨m, hm⟩ s => ⟨m, fun p _ => hm.apply_leftTranslation p.1 p.2⟩, fun h => ?_⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.inter_iInter_nonempty
    (fun p : G × UCB G => {m : Mean G | m (UCB.leftTranslation p.1 p.2) = m p.2})
    (fun p => Mean.isClosed_setOf_apply_leftTranslation_eq p.1 p.2)
    (fun s => have ⟨m, hm⟩ := h s; ⟨m, trivial, Set.mem_iInter₂.2 hm⟩)
  exact ⟨⟨m, Mean.isLeftInvariant_iff.2 fun g f => Set.mem_iInter.1 hm (g, f)⟩⟩

end TauCeti
