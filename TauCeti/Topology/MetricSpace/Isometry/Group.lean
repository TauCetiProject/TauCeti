/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Hom.ContinuousEval
public import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# The isometry group of a compact metric space

This file puts the compact-open topology on the isometric equivalences `α ≃ᵢ β` between two
pseudo-emetric spaces. Isometries are `1`-Lipschitz, hence form an equicontinuous family, so on
them compact convergence is the same as pointwise convergence (`IsometryEquiv.isInducing_coe`):
this is the equicontinuity half of the Arzelà–Ascoli theorem. In this topology evaluation is
jointly continuous, inversion is continuous, and the isometry group `α ≃ᵢ α` is a topological
group.

For a compact metric space `α` every isometric self-map is surjective
(`Isometry.surjective_of_compactSpace`): if `x` were not in the closed range of `f`, the orbit
`x, f x, f (f x), …` would be uniformly separated. Hence the isometric equivalences of `α` are
exactly the isometric maps `α → α`, a closed subset of the compact space `α → α`, and the
isometry group of `α` is a compact Hausdorff topological group acting continuously on `α`. This is
the theorem of van Dantzig and van der Waerden; applied to the Riemannian distance of a compact
Riemannian manifold it is the compactness part of the Myers–Steenrod theorem.

## Main definitions

* `Isometry.isometryEquivOfCompactSpace`: an isometric self-map of a compact metric space, as an
  isometric equivalence.
* `IsometryEquiv.instTopologicalSpace`: the compact-open topology on `α ≃ᵢ β`.

## Main results

* `Isometry.iterate`: the iterates of an isometric self-map are isometries.
* `Isometry.surjective_of_compactSpace`: an isometric self-map of a compact metric space is
  surjective.
* `IsometryEquiv.isInducing_coe`, `IsometryEquiv.tendsto_nhds_iff`, `IsometryEquiv.continuous_iff`:
  the topology on `α ≃ᵢ β` is that of pointwise convergence.
* `IsometryEquiv.instContinuousEval`: evaluation `(α ≃ᵢ β) × α → β` is continuous.
* `IsometryEquiv.continuous_symm`, `IsometryEquiv.instIsTopologicalGroup`: the isometry group is a
  topological group.
* `IsometryEquiv.instCompactSpace`: the isometry group of a compact metric space is compact.

## References

* D. van Dantzig, B. L. van der Waerden, *Über metrisch homogene Räume*, Abh. Math. Sem. Univ.
  Hamburg 6 (1928), 367–376.
* S. B. Myers, N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of Math.
  40 (1939), 400–416.
* D. Burago, Yu. Burago, S. Ivanov, *A Course in Metric Geometry*, Graduate Studies in Mathematics
  33, AMS (2001), Section 1.6, for the surjectivity of isometric self-maps of compact spaces.
-/

public section

open Filter Function Set Topology
open scoped ENNReal

/-! ### Isometric self-maps of compact spaces -/

namespace Isometry

/-- The iterates of an isometric self-map are isometries. -/
protected theorem iterate {α : Type*} [PseudoEMetricSpace α] {f : α → α} (hf : Isometry f) :
    ∀ n : ℕ, Isometry f^[n]
  | 0 => isometry_id
  | n + 1 => (hf.iterate n).comp hf

variable {α : Type*} [EMetricSpace α] [CompactSpace α] {f : α → α}

/-- An isometric self-map of a compact (extended) metric space is surjective. -/
theorem surjective_of_compactSpace (hf : Isometry f) : Surjective f := by
  intro x
  by_contra hx
  -- A neighbourhood `ball x ε` of `x` misses the closed range of `f`.
  obtain ⟨ε, hε, hball⟩ := EMetric.isOpen_iff.1
    (isCompact_range hf.continuous).isClosed.isOpen_compl x hx
  -- So distinct points of the orbit of `x` are at least `ε` apart.
  have hsep {m n : ℕ} (hmn : m < n) : ε ≤ edist (f^[n] x) (f^[m] x) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    rw [show m + k + 1 = m + (k + 1) by omega, iterate_add_apply, (hf.iterate _).edist_eq,
      iterate_succ_apply']
    by_contra h
    exact hball (Metric.mem_eball.2 (not_le.1 h)) (mem_range_self _)
  -- But a convergent subsequence of the orbit is Cauchy.
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    isCompact_univ.tendsto_subseq (x := fun n ↦ f^[n] x) fun _ ↦ mem_univ _
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff'.1 hlim.cauchySeq ε hε
  exact (hsep (hφ N.lt_succ_self)).not_gt (hN (N + 1) N.le_succ)

/-- An isometric self-map of a compact (extended) metric space, as an isometric equivalence. -/
noncomputable def isometryEquivOfCompactSpace (hf : Isometry f) : α ≃ᵢ α where
  toEquiv := Equiv.ofBijective f ⟨hf.injective, hf.surjective_of_compactSpace⟩
  isometry_toFun := hf

@[simp]
theorem coe_isometryEquivOfCompactSpace (hf : Isometry f) :
    ⇑hf.isometryEquivOfCompactSpace = f :=
  (rfl)

end Isometry

/-! ### The compact-open topology on isometric equivalences -/

namespace IsometryEquiv

section PseudoEMetricSpace

variable {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]

/-- The compact-open topology on isometric equivalences, induced from `C(α, β)`. By
`IsometryEquiv.isInducing_coe` it is also the topology of pointwise convergence. -/
instance instTopologicalSpace : TopologicalSpace (α ≃ᵢ β) :=
  .induced (fun e ↦ (e : C(α, β))) ContinuousMap.compactOpen

/-- The topology on `α ≃ᵢ β` is induced from the compact-open topology on `C(α, β)`. -/
theorem isInducing_toContinuousMap : IsInducing fun e : α ≃ᵢ β ↦ (e : C(α, β)) :=
  ⟨rfl⟩

/-- Forgetting to `C(α, β)` is a topological embedding. -/
theorem isEmbedding_toContinuousMap : IsEmbedding fun e : α ≃ᵢ β ↦ (e : C(α, β)) :=
  ⟨isInducing_toContinuousMap, fun _ _ h ↦ ext fun x ↦ congr($h x)⟩

/-- On isometric equivalences, the compact-open topology is the topology of pointwise
convergence, since isometries form an equicontinuous family. -/
theorem isInducing_coe : IsInducing ((⇑) : (α ≃ᵢ β) → α → β) := by
  rw [← EquicontinuousOn.isInducing_uniformOnFun_iff_pi (𝔖 := {K : Set α | IsCompact K})
    (eq_univ_of_forall fun x ↦ mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
    (fun _ ↦ id) fun K _ ↦ ((LipschitzWith.uniformEquicontinuous _ 1
      fun e : α ≃ᵢ β ↦ e.isometry.lipschitzWith).equicontinuous).equicontinuousOn K]
  exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isInducing.comp
    isInducing_toContinuousMap

/-- Forgetting to `α → β` with the product topology is a topological embedding. -/
theorem isEmbedding_coe : IsEmbedding ((⇑) : (α ≃ᵢ β) → α → β) :=
  ⟨isInducing_coe, DFunLike.coe_injective⟩

/-- Isometric equivalences converge exactly when they converge pointwise. -/
theorem tendsto_nhds_iff {ι : Type*} {l : Filter ι} {e : ι → α ≃ᵢ β} {e₀ : α ≃ᵢ β} :
    Tendsto e l (𝓝 e₀) ↔ ∀ x, Tendsto (fun i ↦ e i x) l (𝓝 (e₀ x)) := by
  simp only [isInducing_coe.tendsto_nhds_iff, tendsto_pi_nhds, comp_apply]

/-- A map into `α ≃ᵢ β` is continuous exactly when each of its evaluations is. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → α ≃ᵢ β} :
    Continuous f ↔ ∀ x, Continuous fun y ↦ f y x := by
  simp only [isInducing_coe.continuous_iff, continuous_pi_iff, comp_apply]

/-- Evaluation of isometric equivalences is jointly continuous. -/
instance instContinuousEval : ContinuousEval (α ≃ᵢ β) α β where
  continuous_eval := by
    refine continuous_iff_continuousAt.2 fun p ↦ ?_
    rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
    have h₁ : Tendsto (fun q : (α ≃ᵢ β) × α ↦ edist q.2 p.2) (𝓝 p) (𝓝 0) :=
      tendsto_iff_edist_tendsto_0.1 continuousAt_snd
    have h₂ : Tendsto (fun q : (α ≃ᵢ β) × α ↦ edist (q.1 p.2) (p.1 p.2)) (𝓝 p) (𝓝 0) :=
      tendsto_iff_edist_tendsto_0.1 (tendsto_nhds_iff.1 continuousAt_fst p.2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using h₁.add h₂) (fun _ ↦ zero_le) fun q ↦ ?_
    calc edist (q.1 q.2) (p.1 p.2) ≤ edist (q.1 q.2) (q.1 p.2) + edist (q.1 p.2) (p.1 p.2) :=
          edist_triangle _ _ _
      _ = edist q.2 p.2 + edist (q.1 p.2) (p.1 p.2) := by rw [q.1.edist_eq]

/-- Inversion of isometric equivalences is continuous. -/
theorem continuous_symm : Continuous (IsometryEquiv.symm : (α ≃ᵢ β) → β ≃ᵢ α) := by
  refine continuous_iff_continuousAt.2 fun e ↦ tendsto_nhds_iff.2 fun y ↦ ?_
  rw [tendsto_iff_edist_tendsto_0]
  refine (tendsto_iff_edist_tendsto_0.1 (tendsto_nhds_iff.1 tendsto_id (e.symm y))).congr
    fun f ↦ ?_
  rw [id, e.apply_symm_apply, ← f.edist_eq, f.apply_symm_apply, edist_comm]

/-- Isometric equivalences into a Hausdorff space form a Hausdorff space. -/
instance instT2Space [T2Space β] : T2Space (α ≃ᵢ β) :=
  isEmbedding_coe.t2Space

/-- The isometry group of a pseudo-emetric space is a topological group for the compact-open
topology. -/
instance instIsTopologicalGroup : IsTopologicalGroup (α ≃ᵢ α) where
  continuous_mul := continuous_iff.2 fun _ ↦ continuous_fst.eval (continuous_snd.eval
    continuous_const)
  continuous_inv := continuous_symm

end PseudoEMetricSpace

/-! ### Compactness -/

section Compact

variable {α : Type*} [EMetricSpace α] [CompactSpace α]

/-- The isometric equivalences of a compact metric space are its isometric self-maps. -/
theorem range_coe_of_compactSpace : range ((⇑) : (α ≃ᵢ α) → α → α) = {f | Isometry f} :=
  Subset.antisymm (range_subset_iff.2 fun e ↦ e.isometry) fun _ hf ↦
    ⟨hf.isometryEquivOfCompactSpace, hf.coe_isometryEquivOfCompactSpace⟩

/-- **van Dantzig–van der Waerden.** The isometry group of a compact metric space is compact. -/
instance instCompactSpace : CompactSpace (α ≃ᵢ α) := by
  refine ⟨isInducing_coe.isCompact_iff.2 ?_⟩
  rw [image_univ, range_coe_of_compactSpace]
  refine IsClosed.isCompact ?_
  simp only [Isometry, ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_eq
    ((continuous_apply x).edist (continuous_apply y)) continuous_const

end Compact

end IsometryEquiv
