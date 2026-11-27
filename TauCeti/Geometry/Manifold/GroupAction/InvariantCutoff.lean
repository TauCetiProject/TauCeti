/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
public import Mathlib.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic
import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Invariant smooth cutoffs for compact group actions

Let a compact group `G`, itself a smooth manifold, act smoothly on a boundaryless Hausdorff manifold
`M` modelled on a finite-dimensional space. If `K` is a compact subset of an open set `W` and `K` is
invariant under the action, there is a smooth function `σ : M → [0, 1]`, equal to `1` near `K`,
with compact support in `W`, which is moreover invariant: `σ (a • x) = σ x`
(`IsCompact.exists_contMDiff_one_nhds_tsupport_subset_of_smul_mem`).

It is the average `σ x = ∫ ρ (a • x) da` over the normalized Haar measure of an ordinary cutoff
`ρ` (`IsCompact.exists_contMDiff_one_nhds_tsupport_subset`) supported in the largest invariant open
subset of `W`. Averaging keeps the value `1` on the points whose whole orbit lies where `ρ = 1`,
which form an open neighbourhood of `K`, and the support of the average lies in the compact set
`G • tsupport ρ`.

Invariant cutoffs localize equivariant constructions: a vector field built from invariant data
and cut off by an invariant function is again invariant, so its flow commutes with the action.
-/

public section

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [ChartedSpace HG G] [IsManifold IG ∞ G]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M]

variable (I IG) in
include IG in
/-- **An invariant smooth cutoff around an invariant compact set.** If a compact group acts
smoothly on a boundaryless Hausdorff manifold modelled on a finite-dimensional space, and `K` is
an invariant compact subset of an open set `W`, there is a smooth invariant function
`σ : M → [0, 1]` equal to `1` on a neighbourhood of `K` whose topological support is a compact
subset of `W`. -/
theorem IsCompact.exists_contMDiff_one_nhds_tsupport_subset_of_smul_mem {K W : Set M}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) (hKG : ∀ (a : G), ∀ x ∈ K, a • x ∈ K) :
    ∃ σ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ σ ∧ (∀ᶠ x in 𝓝ˢ K, σ x = 1) ∧ HasCompactSupport σ ∧
      tsupport σ ⊆ W ∧ (∀ x, σ x ∈ Icc 0 1) ∧ ∀ (a : G) x, σ (a • x) = σ x := by
  borelize G
  have := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
  -- An ordinary cutoff supported in the largest invariant open subset of `W`.
  obtain ⟨ρ, hρ, hρ1, hρc, hρW, hρI⟩ := hK.exists_contMDiff_one_nhds_tsupport_subset I
    (TauCeti.isOpen_setOf_forall_smul_mem (G := G) hW) fun x hx a ↦ hKW (hKG a x hx)
  set μ := TauCeti.haarProb G
  have hint (x : M) : Integrable (fun a : G ↦ ρ (a • x)) μ :=
    integrableOn_univ.1 ((hρ.continuous.comp (continuous_id.smul continuous_const)).continuousOn
      |>.integrableOn_compact isCompact_univ)
  -- The average vanishes off the compact set `G • tsupport ρ`, which lies in `W`.
  set S := (fun p : G × M ↦ p.1 • p.2) '' (univ ×ˢ tsupport ρ)
  have hS : IsCompact S := (isCompact_univ.prod hρc).image continuous_smul
  have hsupp : (Function.support fun x ↦ ∫ a, ρ (a • x) ∂μ) ⊆ S := by
    intro x hx
    by_contra hxS
    refine hx (integral_eq_zero_of_ae (Eventually.of_forall fun a ↦ ?_))
    by_contra ha
    exact hxS ⟨(a⁻¹, a • x), ⟨mem_univ _, subset_tsupport _ ha⟩, inv_smul_smul a x⟩
  have htsupp : tsupport (fun x ↦ ∫ a, ρ (a • x) ∂μ) ⊆ S :=
    closure_minimal hsupp hS.isClosed
  refine ⟨fun x ↦ ∫ a, ρ (a • x) ∂μ, ?_, ?_, hS.of_isClosed_subset (isClosed_tsupport _) htsupp,
    htsupp.trans ?_, fun x ↦ ⟨integral_nonneg fun a ↦ (hρI _).1, ?_⟩, fun b x ↦ ?_⟩
  · exact ContMDiff.parametric_integral (μ := μ) (n := ⊤)
      (hρ.comp ((contMDiff_smul (I := IG) (I' := I)).comp
        (contMDiff_snd.prodMk contMDiff_fst)))
  · -- On the points whose orbit lies where `ρ = 1`, an open neighbourhood of `K`, the average is
    -- `1`.
    obtain ⟨U, ⟨hU, hKU⟩, hUρ⟩ := (hasBasis_nhdsSet K).mem_iff.1 hρ1
    refine mem_of_superset ((TauCeti.isOpen_setOf_forall_smul_mem (G := G) hU).mem_nhdsSet.2
      fun x hx a ↦ hKU (hKG a x hx)) fun x hx ↦ ?_
    simp [show ∀ a : G, ρ (a • x) = 1 from fun a ↦ hUρ (hx a)]
  · rintro _ ⟨⟨a, y⟩, ⟨-, hy⟩, rfl⟩
    exact (hρW hy : ∀ b : G, b • y ∈ W) a
  · calc ∫ a, ρ (a • x) ∂μ ≤ ∫ _ : G, (1 : ℝ) ∂μ :=
          integral_mono (hint x) (integrable_const 1) fun a ↦ (hρI _).2
      _ = 1 := by simp
  · -- Right invariance of the Haar measure.
    simpa only [smul_smul] using integral_mul_right_eq_self (μ := μ) (fun a ↦ ρ (a • x)) b
