/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic
import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Invariant cutoff functions for compact group actions

Let a compact group `G`, itself a manifold, act smoothly on a boundaryless Hausdorff manifold
`M` modelled on a finite-dimensional space. Every compact invariant set `K` inside an open set `W`
has an invariant smooth cutoff: a smooth function `σ` with `σ (g • x) = σ x`, equal to `1` near
`K`, with compact topological support inside `W`
(`IsCompact.exists_contMDiff_smul_eq_one_nhds_tsupport_subset`). It is the average
`σ x = ∫ ρ (g • x) dg` over the normalized Haar measure of a cutoff `ρ` of `K` supported in the
open set of points whose whole orbit lies in `W` (`TauCeti.isOpen_setOf_forall_smul_mem`), which
contains `K` because `K` is invariant. Such cutoffs localize constructions built from invariant
data, for instance Moser isotopies, without destroying their equivariance.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI, for averaging over compact transformation groups.
-/

public section

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology Manifold ContDiff

namespace TauCeti

variable {E E' H H' G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [Group G] [TopologicalSpace G] [MulAction G M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℝ E' H') [ChartedSpace H' G] [IsManifold J ∞ G]
  [ContMDiffSMul J I ∞ G M] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]

variable (I) in
include J in
/-- **Invariant cutoffs for compact group actions.** Let a compact group which is a manifold act
smoothly on a boundaryless Hausdorff manifold modelled on a finite-dimensional space. If `K` is a
compact invariant subset of an open set `W`, there is a smooth invariant function `σ`, equal to `1`
on a neighbourhood of `K`, whose topological support is a compact subset of `W`. -/
theorem _root_.IsCompact.exists_contMDiff_smul_eq_one_nhds_tsupport_subset {K W : Set M}
    (hK : IsCompact K) (hKG : ∀ g : G, ∀ x ∈ K, g • x ∈ K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ σ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ σ ∧ (∀ (g : G) x, σ (g • x) = σ x) ∧
      (∀ᶠ x in 𝓝ˢ K, σ x = 1) ∧ HasCompactSupport σ ∧ tsupport σ ⊆ W := by
  have := ContMDiffSMul.continuousSMul (I := J) (I' := I) (G := G) (M := M) ∞
  borelize G
  -- A cutoff `ρ` of `K` supported in the open set `N` of points whose orbit lies in `W`.
  set N := {x : M | ∀ g : G, g • x ∈ W}
  have hKN : K ⊆ N := fun x hx g ↦ hKW (hKG g x hx)
  obtain ⟨ρ, hρ, hρ1, hρc, hρN, -⟩ :=
    hK.exists_contMDiff_one_nhds_tsupport_subset I (isOpen_setOf_forall_smul_mem hW) hKN
  obtain ⟨U, hU, hKU, hUρ⟩ := mem_nhdsSet_iff_exists.1 hρ1
  -- Its average over the normalized Haar measure.
  set σ : M → ℝ := fun x ↦ ∫ g, ρ (g • x) ∂haarProb G
  have hact : ContMDiff (I.prod J) I ∞ (fun p : M × G ↦ p.2 • p.1) :=
    contMDiff_smul.comp (contMDiff_snd.prodMk contMDiff_fst)
  refine ⟨σ, (hρ.comp hact).parametric_integral (f := fun x g ↦ ρ (g • x)), fun b x ↦ ?_, ?_,
    ?_⟩
  · -- Right invariance of the Haar measure.
    simp only [σ, smul_smul]
    exact integral_mul_right_eq_self (μ := haarProb G) (fun g ↦ ρ (g • x)) b
  · -- On the open set of points whose orbit lies in `U`, every value averaged is `1`.
    refine mem_nhdsSet_iff_exists.2 ⟨{x | ∀ g : G, g • x ∈ U}, isOpen_setOf_forall_smul_mem hU,
      fun x hx g ↦ hKU (hKG g x hx), fun x hx ↦ ?_⟩
    have hx' (g : G) : ρ (g • x) = 1 := hUρ (hx g)
    simp [σ, hx']
  · -- The support of the average lies in the compact set `G • tsupport ρ`, inside `W`.
    set S := (fun p : G × M ↦ p.1 • p.2) '' (univ ×ˢ tsupport ρ)
    have hS : IsCompact S := (isCompact_univ.prod hρc.isCompact).image continuous_smul
    have hσS : tsupport σ ⊆ S := by
      refine closure_minimal (fun x hx ↦ ?_) hS.isClosed
      by_contra hxS
      refine hx (integral_eq_zero_of_ae (Eventually.of_forall fun g ↦ ?_))
      refine image_eq_zero_of_notMem_tsupport fun hg ↦ hxS ⟨(g⁻¹, g • x), ⟨mem_univ _, hg⟩, ?_⟩
      simp
    refine ⟨.of_isClosed_subset hS (isClosed_tsupport _) hσS, hσS.trans ?_⟩
    rintro _ ⟨⟨g, y⟩, ⟨-, hy⟩, rfl⟩
    exact hρN hy g

end TauCeti
