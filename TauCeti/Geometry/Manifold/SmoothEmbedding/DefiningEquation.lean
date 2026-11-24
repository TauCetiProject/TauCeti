/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocallyFlat.Smooth
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic

/-!
# Local transverse defining equations of smooth embeddings

Around any point `x₀ : M` of a `C^n` (`n ≠ 0`) smooth embedding `f : M → N` between boundaryless
manifolds over a complete nontrivially normed field `𝕜` with finite-dimensional ambient model `V`
and codimension model `P` (`finrank 𝕜 P = finrank 𝕜 V - finrank 𝕜 E`), projecting a `C^n` ambient
slice chart onto its transverse factor yields an open neighbourhood `S ⊆ N` of `f x₀` and a `C^n`
map `g : N → P` that is regular at every point of `S` and cuts out `Set.range f` on `S`
(`TauCeti.SmoothEmbedding.exists_contMDiffOn_eq_zero`).

When `P` is nontrivial, the image `Set.range f` is closed in `N` if and only if every ambient point
`y₀ : N` admits such a local defining equation regular along `S ∩ Set.range f`
(`TauCeti.SmoothEmbedding.isClosed_range_iff_forall_exists_contMDiffOn_eq_zero`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 5 (Theorem 5.8 and
  Proposition 5.16).
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.1.
-/

public noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P H G M N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] [NormedAddCommGroup P] [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [I.Boundaryless] [J.Boundaryless] {n : ℕ∞ω} [IsManifold J n N]

/-- **Local defining equations of a smooth embedding.** Around every `x₀ : M`, there is an open
ambient set `S ⊆ N` containing `f x₀` and a `C^n` map `g : N → P` cutting out `Set.range f` on `S`
(`y ∈ Set.range f ↔ g y = 0`) and regular at every `y ∈ S`. -/
theorem exists_contMDiffOn_eq_zero (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    ∃ S : Set N, IsOpen S ∧ f x₀ ∈ S ∧ ∃ g : N → P, ContMDiffOn J 𝓘(𝕜, P) n g S ∧
      (∀ y ∈ S, y ∈ range f ↔ g y = 0) ∧ ∀ y ∈ S, IsRegularPoint J 𝓘(𝕜, P) g y := by
  have : IsManifold J 1 N := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn)
  let F := f.isImmersion.complement
  let h : Manifold.IsImmersionAtOfComplement F I J n f x₀ :=
    f.isImmersion.isImmersionOfComplement_complement x₀
  obtain ⟨Φ, hfx₀, hslice, hΦ, hΦsymm⟩ :=
    exists_contMDiffOn_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement f.isEmbedding h
  have : FiniteDimensional 𝕜 (E × F) := h.equiv.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional 𝕜 E :=
    Module.Finite.of_surjective (LinearMap.fst 𝕜 E F) Prod.fst_surjective
  have : FiniteDimensional 𝕜 F :=
    Module.Finite.of_surjective (LinearMap.snd 𝕜 E F) Prod.snd_surjective
  have hFdim : Module.finrank 𝕜 F = Module.finrank 𝕜 P := by
    have heq := h.equiv.toLinearEquiv.finrank_eq
    have hadd := f.finrank_add_eq_of_eq_sub hn hdim x₀
    rw [Module.finrank_prod] at heq; omega
  let c : F ≃L[𝕜] P := ContinuousLinearEquiv.ofFinrankEq hFdim
  let π₂ : E × F →L[𝕜] P := c.toContinuousLinearMap.comp (ContinuousLinearMap.snd 𝕜 E F)
  refine ⟨Φ.source, Φ.open_source, hfx₀, π₂ ∘ Φ, π₂.contDiff.contMDiff.comp_contMDiffOn hΦ,
    fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · rw [(isSliceChart_iff.1 hslice) y hy, I.range_eq_univ, mem_prod, and_iff_right (mem_univ _),
      mem_singleton_iff]
    exact (c.map_eq_zero_iff (x := (Φ y).snd)).symm
  · have hloc := (PartialDiffeomorph.mk Φ.toPartialEquiv Φ.open_source Φ.open_target hΦ
      hΦsymm).isLocalDiffeomorphAt J 𝓘(𝕜, E × F) n hy
    have hΦAt := (hΦ.contMDiffAt (Φ.open_source.mem_nhds hy)).mdifferentiableAt hn
    rw [isRegularPoint_iff, (π₂.hasMFDerivAt.comp y hΦAt.hasMFDerivAt).mfderiv,
      ContinuousLinearMap.coe_comp]
    exact (c.surjective.comp Prod.snd_surjective).comp
      (hloc.mfderivToContinuousLinearEquiv hn).surjective

/-- **Characterization of closed embedded submanifolds by local defining equations.** When the
codimension model `P` is nontrivial, the image of a `C^n` (`n ≠ 0`) smooth embedding `f : M → N`
between boundaryless manifolds is closed in `N` if and only if every ambient point `y₀ : N` admits
an open neighbourhood `S` on which `Set.range f` is cut out by a `C^n` map `g : N → P` that is
regular along `S ∩ Set.range f`. -/
theorem isClosed_range_iff_forall_exists_contMDiffOn_eq_zero [Nontrivial P]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    IsClosed (range f) ↔
      ∀ y₀ : N, ∃ S : Set N, IsOpen S ∧ y₀ ∈ S ∧ ∃ g : N → P, ContMDiffOn J 𝓘(𝕜, P) n g S ∧
        (∀ y ∈ S, y ∈ range f ↔ g y = 0) ∧ ∀ y ∈ S ∩ range f, IsRegularPoint J 𝓘(𝕜, P) g y := by
  refine ⟨fun hclosed y₀ ↦ ?_, fun h ↦ ?_⟩
  · by_cases hy₀ : y₀ ∈ range f
    · obtain ⟨x₀, rfl⟩ := hy₀
      obtain ⟨S, hS, hx₀, g, hg, hzero, hreg⟩ := f.exists_contMDiffOn_eq_zero hn hdim x₀
      exact ⟨S, hS, hx₀, g, hg, hzero, fun y hy ↦ hreg y hy.1⟩
    · obtain ⟨c, hc⟩ := exists_ne (0 : P)
      exact ⟨(range f)ᶜ, hclosed.isOpen_compl, hy₀, fun _ ↦ c, contMDiffOn_const,
        fun y hy ↦ ⟨fun hyr ↦ (hy hyr).elim, fun hcz ↦ (hc hcz).elim⟩, fun y hy ↦ (hy.1 hy.2).elim⟩
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y₀ hy₀
    obtain ⟨S, hS, hy₀S, g, hg, hzero, -⟩ := h y₀
    refine Filter.mem_of_superset ((hg.continuousOn.isOpen_inter_preimage hS
      isClosed_singleton.isOpen_compl).mem_nhds
      ⟨hy₀S, fun hgy₀ ↦ hy₀ ((hzero y₀ hy₀S).2 hgy₀)⟩) fun y hy hyr ↦ hy.2 ((hzero y hy.1).1 hyr)

end TauCeti.SmoothEmbedding
