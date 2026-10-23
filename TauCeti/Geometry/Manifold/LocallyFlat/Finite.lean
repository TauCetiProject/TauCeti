/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

/-!
# Bicollars of finite sets

An injective locally bicollared map from a finite space into a Hausdorff space has a
global bicollar. This includes codimension-one embeddings of zero-dimensional manifolds.
There is no connectedness or choice of complementary sides in the hypothesis: local collars
can be shortened to lie in pairwise disjoint neighbourhoods of the finitely many image points.

The local product neighbourhood is the bicollar notion of M. Brown, *Locally flat imbeddings
of topological manifolds*, Annals of Mathematics 75 (1962), 331–341. Finite separation and the
reparametrization of a line onto an interval use Mathlib's `Set.Finite.t2_separation` and
`OpenPartialHomeomorph.univBall`.
-/

public section

open Set Function Topology

namespace TauCeti

/-- An injective locally bicollared map from a finite space into a Hausdorff space is
bicollared. In particular, no connectedness assumption on the source is needed in dimension
zero. -/
theorem IsLocallyBicollared.isBicollared_of_finite
    {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]
    [Finite N] [T2Space M] {f : N → M}
    (h : IsLocallyBicollared f) (hf : Injective f) : IsBicollared f := by
  classical
  have := T2Space.of_injective_continuous hf h.continuous
  -- Separate the finitely many core points before shortening their local bicollars.
  obtain ⟨O, hO, hdisj⟩ := (finite_range f).t2_separation
  have hlocal : ∀ x : N, ∃ c : ℝ → M,
      IsOpenEmbedding c ∧ c 0 = f x ∧ range c ⊆ O (f x) := by
    intro x
    obtain ⟨U, -, hxU, hU⟩ := isLocallyBicollared_iff.1 h x
    obtain ⟨b, hb⟩ := isBicollared_iff.1 hU
    let xU : U := ⟨x, hxU⟩
    have hslice : IsOpenEmbedding (fun t : ℝ => (xU, t)) := by
      refine IsOpenEmbedding.of_isEmbedding_isOpenMap (isEmbedding_prodMkRight xU) ?_
      intro s hs
      rw [← singleton_prod]
      exact (isOpen_discrete {xU}).prod hs
    have hc := hb.isOpenEmbedding.comp hslice
    have hzero : b (xU, 0) = f x := hb.apply_zero xU
    have hnbhd : (fun t : ℝ => b (xU, t)) ⁻¹' O (f x) ∈ nhds 0 :=
      (hc.continuous.tendsto 0).eventually (hzero ▸ (hO (f x)).2.mem_nhds (hO (f x)).1)
    obtain ⟨ε, hε, hεO⟩ := Metric.mem_nhds_iff.1 hnbhd
    let ρ := OpenPartialHomeomorph.univBall (0 : ℝ) ε
    have hρ : IsOpenEmbedding ρ :=
      ρ.isOpenEmbedding (OpenPartialHomeomorph.univBall_source _ _)
    refine ⟨(fun t : ℝ => b (xU, t)) ∘ ρ, hc.comp hρ, ?_, ?_⟩
    · simpa [ρ] using hzero
    · rintro _ ⟨t, rfl⟩
      apply hεO
      rw [← OpenPartialHomeomorph.univBall_target (0 : ℝ) hε]
      exact ρ.map_source (by simp [ρ])
  choose c hc hc0 hcO using hlocal
  -- The shortened lines have disjoint ranges and assemble over the discrete source.
  refine isBicollared_iff.2 ⟨fun p => c p.1 p.2, ?_⟩
  refine ⟨IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_, fun x => hc0 x⟩
  · exact continuous_prod_of_discrete_left.2 fun x => (hc x).continuous
  · rintro ⟨x, s⟩ ⟨y, t⟩ heq
    dsimp only at heq
    have hxy : x = y := by
      by_contra hne
      exact disjoint_left.1 (hdisj (mem_range_self x) (mem_range_self y)
        (fun he => hne (hf he))) (hcO x (mem_range_self s))
        (by rw [heq]; exact hcO y (mem_range_self t))
    subst y
    exact Prod.ext rfl ((hc x).injective heq)
  · intro s hs
    have himage : (fun p : N × ℝ => c p.1 p.2) '' s =
        ⋃ x, c x '' ((fun t : ℝ => (x, t)) ⁻¹' s) := by
      ext z
      simp only [mem_image, mem_iUnion, mem_preimage, Prod.exists]
    rw [himage]
    exact isOpen_iUnion fun x => (hc x).isOpenMap _
      (hs.preimage (continuous_const.prodMk continuous_id))

end TauCeti
