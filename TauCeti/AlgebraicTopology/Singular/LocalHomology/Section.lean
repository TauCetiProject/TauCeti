/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact

/-!
# Gluing parallel sections of local homology

On a finite-dimensional Hausdorff manifold without boundary, a family of local homology classes
invariant under path transport is locally represented by a single relative class. In the
manifold dimension, it therefore glues uniquely over every
compact subset. For a compact manifold, this gives a unique absolute homology class with the
prescribed local values. For integral coefficients and a parallel family of local generators,
this is the existence and uniqueness argument for the fundamental class.

No connectedness assumption is needed: orientations may be chosen independently on components.
The comparison of homological orientations with tangent-space orientations, and the boundary
formula for manifolds with boundary, are separate matters.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, Lemma 3.27 and Theorem 3.26.
-/

public section

noncomputable section

open CategoryTheory Metric Module Set Topology

universe w

namespace TauCeti

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ)
  {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- A transport-invariant family of local homology classes is represented near every point by a
single relative class. This holds in every degree, not only in the dimension of the manifold. -/
theorem exists_mem_nhds_localHomologyRestriction_eq_of_invariant (k : ℕ)
    (α : ∀ x : M, (localHomology N {x} k : ModuleCat.{w} Λ))
    (hα : ∀ {x y : FundamentalGroupoid M} (f : x ⟶ y),
      localHomologyTransport N M E k f (α x.as) = α y.as) (x : M) :
    ∃ U ∈ 𝓝 x, ∃ β : (localHomology N U k : ModuleCat.{w} Λ),
      ∀ y (hy : y ∈ U), localHomologyRestriction N (singleton_subset_iff.2 hy) k β = α y := by
  -- Lift the value at `x` through a compact convex chart neighbourhood.
  let φ := chartAt E x
  have hx : x ∈ φ.source := mem_chart_source E x
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.mp φ.open_target (φ x) (φ.map_source hx)
  let K := closedBall (φ x) (r / 2)
  have hKφ : K ⊆ φ.target :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans hrt
  have hxK : φ x ∈ K := mem_closedBall_self (by positivity)
  have hxU : x ∈ φ.symm '' K := ⟨φ x, hxK, φ.left_inv hx⟩
  have hiso : IsIso (localHomologyRestriction N (singleton_subset_iff.2 hxU) k) :=
    isIso_localHomologyRestriction_symm_image N φ
      ((convex_closedBall _ _).starConvex hxK) (isCompact_closedBall _ _) hKφ hx hxK k
  let e := asIso (localHomologyRestriction N (singleton_subset_iff.2 hxU) k)
  refine ⟨φ.symm '' K, ?_, e.inv (α x), fun y hy ↦ ?_⟩
  · have hU := φ.symm.image_mem_nhds (φ.map_source hx)
      (closedBall_mem_nhds (φ x) (by positivity : 0 < r / 2))
    rwa [φ.left_inv hx] at hU
  -- Paths inside that neighbourhood identify all of its local values by transport.
  · have hpc : IsPathConnected (φ.symm '' K) :=
      ((convex_closedBall _ _).isPathConnected ⟨φ x, hxK⟩).image'
        (φ.symm.continuousOn.mono hKφ)
    obtain ⟨γ, hγ⟩ := hpc.joinedIn x hxU y hy
    have ht := localHomologyRestriction_comp_localHomologyTransport N φ
      (convex_closedBall _ _) (isCompact_closedBall _ _) hKφ γ hγ k
    have he : localHomologyTransport N M E k (Path.Homotopic.Quotient.mk γ)
        (e.hom (e.inv (α x))) =
        localHomologyRestriction N (singleton_subset_iff.2 hy) k (e.inv (α x)) :=
      congrArg (fun f ↦ f (e.inv (α x))) ht
    rw [e.inv_hom_id_apply] at he
    exact he.symm.trans (hα (Path.Homotopic.Quotient.mk γ))

/-- A parallel family of top-dimensional local classes glues uniquely over a compact subset.
The compatibility hypothesis is path transport, rather than the existence of local lifts. -/
theorem existsUnique_localHomologyRestriction_eq_of_invariant {n : ℕ}
    (hn : finrank ℝ E = n) {A : Set M} (hA : IsCompact A)
    (α : ∀ x : M, (localHomology N {x} n : ModuleCat.{w} Λ))
    (hα : ∀ {x y : FundamentalGroupoid M} (f : x ⟶ y),
      localHomologyTransport N M E n f (α x.as) = α y.as) :
    ∃! γ : (localHomology N A n : ModuleCat.{w} Λ),
      ∀ x (hx : x ∈ A), localHomologyRestriction N (singleton_subset_iff.2 hx) n γ = α x := by
  refine existsUnique_localHomologyRestriction_eq_of_isCompact N hn hA α fun x _ ↦ ?_
  obtain ⟨U, hU, β, hβ⟩ :=
    exists_mem_nhds_localHomologyRestriction_eq_of_invariant N n α hα x
  exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, β, fun y hy _ ↦ hβ y hy⟩

/-- On a compact manifold, a parallel family of top-dimensional local classes is the family of
local values of exactly one absolute singular homology class. The map to local homology is the
ordinary-to-relative quotient map followed by restriction. -/
theorem existsUnique_singularHomology_localHomologyRestriction_eq_of_invariant [CompactSpace M]
    {n : ℕ} (hn : finrank ℝ E = n)
    (α : ∀ x : M, (localHomology N {x} n : ModuleCat.{w} Λ))
    (hα : ∀ {x y : FundamentalGroupoid M} (f : x ⟶ y),
      localHomologyTransport N M E n f (α x.as) = α y.as) :
    ∃! γ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} Λ),
      ∀ x : M, localHomologyRestriction N (subset_univ {x}) n
        (((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
          (C := ModuleCat.{w} Λ) N n).hom γ) = α x := by
  obtain ⟨β, hβ, huniq⟩ :=
    existsUnique_localHomologyRestriction_eq_of_invariant N hn isCompact_univ α hα
  have : IsEmpty (TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).snd := by
    simp only [compl_univ]
    exact inferInstanceAs (IsEmpty (∅ : Set M))
  let e := asIso ((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
    (C := ModuleCat.{w} Λ) N n)
  refine ⟨e.inv β, fun x ↦ ?_, fun δ hδ ↦ ?_⟩
  · have he : ((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
        (C := ModuleCat.{w} Λ) N n).hom (e.inv β) = β := e.inv_hom_id_apply β
    rw [he]
    exact hβ x (mem_univ x)
  · apply (ModuleCat.mono_iff_injective e.hom).1 inferInstance
    exact (huniq (e.hom δ) (fun x _ ↦ hδ x)).trans (e.inv_hom_id_apply β).symm

end TauCeti
