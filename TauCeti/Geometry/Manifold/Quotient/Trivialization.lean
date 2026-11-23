/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Topology.FiberBundle.OrbitRelQuotient

/-!
# Smooth trivializations descend to quotient manifolds

Let a group `G` act freely and properly discontinuously by `C^n` maps on `C^n` manifolds `M` and
`N`, so that both orbit spaces are `C^n` manifolds whose orbit projections are local
diffeomorphisms (`TauCeti.isLocalDiffeomorph_quotientMk`). An equivariant map `φ : M → N` induces
a map `φ' : M/G → N/G`, and a trivialization `e` of `φ` over a set `U` on which the orbit
projection of `N` is injective descends to a trivialization `e'` of `φ'` over the image of `U`
(`Bundle.Trivialization.orbitRelQuotient`).

This file shows that `e'` is `C^n` whenever `e` is, and likewise for the inverses: `e'` is `e` read
through the orbit projections, which are `C^n`, and through their inverses on open sets where they
are injective, which are `C^n` because the orbit projections are local diffeomorphisms
(`IsLocalDiffeomorphOn.contMDiffOn_invFunOn`). Thus smooth local trivializations of an
equivariant map descend to smooth local trivializations of the induced map of quotient manifolds,
and holomorphic ones to holomorphic ones over `ℂ`.

## Main results

* `Bundle.Trivialization.contMDiffOn_orbitRelQuotient`: the descended trivialization is `C^n` on
  its source if `e` is.
* `Bundle.Trivialization.contMDiffOn_orbitRelQuotient_symm`: its inverse is `C^n` on its target if
  the inverse of `e` is.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

open Function Set TauCeti
open scoped Manifold ContDiff

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM}
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] {HN : Type*} [TopologicalSpace HN]
  {IN : ModelWithCorners 𝕜 EN HN}
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {n : ℕ∞ω}
  {G M N F : Type*} [Group G] [TopologicalSpace F] [ChartedSpace HF F]
  [MulAction G M] [TopologicalSpace M] [ChartedSpace HM M] [ProperlyDiscontinuousSMul G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M] [LocallyCompactSpace M]
  [IsManifold IM n M] [ContMDiffConstSMul IM n G M]
  [MulAction G N] [TopologicalSpace N] [ChartedSpace HN N] [ProperlyDiscontinuousSMul G N]
  [ContinuousConstSMul G N] [IsCancelSMul G N] [T2Space N] [LocallyCompactSpace N]
  [IsManifold IN n N] [ContMDiffConstSMul IN n G N]
  [Nonempty M] {φ : M →[G] N} (e : Trivialization F φ)
  (hinj : InjOn (Quotient.mk (MulAction.orbitRel G N)) e.baseSet)
  (hfree : ∀ y ∈ e.baseSet, ∀ g : G, g • y = y → g = 1)

/-- **A `C^n` trivialization descends to a `C^n` trivialization.** If a trivialization `e` of an
equivariant map between manifolds with free properly discontinuous actions by `C^n` maps is `C^n`
on its source, so is the trivialization it induces on the orbit spaces. -/
theorem contMDiffOn_orbitRelQuotient (he : ContMDiffOn IM (IN.prod IF) n e e.source) :
    ContMDiffOn IM (IN.prod IF) n (e.orbitRelQuotient hinj hfree)
      (e.orbitRelQuotient hinj hfree).source := by
  rw [coe_orbitRelQuotient, orbitRelQuotient_source]
  have hinjM := e.injOn_quotientMk_source hinj hfree
  refine ((isLocalDiffeomorph_quotientMk (I := IN) (n := n) (G := G)).contMDiff.prodMap
    contMDiff_id).comp_contMDiffOn (he.comp
    ((isLocalDiffeomorph_quotientMk (I := IM) (n := n) (G := G)).isLocalDiffeomorphOn
      e.source |>.contMDiffOn_invFunOn e.open_source hinjM) (surjOn_image _ _).mapsTo_invFunOn)

/-- **The inverse of a `C^n` trivialization descends to a `C^n` map.** If the inverse of a
trivialization `e` of an equivariant map between manifolds with free properly discontinuous
actions by `C^n` maps is `C^n` on its target, so is the inverse of the trivialization it induces
on the orbit spaces. -/
theorem contMDiffOn_orbitRelQuotient_symm
    (he : ContMDiffOn (IN.prod IF) IM n e.toOpenPartialHomeomorph.symm e.target) :
    ContMDiffOn (IN.prod IF) IM n (e.orbitRelQuotient hinj hfree).toOpenPartialHomeomorph.symm
      (e.orbitRelQuotient hinj hfree).target := by
  have : Nonempty N := ⟨φ (Classical.arbitrary M)⟩
  rw [coe_orbitRelQuotient_symm, (e.orbitRelQuotient hinj hfree).target_eq,
    orbitRelQuotient_baseSet]
  refine (isLocalDiffeomorph_quotientMk (I := IM) (n := n) (G := G)).contMDiff.comp_contMDiffOn
    (he.comp (((isLocalDiffeomorph_quotientMk (I := IN) (n := n) (G := G)).isLocalDiffeomorphOn
      e.baseSet |>.contMDiffOn_invFunOn e.open_baseSet hinj).prodMap contMDiffOn_id) ?_)
  rintro ⟨_, f⟩ ⟨⟨y, hy, rfl⟩, -⟩
  rw [e.target_eq]
  exact ⟨(surjOn_image _ _).mapsTo_invFunOn ⟨y, hy, rfl⟩, mem_univ f⟩

end Bundle.Trivialization
