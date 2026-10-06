/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ConjInvariants
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Extension

/-!
# The invariant part of `H¹(N, 𝔽_p)` and the rank of `N ⧸ Nᵖ[N, G]`

Let `G` be a profinite group, `N` a closed normal subgroup, and `𝔽_p` the trivial `G`-module.
The `G`-invariant classes in `H¹(N, 𝔽_p)` are the continuous homomorphisms `N ⧸ Nᵖ[N, G] → 𝔽_p`
(`TauCeti.ContCohomology.H1ConjInvariantsEquivOfSmulEqSelf`), that is, the continuous `𝔽_p`-dual
of `N ⧸ Nᵖ[N, G]`. This quotient is a profinite group killed by `p`, hence pro-`p` whether or not
`G` is, so by Burnside's basis theorem the dimension of its dual is its topological generator rank.
So `H¹(N, 𝔽_p)^G` is finite exactly when `N ⧸ Nᵖ[N, G]` is topologically finitely generated, and
then it has `p ^ d(N ⧸ Nᵖ[N, G])` elements.

For a minimal presentation `1 → R → F → G → 1` of a pro-`p` group by a free pro-`p` group `F`,
the transgression identifies `H¹(R, 𝔽_p)^F` with `H²(G, 𝔽_p)`, and `d(R ⧸ Rᵖ[R, F])` is the least
number of generators of `R` as a closed normal subgroup of `F`. The count here is therefore what
makes the dimension of `H²(G, 𝔽_p)` the relation rank of `G`.

## Main results

* `TauCeti.pLowerCentralStep_proPKernel`: the relative elementary abelian `p`-quotient of the
  pro-`p` kernel is trivial, so `H¹(R, M)^G` vanishes for `R` the pro-`p` kernel and trivial
  coefficients `M` killed by `p` (`TauCeti.subsingleton_h1ConjInvariants_proPKernel`).
* `TauCeti.finite_H1ConjInvariants_iff`: `H¹(N, 𝔽_p)^G` is finite exactly when
  `N ⧸ Nᵖ[N, G]` is topologically finitely generated.
* `TauCeti.natCard_H1ConjInvariants`: in that case `H¹(N, 𝔽_p)^G` has `p ^ d(N ⧸ Nᵖ[N, G])`
  elements.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (3.9.1) and (3.9.5).
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §1.4.
-/

public section

namespace TauCeti

open ContCohomology

universe u v

-- For prime `p`, `AddCommGroup (ZMod p)` is also derivable from `[IsSimpleAddGroup (ZMod p)]
-- [AddGroup.IsNilpotent (ZMod p)]`; that structure is not reducibly the ring one, so the
-- `DistribMulAction G (ZMod p)` hypothesis below would not match what `H1ConjInvariants` expects.
-- Preferring the ring path locally keeps a single additive structure on `ZMod p`.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]

/-! ### The maximal pro-`p` kernel -/

section MaximalKernel

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The pro-`p` kernel has no nontrivial elementary abelian `p`-quotient invariant under the
ambient group: `Rᵖ[R,G] = R` for `R = proPKernel p G`. -/
theorem pLowerCentralStep_proPKernel :
    pLowerCentralStep p (proPKernel p G) = proPKernel p G := by
  -- The quotient of `G` by `Rᵖ[R,G]` is an extension of `G(p)` by an elementary abelian
  -- pro-`p` group, hence is itself pro-`p`; the universal property then forces `R` into
  -- `Rᵖ[R,G]`.
  let R : Subgroup G := proPKernel p G
  let _ : R.Normal := by dsimp [R]; infer_instance
  let S : Subgroup G := pLowerCentralStep p R
  let _ : S.Normal := by dsimp [S]; infer_instance
  let _ : IsClosed (S : Set G) := isClosed_pLowerCentralStep R
  let f : (G ⧸ S) →* (G ⧸ R) := QuotientGroup.map S R (MonoidHom.id G)
    (by simpa only [Subgroup.comap_id] using
      pLowerCentralStep_le (p := p) (H := R) (isClosed_proPKernel (p := p) (G := G)))
  have hf : Continuous f :=
    -- `f ∘ QuotientGroup.mk` is `QuotientGroup.mk` by `QuotientGroup.map_mk`, definitionally.
    (QuotientGroup.isQuotientMap_mk S).continuous_iff.mpr QuotientGroup.continuous_mk
  have hsurj : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective (N := S) (M := R) (MonoidHom.id G)
      (QuotientGroup.mk'_surjective R)
      (by simpa only [Subgroup.comap_id] using
        pLowerCentralStep_le (p := p) (H := R) (isClosed_proPKernel (p := p) (G := G)))
  have hker : IsPGroup p f.ker := by
    refine IsPGroup.of_exponent_dvd_pow (n := 1) ?_
    rw [pow_one, Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.1
    have hgR : g ∈ R := by
      have hx : f x.1 = 1 := x.2
      rwa [← hg, QuotientGroup.map_mk, MonoidHom.id_apply, QuotientGroup.eq_one_iff] at hx
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hg, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff]
    exact pow_mem_pLowerCentralStep hgR
  have hGS : IsProP p (G ⧸ S) :=
    (isProP_maximalProPQuotient (p := p) (G := G)).of_ker_isProP hf hsurj hker.isProP
  apply le_antisymm
    (pLowerCentralStep_le (p := p) (H := proPKernel p G)
      (isClosed_proPKernel (p := p) (G := G)))
  intro g hg
  exact (QuotientGroup.eq_one_iff g).mp
    (proPKernel_le_ker hGS (QuotientGroup.mk' S) QuotientGroup.continuous_mk hg)

/-- **The pro-`p` kernel has no invariant degree-one classes with trivial `p`-torsion
coefficients.** For `R = proPKernel p G` and a `T1Space` module `M` with trivial action and killed
by `p`, `H¹(R, M)^G` is trivial. -/
theorem subsingleton_h1ConjInvariants_proPKernel {M : Type v} [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [T1Space M] [DistribMulAction G M]
    [ContinuousSMul G M] (htriv : ∀ (g : G) (m : M), g • m = m) (hpM : ∀ m : M, p • m = 0) :
    Subsingleton (H1ConjInvariants G M (proPKernel p G)) := by
  -- `H¹(R, M)^G` is the group of continuous homomorphisms `R ⧸ Rᵖ[R, G] → M`, and the quotient
  -- is trivial by `pLowerCentralStep_proPKernel`.
  let e := H1ConjInvariantsEquivOfSmulEqSelf htriv p (isClosed_proPKernel (p := p) (G := G)) hpM
  refine ⟨fun x y ↦ e.injective (Additive.toMul.injective (ContinuousMonoidHom.ext fun q ↦ ?_))⟩
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
  have hr : (r : proPKernel p G ⧸ (pLowerCentralStep p (proPKernel p G)).subgroupOf
      (proPKernel p G)) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, pLowerCentralStep_proPKernel]
    exact r.2
  rw [hr, map_one, map_one]

end MaximalKernel

/-! ### Invariant degree-one classes -/

variable [Fact p.Prime] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable {N : Subgroup G} [N.Normal]
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]

variable (hN : IsClosed (N : Set G)) (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include hN htriv

/-- **Finiteness of `H¹(N, 𝔽_p)^G`.** For a closed normal subgroup `N` of a profinite group `G`,
the `G`-invariant part of `H¹(N, 𝔽_p)` is finite exactly when `N ⧸ Nᵖ[N, G]` is topologically
finitely generated. -/
theorem finite_H1ConjInvariants_iff :
    Finite (H1ConjInvariants G (ZMod p) N) ↔
      IsTopologicallyFinitelyGenerated (N ⧸ (pLowerCentralStep p N).subgroupOf N) := by
  have hK := isClosed_pLowerCentralStep_subgroupOf (p := p) N
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  have hQ : IsProP p (N ⧸ (pLowerCentralStep p N).subgroupOf N) :=
    (isPGroup_quotient_pLowerCentralStep_subgroupOf N).isProP
  rw [(H1ConjInvariantsEquivOfSmulEqSelf htriv p hN fun m ↦ by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]).toEquiv.finite_iff,
    ← Module.finite_iff_finite (R := ZMod p), hQ.finite_continuousZModDual_iff]

/-- **`H¹(N, 𝔽_p)^G` counts the generators of `N ⧸ Nᵖ[N, G]`.** For a closed normal subgroup `N`
of a profinite group `G` with `N ⧸ Nᵖ[N, G]` topologically finitely generated, the
`G`-invariant part of `H¹(N, 𝔽_p)` has `p ^ d(N ⧸ Nᵖ[N, G])` elements, where `d` is the
topological generator rank. -/
theorem natCard_H1ConjInvariants
    (h : IsTopologicallyFinitelyGenerated (N ⧸ (pLowerCentralStep p N).subgroupOf N)) :
    Nat.card (H1ConjInvariants G (ZMod p) N) =
      p ^ topologicalGeneratorRankNat (N ⧸ (pLowerCentralStep p N).subgroupOf N) h := by
  have hK := isClosed_pLowerCentralStep_subgroupOf (p := p) N
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  have hQ : IsProP p (N ⧸ (pLowerCentralStep p N).subgroupOf N) :=
    (isPGroup_quotient_pLowerCentralStep_subgroupOf N).isProP
  have := finite_continuousZModDual (p := p) h
  rw [Nat.card_congr (H1ConjInvariantsEquivOfSmulEqSelf htriv p hN fun m ↦ by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
    hQ.finrank_continuousZModDual_eq_topologicalGeneratorRankNat h]

end TauCeti
