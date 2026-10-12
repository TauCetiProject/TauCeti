/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Duality.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomologicalDimension

/-!
# The cohomological dimension of a Demushkin group

**Tate's theorem: an infinite Demushkin group has `cd_p G = 2`** (Serre's exposé, §9.1). The lower
bound holds for every Demushkin group: `H²(G, 𝔽_p)` is one-dimensional, so `H²(G, 𝔽_p) ≠ 0` and
`Hⁿ(G, 𝔽_p) ≠ 0 → n ≤ cd_p G` (`TauCeti.le_cohomologicalDimensionAt_of_nontrivial_cohomFp`) gives
`2 ≤ cd_p G`. The upper bound is the right exactness of `H²` on the finite `𝔽_p[G]`-modules, which
follows from Tate's perfect duality on those modules
(`TauCeti.IsDemushkin.dualityMap2_bijective`) through
`TauCeti.IsProP.cohomologicalDimensionAt_le_two_of_forall_dualityMap2_bijective`.

The hypothesis "infinite" is needed for the upper bound and not for the lower one: the finite
Demushkin group `ℤ/2` has `cd_2 (ℤ/2) = ⊤`.

## Main results

* `TauCeti.IsDemushkin.two_le_cohomologicalDimensionAt`: a Demushkin group has `2 ≤ cd_p G`.
* `TauCeti.IsDemushkin.cohomologicalDimensionAt_eq_two`: an infinite Demushkin group has
  `cd_p G = 2`.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.1.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- **A Demushkin group has `p`-cohomological dimension at least `2`**: its `H²(G, 𝔽_p)` is
one-dimensional, hence nonzero. -/
theorem IsDemushkin.two_le_cohomologicalDimensionAt (hG : IsDemushkin p G) :
    2 ≤ cohomologicalDimensionAt.{u} p G :=
  le_cohomologicalDimensionAt_of_nontrivial_cohomFp
    (Module.nontrivial_of_finrank_eq_succ hG.finrank_cohomFp_two)

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the duality maps
-- on `ZMod p` are the ones `TauCeti.IsDemushkin.dualityMap2_bijective` is stated against.
attribute [local instance 2000] Ring.toAddCommGroup

/-- **Tate's theorem: an infinite Demushkin group has `p`-cohomological dimension exactly `2`.**
The lower bound is `H²(G, 𝔽_p) ≠ 0`; the upper bound is the right exactness of `H²` on the finite
`𝔽_p[G]`-modules, which Tate's perfect duality provides. -/
theorem IsDemushkin.cohomologicalDimensionAt_eq_two [CompactSpace G] [TotallyDisconnectedSpace G]
    [Infinite G] (hG : IsDemushkin p G) : cohomologicalDimensionAt.{u} p G = 2 := by
  -- The duality maps need an action of `G` on `𝔽_p`; the trivial one is installed.
  let : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  exact le_antisymm
    (hG.isProP.cohomologicalDimensionAt_le_two_of_forall_dualityMap2_bijective (ZMod p)
      fun M _ _ _ _ _ _ hM ↦ hG.dualityMap2_bijective htriv M hM)
    hG.two_le_cohomologicalDimensionAt

end TauCeti
