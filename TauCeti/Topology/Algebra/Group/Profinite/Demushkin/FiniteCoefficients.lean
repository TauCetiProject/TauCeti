/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FiniteCohomology

/-!
# The second cohomology of a Demushkin group with finite coefficients is finite

A Demushkin group `G` has `H²(G, 𝔽_p)` one-dimensional, hence finite
(`TauCeti.IsDemushkin.finite_cohomFp_two`). The finiteness dévissage for pro-`p` groups
(`TauCeti.IsProP.finite_continuousCohomology_of_finite_cohomFp`) then makes
`H²(G, M)` finite for every finite discrete `p`-primary `G`-module `M`, whatever the action. This
holds for every Demushkin group, including the finite one `ℤ/2`, and uses no bound on the
cohomological dimension of `G`.

This is the finiteness input of Tate's duality argument for Demushkin groups (Serre, *Structure de
certains pro-p-groupes*, §9.1): the duality maps `Hⁱ(G, M) → Hom(H²⁻ⁱ(G, M^∨), H²(G, 𝔽_p))` are
compared by counting, and the count needs `H²(G, M)` to be finite for the finite `𝔽_p[G]`-modules
`M` before the equality `cd_p G = 2` is known.

## Main results

* `TauCeti.IsDemushkin.finite_continuousCohomology_two`,
  `TauCeti.IsDemushkin.finite_H2`: `H²(G, M)` is finite for every finite discrete `p`-primary
  `G`-module `M`, on Mathlib's carrier and on the explicit cocycle model.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki
  exp. 252 (1963), §9.1.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

namespace IsDemushkin

variable (hG : IsDemushkin p G)
include hG

/-- **`H²(G, M)` of a Demushkin group is finite for every finite `p`-primary `M`**, on Mathlib's
carrier. -/
theorem finite_continuousCohomology_two (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    (hM : IsPPrimaryTorsion p M) : Finite (continuousCohomology 2 (ofDiscreteModule ℤ G M)) :=
  have := hG.finite_cohomFp_two
  hG.isProP.finite_continuousCohomology_of_finite_cohomFp (n := 2) M hM

/-- **`H²(G, M)` of a Demushkin group is finite for every finite `p`-primary `M`**, on the explicit
cocycle model. -/
theorem finite_H2 (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : IsPPrimaryTorsion p M) :
    Finite (H2 G M) :=
  have := hG.finite_cohomFp_two
  hG.isProP.finite_H2 M hM

end IsDemushkin

end TauCeti
