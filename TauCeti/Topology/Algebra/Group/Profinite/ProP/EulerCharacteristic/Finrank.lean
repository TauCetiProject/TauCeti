/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Zero
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomFp
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic.ThreeTerm

/-!
# The Euler formulas for the dimensions of `Hⁱ(-, 𝔽_p)`

Let `G` be a topologically finitely generated pro-`p` group and `U` an open subgroup. This file
states the two-term and the three-term Euler formulas as identities between the `𝔽_p`-dimensions
of the cohomology groups `Hⁱ(-, 𝔽_p) = cohomFp p - i` with trivial coefficients, with the
alternating sums taken in `ℤ`:

```text
dim H⁰(U) - dim H¹(U) = [G : U] * (dim H⁰(G) - dim H¹(G))                       (cd_p G ≤ 1),
dim H⁰(U) - dim H¹(U) + dim H²(U) = [G : U] * (dim H⁰(G) - dim H¹(G) + dim H²(G)) (cd_p G ≤ 2).
```

All the spaces involved are finite-dimensional: `H⁰(-, 𝔽_p) ≅ 𝔽_p` has dimension one
(`TauCeti.finrank_cohomFp_zero`); `H¹(-, 𝔽_p)` is finite-dimensional of dimension the topological
generator rank (`TauCeti.IsProP.finite_cohomFp_one_iff`, `TauCeti.IsProP.finrank_cohomFp_one`),
and `U` is topologically finitely generated with `G`; and in the three-term formula `H²(G, 𝔽_p)`
is finite by hypothesis, which makes `H²(U, 𝔽_p)` finite
(`TauCeti.IsProP.finite_cohomFp_openSubgroup`). The hypothesis on `H²(G, 𝔽_p)` is not
redundant: topological finite generation bounds `H⁰` and `H¹` only, and `dim H²(G, 𝔽_p)` is the
relation rank of `G`.

The formulas are the generator-rank identities of
`TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic.Basic` and
`TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic.ThreeTerm`, read through these
dimension counts. For a free pro-`p` group of finite rank the two-term formula is the Schreier
index formula; for a Demushkin group, where `dim H⁰ = dim H² = 1`, the three-term formula is the
rank formula `d(U) - 2 = [G : U] * (d(G) - 2)` of an open subgroup.

## Main results

* `TauCeti.IsProP.finrank_cohomFp_zero_sub_finrank_cohomFp_one_openSubgroup` and its form
  `TauCeti.CohomologicalDimensionLE.finrank_cohomFp_zero_sub_finrank_cohomFp_one_openSubgroup`
  under `cd_p G ≤ 1`: the two-term Euler formula.
* `finrank_cohomFp_zero_sub_finrank_cohomFp_one_add_finrank_cohomFp_two_openSubgroup`, in the
  namespace `TauCeti.IsProP` and, under `cd_p G ≤ 2`, in `TauCeti.CohomologicalDimensionLE`: the
  three-term Euler formula.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.1.
* H. Koch, *Galois Theory of `p`-Extensions*, §5.4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III §3.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

namespace IsProP

section TwoTerm

variable (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
  (h2 : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
    (∀ (g : G) (a : A), g • a = a) → Subsingleton (H2 G A))
include hG hfg h2

/-- **The two-term Euler formula.** Let `G` be a topologically finitely generated profinite pro-`p`
group whose explicit `H²` vanishes on the discrete modules of order `p` with trivial action, and
let `U` be an open subgroup. Then, in `ℤ`,

```text
dim H⁰(U, 𝔽_p) - dim H¹(U, 𝔽_p) = [G : U] * (dim H⁰(G, 𝔽_p) - dim H¹(G, 𝔽_p)).
```

The four spaces are finite-dimensional: `H⁰` always, and `H¹` because `G` and `U` are
topologically finitely generated (`TauCeti.IsProP.finite_cohomFp_one_iff`). -/
theorem finrank_cohomFp_zero_sub_finrank_cohomFp_one_openSubgroup (U : OpenSubgroup G) :
    (Module.finrank (ZMod p) (cohomFp p U.toSubgroup 0) : ℤ) -
        Module.finrank (ZMod p) (cohomFp p U.toSubgroup 1) =
      U.toSubgroup.index * ((Module.finrank (ZMod p) (cohomFp p G 0) : ℤ) -
        Module.finrank (ZMod p) (cohomFp p G 1)) := by
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp U.isClosed.isCompact
  rw [finrank_cohomFp_zero, finrank_cohomFp_zero,
    (hG.subgroup U.toSubgroup).finrank_cohomFp_one (hfg.of_openSubgroup U),
    hG.finrank_cohomFp_one hfg, Nat.cast_one]
  exact hG.one_sub_topologicalGeneratorRankNat_eq hfg h2 U

end TwoTerm

section ThreeTerm

variable (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
  (h3 : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
    (∀ (g : G) (a : A), g • a = a) →
    Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ G A)))
  [Finite (cohomFp p G 2)]
include hG hfg h3

/-- **The three-term Euler formula.** Let `G` be a topologically finitely generated profinite
pro-`p` group whose canonical `H³` vanishes on the discrete modules of order `p` with trivial
action, with `H²(G, 𝔽_p)` finite, and let `U` be an open subgroup. Then, in `ℤ`,

```text
dim H⁰(U) - dim H¹(U) + dim H²(U) = [G : U] * (dim H⁰(G) - dim H¹(G) + dim H²(G)),
```

for the cohomology with trivial coefficients `𝔽_p`. The six spaces are finite-dimensional: `H⁰`
always, `H¹` because `G` and `U` are topologically finitely generated, and `H²(U, 𝔽_p)` by
`TauCeti.IsProP.finite_cohomFp_openSubgroup`. -/
theorem finrank_cohomFp_zero_sub_finrank_cohomFp_one_add_finrank_cohomFp_two_openSubgroup
    (U : OpenSubgroup G) :
    (Module.finrank (ZMod p) (cohomFp p U.toSubgroup 0) : ℤ) -
        Module.finrank (ZMod p) (cohomFp p U.toSubgroup 1) +
        Module.finrank (ZMod p) (cohomFp p U.toSubgroup 2) =
      U.toSubgroup.index * ((Module.finrank (ZMod p) (cohomFp p G 0) : ℤ) -
        Module.finrank (ZMod p) (cohomFp p G 1) + Module.finrank (ZMod p) (cohomFp p G 2)) := by
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp U.isClosed.isCompact
  -- the explicit `H²` of the rank identity needs an action on `ZMod p`; the trivial one is
  -- installed for the proof and does not appear in the statement
  let := trivialZModAction p G
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  have htriv : ∀ (g : G) (x : ZMod p), g • x = x := fun _ _ ↦ rfl
  have : Finite (H2 G (ZMod p)) := Finite.of_equiv _ (cohomFpAddEquivH2 p G htriv).toEquiv
  rw [finrank_cohomFp_zero, finrank_cohomFp_zero,
    (hG.subgroup U.toSubgroup).finrank_cohomFp_one (hfg.of_openSubgroup U),
    hG.finrank_cohomFp_one hfg, (cohomFpLinearEquivH2 p G htriv).finrank_eq,
    (cohomFpLinearEquivH2 p U.toSubgroup fun u ↦ htriv u).finrank_eq, Nat.cast_one]
  exact hG.one_sub_topologicalGeneratorRankNat_add_finrank_H2 hfg htriv h3 U

end ThreeTerm

end IsProP

namespace CohomologicalDimensionLE

variable (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
include hG hfg

/-- **The two-term Euler formula under `cd_p G ≤ 1`.** For a topologically finitely generated
profinite pro-`p` group `G` with `cd_p G ≤ 1` and an open subgroup `U`, in `ℤ`:
`dim H⁰(U, 𝔽_p) - dim H¹(U, 𝔽_p) = [G : U] * (dim H⁰(G, 𝔽_p) - dim H¹(G, 𝔽_p))`. -/
theorem finrank_cohomFp_zero_sub_finrank_cohomFp_one_openSubgroup
    (hcd : CohomologicalDimensionLE.{u} p G 1) (U : OpenSubgroup G) :
    (Module.finrank (ZMod p) (cohomFp p U.toSubgroup 0) : ℤ) -
        Module.finrank (ZMod p) (cohomFp p U.toSubgroup 1) =
      U.toSubgroup.index * ((Module.finrank (ZMod p) (cohomFp p G 0) : ℤ) -
        Module.finrank (ZMod p) (cohomFp p G 1)) :=
  hG.finrank_cohomFp_zero_sub_finrank_cohomFp_one_openSubgroup hfg
    (fun A _ _ _ _ _ _ hA _ ↦ hcd.subsingleton_H2 A
      (isPPrimaryTorsion_of_natCard_eq_pow (hA.trans (pow_one p).symm))) U

/-- **The three-term Euler formula under `cd_p G ≤ 2`.** For a topologically finitely generated
profinite pro-`p` group `G` with `cd_p G ≤ 2` and `H²(G, 𝔽_p)` finite, and an open
subgroup `U`, in `ℤ`:
`dim H⁰(U) - dim H¹(U) + dim H²(U) = [G : U] * (dim H⁰(G) - dim H¹(G) + dim H²(G))` for the
cohomology with trivial coefficients `𝔽_p`. -/
theorem finrank_cohomFp_zero_sub_finrank_cohomFp_one_add_finrank_cohomFp_two_openSubgroup
    (hcd : CohomologicalDimensionLE.{u} p G 2) [Finite (cohomFp p G 2)]
    (U : OpenSubgroup G) :
    (Module.finrank (ZMod p) (cohomFp p U.toSubgroup 0) : ℤ) -
        Module.finrank (ZMod p) (cohomFp p U.toSubgroup 1) +
        Module.finrank (ZMod p) (cohomFp p U.toSubgroup 2) =
      U.toSubgroup.index * ((Module.finrank (ZMod p) (cohomFp p G 0) : ℤ) -
        Module.finrank (ZMod p) (cohomFp p G 1) + Module.finrank (ZMod p) (cohomFp p G 2)) :=
  hG.finrank_cohomFp_zero_sub_finrank_cohomFp_one_add_finrank_cohomFp_two_openSubgroup hfg
    (fun A _ _ _ _ _ _ hA _ ↦ cohomologicalDimensionLE_iff.mp hcd A
      (isPPrimaryTorsion_of_natCard_eq_pow (hA.trans (pow_one p).symm)) 3 (by norm_num)) U

end CohomologicalDimensionLE

end TauCeti
