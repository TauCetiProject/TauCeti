/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ConnectingMapComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H2ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TopologicallyFinitelyGenerated
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FiniteCohomology

/-!
# The three-term Euler formula for pro-`p` groups

Let `G` be a topologically finitely generated pro-`p` group whose third cohomology vanishes on the
trivial modules of order `p`; a group with `cd_p G ≤ 2` is one. For a finite discrete `p`-primary
`G`-module `M` of order `p ^ k`, the three-term Euler characteristic `|H⁰| * |H²| / |H¹|` is
multiplicative in the order of `M`:

```text
|H⁰(G, M)| * |H²(G, M)| * p ^ (k * d(G)) = |H¹(G, M)| * p ^ k * |H²(G, 𝔽_p)| ^ k,
```

where `d(G)` is the topological generator rank and `𝔽_p` carries the trivial action. For `M = 𝔽_p`
the identity is a tautology, given that `|H¹(G, 𝔽_p)| = p ^ d(G)`; the general case follows by
induction on `k` along the trivial filtration of
`TauCeti.exists_addSubgroup_natCard_eq_invariant_of_isProP`, each step being the nine-term exact
sequence

```text
0 → H⁰(N) → H⁰(M) → H⁰(M ⧸ N) → H¹(N) → H¹(M) → H¹(M ⧸ N) → H²(N) → H²(M) → H²(M ⧸ N) → 0
```

of the explicit long exact sequence, exact on the right because `H³(G, N) = 0`, and read through the
alternating identity `AddMonoidHom.card_mul_card_mul_card_mul_card_mul_card_of_exact`. The
cancellation in the induction step uses that `H¹(G, M ⧸ N)` is finite, which holds over any
topologically finitely generated group.

Applied to the permutation module `Coind_U^G 𝔽_p` of an open subgroup `U`, of order `p ^ [G : U]`,
Shapiro's lemma in degrees `0`, `1` and `2` turns the identity into the **three-term Euler
formula**: if `H²(G, 𝔽_p)` is finite then so is `H²(U, 𝔽_p) ≅ H²(G, Coind_U^G 𝔽_p)`
(`TauCeti.IsProP.finite_cohomFp_openSubgroup`, by the finiteness dévissage, with no hypothesis
on `H³`), and in `ℤ`

```text
1 - d(U) + dim H²(U, 𝔽_p) = [G : U] * (1 - d(G) + dim H²(G, 𝔽_p)).
```

Here `1 = dim H⁰` and `d = dim H¹` for the trivial module `𝔽_p`, so this is the identity
`χ(U) = [G : U] * χ(G)` for the truncated Euler characteristic
`χ = Σ_{i ≤ 2} (-1)^i dim Hⁱ(-, 𝔽_p)`.
When `H²(G, 𝔽_p)` and `H²(U, 𝔽_p)` are both one-dimensional, as for a Demushkin group `G` and an
open subgroup `U` that is again Demushkin, it becomes the rank formula
`d(U) - 2 = [G : U] * (d(G) - 2)`.

## Main results

* `TauCeti.IsProP.natCard_H0_mul_natCard_H2_mul_pow`: the multiplicative three-term Euler identity
  for a finite `p`-primary module of order `p ^ k`.
* `TauCeti.IsProP.natCard_H2_openSubgroup_mul_pow`: the identity for `Coind_U^G 𝔽_p`, read through
  Shapiro's lemma as an identity between `|H²(U, 𝔽_p)|`, `d(U)`, `[G : U]`, `d(G)` and
  `|H²(G, 𝔽_p)|`.
* `TauCeti.IsProP.one_sub_topologicalGeneratorRankNat_add_finrank_H2`: the three-term Euler
  formula in `ℤ`.
* `TauCeti.CohomologicalDimensionLE.natCard_H0_mul_natCard_H2_mul_pow`,
  `TauCeti.CohomologicalDimensionLE.natCard_H2_openSubgroup_mul_pow`,
  `TauCeti.CohomologicalDimensionLE.one_sub_topologicalGeneratorRankNat_add_finrank_H2`: the same
  under the hypothesis `cd_p G ≤ 2`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.1.
* H. Koch, *Galois Theory of `p`-Extensions*, §5.4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III §3.
-/

public section

namespace TauCeti

open ContCohomology

universe u

-- For prime `p`, `AddCommGroup (ZMod p)` is also derivable from `[IsSimpleAddGroup (ZMod p)]
-- [AddGroup.IsNilpotent (ZMod p)]`; that structure is not reducibly the ring one, so the
-- `DistribMulAction` hypotheses below would not match what the cohomology API expects.
-- Preferring the ring path locally keeps a single additive structure on `ZMod p`.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]

namespace IsProP

variable (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
  (htriv : ∀ (g : G) (x : ZMod p), g • x = x)
  (h3 : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
    (∀ (g : G) (a : A), g • a = a) →
    Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ G A)))
include hG hfg htriv h3

/-- **The three-term Euler characteristic of a finite `p`-primary module is multiplicative in its
order.** Let `G` be a topologically finitely generated profinite pro-`p` group whose canonical `H³`
vanishes on the discrete modules of order `p` with trivial action, and let `𝔽_p` carry the trivial
action. Then for every finite discrete `G`-module `M` of order `p ^ k`,

```text
|H⁰(G, M)| * |H²(G, M)| * p ^ (k * d(G)) = |H¹(G, M)| * p ^ k * |H²(G, 𝔽_p)| ^ k.
```

For `M = 𝔽_p` this is `|H¹(G, 𝔽_p)| = p ^ d(G)`; in general it is the additivity of the Euler
characteristic `|H⁰| * |H²| / |H¹|` along the trivial filtration of `M`. The identity holds for
`Nat.card` with no finiteness hypothesis on `H²(G, 𝔽_p)`, an infinite `H²` contributing the factor
`0` to both sides. -/
theorem natCard_H0_mul_natCard_H2_mul_pow (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] {k : ℕ}
    (hk : Nat.card M = p ^ k) :
    Nat.card (H0 G M) * Nat.card (H2 G M) * p ^ (k * topologicalGeneratorRankNat G hfg) =
      Nat.card (H1 G M) * p ^ k * Nat.card (H2 G (ZMod p)) ^ k := by
  induction k generalizing M with
  | zero =>
    have : Subsingleton M := (Nat.card_eq_one_iff_unique.1 (by simpa using hk)).1
    rw [Nat.card_of_subsingleton (0 : H0 G M), Nat.card_of_subsingleton (0 : H1 G M),
      Nat.card_of_subsingleton (0 : H2 G M)]
    simp
  | succ k ih =>
    have : Finite M := Nat.finite_of_card_ne_zero (hk ▸ pow_ne_zero _ hp.out.ne_zero)
    have : Nontrivial M := by
      rcases subsingleton_or_nontrivial M with hM | hM
      · exact absurd (hk ▸ Nat.card_of_subsingleton (0 : M))
          (Nat.one_lt_pow k.succ_ne_zero hp.out.one_lt).ne'
      · exact hM
    -- a `G`-stable subgroup `N` of order `p` with trivial action
    obtain ⟨N, hNcard, hNfix⟩ := exists_addSubgroup_natCard_eq_invariant_of_isProP hG
      (isPPrimaryTorsion_iff.1 (isPPrimaryTorsion_of_natCard_eq_pow hk))
    have hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N := fun g x hx ↦ (hNfix g x hx).symm ▸ hx
    let := N.restrictDistribMulAction hN
    let := N.quotientDistribMulAction hN
    have : ContinuousSMul G N := N.restrictDistribMulAction_continuousSMul hN
    have : ContinuousAdd M := ⟨continuous_of_discreteTopology⟩
    have : ContinuousSMul G (M ⧸ N) := N.quotientDistribMulAction_continuousSMul hN
    have hNtriv : ∀ (g : G) (a : N), g • a = a := fun g a ↦
      Subtype.ext ((N.restrictDistribMulAction_coe_smul hN g a).trans (hNfix g a a.2))
    -- the nine-term exact sequence
    -- `0 → H⁰(N) → H⁰(M) → H⁰(M ⧸ N) → H¹(N) → H¹(M) → H¹(M ⧸ N) → H²(N) → H²(M) → H²(M ⧸ N) → 0`,
    -- exact on the right because `H³(G, N) = 0`
    set S := DiscreteShortExact.ofAddSubgroup N hN
    have h3N : Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ G N)) := h3 N hNcard hNtriv
    have hex := AddMonoidHom.card_mul_card_mul_card_mul_card_mul_card_of_exact
      (explicitCoeff0 G N S.inclDistribMulActionHom) (explicitCoeff0 G M S.projDistribMulActionHom)
      S.explicitDelta0 (explicitCoeff1 G N S.inclDistribMulActionHom continuous_of_discreteTopology)
      (explicitCoeff1 G M S.projDistribMulActionHom continuous_of_discreteTopology)
      S.explicitDelta1 (explicitCoeff2 G N S.inclDistribMulActionHom continuous_of_discreteTopology)
      (explicitCoeff2 G M S.projDistribMulActionHom continuous_of_discreteTopology)
      S.explicitLongExact_H0A S.explicitLongExact_H0B S.explicitLongExact_H0C
      S.explicitLongExact_H1A S.explicitLongExact_H1B S.explicitLongExact_H1C
      S.explicitLongExact_H2A S.explicitLongExact_H2B
      S.explicitCoeff2_proj_surjective_of_subsingleton
    -- the orders of the terms attached to `N`: `H²(G, N)` is `H²(G, 𝔽_p)` through `N ≃+ ZMod p`
    have hH2N : Nat.card (H2 G N) = Nat.card (H2 G (ZMod p)) := by
      have : IsAddCyclic N := isAddCyclic_of_prime_card hNcard
      let e : N ≃+ ZMod p := addEquivOfAddCyclicCardEq (hNcard.trans (Nat.card_zmod p).symm)
      exact Nat.card_congr (explicitMap2Equiv G N G (ZMod p) (ContinuousMulEquiv.refl G) e
        continuous_of_discreteTopology continuous_of_discreteTopology
        (fun g n ↦ by rw [ContinuousMulEquiv.refl_apply, hNtriv, htriv])).toEquiv
    rw [H0_eq_top_of_smul_eq_self hNtriv, AddSubgroup.card_top, hNcard,
      hG.natCard_H1_of_natCard_eq hfg hNcard hNtriv, hH2N] at hex
    -- the quotient has order `p ^ k`, and the induction hypothesis applies to it
    have hQcard : Nat.card (M ⧸ N) = p ^ k := by
      have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N
      rw [hk, hNcard, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_right hp.out.pos h.symm
    have hQ := ih (M ⧸ N) hQcard
    have : Finite (H1 G (M ⧸ N)) := hfg.finite_H1
    -- assemble, cancelling the nonzero factor `p ^ d(G) * |H¹(G, M ⧸ N)|`
    generalize topologicalGeneratorRankNat G hfg = d at hex hQ ⊢
    refine Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos (pow_pos hp.out.pos d) (Nat.card_pos (α := H1 G (M ⧸ N)))) ?_
    calc p ^ d * Nat.card (H1 G (M ⧸ N)) *
          (Nat.card (H0 G M) * Nat.card (H2 G M) * p ^ ((k + 1) * d))
        = Nat.card (H0 G M) * p ^ d * Nat.card (H1 G (M ⧸ N)) * Nat.card (H2 G M) *
            p ^ ((k + 1) * d) := by ring
      _ = p * Nat.card (H0 G (M ⧸ N)) * Nat.card (H1 G M) * Nat.card (H2 G (ZMod p)) *
            Nat.card (H2 G (M ⧸ N)) * p ^ ((k + 1) * d) := by rw [hex]
      _ = p * Nat.card (H1 G M) * Nat.card (H2 G (ZMod p)) * p ^ d *
            (Nat.card (H0 G (M ⧸ N)) * Nat.card (H2 G (M ⧸ N)) * p ^ (k * d)) := by ring
      _ = p * Nat.card (H1 G M) * Nat.card (H2 G (ZMod p)) * p ^ d *
            (Nat.card (H1 G (M ⧸ N)) * p ^ k * Nat.card (H2 G (ZMod p)) ^ k) := by rw [hQ]
      _ = p ^ d * Nat.card (H1 G (M ⧸ N)) *
            (Nat.card (H1 G M) * p ^ (k + 1) * Nat.card (H2 G (ZMod p)) ^ (k + 1)) := by ring

section OpenSubgroup

variable (U : OpenSubgroup G)

/-- **The three-term Euler identity for the permutation module of an open subgroup, read through
Shapiro's lemma.** Let `G` be a topologically finitely generated profinite pro-`p` group whose
canonical `H³` vanishes on the discrete modules of order `p` with trivial action, let `𝔽_p` carry
the trivial action, and let `U` be an open subgroup. Then

```text
p * |H²(U, 𝔽_p)| * p ^ ([G : U] * d(G)) = p ^ d(U) * p ^ [G : U] * |H²(G, 𝔽_p)| ^ [G : U].
```

This is `TauCeti.IsProP.natCard_H0_mul_natCard_H2_mul_pow` for `Coind_U^G 𝔽_p`, of order
`p ^ [G : U]`, with `Hⁱ(G, Coind_U^G 𝔽_p) ≅ Hⁱ(U, 𝔽_p)` for `i = 0, 1, 2`. -/
theorem natCard_H2_openSubgroup_mul_pow :
    p * Nat.card (H2 U.toSubgroup (ZMod p)) *
        p ^ (U.toSubgroup.index * topologicalGeneratorRankNat G hfg) =
      p ^ topologicalGeneratorRankNat U.toSubgroup (hfg.of_openSubgroup U) *
        p ^ U.toSubgroup.index * Nat.card (H2 G (ZMod p)) ^ U.toSubgroup.index := by
  -- `U` is a topologically finitely generated profinite pro-`p` group acting trivially on `𝔽_p`
  have hUc : IsClosed (U.toSubgroup : Set G) := U.isClosed
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp hUc.isCompact
  have hU : IsProP p U.toSubgroup := hG.subgroup _
  have hUfg := hfg.of_openSubgroup U
  have htrivU : ∀ (u : U.toSubgroup) (m : ZMod p), u • m = m := fun u m ↦ htriv u m
  -- the Euler identity for `Coind_U^G 𝔽_p`, read through Shapiro's lemma in degrees `0`, `1`, `2`
  have key := hG.natCard_H0_mul_natCard_H2_mul_pow hfg htriv h3
    (DiscreteCoind G U.toSubgroup (ZMod p)) (k := U.toSubgroup.index)
    (by rw [DiscreteCoind.natCard_of_isOpen U.isOpen htrivU, Nat.card_zmod])
  rwa [Nat.card_congr (explicitShapiro2 G U.toSubgroup (ZMod p) hUc).toEquiv,
    Nat.card_congr (explicitShapiro1 G U.toSubgroup (ZMod p) hUc).toEquiv,
    Nat.card_congr (explicitShapiro0 G U.toSubgroup (ZMod p)).toEquiv,
    hU.natCard_H1_of_natCard_eq hUfg (Nat.card_zmod p) htrivU, H0_eq_top_of_smul_eq_self htrivU,
    AddSubgroup.card_top, Nat.card_zmod] at key

variable [Finite (H2 G (ZMod p))]

/-- **The three-term Euler formula.** Let `G` be a topologically finitely generated profinite
pro-`p` group whose canonical `H³` vanishes on the discrete modules of order `p` with trivial
action, with `H²(G, 𝔽_p)` finite for the trivial action on `𝔽_p`, and let `U` be an open subgroup.
Then, in `ℤ`,

```text
1 - d(U) + dim H²(U, 𝔽_p) = [G : U] * (1 - d(G) + dim H²(G, 𝔽_p)),
```

the identity `χ(U) = [G : U] * χ(G)` for `χ = dim H⁰ - dim H¹ + dim H²` with `𝔽_p` coefficients,
since `dim H⁰ = 1` and `dim H¹ = d` for the trivial module `𝔽_p`. The space `H²(U, 𝔽_p)` is finite
by `TauCeti.IsProP.finite_cohomFp_openSubgroup`. -/
theorem one_sub_topologicalGeneratorRankNat_add_finrank_H2 :
    (1 : ℤ) - topologicalGeneratorRankNat U.toSubgroup (hfg.of_openSubgroup U) +
        Module.finrank (ZMod p) (H2 U.toSubgroup (ZMod p)) =
      U.toSubgroup.index * (1 - topologicalGeneratorRankNat G hfg +
        Module.finrank (ZMod p) (H2 G (ZMod p))) := by
  -- `H²(U, 𝔽_p)` is finite because `H²(G, 𝔽_p)` is, by the finiteness dévissage
  have : Finite (cohomFp p G 2) := Finite.of_equiv _ (cohomFpAddEquivH2 p G htriv).symm.toEquiv
  have := hG.finite_cohomFp_openSubgroup (n := 2) U
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp U.isClosed.isCompact
  have : Finite (H2 U.toSubgroup (ZMod p)) :=
    Finite.of_equiv _ (cohomFpAddEquivH2 p U.toSubgroup fun u m ↦ htriv u m).toEquiv
  have : Module.Finite (ZMod p) (H2 G (ZMod p)) := Module.Finite.of_finite
  have : Module.Finite (ZMod p) (H2 U.toSubgroup (ZMod p)) := Module.Finite.of_finite
  have key := hG.natCard_H2_openSubgroup_mul_pow hfg htriv h3 U
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := H2 U.toSubgroup (ZMod p)),
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := H2 G (ZMod p)), Nat.card_zmod] at key
  -- compare exponents of `p`
  have key' : p ^ (1 + Module.finrank (ZMod p) (H2 U.toSubgroup (ZMod p)) +
        U.toSubgroup.index * topologicalGeneratorRankNat G hfg) =
      p ^ (topologicalGeneratorRankNat U.toSubgroup (hfg.of_openSubgroup U) + U.toSubgroup.index +
        Module.finrank (ZMod p) (H2 G (ZMod p)) * U.toSubgroup.index) := by
    simpa only [pow_add, pow_one, pow_mul] using key
  have h := congrArg (Nat.cast : ℕ → ℤ) (Nat.pow_right_injective hp.out.two_le key')
  push_cast at h
  linear_combination h

end OpenSubgroup

end IsProP

namespace CohomologicalDimensionLE

variable (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
  (htriv : ∀ (g : G) (x : ZMod p), g • x = x) (hcd : CohomologicalDimensionLE.{u} p G 2)
include hcd

omit hp [CompactSpace G] [TotallyDisconnectedSpace G] [DistribMulAction G (ZMod p)]
  [ContinuousSMul G (ZMod p)] in
/-- `cd_p G ≤ 2` kills the canonical `H³` of every discrete module of order `p`. -/
private theorem subsingleton_continuousCohomology_three (A : Type u) [AddCommGroup A]
    [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A]
    (hA : Nat.card A = p) :
    Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ G A)) :=
  cohomologicalDimensionLE_iff.mp hcd A
    (isPPrimaryTorsion_of_natCard_eq_pow (hA.trans (pow_one p).symm)) 3 (by norm_num)

include hG hfg htriv

/-- **The three-term Euler identity under `cd_p G ≤ 2`.** For a topologically finitely generated
profinite pro-`p` group `G` with `cd_p G ≤ 2`, the trivial action on `𝔽_p`, and a finite discrete
`G`-module `M` of order `p ^ k`,
`|H⁰(G, M)| * |H²(G, M)| * p ^ (k * d(G)) = |H¹(G, M)| * p ^ k * |H²(G, 𝔽_p)| ^ k`. -/
theorem natCard_H0_mul_natCard_H2_mul_pow (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] {k : ℕ}
    (hk : Nat.card M = p ^ k) :
    Nat.card (H0 G M) * Nat.card (H2 G M) * p ^ (k * topologicalGeneratorRankNat G hfg) =
      Nat.card (H1 G M) * p ^ k * Nat.card (H2 G (ZMod p)) ^ k :=
  hG.natCard_H0_mul_natCard_H2_mul_pow hfg htriv
    (fun A _ _ _ _ _ _ hA _ ↦ subsingleton_continuousCohomology_three hcd A hA) M hk

variable (U : OpenSubgroup G)

/-- **The three-term Euler identity for an open subgroup under `cd_p G ≤ 2`.** For a topologically
finitely generated profinite pro-`p` group `G` with `cd_p G ≤ 2`, the trivial action on `𝔽_p`, and
an open subgroup `U`,
`p * |H²(U, 𝔽_p)| * p ^ ([G : U] * d(G)) = p ^ d(U) * p ^ [G : U] * |H²(G, 𝔽_p)| ^ [G : U]`. -/
theorem natCard_H2_openSubgroup_mul_pow :
    p * Nat.card (H2 U.toSubgroup (ZMod p)) *
        p ^ (U.toSubgroup.index * topologicalGeneratorRankNat G hfg) =
      p ^ topologicalGeneratorRankNat U.toSubgroup (hfg.of_openSubgroup U) *
        p ^ U.toSubgroup.index * Nat.card (H2 G (ZMod p)) ^ U.toSubgroup.index :=
  hG.natCard_H2_openSubgroup_mul_pow hfg htriv
    (fun A _ _ _ _ _ _ hA _ ↦ subsingleton_continuousCohomology_three hcd A hA) U

variable [Finite (H2 G (ZMod p))]

/-- **The three-term Euler formula under `cd_p G ≤ 2`.** For a topologically finitely generated
profinite pro-`p` group `G` with `cd_p G ≤ 2` and `H²(G, 𝔽_p)` finite, and an open subgroup `U`,
in `ℤ`: `1 - d(U) + dim H²(U, 𝔽_p) = [G : U] * (1 - d(G) + dim H²(G, 𝔽_p))`. -/
theorem one_sub_topologicalGeneratorRankNat_add_finrank_H2 :
    (1 : ℤ) - topologicalGeneratorRankNat U.toSubgroup (hfg.of_openSubgroup U) +
        Module.finrank (ZMod p) (H2 U.toSubgroup (ZMod p)) =
      U.toSubgroup.index * (1 - topologicalGeneratorRankNat G hfg +
        Module.finrank (ZMod p) (H2 G (ZMod p))) :=
  hG.one_sub_topologicalGeneratorRankNat_add_finrank_H2 hfg htriv
    (fun A _ _ _ _ _ _ hA _ ↦ subsingleton_continuousCohomology_three hcd A hA) U

end CohomologicalDimensionLE

end TauCeti
