/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index.Exact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Comparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FixedPoints
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# The two-term Euler formula for pro-`p` groups

Let `G` be a topologically finitely generated pro-`p` group whose second cohomology vanishes on
the trivial modules of order `p`; a group with `cd_p G ≤ 1` is one, and so is a free pro-`p` group
of finite rank. For a finite discrete `p`-primary `G`-module `M` the two-term Euler characteristic
`|H⁰(G, M)| / |H¹(G, M)|` is multiplicative in the order of `M`:

```text
|H¹(G, M)| * |M| = |H⁰(G, M)| * |M| ^ d(G),
```

where `d(G)` is the topological generator rank. For `M = 𝔽_p` this is `|H¹(G, 𝔽_p)| = p ^ d(G)`,
the count of generators through the continuous dual (`TauCeti.IsProP.natCard_H1_of_natCard_eq`);
the general case follows by induction on `|M|` along the trivial filtration of
`TauCeti.exists_addSubgroup_natCard_eq_invariant_of_isProP`, each step being the six-term exact
sequence `0 → H⁰(N) → H⁰(M) → H⁰(M ⧸ N) → H¹(N) → H¹(M) → H¹(M ⧸ N) → H²(N) = 0` of the explicit
long exact sequence, read through the alternating identity
`AddMonoidHom.card_mul_card_mul_card_of_exact`.

Applied to the permutation module `Coind_U^G 𝔽_p` of an open subgroup `U`, which has order
`p ^ [G : U]`, Shapiro's lemma turns the identity into the **two-term Euler formula**

```text
d(U) + [G : U] = 1 + [G : U] * d(G),   that is   1 - d(U) = [G : U] * (1 - d(G)) in ℤ,
```

the case `cd_p G ≤ 1` of the Euler characteristic formula `χ(U) = [G : U] * χ(G)`. For a free
pro-`p` group of finite rank it becomes the Schreier index formula for the generator rank of an
open subgroup, `TauCeti.Topology.Algebra.Group.Profinite.Free.OpenSubgroup`.

## Main results

* `TauCeti.IsProP.natCard_H1_of_natCard_eq`: `|H¹(G, A)| = p ^ d(G)` for a trivial module `A` of
  order `p`.
* `TauCeti.IsProP.natCard_H1_mul_natCard`: the multiplicative Euler identity
  `|H¹(G, M)| * |M| = |H⁰(G, M)| * |M| ^ d(G)`.
* `TauCeti.IsProP.topologicalGeneratorRankNat_add_index` and
  `TauCeti.IsProP.one_sub_topologicalGeneratorRankNat_eq`: the two-term Euler formula for an open
  subgroup, in `ℕ` and in `ℤ`.
* `TauCeti.CohomologicalDimensionLE.natCard_H1_mul_natCard`,
  `TauCeti.CohomologicalDimensionLE.topologicalGeneratorRankNat_add_index`: the same under the
  hypothesis `cd_p G ≤ 1`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.1 and §4.2.
* H. Koch, *Galois Theory of `p`-Extensions*, §5.4 and Example 6.3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.2) and
  Ch. III §9.
-/

public section

namespace TauCeti

open ContCohomology

universe u v

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

namespace IsProP

section DegreeOne

/-- **`H¹` with trivial coefficients of order `p` counts generators.** For a topologically finitely
generated profinite pro-`p` group `G` and a discrete module `A` of order `p` with trivial action,
`H¹(G, A)` has `p ^ d(G)` elements: it is the group of continuous characters `G → A`, and the
additive group `A` is isomorphic to `ZMod p`. -/
theorem natCard_H1_of_natCard_eq (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
    {A : Type v} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] (hA : Nat.card A = p)
    (htriv : ∀ (g : G) (a : A), g • a = a) :
    Nat.card (H1 G A) = p ^ topologicalGeneratorRankNat G hfg := by
  -- `A` is cyclic of order `p`, hence isomorphic to `ZMod p`
  have : IsAddCyclic A := isAddCyclic_of_prime_card hA
  let e₀ : ZMod p ≃+ A := addEquivOfAddCyclicCardEq ((Nat.card_zmod p).trans hA.symm)
  let e : Multiplicative A ≃* Multiplicative (ZMod p) := AddEquiv.toMultiplicative e₀.symm
  -- composing with `e` identifies the continuous characters of `G` valued in `A` and in `ZMod p`
  let φ : (G →ₜ* Multiplicative A) ≃ (G →ₜ* Multiplicative (ZMod p)) :=
    { toFun := fun f => (⟨(e : Multiplicative A →* Multiplicative (ZMod p)),
        continuous_of_discreteTopology⟩ : Multiplicative A →ₜ* Multiplicative (ZMod p)).comp f
      invFun := fun f => (⟨(e.symm : Multiplicative (ZMod p) →* Multiplicative A),
        continuous_of_discreteTopology⟩ : Multiplicative (ZMod p) →ₜ* Multiplicative A).comp f
      left_inv := fun f => ContinuousMonoidHom.ext fun g => e.symm_apply_apply (f g)
      right_inv := fun f => ContinuousMonoidHom.ext fun g => e.apply_symm_apply (f g) }
  calc Nat.card (H1 G A) = Nat.card (continuousZModDual p G) :=
        Nat.card_congr ((H1EquivOfSmulEqSelf htriv).toEquiv.trans
          (Additive.toMul.trans (φ.trans Additive.ofMul)))
    _ = p ^ topologicalGeneratorRankNat G hfg := by
        have := finite_continuousZModDual (p := p) hfg
        rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
          hG.finrank_continuousZModDual_eq_topologicalGeneratorRankNat hfg]

end DegreeOne

section Euler

variable (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
  (h2 : ∀ (A : Type v) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
    (∀ (g : G) (a : A), g • a = a) → Subsingleton (H2 G A))
include hG hfg h2

/-- **The Euler characteristic of a finite `p`-primary module is multiplicative in its order.** Let
`G` be a topologically finitely generated profinite pro-`p` group whose explicit `H²` vanishes on
the discrete modules of order `p` with trivial action. Then for every finite discrete `p`-primary
`G`-module `M`,

```text
|H¹(G, M)| * |M| = |H⁰(G, M)| * |M| ^ d(G).
```

For `M` of order `p` with trivial action this is `|H¹(G, M)| = p ^ d(G)`; in general it is the
additivity of the Euler characteristic `|H⁰| / |H¹|` along the trivial filtration of `M`. -/
theorem natCard_H1_mul_natCard (M : Type v) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    (hM : IsPPrimaryTorsion p M) :
    Nat.card (H1 G M) * Nat.card M =
      Nat.card (H0 G M) * Nat.card M ^ topologicalGeneratorRankNat G hfg := by
  -- strong induction on the order of the coefficient module
  suffices H : ∀ (k : ℕ) (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
      Nat.card M = k → Nat.card (H1 G M) * Nat.card M =
        Nat.card (H0 G M) * Nat.card M ^ topologicalGeneratorRankNat G hfg from
    H _ M hM rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M _ _ _ _ _ _ hM hk
  rcases subsingleton_or_nontrivial M with hM₀ | _
  · rw [Nat.card_of_subsingleton (0 : M), Nat.card_of_subsingleton (0 : H1 G M),
      Nat.card_of_subsingleton (0 : H0 G M), one_pow]
  -- a `G`-stable subgroup `N` of order `p` with trivial action
  obtain ⟨N, hNcard, hNfix⟩ :=
    exists_addSubgroup_natCard_eq_invariant_of_isProP hG (isPPrimaryTorsion_iff.1 hM)
  have hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N := fun g x hx ↦ (hNfix g x hx).symm ▸ hx
  let := N.restrictDistribMulAction hN
  let := N.quotientDistribMulAction hN
  have : ContinuousSMul G N := N.restrictDistribMulAction_continuousSMul hN
  have : ContinuousAdd M := ⟨continuous_of_discreteTopology⟩
  have : ContinuousSMul G (M ⧸ N) := N.quotientDistribMulAction_continuousSMul hN
  have hNtriv : ∀ (g : G) (a : N), g • a = a := fun g a ↦
    Subtype.ext ((N.restrictDistribMulAction_coe_smul hN g a).trans (hNfix g a a.2))
  -- the six-term exact sequence `0 → H⁰(N) → H⁰(M) → H⁰(M ⧸ N) → H¹(N) → H¹(M) → H¹(M ⧸ N) → 0`,
  -- exact on the right because `H²(G, N) = 0`
  set S := DiscreteShortExact.ofAddSubgroup N hN
  have h2N : Subsingleton (H2 G N) := h2 N hNcard hNtriv
  have hsurj : Function.Surjective
      (explicitCoeff1 G M S.projDistribMulActionHom continuous_of_discreteTopology) := by
    rw [← AddMonoidHom.range_eq_top, S.explicitLongExact_H1C]
    exact eq_top_iff.2 fun x _ ↦ AddMonoidHom.mem_ker.2 (Subsingleton.elim _ _)
  have hex := AddMonoidHom.card_mul_card_mul_card_of_exact
    (explicitCoeff0 G N S.inclDistribMulActionHom) (explicitCoeff0 G M S.projDistribMulActionHom)
    S.explicitDelta0 (explicitCoeff1 G N S.inclDistribMulActionHom continuous_of_discreteTopology)
    (explicitCoeff1 G M S.projDistribMulActionHom continuous_of_discreteTopology)
    S.explicitLongExact_H0A S.explicitLongExact_H0B S.explicitLongExact_H0C
    S.explicitLongExact_H1A S.explicitLongExact_H1B hsurj
  -- the orders of the terms attached to `N`, and the induction hypothesis for `M ⧸ N`
  rw [H0_eq_top_of_smul_eq_self hNtriv, AddSubgroup.card_top, hNcard,
    hG.natCard_H1_of_natCard_eq hfg hNcard hNtriv] at hex
  have hQ := ih _ ?_ (M ⧸ N)
    (hM.of_surjective (QuotientAddGroup.mk' N) (QuotientAddGroup.mk'_surjective N)) rfl
  swap
  · rw [← hk, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N, hNcard]
    exact lt_mul_of_one_lt_right Nat.card_pos hp.out.one_lt
  have hMcard : Nat.card M = Nat.card (M ⧸ N) * p := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N, hNcard]
  -- assemble, cancelling the nonzero factor `p * |H⁰(G, M ⧸ N)|`
  generalize topologicalGeneratorRankNat G hfg = d at hex hQ ⊢
  refine Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos hp.out.pos (Nat.card_pos (α := H0 G (M ⧸ N)))) ?_
  calc p * Nat.card (H0 G (M ⧸ N)) * (Nat.card (H1 G M) * Nat.card M)
      = p * Nat.card (H0 G (M ⧸ N)) * Nat.card (H1 G M) * (Nat.card (M ⧸ N) * p) := by
        rw [hMcard]; ring
    _ = Nat.card (H0 G M) * p ^ d * Nat.card (H1 G (M ⧸ N)) * (Nat.card (M ⧸ N) * p) := by
        rw [hex]
    _ = Nat.card (H0 G M) * p ^ d * (Nat.card (H1 G (M ⧸ N)) * Nat.card (M ⧸ N)) * p := by
        ring
    _ = Nat.card (H0 G M) * p ^ d * (Nat.card (H0 G (M ⧸ N)) * Nat.card (M ⧸ N) ^ d) * p := by
        rw [hQ]
    _ = p * Nat.card (H0 G (M ⧸ N)) * (Nat.card (H0 G M) * Nat.card M ^ d) := by
        rw [hMcard]; ring

end Euler

section OpenSubgroup

variable (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
  (h2 : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
    (∀ (g : G) (a : A), g • a = a) → Subsingleton (H2 G A))
include hG hfg h2

/-- **The two-term Euler formula.** Let `G` be a topologically finitely generated profinite pro-`p`
group whose explicit `H²` vanishes on the discrete modules of order `p` with trivial action, and
let `U` be an open subgroup. Then `d(U) + [G : U] = 1 + [G : U] * d(G)`, the natural-number form
of `1 - d(U) = [G : U] * (1 - d(G))`.

The proof applies `TauCeti.IsProP.natCard_H1_mul_natCard` to the permutation module
`Coind_U^G 𝔽_p`, of order `p ^ [G : U]`, and reads both sides through Shapiro's lemma. -/
theorem topologicalGeneratorRankNat_add_index (U : OpenSubgroup G) :
    topologicalGeneratorRankNat U.toSubgroup (hfg.of_openSubgroup U) + U.toSubgroup.index =
      1 + U.toSubgroup.index * topologicalGeneratorRankNat G hfg := by
  -- `U` is a topologically finitely generated profinite pro-`p` group
  have hUc : IsClosed (U.toSubgroup : Set G) := U.isClosed
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp hUc.isCompact
  have hU : IsProP p U.toSubgroup := hG.subgroup _
  have hUfg := hfg.of_openSubgroup U
  -- the trivial `U`-module `𝔽_p`
  let : DistribMulAction U.toSubgroup (ZMod p) :=
    DistribMulAction.compHom (ZMod p) (1 : U.toSubgroup →* (ZMod p)ˣ)
  have htriv : ∀ (u : U.toSubgroup) (m : ZMod p), u • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul U.toSubgroup (ZMod p) :=
    ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  -- the Euler identity for `Coind_U^G 𝔽_p`, read through Shapiro's lemma in degrees `0` and `1`
  have key := hG.natCard_H1_mul_natCard hfg h2 (DiscreteCoind G U.toSubgroup (ZMod p))
    (isPPrimaryTorsion_discreteCoind G U.toSubgroup (ZMod p)
      (isPPrimaryTorsion_of_natCard_eq_pow ((Nat.card_zmod p).trans (pow_one p).symm)))
  rw [Nat.card_congr (explicitShapiro1 G U.toSubgroup (ZMod p) hUc).toEquiv,
    Nat.card_congr (explicitShapiro0 G U.toSubgroup (ZMod p)).toEquiv,
    DiscreteCoind.natCard_of_isOpen U.isOpen htriv, Nat.card_zmod,
    hU.natCard_H1_of_natCard_eq hUfg (Nat.card_zmod p) htriv, H0_eq_top_of_smul_eq_self htriv,
    AddSubgroup.card_top, Nat.card_zmod, ← pow_mul, ← pow_add, ← pow_succ'] at key
  have := Nat.pow_right_injective hp.out.two_le key
  omega

/-- **The two-term Euler formula, in `ℤ`.** Under the hypotheses of
`TauCeti.IsProP.topologicalGeneratorRankNat_add_index`, `1 - d(U) = [G : U] * (1 - d(G))`. -/
theorem one_sub_topologicalGeneratorRankNat_eq (U : OpenSubgroup G) :
    (1 : ℤ) - topologicalGeneratorRankNat U.toSubgroup (hfg.of_openSubgroup U) =
      U.toSubgroup.index * (1 - topologicalGeneratorRankNat G hfg) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (hG.topologicalGeneratorRankNat_add_index hfg h2 U)
  push_cast at h
  linarith

end OpenSubgroup

end IsProP

namespace CohomologicalDimensionLE

variable (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
  (hcd : CohomologicalDimensionLE.{u} p G 1)
include hG hfg hcd

/-- **The Euler characteristic of a finite `p`-primary module under `cd_p G ≤ 1`.** For a
topologically finitely generated profinite pro-`p` group `G` with `cd_p G ≤ 1` and a finite
discrete `p`-primary `G`-module `M`, `|H¹(G, M)| * |M| = |H⁰(G, M)| * |M| ^ d(G)`. -/
theorem natCard_H1_mul_natCard (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    (hM : IsPPrimaryTorsion p M) :
    Nat.card (H1 G M) * Nat.card M =
      Nat.card (H0 G M) * Nat.card M ^ topologicalGeneratorRankNat G hfg :=
  hG.natCard_H1_mul_natCard hfg (fun A _ _ _ _ _ _ hA _ ↦ hcd.subsingleton_H2 A
    (isPPrimaryTorsion_of_natCard_eq_pow (hA.trans (pow_one p).symm))) M hM

/-- **The two-term Euler formula under `cd_p G ≤ 1`.** For a topologically finitely generated
profinite pro-`p` group `G` with `cd_p G ≤ 1` and an open subgroup `U`,
`d(U) + [G : U] = 1 + [G : U] * d(G)`. -/
theorem topologicalGeneratorRankNat_add_index (U : OpenSubgroup G) :
    topologicalGeneratorRankNat U.toSubgroup (hfg.of_openSubgroup U) + U.toSubgroup.index =
      1 + U.toSubgroup.index * topologicalGeneratorRankNat G hfg :=
  hG.topologicalGeneratorRankNat_add_index hfg (fun A _ _ _ _ _ _ hA _ ↦ hcd.subsingleton_H2 A
    (isPPrimaryTorsion_of_natCard_eq_pow (hA.trans (pow_one p).symm))) U

/-- **The two-term Euler formula under `cd_p G ≤ 1`, in `ℤ`:** `1 - d(U) = [G : U] * (1 - d(G))`
for an open subgroup `U` of a topologically finitely generated profinite pro-`p` group with
`cd_p G ≤ 1`. -/
theorem one_sub_topologicalGeneratorRankNat_eq (U : OpenSubgroup G) :
    (1 : ℤ) - topologicalGeneratorRankNat U.toSubgroup (hfg.of_openSubgroup U) =
      U.toSubgroup.index * (1 - topologicalGeneratorRankNat G hfg) :=
  hG.one_sub_topologicalGeneratorRankNat_eq hfg (fun A _ _ _ _ _ _ hA _ ↦ hcd.subsingleton_H2 A
    (isPPrimaryTorsion_of_natCard_eq_pow (hA.trans (pow_one p).symm))) U

end CohomologicalDimensionLE

end TauCeti
