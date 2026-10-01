/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index.Exact
public import TauCeti.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FixedPoints
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup
import TauCeti.LinearAlgebra.Exact

/-!
# Dévissage of finite `p`-primary coefficients for pro-`p` groups

Let `G` be a pro-`p` group. A finite discrete `p`-primary `G`-module `M` is built from
copies of `𝔽_p` with trivial action: by the trivial-filtration theorem
`TauCeti.exists_addSubgroup_natCard_eq_invariant_of_isProP`, every nonzero such `M` contains a
`G`-stable subgroup `N` of order `p` on which `G` acts trivially, and `M ⧸ N` is again finite and
`p`-primary, of smaller order. Hence a property of finite discrete `p`-primary `G`-modules which
holds for the zero module and for the trivial modules of order `p`, and which passes from `N` and
`M ⧸ N` to `M` for every such extension, holds for every `M`. This is the **dévissage induction
principle** `TauCeti.IsProP.finite_pPrimary_induction`, the pro-`p` case of dévissage
(NSW (3.3.2), final clause; Koch takes it as the definition of cohomological dimension for pro-`p`
groups). The principle itself needs no topology on `G` beyond the pro-`p` hypothesis; compactness
enters only through the long exact cohomology sequence in the corollaries below.

For a compact pro-`p` group `G`, two properties of the continuous cohomology `Hⁿ(G, -)` in a fixed
degree `n` are run through it, using exactness of the long exact sequence at `Hⁿ(G, M)`
(`TauCeti.ContCohomology.DiscreteShortExact.longExact_exact₂`), which passes a property from
`Hⁿ(G, N)` and `Hⁿ(G, M ⧸ N)` to `Hⁿ(G, M)`. If `Hⁿ(G, A)` vanishes for every discrete `G`-module
`A` of order `p` with **trivial** action, then it vanishes for every finite discrete `p`-primary
`G`-module `M`, whatever the action; and if `Hⁿ(G, A)` is finite for every such `A`, then
`Hⁿ(G, M)` is finite for every such `M`. The test class consists of the trivial modules of order
`p`; the file also records the vanishing statement over all finite trivial modules killed by `p`,
that is over the finite elementary abelian `p`-groups with trivial action, as a corollary and as an
equivalence. It does not identify the trivial modules of order `p` with the single module `𝔽_p`.

The coefficients range over finite modules only. Passing from finite `p`-primary coefficients to
all discrete `p`-primary torsion coefficients, as in the vanishing predicate
`TauCeti.CohomologicalDimensionLE`, is a separate reduction that rests on the compatibility of
continuous cohomology with filtered colimits of coefficients, and is not part of this file.

## Main results

* `TauCeti.IsProP.finite_pPrimary_induction`: **the dévissage induction principle**: a property of
  finite discrete `p`-primary modules of a pro-`p` group holds everywhere once it holds for the
  zero module and the trivial modules of order `p` and is closed under extensions by a trivial
  module of order `p`.
* `TauCeti.IsProP.subsingleton_continuousCohomology_of_forall_natCard_eq_smul_eq_self`: for a
  compact pro-`p` group, vanishing of `Hⁿ` on the trivial modules of order `p` gives vanishing on
  every finite discrete `p`-primary module.
* `TauCeti.IsProP.subsingleton_continuousCohomology_of_forall_smul_eq_self`: the same with the
  finite trivial modules killed by `p` as test class.
* `TauCeti.IsProP.forall_subsingleton_continuousCohomology_iff_forall_natCard_eq` and
  `TauCeti.IsProP.forall_subsingleton_continuousCohomology_iff`: vanishing on every finite discrete
  `p`-primary module is equivalent to vanishing on either test class.
* `TauCeti.IsProP.finite_continuousCohomology_of_forall_natCard_eq_smul_eq_self`: for a compact
  pro-`p` group, finiteness of `Hⁿ` on the trivial modules of order `p` gives finiteness on every
  finite discrete `p`-primary module.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Proposition (3.3.2).
* J.-P. Serre, *Galois Cohomology*, Chapter I, §3.3 and §4.1.
* H. Koch, *Galois Theory of `p`-Extensions*, Springer (2002), Definition 5.1.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- **The dévissage induction principle for pro-`p` groups.** Let `G` be a pro-`p` group and let
`motive` be a property of discrete `G`-modules. Suppose that `motive` holds for the zero module and
for every discrete `G`-module of order `p` with trivial action, and that `motive` is closed under
extensions by such a module: for every short exact sequence `0 → A → B → C → 0` of finite discrete
`p`-primary `G`-modules with `A` of order `p` and trivial action, `motive A` and `motive C` imply
`motive B`. Then `motive` holds for every finite discrete `p`-primary `G`-module. -/
theorem IsProP.finite_pPrimary_induction (hG : IsProP p G)
    {motive : ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M], Prop}
    (zero : ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M] [Subsingleton M], motive M)
    (prime : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
      (∀ (g : G) (a : A), g • a = a) → motive A)
    (extension : ∀ (A B C : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A] [AddCommGroup B] [TopologicalSpace B]
      [DiscreteTopology B] [DistribMulAction G B] [ContinuousSMul G B] [Finite B] [AddCommGroup C]
      [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C] [ContinuousSMul G C]
      [Finite C], DiscreteShortExact G A B C → Nat.card A = p → (∀ (g : G) (a : A), g • a = a) →
      IsPPrimaryTorsion p A → IsPPrimaryTorsion p B → IsPPrimaryTorsion p C →
      motive A → motive C → motive B)
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : IsPPrimaryTorsion p M) :
    motive M := by
  -- strong induction on the order of the coefficient module
  suffices H : ∀ (k : ℕ) (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
      Nat.card M = k → motive M from
    H _ M hM rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M _ _ _ _ _ _ hM hk
  rcases subsingleton_or_nontrivial M with hM₀ | _
  · exact zero M
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
  have hMN : IsPPrimaryTorsion p (M ⧸ N) :=
    hM.of_surjective (QuotientAddGroup.mk' N) (QuotientAddGroup.mk'_surjective N)
  refine extension N M (M ⧸ N) (DiscreteShortExact.ofAddSubgroup N hN) hNcard hNtriv
    (isPPrimaryTorsion_of_natCard_eq_pow (hNcard.trans (pow_one p).symm)) hM hMN
    (prime N hNcard hNtriv) ?_
  -- the quotient has smaller order, and the induction hypothesis applies to it
  refine ih _ ?_ (M ⧸ N) hMN rfl
  rw [← hk, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N, hNcard]
  exact lt_mul_of_one_lt_right Nat.card_pos hp.out.one_lt

/-- **Dévissage for pro-`p` groups.** Let `G` be a compact pro-`p` group. If `Hⁿ(G, A)` vanishes
for every discrete `G`-module `A` of order `p` on which `G` acts trivially, then `Hⁿ(G, M)`
vanishes for every finite discrete `p`-primary `G`-module `M`. -/
theorem IsProP.subsingleton_continuousCohomology_of_forall_natCard_eq_smul_eq_self
    (hG : IsProP p G) {n : ℕ}
    (h : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
      (∀ (g : G) (a : A), g • a = a) →
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G A)))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : IsPPrimaryTorsion p M) :
    Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G M)) := by
  refine hG.finite_pPrimary_induction
    (motive := fun M _ _ _ _ _ ↦ Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G M)))
    (fun M _ _ _ _ _ _ ↦
      ContinuousCohomology.subsingleton_continuousCohomology_ofDiscreteModule_of_subsingleton M n)
    h (fun A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ _ _ _ _ hA hC ↦ ?_) M hM
  · -- exactness in the middle of `Hⁿ(G, A) → Hⁿ(G, B) → Hⁿ(G, C)`, with trivial outer terms
    exact subsingleton_of_exact (S.longExact_exact₂ n)

/-- **Dévissage for pro-`p` groups, elementary abelian test class.** Let `G` be a compact pro-`p`
group. If `Hⁿ(G, A)` vanishes for every finite discrete `G`-module `A` killed by `p` on which `G`
acts trivially, then `Hⁿ(G, M)` vanishes for every finite discrete `p`-primary `G`-module `M`. -/
theorem IsProP.subsingleton_continuousCohomology_of_forall_smul_eq_self (hG : IsProP p G)
    {n : ℕ}
    (h : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A], (∀ a : A, p • a = 0) →
      (∀ (g : G) (a : A), g • a = a) →
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G A)))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : IsPPrimaryTorsion p M) :
    Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G M)) :=
  hG.subsingleton_continuousCohomology_of_forall_natCard_eq_smul_eq_self
    (fun A _ _ _ _ _ _ hA ↦ h A fun a ↦ by rw [← hA]; exact card_nsmul_eq_zero') M hM

/-- **Dévissage for pro-`p` groups, as an equivalence.** For a compact pro-`p` group `G` and a
degree `n`, the continuous cohomology `Hⁿ(G, M)` vanishes for every finite discrete `p`-primary
`G`-module `M` if and only if it vanishes for every discrete `G`-module of order `p` on which `G`
acts trivially. -/
theorem IsProP.forall_subsingleton_continuousCohomology_iff_forall_natCard_eq (hG : IsProP p G)
    (n : ℕ) :
    (∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G M))) ↔
    ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
      (∀ (g : G) (a : A), g • a = a) →
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G A)) :=
  ⟨fun H A _ _ _ _ _ _ hA _ ↦ H A (isPPrimaryTorsion_of_natCard_eq_pow (hA.trans (pow_one p).symm)),
    fun h M _ _ _ _ _ _ hM ↦
      hG.subsingleton_continuousCohomology_of_forall_natCard_eq_smul_eq_self h M hM⟩

/-- **Dévissage for pro-`p` groups, as an equivalence with the elementary abelian test class.**
For a compact pro-`p` group `G` and a degree `n`, the continuous cohomology `Hⁿ(G, M)` vanishes
for every finite discrete `p`-primary `G`-module `M` if and only if it vanishes for every finite
discrete `G`-module killed by `p` on which `G` acts trivially. -/
theorem IsProP.forall_subsingleton_continuousCohomology_iff (hG : IsProP p G) (n : ℕ) :
    (∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G M))) ↔
    ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A], (∀ a : A, p • a = 0) →
      (∀ (g : G) (a : A), g • a = a) →
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G A)) :=
  ⟨fun H A _ _ _ _ _ _ hA _ ↦
    H A (isPPrimaryTorsion_iff.2 fun a ↦ ⟨1, by rw [pow_one]; exact hA a⟩),
    fun h M _ _ _ _ _ _ hM ↦ hG.subsingleton_continuousCohomology_of_forall_smul_eq_self h M hM⟩

/-- **Finiteness dévissage for pro-`p` groups.** Let `G` be a compact pro-`p` group. If `Hⁿ(G, A)`
is finite for every discrete `G`-module `A` of order `p` on which `G` acts trivially, then
`Hⁿ(G, M)` is finite for every finite discrete `p`-primary `G`-module `M`. -/
theorem IsProP.finite_continuousCohomology_of_forall_natCard_eq_smul_eq_self (hG : IsProP p G)
    {n : ℕ}
    (h : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
      (∀ (g : G) (a : A), g • a = a) →
      Finite (continuousCohomology n (ofDiscreteModule ℤ G A)))
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : IsPPrimaryTorsion p M) :
    Finite (continuousCohomology n (ofDiscreteModule ℤ G M)) := by
  refine hG.finite_pPrimary_induction
    (motive := fun M _ _ _ _ _ ↦ Finite (continuousCohomology n (ofDiscreteModule ℤ G M)))
    (fun M _ _ _ _ _ _ ↦
      have :=
        ContinuousCohomology.subsingleton_continuousCohomology_ofDiscreteModule_of_subsingleton
          (R := ℤ) (G := G) M n
      Finite.of_subsingleton)
    h (fun A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ _ _ _ _ hA hC ↦ ?_) M hM
  · -- exactness in the middle of `Hⁿ(G, A) → Hⁿ(G, B) → Hⁿ(G, C)`, with finite outer terms
    exact (S.longExact_exact₂ n).finite

end TauCeti
