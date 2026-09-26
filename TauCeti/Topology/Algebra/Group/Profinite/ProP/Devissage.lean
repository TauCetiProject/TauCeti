/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FixedPoints
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# Dévissage of finite `p`-primary coefficients for pro-`p` groups

Let `G` be a compact pro-`p` group and `n` a degree. If the continuous cohomology `Hⁿ(G, A)`
vanishes for every discrete `G`-module `A` of order `p` with **trivial** action, then it vanishes
for every finite discrete `p`-primary `G`-module `M`, whatever the action. This is the pro-`p` case
of dévissage (NSW (3.3.2), final clause; Koch takes it as the definition of cohomological dimension
for pro-`p` groups). The test class consists of the trivial modules of order `p`; the file also
records the formulation over all finite trivial modules killed by `p`, that is over the finite
elementary abelian `p`-groups with trivial action, as a corollary and as an equivalence. It does not
identify the trivial modules of order `p` with the single module `𝔽_p`.

The result combines the trivial-filtration theorem
`TauCeti.exists_addSubgroup_natCard_eq_invariant_of_isProP`, which places a `G`-stable subgroup
of order `p` with trivial action inside every nonzero finite `p`-primary module, with exactness
of the long exact sequence at `Hⁿ(G, M)`
(`TauCeti.ContCohomology.DiscreteShortExact.longExact_exact₂`), which passes vanishing from that
subgroup and the quotient by it to `M`. The zero module is covered by
`TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_of_subsingleton`.

The coefficients range over finite modules only. Passing from finite `p`-primary coefficients to
all discrete `p`-primary torsion coefficients, as in the vanishing predicate
`TauCeti.CohomologicalDimensionLE`, is a separate reduction that rests on the compatibility of
continuous cohomology with filtered colimits of coefficients, and is not part of this file.

## Main results

* `TauCeti.IsProP.subsingleton_continuousCohomology_of_forall_natCard_eq_smul_eq_self`: for a
  compact pro-`p` group, vanishing of `Hⁿ` on the trivial modules of order `p` gives vanishing on
  every finite discrete `p`-primary module.
* `TauCeti.IsProP.subsingleton_continuousCohomology_of_forall_smul_eq_self`: the same with the
  finite trivial modules killed by `p` as test class.
* `TauCeti.IsProP.forall_subsingleton_continuousCohomology_iff_forall_natCard_eq` and
  `TauCeti.IsProP.forall_subsingleton_continuousCohomology_iff`: vanishing on every finite discrete
  `p`-primary module is equivalent to vanishing on either test class.

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
  -- strong induction on the order of the coefficient module
  suffices H : ∀ (k : ℕ) (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
      Nat.card M = k → Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G M)) from
    H _ M hM rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M _ _ _ _ _ _ hM hk
  rcases subsingleton_or_nontrivial M with hM₀ | _
  · have : Subsingleton (ofDiscreteModule ℤ G M) := hM₀
    exact ContinuousCohomology.subsingleton_continuousCohomology_of_subsingleton _ n
  -- a `G`-stable subgroup `N` of order `p` with trivial action
  obtain ⟨N, hNcard, hNfix⟩ :=
    exists_addSubgroup_natCard_eq_invariant_of_isProP hG (isPPrimaryTorsion_iff.1 hM)
  have hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N := fun g x hx ↦ (hNfix g x hx).symm ▸ hx
  let := N.restrictDistribMulAction hN
  let := N.quotientDistribMulAction hN
  have : ContinuousSMul G N := N.restrictDistribMulAction_continuousSMul hN
  have : ContinuousAdd M := ⟨continuous_of_discreteTopology⟩
  have : ContinuousSMul G (M ⧸ N) := N.quotientDistribMulAction_continuousSMul hN
  -- the two outer terms of `Hⁿ(G, N) → Hⁿ(G, M) → Hⁿ(G, M ⧸ N)` vanish
  have : Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G N)) :=
    h N hNcard fun g a ↦
      Subtype.ext ((N.restrictDistribMulAction_coe_smul hN g a).trans (hNfix g a a.2))
  have : Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G (M ⧸ N))) := by
    refine ih _ ?_ (M ⧸ N)
      (hM.of_surjective (QuotientAddGroup.mk' N) (QuotientAddGroup.mk'_surjective N)) rfl
    rw [← hk, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N, hNcard]
    exact lt_mul_of_one_lt_right Nat.card_pos hp.out.one_lt
  -- exactness in the middle
  have hex := (DiscreteShortExact.ofAddSubgroup N hN).longExact_exact₂ n
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨a, rfl⟩ := (hex x).1 (Subsingleton.elim _ _)
  rw [Subsingleton.elim a 0, map_zero]

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
  ⟨fun H A _ _ _ _ _ _ hA _ ↦
    H A (isPPrimaryTorsion_iff.2 fun a ↦ ⟨1, by rw [pow_one, ← hA]; exact card_nsmul_eq_zero'⟩),
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

end TauCeti
