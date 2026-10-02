/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# The dévissage induction principle for finite discrete modules

Let `G` be a topological group and `Q` a class of discrete `G`-modules which is closed under
equivariant surjections. Suppose that every nontrivial finite module in `Q` contains a subgroup
`P` on which `G` acts trivially and whose order lies in a fixed set `S` of integers `> 1`. Then
every finite module `M` in `Q` is built from such trivial modules by extensions: `M ⧸ P` is again
in `Q`, of smaller order. Hence a property of discrete `G`-modules which holds for the zero module
and passes along each extension `0 → P → M → M ⧸ P → 0` from `M ⧸ P` to `M` holds for every
finite module in `Q`. This is the **dévissage induction principle**
`TauCeti.ContCohomology.finite_induction_of_exists_addSubgroup`.

It is the common skeleton of two dévissages. For a pro-`p` group and the `p`-primary modules, the
subgroup `P` of order `p` comes from the trivial-filtration theorem
(`TauCeti.IsProP.finite_pPrimary_induction`). For the trivial modules killed by `N`, it comes
from Cauchy's theorem, and has prime order dividing `N`
(`TauCeti.ContinuousCohomology.finite_continuousCohomology_of_forall_smul_eq_self`).

## Main results

* `TauCeti.ContCohomology.finite_induction_of_exists_addSubgroup`: the dévissage induction
  principle.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Proposition (3.3.2).
-/

public section

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The dévissage induction principle.** Let `Q` be a class of discrete `G`-modules closed
under equivariant surjections, and `S` a set of natural numbers `> 1`. Suppose that every
nontrivial finite discrete `G`-module in `Q` has an additive subgroup of order in `S` on which `G`
acts trivially. Let `motive` be a property of discrete `G`-modules which holds for the zero module
and is closed under extensions by such a subgroup: for every short exact sequence `0 → A → B → C →
0` of finite discrete `G`-modules with `B` and `C` in `Q`, and `A` of order in `S` with trivial
action, `motive C` implies `motive B`. Then `motive` holds for every finite discrete `G`-module in
`Q`. -/
theorem finite_induction_of_exists_addSubgroup
    {motive : ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M], Prop}
    (Q : ∀ (M : Type u) [AddCommGroup M] [DistribMulAction G M], Prop) (S : ℕ → Prop)
    (one_lt : ∀ k, S k → 1 < k)
    (map : ∀ (M M' : Type u) [AddCommGroup M] [DistribMulAction G M] [AddCommGroup M']
      [DistribMulAction G M'] (f : M →+[G] M'), Function.Surjective f → Q M → Q M')
    (exists_addSubgroup : ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M]
      [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M] [Nontrivial M],
      Q M → ∃ P : AddSubgroup M, S (Nat.card P) ∧ ∀ g : G, ∀ x ∈ P, g • x = x)
    (zero : ∀ (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M] [Subsingleton M], motive M)
    (extension : ∀ (A B C : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A] [AddCommGroup B] [TopologicalSpace B]
      [DiscreteTopology B] [DistribMulAction G B] [ContinuousSMul G B] [Finite B] [AddCommGroup C]
      [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C] [ContinuousSMul G C]
      [Finite C], DiscreteShortExact G A B C → S (Nat.card A) → (∀ (g : G) (a : A), g • a = a) →
      Q B → Q C → motive C → motive B)
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : Q M) :
    motive M := by
  -- strong induction on the order of the coefficient module
  suffices H : ∀ (k : ℕ) (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction G M] [ContinuousSMul G M] [Finite M], Q M → Nat.card M = k → motive M from
    H _ M hM rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M _ _ _ _ _ _ hM hk
  rcases subsingleton_or_nontrivial M with hM₀ | _
  · exact zero M
  -- a subgroup `P` of order in `S` with trivial action, hence `G`-stable
  obtain ⟨P, hPS, hPfix⟩ := exists_addSubgroup M hM
  have hP : ∀ g : G, ∀ x ∈ P, g • x ∈ P := fun g x hx ↦ (hPfix g x hx).symm ▸ hx
  let := P.restrictDistribMulAction hP
  let := P.quotientDistribMulAction hP
  have : ContinuousSMul G P := P.restrictDistribMulAction_continuousSMul hP
  have : ContinuousAdd M := ⟨continuous_of_discreteTopology⟩
  have : ContinuousSMul G (M ⧸ P) := P.quotientDistribMulAction_continuousSMul hP
  set E := DiscreteShortExact.ofAddSubgroup P hP
  have hMP : Q (M ⧸ P) :=
    map M (M ⧸ P) E.projDistribMulActionHom E.projDistribMulActionHom_surjective hM
  refine extension P M (M ⧸ P) E hPS
    (fun g a ↦ Subtype.ext ((P.restrictDistribMulAction_coe_smul hP g a).trans (hPfix g a a.2)))
    hM hMP ?_
  -- the quotient has smaller order, and the induction hypothesis applies to it
  refine ih _ ?_ (M ⧸ P) hMP rfl
  rw [← hk, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup P]
  exact lt_mul_of_one_lt_right Nat.card_pos (one_lt _ hPS)

end TauCeti.ContCohomology
