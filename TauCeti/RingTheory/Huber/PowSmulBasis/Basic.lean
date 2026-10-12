/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
import TauCeti.Topology.Algebra.Nonarchimedean.SubmodulesBasis
public import TauCeti.Topology.Algebra.Ring.Subring

/-!
# The `ϖⁿ • M₀` submodules basis, and the `A`-module topology it induces

Let `A` be a Tate ring, `A₀` a ring of definition, `ϖ ∈ A₀` a pseudouniformiser, and `M₀` an
`A₀`-submodule of an `A`-module `M` with `A · M₀ = M`. This file exhibits the family `ϖⁿ • M₀`
as a `SubmodulesBasis`, which is Mathlib's machinery for turning such a family into a topology;
`SubmodulesBasis.topology` and `.nonarchimedean` then apply.

The result that the family is a neighbourhood basis at `0` says nothing about `ϖ`: it is proved
for an arbitrary `SubmodulesBasis` in
`TauCeti/Topology/Algebra/Nonarchimedean/SubmodulesBasis.lean`, and
`hasBasis_nhds_zero_pow_smul` specializes it to this family. The abstract result that mutually
cofinal families induce the same topology is `SubmodulesBasis.topology_eq`;
`submodulesBasis_pow_smul_topology_eq` combines it with the lattice- and
pseudouniformiser-cofinality lemmas for open subrings.

**Two of Proposition 6.18(1)'s clauses are established for the induced topology** — that it is an
`A`-module topology (`powSmulModuleFilterBasis`, since `SubmodulesBasis.toModuleFilterBasis`
gives only an `A₀`-module one) and that it is first countable at `0`
(`isCountablyGenerated_nhds_zero`).

**Completeness and uniqueness are not.** 6.18(1) asserts the topology is the *unique* complete
first-countable `A`-module topology on a finitely generated module; neither half is proved below,
so this is a construction of that topology's neighbourhood basis together with three of its
properties, not an identification with the topology 6.18(1) characterises. What *is* proved is
the weaker statement that the construction does not depend on the lattice or the
pseudouniformiser it starts from (`submodulesBasis_pow_smul_topology_eq`): two finitely generated
lattices spanning `M`, and two pseudouniformisers lying in the fixed ring of definition, give the
same topology. That is well-definedness of Remark 6.19's recipe in those two choices, for a fixed
ring of definition `A₀`: the remark chooses `A₀` as well, and independence of that choice is not
proved here. Nor is it 6.18(1)'s uniqueness, which quantifies over topologies never presented by a
lattice at all.

**The hypotheses are weaker than Wedhorn's.** Remark 6.19 assumes `A` noetherian and `M₀`
finitely generated. The basis and topology declarations use neither — only `A · M₀ = M`.
The absorption and cofinality lemmas in `TauCeti.Topology.Algebra.Ring.Subring` work over any
open subring and need only separately continuous multiplication on `A`. Their finite-generation
hypotheses enter when one exponent must serve a whole submodule. The topology comparison here
uses both spanning and finite generation for both lattices. `A` noetherian is used nowhere.

## Main results

* `TauCeti.Huber.PairOfDefinition.submodulesBasis_pow_smul`: the family is a `SubmodulesBasis`.
* `TauCeti.Huber.PairOfDefinition.powSmulModuleFilterBasis`: the same family as a filter basis
  for scalars from `A`, not just from `A₀` — Proposition 6.18(1)'s `A`-module clause.
* `TauCeti.Huber.PairOfDefinition.submodulesBasis_pow_smul_topology_eq_of_isPseudoUniformizer`:
  changing the pseudouniformiser does not change the topology induced by a fixed spanning lattice.
* `TauCeti.Huber.PairOfDefinition.submodulesBasis_pow_smul_topology_eq`: two finitely
  generated lattices spanning `M` over `A`, filtered by two pseudouniformisers, induce the *same*
  topology — Remark 6.19's recipe is well defined in these choices, for a fixed `A₀`.
* `TauCeti.Huber.PairOfDefinition.hasBasis_nhds_zero_pow_smul`: the family, ℕ-indexed, is a
  neighbourhood basis at `0` for the induced topology.
* `TauCeti.Huber.PairOfDefinition.isCountablyGenerated_nhds_zero`: the induced topology has a
  countable fundamental system of neighbourhoods of `0` — 6.18(1)'s first-countability clause.

The elementary facts about `rⁿ • M₀` over an arbitrary subring — antitonicity, absorption of
further powers, and the ambient-scalar bridge — carry no Huber content and live in
`TauCeti.Algebra.Module.Submodule.Pointwise`.

## Implementation notes

The neighbourhoods are `A₀`-submodules, not `A`-submodules, so `SubmodulesBasis` is instantiated
at `R := P.ringOfDefinition`: `M` carries its `A₀`-module structure by restriction of scalars
along `A₀ → A`, which typeclass inference supplies unaided.

The family is written out as `ϖⁿ • M₀` rather than wrapped in a definition of its own: Mathlib's
pointwise action on submodules already *is* that operation, and
`TauCeti.Algebra.Module.Submodule.Pointwise` supplies the facts about it.

The family is `ϖⁿ • M₀` rather than `Iⁿ • M₀` for the ideal of definition `I`. That is Wedhorn's
own indexing. The topology constructions consume the pseudouniformiser's neighbourhood basis,
`TauCeti.Huber.IsPseudoUniformizer.hasBasis_nhds_zero`; the absorption lemmas need only
topological nilpotence and the openness of the ring of definition. This is a choice of
presentation and not a constraint — nothing here shows an `I`-indexed family would fail.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.18 and
  Remark 6.19.
-/

public section

open Filter
open scoped Topology Pointwise

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M]


/-- **The `smul` half of `SubmodulesBasis`**: every scalar close enough to `0` in `A₀` carries a
given `m` into `ϖⁿ • M₀`.

`m` is carried into `M₀` by `ϖᵏ` for some `k` (`Subring.exists_pow_smul_mem`), and `ϖⁿ⁺ᵏ A₀` is a
neighbourhood of `0`; the two combine by arithmetic inside `A₀`. -/
theorem eventually_smul_mem_pow_smul (P : PairOfDefinition A) {s : A} (hs : IsPseudoUniformizer s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M) {m : M}
    (hm : m ∈ Submodule.span A (M₀ : Set M)) (n : ℕ) :
    ∀ᶠ a in 𝓝 (0 : P.ringOfDefinition), a • m ∈ (⟨s, hs0⟩ : P.ringOfDefinition) ^ n • M₀ := by
  obtain ⟨k, hk⟩ := P.ringOfDefinition.exists_pow_smul_mem P.isOpen_ringOfDefinition
    hs.isTopologicallyNilpotent hs0 M₀ hm
  have hnhd : ∀ᶠ a : P.ringOfDefinition in 𝓝 0,
      (a : A) ∈ (s ^ (n + k)) • (P.ringOfDefinition : Set A) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (by simpa using (hs.hasBasis_nhds_zero P).mem_of_mem (i := n + k) trivial)
  filter_upwards [hnhd] with a ha
  obtain ⟨b, hb, hab⟩ := ha
  -- `a` is an `A₀`-scalar while the shared lemma speaks the ambient `A`; the two actions on `M`
  -- agree because the `A₀`-action is restriction of scalars along `A₀ → A`.
  rw [Subring.smul_def]
  exact M₀.smul_mem_pow_smul hs0 hb hab hk

/-- **The `ϖⁿ • M₀` family is a `SubmodulesBasis`**, for a pseudouniformiser `ϖ` in a ring of
definition `A₀` and an `A₀`-submodule `M₀` spanning `M` over `A`.

`SubmodulesBasis.topology` then makes `M` a topological `A₀`-module for which this family is a
neighbourhood basis of `0`, and `SubmodulesBasis.nonarchimedean` makes it a nonarchimedean
additive group.

This is the basis half of Wedhorn's Remark 6.19. He states it for `A` noetherian and `M₀`
finitely generated, and identifies the resulting topology with the one of his Proposition
6.18(1); neither hypothesis is used here, and no such identification is proved here. -/
theorem submodulesBasis_pow_smul (P : PairOfDefinition A) {s : A} (hs : IsPseudoUniformizer s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M)
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    SubmodulesBasis ((⟨s, hs0⟩ : P.ringOfDefinition) ^ · • M₀) where
  inter i j :=
    ⟨max i j, le_inf (M₀.pow_smul_antitone (le_max_left i j))
      (M₀.pow_smul_antitone (le_max_right i j))⟩
  smul _ i := P.eventually_smul_mem_pow_smul hs hs0 M₀ (hspan ▸ Submodule.mem_top) i

/-- **The A-module filter basis.** `SubmodulesBasis.toModuleFilterBasis` only ever produces a
filter basis over `A₀`; Wedhorn's Proposition 6.18(1) is about an `A`-module topology, so the
three `ModuleFilterBasis` axioms are re-established with scalars from `A`. -/
def powSmulModuleFilterBasis (P : PairOfDefinition A) {s : A} (hs : IsPseudoUniformizer s)
    (hs0 : s ∈ P.ringOfDefinition) (M₀ : Submodule P.ringOfDefinition M)
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) : ModuleFilterBasis A M where
  __ := (P.submodulesBasis_pow_smul hs hs0 M₀ hspan).toModuleFilterBasis.toAddGroupFilterBasis
  smul' := by
    -- `V = A₀` works because each `ϖⁿ • M₀` is an `A₀`-submodule; Mathlib's `A₀`-level
    -- construction can take `V = univ` for the same reason one level down.
    rintro _ ⟨n, rfl⟩
    refine ⟨(P.ringOfDefinition : Set A),
      P.isOpen_ringOfDefinition.mem_nhds P.ringOfDefinition.zero_mem, _, ⟨n, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, m, hm, rfl⟩
    exact ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n • M₀).smul_mem ⟨a, ha⟩ hm
  smul_left' := by
    rintro a _ ⟨n, rfl⟩
    obtain ⟨k, hk⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent
      hs.isTopologicallyNilpotent P.isOpen_ringOfDefinition a
    rw [mul_comm] at hk
    refine ⟨_, ⟨n + k, rfl⟩, fun x hx ↦ ?_⟩
    simp only [SetLike.mem_coe, Set.mem_preimage, Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(⟨s ^ k * a, hk⟩ : P.ringOfDefinition) • y, M₀.smul_mem _ hy, ?_⟩
    -- Both sides scale `y`; `Subring.smul_def` puts the `A₀`-scalars into `A` so that the two
    -- can be compared there.
    simp only [Subring.smul_def]
    rw [smul_smul, smul_smul]
    congr 1
    push_cast
    rw [pow_add]; ring
  smul_right' := by
    rintro m _ ⟨n, rfl⟩
    obtain ⟨k, hk⟩ := P.ringOfDefinition.exists_pow_smul_mem P.isOpen_ringOfDefinition
      hs.isTopologicallyNilpotent hs0 M₀
      (hspan ▸ Submodule.mem_top)
    filter_upwards [(hs.hasBasis_nhds_zero P).mem_of_mem (i := n + k) trivial] with c hc
    obtain ⟨b, hb, hcb⟩ := hc
    rw [SetLike.mem_coe]
    exact M₀.smul_mem_pow_smul hs0 hb hcb hk

/-- **Membership in the filter basis is the `ϖⁿ • M₀` family**, in normal form, so a consumer
never unfolds `TauCeti.Huber.PairOfDefinition.powSmulModuleFilterBasis`. -/
@[simp]
theorem mem_powSmulModuleFilterBasis (P : PairOfDefinition A) {s : A}
    (hs : IsPseudoUniformizer s) (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (hspan : Submodule.span A (M₀ : Set M) = ⊤)
    {U : Set M} :
    U ∈ (P.powSmulModuleFilterBasis hs hs0 M₀ hspan).toFilterBasis ↔
      ∃ n : ℕ, U = ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n • M₀ : Submodule _ M) :=
  (Iff.rfl)

/-- **The `A`-module topology is the `A₀`-level one.** Widening the scalars from `A₀` to `A`
re-establishes the `ModuleFilterBasis` axioms but leaves the underlying `AddGroupFilterBasis`
untouched, hence the topology too. This is what lets a consumer transport
`SubmodulesBasis.nonarchimedean` and the rest of the `A₀`-level API across. -/
@[simp]
theorem powSmulModuleFilterBasis_topology (P : PairOfDefinition A) {s : A}
    (hs : IsPseudoUniformizer s) (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    (P.powSmulModuleFilterBasis hs hs0 M₀ hspan).topology
      = (P.submodulesBasis_pow_smul hs hs0 M₀ hspan).topology :=
  (rfl)

/-- **The `ϖⁿ • M₀` family is a neighbourhood basis at `0`, indexed by `ℕ`.** A set is a
neighbourhood of `0` for the topology `M₀` induces exactly when it contains `ϖⁿ • M₀` for some
`n`.

This is `SubmodulesBasis.hasBasis_nhds_zero` at this family; nothing about `ϖ`, `M₀` or the Huber
data enters. Stated for the `SubmodulesBasis` topology;
`TauCeti.Huber.PairOfDefinition.powSmulModuleFilterBasis_topology` identifies that with the
`A`-module one. -/
theorem hasBasis_nhds_zero_pow_smul (P : PairOfDefinition A) {s : A}
    (hs : IsPseudoUniformizer s) (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    (@nhds M (P.submodulesBasis_pow_smul hs hs0 M₀ hspan).topology 0).HasBasis
      (fun _ : ℕ ↦ True) fun n ↦ ((⟨s, hs0⟩ : P.ringOfDefinition) ^ n • M₀ : Set M) :=
  (P.submodulesBasis_pow_smul hs hs0 M₀ hspan).hasBasis_nhds_zero

/-- **The topology has a countable fundamental system of neighbourhoods of `0`**, namely the
`ℕ`-indexed family `ϖⁿ • M₀`. This is the first-countability clause of Proposition 6.18(1).

Stated for the `SubmodulesBasis` topology, as the two neighbourhood facts above are;
`TauCeti.Huber.PairOfDefinition.powSmulModuleFilterBasis_topology` identifies that with the
`A`-module topology Proposition 6.18(1) is about. -/
theorem isCountablyGenerated_nhds_zero (P : PairOfDefinition A) {s : A}
    (hs : IsPseudoUniformizer s) (hs0 : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    (@nhds M (P.submodulesBasis_pow_smul hs hs0 M₀ hspan).topology 0).IsCountablyGenerated :=
  (P.hasBasis_nhds_zero_pow_smul hs hs0 M₀ hspan).isCountablyGenerated

/-- **Changing the pseudouniformiser does not change the induced topology.** This is the direct
topological form of
`Subring.exists_pow_smul_le_pow_smul_of_isUnit`; unlike the
comparison of two lattices, it requires no finite-generation hypothesis. -/
theorem submodulesBasis_pow_smul_topology_eq_of_isPseudoUniformizer (P : PairOfDefinition A)
    {s t : A} (hs : IsPseudoUniformizer s) (ht : IsPseudoUniformizer t)
    (hs0 : s ∈ P.ringOfDefinition) (ht0 : t ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    (P.submodulesBasis_pow_smul hs hs0 M₀ hspan).topology
      = (P.submodulesBasis_pow_smul ht ht0 M₀ hspan).topology :=
  (P.submodulesBasis_pow_smul hs hs0 M₀ hspan).topology_eq
    (P.submodulesBasis_pow_smul ht ht0 M₀ hspan)
    (P.ringOfDefinition.exists_pow_smul_le_pow_smul_of_isUnit P.isOpen_ringOfDefinition
      hs.isUnit ht.isTopologicallyNilpotent hs0 ht0 M₀)
    (P.ringOfDefinition.exists_pow_smul_le_pow_smul_of_isUnit P.isOpen_ringOfDefinition
      ht.isUnit hs.isTopologicallyNilpotent ht0 hs0 M₀)

/-- **The induced topology does not depend on the lattice or the pseudouniformiser.** Two finitely
generated `A₀`-submodules that each span `M` over `A`, filtered by any two pseudouniformisers in
`A₀`, induce the same topology.

This is what makes Remark 6.19 well posed in its lattice. The remark says to *choose* a
finitely generated `M₀` with `A · M₀ = M` and then describes the topology by the family
`ϖⁿ • M₀`; for that description to name a topology at all, neither the lattice nor the
pseudouniformiser may matter.
The ring of definition `P` is still fixed on both sides here, so independence of that remaining
choice — which Remark 6.19 makes as well — is not proved.

Finite generation is required of both lattices. Nothing else is: each already spans `M`, so no
containment hypothesis between them is needed.

Proposition 6.18(1) asserts something strictly stronger — uniqueness among *all* complete
first-countable `A`-module topologies, including those given by no lattice — which is not proved
here. -/
theorem submodulesBasis_pow_smul_topology_eq (P : PairOfDefinition A) {s t : A}
    (hs : IsPseudoUniformizer s) (ht : IsPseudoUniformizer t)
    (hs0 : s ∈ P.ringOfDefinition) (ht0 : t ∈ P.ringOfDefinition)
    (M₀ M₁ : Submodule P.ringOfDefinition M) (hspan₀ : Submodule.span A (M₀ : Set M) = ⊤)
    (hspan₁ : Submodule.span A (M₁ : Set M) = ⊤) (hfg₀ : M₀.FG) (hfg₁ : M₁.FG) :
    (P.submodulesBasis_pow_smul hs hs0 M₀ hspan₀).topology
      = (P.submodulesBasis_pow_smul ht ht0 M₁ hspan₁).topology := by
  apply (P.submodulesBasis_pow_smul hs hs0 M₀ hspan₀).topology_eq
    (P.submodulesBasis_pow_smul ht ht0 M₁ hspan₁)
  · intro n
    obtain ⟨j, hj⟩ := P.ringOfDefinition.exists_pow_smul_le_pow_smul P.isOpen_ringOfDefinition
      hs.isTopologicallyNilpotent hs0 M₀ M₁
      (by rw [hspan₀]; exact fun _ _ ↦ Submodule.mem_top) hfg₁ n
    obtain ⟨k, hk⟩ :=
      P.ringOfDefinition.exists_pow_smul_le_pow_smul_of_isUnit P.isOpen_ringOfDefinition
        hs.isUnit ht.isTopologicallyNilpotent hs0 ht0 M₁ j
    exact ⟨k, hk.trans hj⟩
  · intro n
    obtain ⟨j, hj⟩ := P.ringOfDefinition.exists_pow_smul_le_pow_smul P.isOpen_ringOfDefinition
      ht.isTopologicallyNilpotent ht0 M₁ M₀
      (by rw [hspan₁]; exact fun _ _ ↦ Submodule.mem_top) hfg₀ n
    obtain ⟨k, hk⟩ :=
      P.ringOfDefinition.exists_pow_smul_le_pow_smul_of_isUnit P.isOpen_ringOfDefinition
        ht.isUnit hs.isTopologicallyNilpotent ht0 hs0 M₀ j
    exact ⟨k, hk.trans hj⟩

end TauCeti.Huber.PairOfDefinition
