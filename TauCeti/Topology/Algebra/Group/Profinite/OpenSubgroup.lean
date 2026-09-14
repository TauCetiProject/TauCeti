/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.Generation

/-!
# Open subgroups of a topologically finitely generated compact group

A compact group has, for each `n`, only finitely many open subgroups of index `n`. The reason is
the permutation representation: an open subgroup `U` of index `n` makes `G` act on the `n`-element
coset space `G ⧸ U`, and `U` is recovered from that action as the stabilizer of the trivial coset.
Transporting the coset space to `Fin n` turns the action into a homomorphism `G →* Equiv.Perm
(Fin n)` whose kernel, the normal core of `U`, is open; and a topologically finitely generated
group admits only finitely many homomorphisms with open kernel into a fixed finite group
(`TauCeti.IsTopologicallyFinitelyGenerated.finite_monoidHom_isOpen_ker`).

Counting over all indices, the open subgroups then form a countable family, as do the open normal
subgroups, and the latter can be arranged in a single descending sequence cofinal among them. That
sequence is what lets an inverse-limit argument over the finite quotients be run along `ℕ`, using
Mathlib's `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` in place of the
directed form.

Only compactness of `G` is used, never total disconnectedness: for a connected compact group the
statements below are true but empty, since `⊤` is then the one open subgroup. The intended case is
of course a profinite group, where the open subgroups carry all the information.

## Main results

* `TauCeti.IsTopologicallyFinitelyGenerated.finite_openSubgroup_index_eq`: finitely many open
  subgroups of each index.
* `TauCeti.IsTopologicallyFinitelyGenerated.countable_openSubgroup`,
  `TauCeti.IsTopologicallyFinitelyGenerated.countable_openNormalSubgroup`: countably many open
  subgroups, and countably many open normal subgroups.
* `TauCeti.IsTopologicallyFinitelyGenerated.exists_antitone_openNormalSubgroup`: a descending
  sequence of open normal subgroups cofinal among them.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.5.
-/

public section

namespace TauCeti

namespace IsTopologicallyFinitelyGenerated

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- **A topologically finitely generated compact group has finitely many open subgroups of each
index.** An open subgroup of index `n` is the stabilizer of the trivial coset for the action of
`G` on its `n` cosets, so it is determined by that action together with the trivial coset; both
range over finite sets once the coset space is transported to `Fin n`. -/
theorem finite_openSubgroup_index_eq (hG : IsTopologicallyFinitelyGenerated G) (n : ℕ) :
    Finite {U : OpenSubgroup G // (U : Subgroup G).index = n} := by
  classical
  set S := {U : OpenSubgroup G // (U : Subgroup G).index = n}
  -- Each coset space has exactly `n` elements, so it can be transported to `Fin n`.
  have hcard : ∀ U : S, Nonempty ((G ⧸ (U.1 : Subgroup G)) ≃ Fin n) := fun U ↦ by
    have : Fintype (G ⧸ (U.1 : Subgroup G)) := Fintype.ofFinite _
    exact ⟨Fintype.equivFinOfCardEq <| by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, U.2]⟩
  set e : ∀ U : S, (G ⧸ (U.1 : Subgroup G)) ≃ Fin n := fun U ↦ (hcard U).some
  -- The permutation representation of `G` on the cosets of `U`, read on `Fin n`.
  set ψ : ∀ U : S, G →* Equiv.Perm (Fin n) := fun U ↦
    ((e U).permCongrHom : Equiv.Perm (G ⧸ (U.1 : Subgroup G)) →* Equiv.Perm (Fin n)).comp
      (MulAction.toPermHom G (G ⧸ (U.1 : Subgroup G))) with hψ
  have hker : ∀ U : S, ((ψ U).ker : Subgroup G) = (U.1 : Subgroup G).normalCore := fun U ↦ by
    rw [hψ, MonoidHom.ker_mulEquiv_comp, ← Subgroup.normalCore_eq_ker]
  have hopen : ∀ U : S, IsOpen (((ψ U).ker : Subgroup G) : Set G) := fun U ↦ by
    have : (U.1 : Subgroup G).FiniteIndex := U.1.finiteIndex_of_finite_quotient
    rw [hker U]
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (Subgroup.normalCore_isClosed _ U.1.isClosed)
  -- `U` is exactly the stabilizer of the trivial coset under that representation.
  have hmem : ∀ (U : S) (g : G), g ∈ (U.1 : Subgroup G) ↔
      ψ U g (e U (QuotientGroup.mk 1)) = e U (QuotientGroup.mk 1) := fun U g ↦ by
    have hact : ψ U g (e U (QuotientGroup.mk 1)) = e U (QuotientGroup.mk g) := by
      simp only [hψ, MonoidHom.coe_comp, MonoidHom.coe_coe, Equiv.permCongrHom_coe,
        Function.comp_apply, MulAction.toPermHom_apply, Equiv.permCongr_apply,
        Equiv.symm_apply_apply, MulAction.toPerm_apply, MulAction.Quotient.smul_mk, smul_eq_mul,
        mul_one]
    rw [hact, (e U).apply_eq_iff_eq, QuotientGroup.eq, mul_one, inv_mem_iff]
  have := hG.finite_monoidHom_isOpen_ker (Equiv.Perm (Fin n))
  refine Finite.of_injective
    (fun U : S ↦ ((⟨ψ U, hopen U⟩ : {f : G →* Equiv.Perm (Fin n) // IsOpen (f.ker : Set G)}),
      e U (QuotientGroup.mk 1))) fun U V huv ↦ ?_
  have hUV : ψ U = ψ V := congrArg (fun x ↦ (Prod.fst x).1) huv
  have hpt : e U (QuotientGroup.mk 1) = e V (QuotientGroup.mk 1) := congrArg Prod.snd huv
  refine Subtype.ext (OpenSubgroup.toSubgroup_injective (SetLike.ext fun g ↦ ?_))
  rw [hmem U g, hmem V g, hUV, hpt]

/-- A topologically finitely generated compact group has only countably many open subgroups: they
are sorted into finitely many of each index. -/
theorem countable_openSubgroup (hG : IsTopologicallyFinitelyGenerated G) :
    Countable (OpenSubgroup G) := by
  have : ∀ n : ℕ, Countable {U : OpenSubgroup G // (U : Subgroup G).index = n} := fun n ↦
    have := hG.finite_openSubgroup_index_eq n
    inferInstance
  exact Countable.of_equiv _ (Equiv.sigmaFiberEquiv fun U : OpenSubgroup G ↦ (U : Subgroup G).index)

/-- A topologically finitely generated compact group has only countably many open normal
subgroups. -/
theorem countable_openNormalSubgroup (hG : IsTopologicallyFinitelyGenerated G) :
    Countable (OpenNormalSubgroup G) := by
  have := hG.countable_openSubgroup
  exact Function.Injective.countable (f := fun N : OpenNormalSubgroup G ↦ N.toOpenSubgroup)
    fun N M h ↦ OpenNormalSubgroup.toSubgroup_injective (congrArg OpenSubgroup.toSubgroup h)

/-- **A cofinal descending sequence of open normal subgroups.** In a topologically finitely
generated compact group the open normal subgroups, being countable and closed under binary
infima, are refined by a single antitone sequence. This is what turns an inverse-limit argument
over the finite quotients into a statement about a sequence. -/
theorem exists_antitone_openNormalSubgroup (hG : IsTopologicallyFinitelyGenerated G) :
    ∃ N : ℕ → OpenNormalSubgroup G, Antitone N ∧ ∀ U : OpenNormalSubgroup G, ∃ k, N k ≤ U := by
  have hcount := hG.countable_openNormalSubgroup
  have hne : Nonempty (OpenNormalSubgroup G) := ⟨{ toOpenSubgroup := ⟨⊤, isOpen_univ⟩ }⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat (OpenNormalSubgroup G)
  -- Take the intersection of the first `k + 1` members of an enumeration.
  refine ⟨fun k ↦ Nat.rec (f 0) (fun i N ↦ N ⊓ f (i + 1)) k, antitone_nat_of_succ_le fun k ↦
    inf_le_left, fun U ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hf U
  refine ⟨k, ?_⟩
  cases k with
  | zero => exact le_rfl
  | succ i => exact inf_le_right

end IsTopologicallyFinitelyGenerated

end TauCeti
