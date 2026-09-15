/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Topology.Algebra.Group.Generation

/-!
# Open subgroups of a topologically finitely generated compact group

A topologically finitely generated compact group has, for each `n`, only finitely many open
subgroups of index `n`. The reason is the permutation representation: an open subgroup `U` of
index `n` makes `G` act on the `n`-element coset space `G ⧸ U`, and `U` is recovered from that
action as the stabilizer of the trivial coset. Transporting the coset space to `Fin n` turns the
action into a homomorphism `G →* Equiv.Perm (Fin n)` whose kernel, the normal core of `U`, is open;
and a topologically finitely generated group admits only finitely many homomorphisms with open
kernel into a fixed finite group
(`TauCeti.IsTopologicallyFinitelyGenerated.finite_monoidHom_isOpen_ker`).

Counting over all indices, the open subgroups then form a countable family, as do the open normal
subgroups, and the latter can be arranged in a single descending sequence cofinal among them. That
sequence is what lets an inverse-limit argument over the finite quotients be run along `ℕ`, using
Mathlib's `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` in place of the
directed form.

The same count has a rigidity consequence. A continuous surjective endomorphism `f` of `G` pulls
open subgroups back to open subgroups of the same index, injectively; on each of the finite fibers
of the index an injective self-map is a bijection, so *every* open subgroup of `G` is a preimage
`f ⁻¹' V`. This is the combinatorial half of the Hopf property of a topologically finitely
generated profinite group.

Only compactness of `G` is used, never total disconnectedness: for a connected compact group the
statements below are trivial, since `⊤` is then the one open subgroup. The intended case is of
course a profinite group, where the open subgroups carry all the information.

## Main results

* `TauCeti.IsTopologicallyFinitelyGenerated.finite_openSubgroup_index_eq`: finitely many open
  subgroups of each index.
* `TauCeti.IsTopologicallyFinitelyGenerated.openSubgroup_comap_surjective`: every open subgroup
  is the preimage of an open subgroup along a continuous surjective endomorphism.
* `TauCeti.IsTopologicallyFinitelyGenerated.countable_openSubgroup`,
  `TauCeti.IsTopologicallyFinitelyGenerated.countable_openNormalSubgroup`: countably many open
  subgroups, and countably many open normal subgroups.
* `TauCeti.IsTopologicallyFinitelyGenerated.exists_antitone_openNormalSubgroup_cofinal`: a
  descending sequence of open normal subgroups cofinal among them.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.5.
-/

public section

namespace TauCeti

namespace IsTopologicallyFinitelyGenerated

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **A topologically finitely generated group has finitely many open subgroups of each nonzero
index.** An open subgroup of index `n` is the stabilizer of the trivial coset for the action of
`G` on its `n` cosets, so it is determined by that action together with the trivial coset; both
range over finite sets once the coset space is transported to `Fin n`. -/
theorem finite_openSubgroup_index_eq_of_ne_zero (hG : IsTopologicallyFinitelyGenerated G)
    (n : ℕ) (hn : n ≠ 0) :
    Finite {U : OpenSubgroup G // (U : Subgroup G).index = n} := by
  classical
  set S := {U : OpenSubgroup G // (U : Subgroup G).index = n}
  have hindex : ∀ U : S, (U.1 : Subgroup G).index ≠ 0 := fun U ↦ U.2.symm ▸ hn
  -- Each coset space has exactly `n` elements, so it can be transported to `Fin n`.
  have hcard : ∀ U : S, Nonempty ((G ⧸ (U.1 : Subgroup G)) ≃ Fin n) := fun U ↦ by
    let _ := (U.1 : Subgroup G).fintypeOfIndexNeZero (hindex U)
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
    let _ : (U.1 : Subgroup G).FiniteIndex := ⟨hindex U⟩
    rw [hker U]
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (Subgroup.normalCore_isClosed _ U.1.isClosed)
  -- `U` is exactly the stabilizer of the trivial coset under that representation.
  have hmem : ∀ (U : S) (g : G), g ∈ (U.1 : Subgroup G) ↔
      ψ U g (e U (QuotientGroup.mk 1)) = e U (QuotientGroup.mk 1) := fun U g ↦ by
    have hact : ψ U g (e U (QuotientGroup.mk 1)) = e U (QuotientGroup.mk g) := by
      simp [hψ]
    rw [hact, (e U).apply_eq_iff_eq, QuotientGroup.eq, mul_one, inv_mem_iff]
  have := hG.finite_monoidHom_isOpen_ker (Equiv.Perm (Fin n))
  refine Finite.of_injective
    (fun U : S ↦ ((⟨ψ U, hopen U⟩ : {f : G →* Equiv.Perm (Fin n) // IsOpen (f.ker : Set G)}),
      e U (QuotientGroup.mk 1))) fun U V huv ↦ ?_
  have hUV : ψ U = ψ V := congrArg (fun x ↦ (Prod.fst x).1) huv
  have hpt : e U (QuotientGroup.mk 1) = e V (QuotientGroup.mk 1) := congrArg Prod.snd huv
  refine Subtype.ext (OpenSubgroup.toSubgroup_injective (SetLike.ext fun g ↦ ?_))
  rw [hmem U g, hmem V g, hUV, hpt]

variable [CompactSpace G]

/-- **A topologically finitely generated compact group has finitely many open subgroups of each
index.** This includes index zero, whose fiber is empty because open subgroups of a compact group
have finite index. -/
theorem finite_openSubgroup_index_eq (hG : IsTopologicallyFinitelyGenerated G) (n : ℕ) :
    Finite {U : OpenSubgroup G // (U : Subgroup G).index = n} := by
  rcases eq_or_ne n 0 with rfl | hn
  · let _ : IsEmpty {U : OpenSubgroup G // (U : Subgroup G).index = 0} :=
      ⟨fun U ↦ (U.1 : Subgroup G).index_ne_zero_of_finite U.2⟩
    infer_instance
  · exact hG.finite_openSubgroup_index_eq_of_ne_zero n hn

/-- **Pulling back open subgroups along a continuous surjective endomorphism is surjective.** If
`f : G →* G` is continuous and surjective, every open subgroup of a topologically finitely
generated compact group `G` is of the form `f ⁻¹' V` for an open subgroup `V`.

Pulling back preserves the index and is injective, so on the finite set of open subgroups of a
given index it is a bijection. -/
theorem openSubgroup_comap_surjective (hG : IsTopologicallyFinitelyGenerated G) {f : G →* G}
    (hf : Continuous f) (hsurj : Function.Surjective f) :
    Function.Surjective fun V : OpenSubgroup G ↦ V.comap f hf := by
  intro U
  -- Pulling back preserves the index, so it restricts to the open subgroups of index `U.index`.
  have hindex : ∀ V : OpenSubgroup G,
      ((V.comap f hf : Subgroup G)).index = (V : Subgroup G).index := fun V ↦ by
    rw [OpenSubgroup.toSubgroup_comap, Subgroup.index_comap_of_surjective _ hsurj]
  have := hG.finite_openSubgroup_index_eq (U : Subgroup G).index
  set Φ : {V : OpenSubgroup G // (V : Subgroup G).index = (U : Subgroup G).index} →
      {V : OpenSubgroup G // (V : Subgroup G).index = (U : Subgroup G).index} := fun V ↦
    ⟨V.1.comap f hf, (hindex V.1).trans V.2⟩ with hΦ
  have hinj : Function.Injective Φ := fun V W hVW ↦
    Subtype.ext (OpenSubgroup.toSubgroup_injective (Subgroup.comap_injective hsurj
      (congrArg (fun X : OpenSubgroup G ↦ (X : Subgroup G)) (Subtype.ext_iff.mp hVW))))
  obtain ⟨V, hV⟩ := Finite.injective_iff_surjective.mp hinj ⟨U, rfl⟩
  exact ⟨V.1, congrArg Subtype.val hV⟩

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
theorem exists_antitone_openNormalSubgroup_cofinal (hG : IsTopologicallyFinitelyGenerated G) :
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
