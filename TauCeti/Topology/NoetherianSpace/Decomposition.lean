/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.NoetherianSpace

/-!
# Finite covers by irreducible closed sets and irredundant decompositions

Let `s = s₁ ∪ ⋯ ∪ sₘ` be a finite union of irreducible closed sets. An irreducible set contained
in a finite union of closed sets lies in one of them, so the maximal irreducible subsets of `s`
are exactly the inclusion-maximal members `sᵢ`, whether or not the cover contains redundant or
repeated members. Since `s` is closed, these are also the maximal irreducible closed subsets of
`s`. In particular two finite covers of the same set by irreducible closed sets have the same
maximal members.

The union is *irredundant* when no `sᵢ` is contained in another `sⱼ`, that is, when
`{s₁, …, sₘ}` is an antichain for inclusion. Then every member is maximal, so an irredundant
decomposition is unique, also as an indexed family up to a bijection of the indices. In a
Noetherian space every closed set has an irredundant decomposition, obtained by discarding the
nonmaximal members of Mathlib's finite decomposition
`TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`.

## Main results

* `IsIrreducible.exists_mem_subset_of_subset_sUnion`,
  `IsIrreducible.exists_subset_of_subset_iUnion`: an irreducible subset of a finite union of
  closed sets lies in one of them.
* `TauCeti.maximal_isIrreducible_subset_sUnion_iff`,
  `TauCeti.maximal_isIrreducible_subset_iUnion_iff`: the maximal irreducible subsets of a finite
  union of irreducible closed sets are its inclusion-maximal members.
* `TauCeti.maximal_isClosed_and_isIrreducible_subset_iUnion_iff`: the same for the maximal
  irreducible closed subsets.
* `TauCeti.setOf_maximal_mem_eq_of_sUnion_eq`: two finite covers of the same set by irreducible
  closed sets have the same maximal members.
* `TauCeti.exists_eq_of_iUnion_eq`: an irreducible member of a finite closed cover that is
  inclusion-maximal among its members is a member of every finite cover of the same set by
  irreducible closed sets.
* `TauCeti.eq_setOf_maximal_isIrreducible_of_isAntichain`: the members of an irredundant finite
  decomposition into irreducible closed sets are the maximal irreducible subsets of the union.
* `TauCeti.exists_equiv_eq_of_iUnion_eq`: two irredundant finite decompositions of the same set
  agree up to a bijection of their indices.
* `TauCeti.exists_finite_isAntichain_irreducible_of_noetherianSpace`: in a Noetherian space every
  closed set has an irredundant finite decomposition into irreducible closed sets.

## References

* The Stacks Project, Tag 0052, *Noetherian topological spaces*.
* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §3.6, Proposition 11.
-/

public section

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- An irreducible subset of a finite union of closed sets is contained in one of them. -/
theorem IsIrreducible.exists_mem_subset_of_subset_sUnion {Z : Set X} (hZ : IsIrreducible Z)
    {S : Set (Set X)} (hSf : S.Finite) (hSc : ∀ t ∈ S, IsClosed t) (hZS : Z ⊆ ⋃₀ S) :
    ∃ t ∈ S, Z ⊆ t := by
  lift S to Finset (Set X) using hSf
  exact isIrreducible_iff_sUnion_isClosed.1 hZ S hSc hZS

/-- An irreducible subset of a finite union of closed sets is contained in one of them. -/
theorem IsIrreducible.exists_subset_of_subset_iUnion {Z : Set X} (hZ : IsIrreducible Z)
    {ι : Type*} [Finite ι] {C : ι → Set X} (hc : ∀ i, IsClosed (C i)) (hZC : Z ⊆ ⋃ i, C i) :
    ∃ i, Z ⊆ C i := by
  simpa using hZ.exists_mem_subset_of_subset_sUnion (Set.finite_range C)
    (Set.forall_mem_range.2 hc) (Set.sUnion_range C ▸ hZC)

namespace TauCeti

/-! ### Maximal members of a finite cover -/

/-- The maximal irreducible subsets of a finite union of irreducible closed sets are exactly the
inclusion-maximal members of the union. The members need not be pairwise incomparable. -/
theorem maximal_isIrreducible_subset_sUnion_iff {S : Set (Set X)} (hSf : S.Finite)
    (hSc : ∀ t ∈ S, IsClosed t) (hSi : ∀ t ∈ S, IsIrreducible t) {Z : Set X} :
    Maximal (fun Z ↦ IsIrreducible Z ∧ Z ⊆ ⋃₀ S) Z ↔ Maximal (· ∈ S) Z := by
  refine ⟨fun hZ ↦ ?_, fun hZ ↦ ⟨⟨hSi Z hZ.1, Set.subset_sUnion_of_mem hZ.1⟩, fun W hW hZW ↦ ?_⟩⟩
  · obtain ⟨t, ht, hZt⟩ := hZ.1.1.exists_mem_subset_of_subset_sUnion hSf hSc hZ.1.2
    obtain rfl : Z = t := hZt.antisymm (hZ.2 ⟨hSi t ht, Set.subset_sUnion_of_mem ht⟩ hZt)
    exact ⟨ht, fun u hu hZu ↦ hZ.2 ⟨hSi u hu, Set.subset_sUnion_of_mem hu⟩ hZu⟩
  · obtain ⟨t, ht, hWt⟩ := hW.1.exists_mem_subset_of_subset_sUnion hSf hSc hW.2
    exact hWt.trans (hZ.2 ht (hZW.trans hWt))

/-- The maximal irreducible closed subsets of a closed set are its maximal irreducible subsets:
the closure of an irreducible subset is an irreducible subset. -/
theorem maximal_isClosed_and_isIrreducible_subset_iff {Y : Set X} (hY : IsClosed Y) {Z : Set X} :
    Maximal (fun Z ↦ IsClosed Z ∧ IsIrreducible Z ∧ Z ⊆ Y) Z ↔
      Maximal (fun Z ↦ IsIrreducible Z ∧ Z ⊆ Y) Z := by
  refine ⟨fun hZ ↦ ⟨hZ.1.2, fun W hW hZW ↦ subset_closure.trans ?_⟩, fun hZ ↦ ?_⟩
  · exact hZ.2 ⟨isClosed_closure, hW.1.closure, closure_minimal hW.2 hY⟩
      (hZW.trans subset_closure)
  · have hc : IsClosed Z := closure_subset_iff_isClosed.1 <|
      hZ.2 ⟨hZ.1.1.closure, closure_minimal hZ.1.2 hY⟩ subset_closure
    exact ⟨⟨hc, hZ.1⟩, fun W hW hZW ↦ hZ.2 hW.2 hZW⟩

/-- If finitely many irreducible closed sets `C i` cover a set, then its maximal irreducible
subsets are exactly the inclusion-maximal `C i`. The family may contain repeated members and
members contained in other members. -/
theorem maximal_isIrreducible_subset_iUnion_iff {ι : Type*} [Finite ι] {C : ι → Set X}
    (hc : ∀ i, IsClosed (C i)) (hi : ∀ i, IsIrreducible (C i)) {Z : Set X} :
    Maximal (fun Z ↦ IsIrreducible Z ∧ Z ⊆ ⋃ i, C i) Z ↔
      ∃ i, Z = C i ∧ ∀ j, C i ⊆ C j → C j ⊆ C i := by
  rw [← Set.sUnion_range, maximal_isIrreducible_subset_sUnion_iff (Set.finite_range C)
    (Set.forall_mem_range.2 hc) (Set.forall_mem_range.2 hi)]
  constructor
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact ⟨i, rfl, fun j hj ↦ h ⟨j, rfl⟩ hj⟩
  · rintro ⟨i, rfl, h⟩
    exact ⟨⟨i, rfl⟩, by rintro _ ⟨j, rfl⟩ hj; exact h j hj⟩

/-- If finitely many irreducible closed sets `C i` cover a set, then its maximal irreducible
closed subsets are exactly the inclusion-maximal `C i`. The family may contain repeated members
and members contained in other members. -/
theorem maximal_isClosed_and_isIrreducible_subset_iUnion_iff {ι : Type*} [Finite ι]
    {C : ι → Set X} (hc : ∀ i, IsClosed (C i)) (hi : ∀ i, IsIrreducible (C i)) {Z : Set X} :
    Maximal (fun Z ↦ IsClosed Z ∧ IsIrreducible Z ∧ Z ⊆ ⋃ i, C i) Z ↔
      ∃ i, Z = C i ∧ ∀ j, C i ⊆ C j → C j ⊆ C i := by
  rw [maximal_isClosed_and_isIrreducible_subset_iff (isClosed_iUnion_of_finite hc),
    maximal_isIrreducible_subset_iUnion_iff hc hi]

/-- Two finite families of irreducible closed sets with the same union have the same
inclusion-maximal members: adding or removing members contained in other members changes
neither. -/
theorem setOf_maximal_mem_eq_of_sUnion_eq {S T : Set (Set X)} (hSf : S.Finite)
    (hSc : ∀ t ∈ S, IsClosed t) (hSi : ∀ t ∈ S, IsIrreducible t) (hTf : T.Finite)
    (hTc : ∀ t ∈ T, IsClosed t) (hTi : ∀ t ∈ T, IsIrreducible t) (h : ⋃₀ S = ⋃₀ T) :
    {Z | Maximal (· ∈ S) Z} = {Z | Maximal (· ∈ T) Z} := by
  refine Set.ext fun Z ↦ (maximal_isIrreducible_subset_sUnion_iff hSf hSc hSi).symm.trans ?_
  rw [h]
  exact maximal_isIrreducible_subset_sUnion_iff hTf hTc hTi

/-- If finitely many irreducible closed sets cover the whole space, then the irreducible
components of the space are the inclusion-maximal members of the cover. -/
theorem irreducibleComponents_eq_setOf_maximal_mem {S : Set (Set X)} (hSf : S.Finite)
    (hSc : ∀ t ∈ S, IsClosed t) (hSi : ∀ t ∈ S, IsIrreducible t) (hS : ⋃₀ S = Set.univ) :
    irreducibleComponents X = {Z | Maximal (· ∈ S) Z} := by
  refine Set.ext fun Z ↦ Iff.trans ?_ (maximal_isIrreducible_subset_sUnion_iff hSf hSc hSi)
  simp [irreducibleComponents, hS]

/-- If finitely many closed sets `C i` have the same union as finitely many irreducible closed
sets `D k`, then every irreducible `C i` that is inclusion-maximal among the `C j` is one of the
`D k`. The other `C j` need not be irreducible, and the `C j` may be repeated or contained in one
another. -/
theorem exists_eq_of_iUnion_eq {ι κ : Type*} [Finite ι] [Finite κ] {C : ι → Set X} {D : κ → Set X}
    (hCc : ∀ i, IsClosed (C i)) (hDc : ∀ k, IsClosed (D k)) (hDi : ∀ k, IsIrreducible (D k))
    (h : ⋃ i, C i = ⋃ k, D k) {i : ι} (hCi : IsIrreducible (C i))
    (hC : ∀ j, C i ⊆ C j → C j ⊆ C i) : ∃ k, C i = D k := by
  obtain ⟨k, hk⟩ := hCi.exists_subset_of_subset_iUnion hDc ((Set.subset_iUnion C i).trans h.le)
  obtain ⟨j, hj⟩ := (hDi k).exists_subset_of_subset_iUnion hCc ((Set.subset_iUnion D k).trans h.ge)
  exact ⟨k, hk.antisymm (hj.trans (hC j (hk.trans hj)))⟩

/-! ### Irredundant decompositions -/

/-- The members of an irredundant finite decomposition into irreducible closed sets are exactly
the maximal irreducible subsets of their union. In particular such a decomposition is unique. -/
theorem eq_setOf_maximal_isIrreducible_of_isAntichain {S : Set (Set X)} (hSf : S.Finite)
    (hSc : ∀ t ∈ S, IsClosed t) (hSi : ∀ t ∈ S, IsIrreducible t) (hS : IsAntichain (· ⊆ ·) S) :
    S = {Z | Maximal (fun Z ↦ IsIrreducible Z ∧ Z ⊆ ⋃₀ S) Z} :=
  Set.ext fun _ ↦ hS.maximal_mem_iff.symm.trans
    (maximal_isIrreducible_subset_sUnion_iff hSf hSc hSi).symm

/-- Two irredundant finite decompositions of the same set into irreducible closed sets agree up
to a bijection of their indices. -/
theorem exists_equiv_eq_of_iUnion_eq {ι κ : Type*} [Finite ι] [Finite κ] {C : ι → Set X}
    {D : κ → Set X} (hCc : ∀ i, IsClosed (C i)) (hCi : ∀ i, IsIrreducible (C i))
    (hC : ∀ i j, C i ⊆ C j → i = j) (hDc : ∀ k, IsClosed (D k))
    (hDi : ∀ k, IsIrreducible (D k)) (hD : ∀ k l, D k ⊆ D l → k = l)
    (h : ⋃ i, C i = ⋃ k, D k) : ∃ e : ι ≃ κ, ∀ i, C i = D (e i) := by
  choose f hf using fun i ↦ exists_eq_of_iUnion_eq hCc hDc hDi h (hCi i)
    fun j hj ↦ (congrArg C (hC i j hj)).superset
  refine ⟨Equiv.ofBijective f ⟨fun i j hij ↦ hC i j ?_, fun k ↦ ?_⟩, hf⟩
  · rw [hf i, hf j, hij]
  · obtain ⟨i, hi⟩ := exists_eq_of_iUnion_eq hDc hCc hCi h.symm (hDi k)
      fun l hl ↦ (congrArg D (hD k l hl)).superset
    exact ⟨i, hD _ _ ((hf i).symm.trans hi.symm).le⟩

/-- In a Noetherian space every closed set is an irredundant finite union of irreducible closed
sets: no member of the union is contained in another. -/
theorem exists_finite_isAntichain_irreducible_of_noetherianSpace [NoetherianSpace X] {s : Set X}
    (hs : IsClosed s) :
    ∃ S : Set (Set X), S.Finite ∧ (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IsIrreducible t) ∧
      IsAntichain (· ⊆ ·) S ∧ s = ⋃₀ S := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine ⟨{t | Maximal (· ∈ S) t}, hSf.subset fun t ht ↦ ht.1, fun t ht ↦ hSc t ht.1,
    fun t ht ↦ hSi t ht.1, setOfPred_maximal_antichain _, ?_⟩
  refine (Set.sUnion_subset fun t ht ↦ ?_).antisymm (Set.sUnion_subset_sUnion fun t ht ↦ ht.1)
  obtain ⟨u, htu, hu⟩ := hSf.exists_le_maximal ht
  exact htu.trans (Set.subset_sUnion_of_mem hu)

end TauCeti
