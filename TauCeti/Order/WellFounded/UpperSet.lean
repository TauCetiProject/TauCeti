/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.WellQuasiOrder
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import TauCeti.Order.WellFounded.Set

/-!
# Bounds on slices of upper sets are decided by finitely many slices

Let `α` be a well-quasi-order, `S j` a sequence of subsets of `α`, and `σ j` a sequence of
natural numbers. We show that for all large `i`, every upper set `D` of `α` that omits at most
`σ j` elements of `S j` for each `j ≤ i` does so for every `j`: finitely many of the bounds
imply all of them, with a cutoff that does not depend on `D`.

For exponents `ι →₀ ℕ` in finitely many variables, which form a well-quasi-order by Dickson's
lemma (`Finsupp.wellQuasiOrderedLE`), with `S j` the exponents of a fixed degree, this says that
finitely many conditions on the numbers of monomials of given degrees outside a monomial ideal
imply all of them; see `TauCeti.eventually_isDegreeBound`.

The proof takes bad upper sets `D m` and an upper set `E` that they approach. Since every set of
a well-quasi-order lies above finitely many of its elements
(`Set.PartiallyWellOrderedOn.exists_finset_subset_forall_exists`), frequently `D m` contains `E`
and agrees with it on any given finite set; the first property bounds `D m` by `E`, the second
transfers the bounds of the `D m` to `E`.

## Main results

* `TauCeti.exists_frequently_subset_and_agree_on_finite`: for a family of upper sets `D m` of a
  well-quasi-order and a nontrivial filter `l`, there is an upper set `E` such that, for every
  finite set `s`, frequently along `l` the set `D m` contains `E` and agrees with `E` on `s`.
* `TauCeti.eventually_forall_encard_sdiff_le_of_isUpperSet_of_forall_le`: for all large `i`, the
  bounds `#(S j \ D) ≤ σ j` for `j ≤ i` imply them for every `j`, for every upper set `D`.

## References

* The limit set `E` of a sequence of upper sets and its finitely many vertices are the
  finite-vertex diagram argument of E. Bierstone and P. D. Milman, *Uniformization of analytic
  spaces*, J. Amer. Math. Soc. 2 (1989), Theorem 5.2.1, as used in E. Bierstone, P. D. Milman and
  M. Temkin, *𝒬-universal desingularization*, Asian J. Math. 15 (2011), §6.1. The same argument
  proves the lexicographic stabilization `TauCeti.not_strictAnti_toLex_ncard_sdiff`.
-/

public section

open Filter Topology

namespace TauCeti

variable {α : Type*} [LE α] [WellQuasiOrderedLE α]

/-- For a family of upper sets `D m` of a well-quasi-order and a nontrivial filter `l`, there is
an upper set `E` such that, for every finite set `s`, frequently along `l` the set `D m` contains
`E` and agrees with `E` on `s`. -/
theorem exists_frequently_subset_and_agree_on_finite {ι : Type*} {l : Filter ι} [l.NeBot]
    {D : ι → Set α} (hD : ∀ m, IsUpperSet (D m)) :
    ∃ E : Set α, IsUpperSet E ∧ ∀ s : Set α, s.Finite →
      ∃ᶠ m in l, E ⊆ D m ∧ ∀ a ∈ s, (a ∈ D m ↔ a ∈ E) := by
  classical
  -- `E` is given by a cluster point `x` of the indicator functions in the compact `α → Bool`.
  obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace (map (fun m (a : α) ↦ decide (a ∈ D m)) l)
  -- Frequently `D m` agrees with `E` on a given finite set.
  have hagree {s : Set α} (hs : s.Finite) : ∃ᶠ m in l, ∀ a ∈ s, (a ∈ D m ↔ x a = true) := by
    have hmem : s.pi (fun a ↦ {x a}) ∈ 𝓝 x :=
      set_pi_mem_nhds hs fun a _ ↦ by simp [nhds_discrete]
    refine (mapClusterPt_iff_frequently.1 hx _ hmem).mono fun m hm a ha ↦ ?_
    rw [← Set.mem_singleton_iff.1 (Set.mem_pi.1 hm a ha), decide_eq_true_iff]
  refine ⟨{a | x a = true}, fun a b hab ha ↦ ?_, fun s hs ↦ ?_⟩
  · obtain ⟨m, hm⟩ := (hagree (Set.toFinite {a, b})).exists
    have haD := (hm a (Set.mem_insert a {b})).2 ha
    exact (hm b (Set.mem_insert_of_mem a rfl)).1 (hD m hab haD)
  -- Agreement on the finitely many elements `t` below `E` puts `E` inside `D m`.
  obtain ⟨t, htE, hcov⟩ := Set.PartiallyWellOrderedOn.exists_finset_subset_forall_exists
    (Set.partiallyWellOrderedOn_of_wellQuasiOrdered wellQuasiOrdered_le {a | x a = true})
  refine (hagree (hs.union t.finite_toSet)).mono fun m hm ↦ ⟨fun b hb ↦ ?_, fun a ha ↦
    hm a (Set.mem_union_left _ ha)⟩
  obtain ⟨a, hat, hab⟩ := hcov b hb
  exact hD m hab ((hm a (Set.mem_union_right _ hat)).2 (htE hat))

/-- In a well-quasi-order, let `S j` be sets and `σ j` natural numbers. For all large `i`, every
upper set `D` that omits at most `σ j` elements of `S j` for each `j ≤ i` does so for every
`j`. -/
theorem eventually_forall_encard_sdiff_le_of_isUpperSet_of_forall_le (S : ℕ → Set α)
    (σ : ℕ → ℕ) :
    ∀ᶠ i in atTop, ∀ D : Set α, IsUpperSet D →
      (∀ j ≤ i, (S j \ D).encard ≤ σ j) → ∀ j, (S j \ D).encard ≤ σ j := by
  by_contra h
  simp only [not_eventually, not_forall, not_le, exists_prop] at h
  -- Bad upper sets `D m` along a subsequence `φ`, and a set `E` that they approach.
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop h
  choose D hD hgood k hk using hbad
  obtain ⟨E, -, hE⟩ := exists_frequently_subset_and_agree_on_finite (l := atTop) hD
  -- `E` satisfies every bound: `σ j + 1` elements of `S j \ E` are omitted by some `D m` with
  -- `j ≤ φ m`.
  have hEle (j : ℕ) : (S j \ E).encard ≤ σ j := by
    by_contra! hlt
    obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_encard_eq (ENat.natCast_add_one_le_iff.2 hlt)
    have hT : T.Finite := Set.finite_of_encard_eq_coe (k := σ j + 1) (by exact_mod_cast hTcard)
    obtain ⟨m, ⟨-, hm⟩, hjm⟩ := ((hE T hT).and_eventually (eventually_ge_atTop j)).exists
    have hTD : T ⊆ S j \ D m := fun a ha ↦ by
      obtain ⟨haS, haE⟩ := (Set.mem_sdiff a).1 (hTS ha)
      exact (Set.mem_sdiff a).2 ⟨haS, fun haD ↦ haE ((hm a ha).1 haD)⟩
    have hle := (Set.encard_le_encard hTD).trans (hgood m j (hjm.trans (hφ.id_le m)))
    rw [hTcard] at hle
    exact (ENat.natCast_add_one_le_iff.1 hle).false
  -- Some `D m` contains `E`, so it satisfies every bound too.
  obtain ⟨m, hm, -⟩ := (hE ∅ Set.finite_empty).exists
  exact (hk m).not_ge ((Set.encard_le_encard (Set.sdiff_subset_sdiff_right hm)).trans (hEle _))

end TauCeti
