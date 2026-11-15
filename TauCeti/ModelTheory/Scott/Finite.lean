/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Presentation
public import TauCeti.ModelTheory.Scott.Rank
public import Mathlib.Data.Set.Card

/-!
# Finite structures have finite Scott rank

In a relational language, a finite structure `M` is determined by finitely many rounds of the
back-and-forth game. If a tuple `a` of `M` is back-and-forth equivalent to a tuple `b` of some
structure `N` at a natural level `k` with `Nat.card M ≤ k + (Set.range a).ncard`, then the forth
moves can enumerate the remaining elements of `M` one at a time. The final tuples have the same
atomic type and the first one is onto `M`, so it induces an embedding `M ↪[L] N` carrying `a`
to `b`.

When `N = M`, such an embedding is an automorphism. Back-and-forth equivalence at level
`Nat.card M` therefore already pins down automorphism orbits of tuples. Consequently a finite
structure stabilizes internally at `Nat.card M`, and its internal Scott rank is at most
`Nat.card M + 1`, in particular below `ω`. No countability of the language is needed.

## Main results

* `BFEquiv.exists_embedding_comp_eq`: enough rounds of the back-and-forth game from a tuple of a
  finite structure give an embedding of the whole structure.
* `bfEquiv_iff_exists_equiv_comp_eq`: in a finite structure, back-and-forth equivalence at such
  a level is equivalent to lying in one automorphism orbit.
* `internalScottRank_le_natCard_add_one`, `internalScottRank_lt_omega0`: the internal Scott rank
  of a finite structure is finite.

## References

* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, for
  back-and-forth equivalence and Scott rank.
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder FirstOrder.Language Fin
open scoped Ordinal

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] {n : ℕ}

/-- Back-and-forth equivalence of a tuple `a` of a finite structure `M` with a tuple `b`, at a
natural level `k` large enough to enumerate the elements of `M` outside the range of `a`, gives
an embedding of `M` into `N` carrying `a` to `b`. -/
theorem BFEquiv.exists_embedding_comp_eq [Finite M] {k : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hk : Nat.card M ≤ k + (Set.range a).ncard) (h : BFEquiv (L := L) (k : Ordinal.{o}) n a b) :
    ∃ f : M ↪[L] N, f ∘ a = b := by
  induction k generalizing n with
  | zero =>
    -- The range of `a` already has `Nat.card M` elements, so it is all of `M`.
    refine h.sameAtomicType.exists_embedding_comp_eq (Set.range_eq_univ.mp ?_)
    exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ]; omega)
  | succ k ih =>
    by_cases ha : Function.Surjective a
    · exact h.sameAtomicType.exists_embedding_comp_eq ha
    -- Spend one forth move on an element outside the range of `a`.
    obtain ⟨x, hx⟩ := not_forall.mp ha
    rw [Nat.cast_succ, BFEquiv.add_one] at h
    obtain ⟨y, hy⟩ := h.2.1 x
    have hx' : x ∉ Set.range a := fun ⟨i, hi⟩ => hx ⟨i, hi⟩
    obtain ⟨f, hf⟩ := ih (by rw [range_snoc, Set.ncard_insert_of_notMem hx']; omega) hy
    refine ⟨f, funext fun i => ?_⟩
    simpa using congrFun hf (castSucc i)

/-- In a finite structure, back-and-forth equivalence at a natural level `k` large enough to
enumerate the elements outside the range of `a` means lying in one automorphism orbit. -/
theorem bfEquiv_iff_exists_equiv_comp_eq [Finite M] {k : ℕ} {a b : Fin n → M}
    (hk : Nat.card M ≤ k + (Set.range a).ncard) :
    BFEquiv (L := L) (k : Ordinal.{o}) n a b ↔ ∃ σ : M ≃[L] M, σ ∘ a = b := by
  refine ⟨fun h => ?_, fun ⟨σ, hσ⟩ => hσ ▸ σ.bfEquiv _ a⟩
  obtain ⟨f, hf⟩ := h.exists_embedding_comp_eq hk
  exact ⟨⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp f.injective), f.map_fun',
    f.map_rel'⟩, hf⟩

variable (M) in
/-- A finite structure stabilizes internally at its cardinality. -/
theorem selfStabilizesCompletely_natCard [Finite M] :
    SelfStabilizesCompletely (L := L) M (Nat.card M : Ordinal.{o}) := by
  rw [selfStabilizesCompletely_def]
  intro n a b
  refine ⟨fun h => ?_, fun h => h.mono le_self_add⟩
  obtain ⟨σ, rfl⟩ := (bfEquiv_iff_exists_equiv_comp_eq (Nat.le_add_right _ _)).mp h
  exact σ.bfEquiv _ a

/-- The orbit rank of a tuple in a finite structure is at most the number of elements outside
its range. -/
theorem orbitRank_le_natCard_sub_ncard_range [Finite M] (a : Fin n → M) :
    orbitRank (L := L) a ≤ (Nat.card M - (Set.range a).ncard : ℕ) := by
  apply orbitRank_le
  rw [mem_orbitStable_iff]
  intro b h β
  obtain ⟨σ, rfl⟩ := (bfEquiv_iff_exists_equiv_comp_eq (by omega)).mp h
  exact σ.bfEquiv β a

variable (M)

/-- The least internal stabilization ordinal of a finite structure is at most its cardinality. -/
theorem selfStabilizationOrdinal_le_natCard [Finite M] :
    selfStabilizationOrdinal (L := L) M ≤ Nat.card M :=
  selfStabilizationOrdinal_le M (selfStabilizesCompletely_natCard M)

/-- The internal Scott rank of a finite structure is at most one more than its cardinality. -/
theorem internalScottRank_le_natCard_add_one [Finite M] :
    internalScottRank (L := L) M ≤ Nat.card M + 1 :=
  internalScottRank_le_succ_selfStabilizationOrdinal.trans
    (add_le_add_left (selfStabilizationOrdinal_le_natCard M) 1)

/-- A finite structure has finite internal Scott rank. -/
theorem internalScottRank_lt_omega0 [Finite M] : internalScottRank (L := L) M < ω :=
  (internalScottRank_le_natCard_add_one M).trans_lt (by
    exact_mod_cast Ordinal.natCast_lt_omega0 (Nat.card M + 1))

end TauCeti
