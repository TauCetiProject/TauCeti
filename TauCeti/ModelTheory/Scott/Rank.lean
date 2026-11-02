/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.AllLevels
public import TauCeti.ModelTheory.Scott.Stabilization

/-!
# Internal Scott rank

The orbit rank of a finite tuple is the least back-and-forth level at which its class
inside its own structure agrees with its class at every ordinal level. The internal
Scott rank is the supremum of the successors of these tuple ranks, over all tuple
lengths. Both ranks live in the universe of the structure.

The least simultaneous stabilization level is the supremum of the tuple ranks.
Consequently the internal Scott rank lies between that level and its successor,
and is below `ω₁` for every countable structure. No countability assumption on the
relational language is needed for these rank comparisons.

For a countable structure, the back-and-forth class of a tuple at any orbit-stable level, in
particular at its orbit rank, is exactly its automorphism orbit.

The all-levels condition in `orbitStable` is essential: a single tuple's class can
agree at two consecutive levels and still split later. Simultaneous stabilization
at all tuple lengths, supplied by `SelfStabilizesCompletely`, does propagate.

The rank convention follows Cameron Freer's `cameronfreer/infinitary-logic`, checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, `InfinitaryLogic/Scott/OrbitRank.lean`
and `InfinitaryLogic/Scott/OrbitRankStabilization.lean`. Here tuples of all lengths
are indexed by a sigma type, and existence comes from the existing internal
stabilization API.
-/

public section

universe u v w

namespace TauCeti

open FirstOrder
open scoped Ordinal

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M] {n : ℕ}

/-- The levels at which the internal back-and-forth class of `a` already agrees
with its class at every ordinal level. -/
def orbitStable (a : Fin n → M) : Set Ordinal.{w} :=
  {α | ∀ b : Fin n → M, BFEquiv (L := L) α n a b →
    ∀ β : Ordinal.{w}, BFEquiv (L := L) β n a b}

/-- Membership in `orbitStable` is the all-levels upgrade property for a tuple. -/
@[simp]
theorem mem_orbitStable_iff (a : Fin n → M) (α : Ordinal.{w}) :
    α ∈ orbitStable (L := L) a ↔
      ∀ b : Fin n → M, BFEquiv (L := L) α n a b →
        ∀ β : Ordinal.{w}, BFEquiv (L := L) β n a b := Iff.rfl

/-- Orbit stability persists at every larger level. -/
theorem orbitStable_mono (a : Fin n → M) {α β : Ordinal.{w}}
    (h : α ∈ orbitStable (L := L) a) (hαβ : α ≤ β) :
    β ∈ orbitStable (L := L) a := by
  rw [mem_orbitStable_iff] at h ⊢
  exact fun b hab γ => h b (hab.mono hαβ) γ

/-- A simultaneous stabilization level is orbit-stable for every tuple. -/
theorem SelfStabilizesCompletely.mem_orbitStable {α : Ordinal.{w}}
    (h : SelfStabilizesCompletely (L := L) M α) (a : Fin n → M) :
    α ∈ orbitStable (L := L) a := by
  rw [mem_orbitStable_iff]
  intro b hab β
  by_cases hαβ : α ≤ β
  · exact h.bfEquiv_of_le hαβ hab
  · exact hab.mono (le_of_not_ge hαβ)

/-- Every tuple has an orbit-stable level, without any countability assumption. -/
theorem orbitStable_nonempty (a : Fin n → M) : (orbitStable (L := L) a).Nonempty := by
  obtain ⟨α, hα⟩ := exists_selfStabilizesCompletely (L := L) M
  exact ⟨α, hα.mem_orbitStable a⟩

/-- The least level at which a tuple's internal back-and-forth class agrees with
its class at every ordinal level. -/
noncomputable def orbitRank (a : Fin n → M) : Ordinal.{w} :=
  sInf (orbitStable (L := L) a)

/-- The orbit rank is the infimum of the orbit-stable levels. -/
theorem orbitRank_def (a : Fin n → M) :
    orbitRank (L := L) a = sInf (orbitStable (L := L) a) := (rfl)

/-- The infimum defining the orbit rank is attained. -/
theorem orbitRank_mem_orbitStable (a : Fin n → M) :
    orbitRank (L := L) a ∈ orbitStable (L := L) a := by
  rw [orbitRank_def]
  exact csInf_mem (orbitStable_nonempty a)

/-- The orbit rank is no larger than any orbit-stable level. -/
theorem orbitRank_le (a : Fin n → M) {α : Ordinal.{w}}
    (h : α ∈ orbitStable (L := L) a) : orbitRank (L := L) a ≤ α :=
  csInf_le' h

/-- A level is orbit-stable exactly when it is at least the orbit rank. -/
theorem orbitRank_le_iff (a : Fin n → M) (α : Ordinal.{w}) :
    orbitRank (L := L) a ≤ α ↔ α ∈ orbitStable (L := L) a :=
  ⟨orbitStable_mono a (orbitRank_mem_orbitStable a), orbitRank_le a⟩

section Countable

variable [Countable M]

/-- In a countable structure, a level is orbit-stable for `a` exactly when every tuple
back-and-forth equivalent to `a` at that level lies in the automorphism orbit of `a`. -/
theorem mem_orbitStable_iff_of_countable (a : Fin n → M) (α : Ordinal.{w}) :
    α ∈ orbitStable (L := L) a ↔
      ∀ b : Fin n → M, BFEquiv (L := L) α n a b → ∃ σ : M ≃[L] M, σ ∘ a = b := by
  simp only [mem_orbitStable_iff, ← bfEquiv_all_iff_exists_equiv_comp_eq]

/-- In a countable structure, the back-and-forth class of `a` at an orbit-stable level is the
automorphism orbit of `a`. -/
theorem bfEquiv_iff_exists_equiv_comp_eq_of_mem_orbitStable {a b : Fin n → M}
    {α : Ordinal.{w}} (hα : α ∈ orbitStable (L := L) a) :
    BFEquiv (L := L) α n a b ↔ ∃ σ : M ≃[L] M, σ ∘ a = b :=
  ⟨(mem_orbitStable_iff_of_countable a α).mp hα b, fun ⟨σ, hσ⟩ => hσ ▸ σ.bfEquiv α a⟩

/-- In a countable structure, the back-and-forth class of `a` at its orbit rank is the
automorphism orbit of `a`. -/
theorem bfEquiv_orbitRank_iff_exists_equiv_comp_eq (a b : Fin n → M) :
    BFEquiv (L := L) (orbitRank (L := L) a) n a b ↔ ∃ σ : M ≃[L] M, σ ∘ a = b :=
  bfEquiv_iff_exists_equiv_comp_eq_of_mem_orbitStable (orbitRank_mem_orbitStable a)

end Countable

/-- Every tuple's orbit rank is bounded by the least simultaneous stabilization level. -/
theorem orbitRank_le_selfStabilizationOrdinal (a : Fin n → M) :
    orbitRank (L := L) a ≤ selfStabilizationOrdinal (L := L) M :=
  orbitRank_le a ((selfStabilizesCompletely_selfStabilizationOrdinal (L := L) M).mem_orbitStable a)

/-- The least simultaneous stabilization level is the supremum of the orbit ranks
of all finite tuples. This holds for arbitrary structures. -/
theorem selfStabilizationOrdinal_eq_iSup_orbitRank :
    selfStabilizationOrdinal (L := L) M =
      ⨆ p : Σ n, Fin n → M, orbitRank (L := L) p.2 := by
  apply le_antisymm
  · apply selfStabilizationOrdinal_le M
    rw [selfStabilizesCompletely_def]
    intro n a b
    refine ⟨fun hab => ?_, fun hab => hab.mono le_self_add⟩
    have hr := Ordinal.le_iSup (fun p : Σ n, Fin n → M => orbitRank (L := L) p.2) ⟨n, a⟩
    exact (mem_orbitStable_iff a _).mp (orbitRank_mem_orbitStable a) b (hab.mono hr) _
  · exact Ordinal.iSup_le fun p => orbitRank_le_selfStabilizationOrdinal p.2

variable (M)

/-- The internal Scott rank is the supremum, over all finite tuples, of the successor
of the tuple's orbit rank. In particular, even the empty structure has rank at least one. -/
noncomputable def internalScottRank : Ordinal.{w} :=
  ⨆ p : Σ n, Fin n → M, orbitRank (L := L) p.2 + 1

/-- The defining supremum for the internal Scott rank. -/
theorem internalScottRank_def :
    internalScottRank (L := L) M =
      ⨆ p : Σ n, Fin n → M, orbitRank (L := L) p.2 + 1 := (rfl)

/-- The internal Scott rank is at most `α` exactly when every finite tuple has orbit rank
strictly below `α`. -/
@[simp]
theorem internalScottRank_le_iff (α : Ordinal.{w}) :
    internalScottRank (L := L) M ≤ α ↔
      ∀ n (a : Fin n → M), orbitRank (L := L) a < α := by
  simp only [internalScottRank_def, Ordinal.iSup_add_one_le_iff, Sigma.forall]

variable {M}

/-- Every tuple's orbit rank is strictly below the internal Scott rank. -/
theorem orbitRank_lt_internalScottRank (a : Fin n → M) :
    orbitRank (L := L) a < internalScottRank (L := L) M := by
  rw [internalScottRank_def]
  exact (lt_add_one _).trans_le
    (Ordinal.le_iSup (fun p : Σ n, Fin n → M => orbitRank (L := L) p.2 + 1) ⟨n, a⟩)

/-- If every tuple is orbit-stable at `α` and some tuple has orbit rank `α`, then the
internal Scott rank is exactly the successor of `α`. -/
theorem internalScottRank_eq_add_one_of_mem_orbitStable_of_orbitRank_eq {m : ℕ} {a₀ : Fin m → M}
    {α : Ordinal.{w}}
    (hα : ∀ n (a : Fin n → M), α ∈ orbitStable (L := L) a)
    (h₀ : orbitRank (L := L) a₀ = α) :
    internalScottRank (L := L) M = α + 1 := by
  apply le_antisymm
  · rw [internalScottRank_le_iff]
    intro n a
    exact (orbitRank_le a (hα n a)).trans_lt (lt_add_one α)
  · rw [← h₀, Order.add_one_le_iff]
    exact orbitRank_lt_internalScottRank a₀

/-- The internal Scott rank is at least one, including for an empty structure. -/
theorem one_le_internalScottRank : 1 ≤ internalScottRank (L := L) M := by
  exact Order.one_le_iff_pos.mpr (bot_le.trans_lt
    (orbitRank_lt_internalScottRank (L := L) (Fin.elim0 : Fin 0 → M)))

/-- The least simultaneous stabilization level is no larger than the internal Scott rank. -/
theorem selfStabilizationOrdinal_le_internalScottRank :
    selfStabilizationOrdinal (L := L) M ≤ internalScottRank (L := L) M := by
  rw [selfStabilizationOrdinal_eq_iSup_orbitRank]
  exact Ordinal.iSup_le fun p => (orbitRank_lt_internalScottRank p.2).le

/-- The internal Scott rank is at most the successor of the least simultaneous
stabilization level. -/
theorem internalScottRank_le_succ_selfStabilizationOrdinal :
    internalScottRank (L := L) M ≤ selfStabilizationOrdinal (L := L) M + 1 := by
  rw [internalScottRank_def]
  exact Ordinal.iSup_le fun p => add_le_add (orbitRank_le_selfStabilizationOrdinal p.2) le_rfl

/-- Every countable structure has internal Scott rank below the first uncountable ordinal.
The relational language need not be countable. -/
theorem internalScottRank_lt_omega_one [Countable M] :
    internalScottRank (L := L) M < ω₁ :=
  internalScottRank_le_succ_selfStabilizationOrdinal.trans_lt
    ((Cardinal.isSuccLimit_omega 1).add_one_lt
      (selfStabilizationOrdinal_lt_omega_one (L := L) M))

end TauCeti
