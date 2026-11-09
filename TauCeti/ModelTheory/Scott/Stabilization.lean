/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Equivalence
public import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.EventuallyConst

/-!
# Internal stabilization of back-and-forth equivalence

For a fixed structure, simultaneous one-step stabilization at every tuple length implies
stabilization at every later ordinal. The propagation argument is stated for tuples of two
structures, so that it also serves stabilization against other structures. Every structure
stabilizes, and a countable structure stabilizes below the first uncountable ordinal. The least
such level is `selfStabilizationOrdinal`. This supplies an internal level at which
characteristic formulas can be used to construct a Scott sentence.

Apart from that propagation lemma and the upgrade at limit levels of equivalence with a tuple of
another structure, both tuples belong to the same structure. No countability of the language is
needed: the countable set used in the bound consists of pairs of finite tuples of the structure,
rather than formulas. The stabilization ordinal lives in the universe of the structure.

## Main results

* `bfEquiv_of_le_of_forall_add_one`: between two structures, one-step stabilization at every tuple
  length propagates to all later levels.
* `SelfStabilizesCompletely.bfEquiv_of_le`: one-step stabilization propagates to all later levels.
* `SelfStabilizesCompletely.bfEquiv_add_one_of_isSuccLimit`: internal stabilization at `α`
  upgrades equivalence with a tuple of any structure at every limit `β > α` to `β + 1`.
* `exists_selfStabilizesCompletely`: every structure has a stabilizing level.
* `exists_complete_self_stabilization`: a countable structure has one below `ω₁`.
* `selfStabilizationOrdinal_lt_omega_one`: the least stabilizing level is below `ω₁`.

## References

* Dana Scott, Logic with denumerably long formulas and finite strings of quantifiers, 1965.
* Cameron Freer's `cameronfreer/infinitary-logic`, checkpoint
  `9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, `InfinitaryLogic/Scott/Sentence.lean` and
  `InfinitaryLogic/Scott/OrbitRankStabilization.lean`, develops these internal stabilization
  statements. Here the unrestricted existence proof uses Mathlib's eventual constancy of
  ordinal-indexed antitone maps; the countable bound takes a supremum of failure witnesses.
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder Fin
open scoped Ordinal

variable {L : Language.{u, v}} [L.IsRelational]
variable (M : Type w) [L.Structure M]

/-- A structure stabilizes internally at `α` if, simultaneously at every tuple length,
back-and-forth equivalence at `α` is equivalent to equivalence at `α + 1`. -/
def SelfStabilizesCompletely (α : Ordinal.{o}) : Prop :=
  ∀ (n : ℕ) (a b : Fin n → M), BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (α + 1) n a b

/-- Internal stabilization is simultaneous one-step stabilization at all tuple lengths. -/
theorem selfStabilizesCompletely_def (α : Ordinal.{o}) :
    SelfStabilizesCompletely (L := L) M α ↔
      ∀ (n : ℕ) (a b : Fin n → M),
        BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (α + 1) n a b := Iff.rfl

section Propagation

variable {M} {N : Type w'} [L.Structure N]

/-- If, between two fixed structures, back-and-forth equivalence at `α` upgrades to `α + 1` for
tuples of every length, then equivalence at `α` persists at every later level. -/
theorem bfEquiv_of_le_of_forall_add_one {α β : Ordinal.{o}}
    (h : ∀ (n : ℕ) (a : Fin n → M) (b : Fin n → N),
      BFEquiv (L := L) α n a b → BFEquiv (L := L) (α + 1) n a b)
    (hαβ : α ≤ β) {n : ℕ} {a : Fin n → M} {b : Fin n → N} (hab : BFEquiv (L := L) α n a b) :
    BFEquiv (L := L) β n a b := by
  induction β using Ordinal.limitRecOn generalizing n with
  | zero => exact hab.mono bot_le
  | add_one β ih =>
    rcases eq_or_lt_of_le hαβ with heq | hlt
    · exact heq ▸ hab
    · have hαβ' := Order.le_of_lt_succ hlt
      obtain ⟨_, hforth, hback⟩ := (BFEquiv.add_one α a b).mp (h n a b hab)
      refine (BFEquiv.add_one β a b).mpr ⟨ih hαβ' hab, ?_, ?_⟩
      · intro x
        obtain ⟨y, hy⟩ := hforth x
        exact ⟨y, ih hαβ' hy⟩
      · intro y
        obtain ⟨x, hx⟩ := hback y
        exact ⟨x, ih hαβ' hx⟩
  | limit β hβ ih =>
    refine (BFEquiv.limit hβ a b).mpr fun γ hγ => ?_
    by_cases hαγ : α ≤ γ
    · exact ih γ hγ hαγ hab
    · exact hab.mono (le_of_not_ge hαγ)

end Propagation

variable {M}

namespace SelfStabilizesCompletely

/-- Once all tuple lengths stabilize, equivalence at that level persists at every later level. -/
theorem bfEquiv_of_le {α β : Ordinal.{o}} (h : SelfStabilizesCompletely (L := L) M α)
    (hαβ : α ≤ β) {n : ℕ} {a b : Fin n → M} (hab : BFEquiv (L := L) α n a b) :
    BFEquiv (L := L) β n a b :=
  bfEquiv_of_le_of_forall_add_one (fun n a b => (h n a b).mp) hαβ hab

/-- At every level above a stabilizing level, the internal equivalence relations agree. -/
theorem bfEquiv_iff {α β : Ordinal.{o}} (h : SelfStabilizesCompletely (L := L) M α)
    (hαβ : α ≤ β) {n : ℕ} {a b : Fin n → M} :
    BFEquiv (L := L) β n a b ↔ BFEquiv (L := L) α n a b :=
  ⟨fun hab => hab.mono hαβ, h.bfEquiv_of_le hαβ⟩

/-- Every level above a stabilizing level is itself stabilizing. -/
theorem mono {α β : Ordinal.{o}} (h : SelfStabilizesCompletely (L := L) M α)
    (hαβ : α ≤ β) : SelfStabilizesCompletely (L := L) M β := by
  intro n a b
  exact (h.bfEquiv_iff hαβ).trans (h.bfEquiv_iff (hαβ.trans le_self_add)).symm

section Partner

variable {N : Type w'} [L.Structure N] {α : Ordinal.{o}}

/-- In a structure stabilizing internally at `α`, a tuple `α`-equivalent to an outside tuple `v`
is equivalent to `v` at every level `δ ≥ α` at which some tuple of the structure is. -/
theorem bfEquiv_of_bfEquiv_of_le (h : SelfStabilizesCompletely (L := L) M α) {n : ℕ}
    {u w : Fin n → M} {v : Fin n → N} {δ : Ordinal.{o}} (hαδ : α ≤ δ)
    (huv : BFEquiv (L := L) α n u v) (hwv : BFEquiv (L := L) δ n w v) :
    BFEquiv (L := L) δ n u v :=
  (h.bfEquiv_of_le hαδ (huv.trans (hwv.mono hαδ).symm)).trans hwv

/-- **Internal stabilization gives external stabilization at limits.** If `M` stabilizes
internally at `α`, then at every limit level `β > α`, back-and-forth equivalence at `β` between
a tuple of `M` and a tuple of any structure `N` upgrades to `β + 1`. -/
theorem bfEquiv_add_one_of_isSuccLimit (h : SelfStabilizesCompletely (L := L) M α)
    {β : Ordinal.{o}} (hβ : Order.IsSuccLimit β) (hαβ : α < β) {n : ℕ} {a : Fin n → M}
    {b : Fin n → N} (hab : BFEquiv (L := L) β n a b) : BFEquiv (L := L) (β + 1) n a b := by
  have hlt : ∀ γ < β, BFEquiv (L := L) (γ + 1) n a b :=
    fun γ hγ => hab.mono (hβ.add_one_lt hγ).le
  -- An extension pair matched at level `α` is matched at every level below `β`: compare it,
  -- inside `M`, with an extension matched at that level.
  have key : ∀ x y, BFEquiv (L := L) α (n + 1) (snoc a x) (snoc b y) →
      BFEquiv (L := L) β (n + 1) (snoc a x) (snoc b y) := by
    intro x y hxy
    refine (BFEquiv.limit hβ _ _).mpr fun γ hγ => ?_
    obtain ⟨x', hx'⟩ := ((BFEquiv.add_one _ a b).mp (hlt (max γ α) (max_lt hγ hαβ))).2.2 y
    exact (h.bfEquiv_of_bfEquiv_of_le (le_max_right γ α) hxy hx').mono (le_max_left γ α)
  obtain ⟨-, hforth, hback⟩ := (BFEquiv.add_one α a b).mp (hlt α hαβ)
  refine (BFEquiv.add_one β a b).mpr ⟨hab, fun x => ?_, fun y => ?_⟩
  · obtain ⟨y, hy⟩ := hforth x
    exact ⟨y, key x y hy⟩
  · obtain ⟨x, hx⟩ := hback y
    exact ⟨x, key x y hx⟩

end Partner

end SelfStabilizesCompletely

variable (M)

/-- Every structure stabilizes at some ordinal in its own universe, without countability
assumptions on either the structure or its relational language. -/
theorem exists_selfStabilizesCompletely :
    ∃ α : Ordinal.{w}, SelfStabilizesCompletely (L := L) M α := by
  let f : Ordinal.{w} → Set (Σ n, (Fin n → M) × (Fin n → M)) :=
    fun α => {p | BFEquiv (L := L) α p.1 p.2.1 p.2.2}
  have hf : Antitone f := fun _ _ h p hp => hp.mono h
  obtain ⟨α, hα⟩ := Filter.eventuallyConst_atTop.mp (Ordinal.eventuallyConst_of_antitone hf)
  refine ⟨α, fun n a b => ?_⟩
  exact (Set.ext_iff.mp (hα (α + 1) le_self_add) ⟨n, a, b⟩).symm

/-- A countable structure stabilizes below `ω₁`. Only its tuples are counted; the language
may be uncountable. -/
theorem exists_complete_self_stabilization [Countable M] :
    ∃ α : Ordinal.{w}, α < ω₁ ∧ SelfStabilizesCompletely (L := L) M α := by
  classical
  let P (p : Σ n, (Fin n → M) × (Fin n → M)) (β : Ordinal.{w}) :=
    BFEquiv (L := L) β p.1 p.2.1 p.2.2
  -- Choose one failure below `ω₁` for every pair that has such a failure.
  have hw : ∀ p, ∃ β : Ordinal.{w}, β < ω₁ ∧
      ((∃ γ < ω₁, ¬ P p γ) → ¬ P p β) := by
    intro p
    by_cases hp : ∃ γ < ω₁, ¬ P p γ
    · obtain ⟨γ, hγ, hpγ⟩ := hp
      exact ⟨γ, hγ, fun _ => hpγ⟩
    · exact ⟨0, (Cardinal.isSuccLimit_omega 1).pos, fun h => (hp h).elim⟩
  choose f hf hfail using hw
  have hα : (⨆ p, f p) < ω₁ := Ordinal.iSup_lt_omega_one hf
  refine ⟨⨆ p, f p, hα, fun n a b => ⟨fun hab => ?_, fun hab => hab.mono le_self_add⟩⟩
  by_contra hnext
  have hp : ∃ γ < ω₁, ¬ P ⟨n, a, b⟩ γ :=
    ⟨(⨆ p, f p) + 1, (Cardinal.isSuccLimit_omega 1).add_one_lt hα, hnext⟩
  exact hfail ⟨n, a, b⟩ hp (hab.mono (Ordinal.le_iSup f ⟨n, a, b⟩))

/-- The least ordinal, in the universe of the structure, at which all its finite tuples
simultaneously stabilize internally. -/
noncomputable def selfStabilizationOrdinal : Ordinal.{w} :=
  sInf {α | SelfStabilizesCompletely (L := L) M α}

/-- The least internal stabilization ordinal is the infimum of the stabilizing levels. -/
theorem selfStabilizationOrdinal_def :
    selfStabilizationOrdinal (L := L) M = sInf {α | SelfStabilizesCompletely (L := L) M α} :=
  (rfl)

/-- The infimum defining the least internal stabilization ordinal is attained. -/
@[simp]
theorem selfStabilizesCompletely_selfStabilizationOrdinal :
    SelfStabilizesCompletely (L := L) M (selfStabilizationOrdinal (L := L) M) := by
  rw [selfStabilizationOrdinal_def]
  exact csInf_mem (s := {α : Ordinal.{w} | SelfStabilizesCompletely (L := L) M α})
    (exists_selfStabilizesCompletely (L := L) M)

/-- The least internal stabilization ordinal is no larger than any stabilizing level. -/
theorem selfStabilizationOrdinal_le {α : Ordinal.{w}}
    (h : SelfStabilizesCompletely (L := L) M α) : selfStabilizationOrdinal (L := L) M ≤ α :=
  csInf_le' h

/-- A level stabilizes internally exactly when it is above the least stabilizing level. -/
theorem selfStabilizationOrdinal_le_iff {α : Ordinal.{w}} :
    selfStabilizationOrdinal (L := L) M ≤ α ↔ SelfStabilizesCompletely (L := L) M α :=
  ⟨fun h => (selfStabilizesCompletely_selfStabilizationOrdinal (L := L) M).mono h,
    selfStabilizationOrdinal_le M⟩

/-- The least internal stabilization ordinal of a countable structure is countable. -/
theorem selfStabilizationOrdinal_lt_omega_one [Countable M] :
    selfStabilizationOrdinal (L := L) M < ω₁ := by
  obtain ⟨α, hα, hs⟩ := exists_complete_self_stabilization (L := L) M
  exact (selfStabilizationOrdinal_le M hs).trans_lt hα

end TauCeti
