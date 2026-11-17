/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Order.Ring.Rat
import TauCeti.ModelTheory.Scott.WellOrder
import TauCeti.ModelTheory.WellOrdering.Bounded

/-!
# Well-orderings of bounded countable type and rational chains

Examples exercising `TauCeti.ModelTheory.WellOrdering`,
`TauCeti.ModelTheory.WellOrdering.Bounded`, `TauCeti.ModelTheory.BackAndForth.WellOrder`, and
`TauCeti.ModelTheory.Scott.WellOrder`:

* A map `f : ℚ → M` with `RelChain lt f` yields an explicit strictly descending `lt`-sequence
  `f (-1), f (-2), …`, making `lt` ill-founded in `M`.
* For every countable ordinal `α < ω₁`, `boundedWellOrderSentence lt α hα` has as its models
  (both among countable structures and among structures of arbitrary cardinality) precisely the
  well-orders of order type strictly below `α`.
* For `α = ω`, this sentence holds in `(Fin 3, <)`, fails in `(ℕ, <)` (which satisfies
  `wellOrderTypeSentence lt ω`), and fails in `(ℤ, <)` and `(ℚ, <)`.
* Applying `Sentenceω.wellOrder_type_boundedness` to `boundedWellOrderSentence lt α hα` returns a
  countable bound `β < ω₁` with `α ≤ β` whenever `α ≠ 1`, while no single `L_{ω₁ω}` sentence
  defines well-orders of type `< ω₁` or covers all countable well-orders.
* By rigidity of well-orders, `ℕ` has an `L_{ω₁ω}` sentence in `Language.order` whose models in
  `Type 1`, with no countability assumption, are all order-isomorphic to `ℕ`.
-/

open FirstOrder FirstOrder.Language Structure Ordinal TauCeti
open scoped Ordinal

-- A rational `lt`-chain makes `lt` ill-founded explicitly via `f (-1), f (-2), …`.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] {lt : L.Relations 2}
    {f : ℚ → M} (hf : RelChain lt f) :
    (∀ n : ℕ, RelMap lt ![f (-((n + 1 : ℕ) + 1 : ℚ)), f (-((n + 1 : ℕ) : ℚ))]) ∧
      ¬ WellFounded (fun x y : M => RelMap lt ![x, y]) := by
  have hstep : ∀ n : ℕ,
      RelMap lt ![f (-((n + 1 : ℕ) + 1 : ℚ)), f (-((n + 1 : ℕ) : ℚ))] :=
    fun n => (relChain_iff.1 hf) _ _ (neg_lt_neg (lt_add_one _))
  refine ⟨hstep, fun hwf => ?_⟩
  obtain ⟨_, ⟨n, rfl⟩, hmin⟩ :=
    hwf.has_min (Set.range fun n : ℕ => f (-((n + 1 : ℕ) : ℚ))) (Set.range_nonempty _)
  have hnext :
      f (-((n + 1 : ℕ) + 1 : ℚ)) ∈ Set.range fun k : ℕ => f (-((k + 1 : ℕ) : ℚ)) :=
    ⟨n + 1, by push_cast; rfl⟩
  exact hmin _ hnext (hstep n)

-- `RelChain.not_wellFounded` discharges the same rational-chain ill-foundedness directly.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] {lt : L.Relations 2}
    {f : ℚ → M} (hf : RelChain lt f) : ¬ WellFounded (fun x y : M => RelMap lt ![x, y]) :=
  hf.not_wellFounded

-- For `α < ω₁` with `α ≠ 1`, `boundedWellOrderSentence lt α hα` characterizes well-orders of
-- type `< α` (both countable and arbitrary), and `wellOrder_type_boundedness` returns a sharp
-- bound `β < ω₁` with `α ≤ β`.
example {L : Language.{u, v}} (lt : L.Relations 2) {α : Ordinal.{w}} (hα : α < ω₁)
    (hα1 : α ≠ 1) :
    (∀ (M : Type w) [L.Structure M],
      SentenceInf.Realize (boundedWellOrderSentence lt α hα) M ↔
        ∃ h : IsWellOrder M (fun x y => RelMap lt ![x, y]), @Ordinal.type M _ h < α) ∧
    (∃ β : Ordinal.{w}, β < ω₁ ∧ α ≤ β ∧
      ∀ (M : Type w) (inst : L.Structure M)
        (h : SentenceInf.Realize (boundedWellOrderSentence lt α hα) M),
        @Ordinal.type M (fun x y => RelMap lt ![x, y])
          (isWellOrder_of_realize_boundedWellOrderSentence lt hα h) < β) := by
  refine ⟨fun M _ => realize_boundedWellOrderSentence_iff_lt lt hα M, ?_⟩
  obtain ⟨β, hβ, hbound⟩ := Sentenceω.wellOrder_type_boundedness
    (φ := boundedWellOrderSentence lt α hα) (lt := lt)
    fun M _ h => isWellOrder_of_realize_boundedWellOrderSentence lt hα h
  exact ⟨β, hβ,
    le_of_forall_type_lt_of_realize_boundedWellOrderSentence lt hα hα1 hbound, hbound⟩

-- Concrete test at `α = ω`: `(Fin 3, <)` satisfies `boundedWellOrderSentence lt ω`, while
-- `(ℕ, <)` satisfies `wellOrderTypeSentence lt ω` and fails `boundedWellOrderSentence lt ω`,
-- and the non-well-founded linear orders `(ℤ, <)` and `(ℚ, <)` fail it as well.
example :
    let L₀ : Language := ⟨fun _ => Empty, fun k => PLift (k = 2)⟩
    let lt : L₀.Relations 2 := ⟨rfl⟩
    let mkStr (α : Type) [LT α] : L₀.Structure α :=
      { funMap := fun f => Empty.elim f
        RelMap := fun {n} _ xs => match n, xs with | 2, xs => xs 0 < xs 1 | _, _ => False }
    have hω : (ω : Ordinal.{0}) < ω₁ := Ordinal.omega0_lt_omega_one
    letI := mkStr (Fin 3)
    letI := mkStr ℕ
    letI := mkStr ℤ
    letI := mkStr ℚ
    SentenceInf.Realize (boundedWellOrderSentence lt ω hω) (Fin 3) ∧
      SentenceInf.Realize (wellOrderTypeSentence lt ω hω) ℕ ∧
      ¬ SentenceInf.Realize (boundedWellOrderSentence lt ω hω) ℕ ∧
      ¬ SentenceInf.Realize (boundedWellOrderSentence lt ω hω) ℤ ∧
      ¬ SentenceInf.Realize (boundedWellOrderSentence lt ω hω) ℚ := by
  intro L₀ lt mkStr hω
  let := mkStr (Fin 3)
  let := mkStr ℕ
  let := mkStr ℤ
  let := mkStr ℚ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [realize_boundedWellOrderSentence_iff_lt]
    exact ⟨inferInstanceAs (IsWellOrder (Fin 3) (· < ·)), by simp⟩
  · rw [realize_wellOrderTypeSentence_iff_eq]
    exact ⟨inferInstanceAs (IsWellOrder ℕ (· < ·)), Ordinal.type_nat_lt⟩
  · rw [realize_boundedWellOrderSentence_iff_lt]
    rintro ⟨hwo, hlt⟩
    exact (lt_irrefl ω) (Ordinal.type_nat_lt ▸ hlt)
  · intro h
    have hwf : WellFounded (· < · : ℤ → ℤ → Prop) :=
      (isWellOrder_of_realize_boundedWellOrderSentence lt hω h).wf
    exact RelChain.not_wellFounded (L := L₀) (lt := lt) (f := id)
      (relChain_iff.2 fun _ _ hxy => hxy) hwf
  · intro h
    have hwf : WellFounded (· < · : ℚ → ℚ → Prop) :=
      (isWellOrder_of_realize_boundedWellOrderSentence lt hω h).wf
    exact RelChain.not_wellFounded (L := L₀) (lt := lt) (f := id)
      (relChain_iff.2 fun _ _ hxy => hxy) hwf

-- No `L_{ω₁ω}` sentence defines well-orders of type `< ω₁` (even among countable nonempty
-- structures), and no single sentence defines the class of all countable well-orders.
example {L : Language.{u, v}} (lt : L.Relations 2) :
    (¬ ∃ φ : L.Sentenceω, ∀ (M : Type w) (_ : L.Structure M), Nonempty M → Countable M →
      (SentenceInf.Realize φ M ↔
        ∃ h : IsWellOrder M (fun x y => RelMap lt ![x, y]), @Ordinal.type M _ h < ω₁)) ∧
    (¬ ∃ φ : L.Sentenceω, ∀ (M : Type w) (_ : L.Structure M), Nonempty M → Countable M →
      (SentenceInf.Realize φ M ↔ IsWellOrder M (fun x y => RelMap lt ![x, y]))) :=
  ⟨fun h => (lt_irrefl (ω₁ : Ordinal.{w}))
      ((exists_sentenceω_realize_iff_isWellOrder_type_lt_countable_iff lt ω₁).mp h),
    wellOrdering_undefinable lt⟩

-- `ℕ` has an `L_{ω₁ω}` sentence in `Language.order` whose models in `Type 1`, with no countability
-- hypothesis, are all order-isomorphic to `ℕ` (and therefore countable).
example :
    ∃ σ : Language.order.Sentenceω, ∀ (N : Type 1) [Language.order.Structure N] [LE N]
      [Language.order.OrderedStructure N],
      SentenceInf.Realize σ N → Nonempty (ℕ ≃o N) ∧ Countable N := by
  obtain ⟨σ, hσ⟩ := exists_sentenceω_realize_iff_nonempty_orderIso_of_wellFoundedLT.{0, 1} ℕ
  refine ⟨σ, fun N _ _ _ hN => ?_⟩
  obtain ⟨e⟩ := (hσ N).mp hN
  exact ⟨⟨e⟩, e.toEquiv.surjective.countable⟩

-- Isomorphisms out of `(ℕ, ≤)` are unique even into an arbitrary `Language.order`-structure.
example (N : Type w) [Language.order.Structure N] :
    letI := orderStructure ℕ
    Subsingleton (ℕ ≃[Language.order] N) := by
  let := orderStructure ℕ
  exact Equiv.subsingleton_of_wellFoundedLT
