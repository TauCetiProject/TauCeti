/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Scott.WellOrder
import Mathlib.Algebra.Order.Ring.Rat
import TauCeti.ModelTheory.WellOrdering
import TauCeti.ModelTheory.WellOrdering.Bounded

/-!
# Well-orders of bounded type and rational chains

Examples exercising `TauCeti.ModelTheory.WellOrdering`, `TauCeti.ModelTheory.WellOrdering.Bounded`,
`TauCeti.ModelTheory.BackAndForth.WellOrder`, and `TauCeti.ModelTheory.Scott.WellOrder`:
* `boundedWellOrderSentence` on `Language.order` (interpreting `.le` as `<`) characterizes
  well-orders of order type below a countable ordinal `α`, and `α` itself is not a model;
* rational `lt`-chains witness ill-foundedness both via `wellFounded_iff_isEmpty_descending_chain`
  on `f (-1), f (-2), …` and via `RelChain.not_wellFounded`;
* sharpness of `Sentenceω.wellOrder_type_boundedness` on `boundedWellOrderSentence`, concrete
  models at `α = ω` (`Fin 3`, `ℕ`, `ℤ`, `ℚ`), undefinability at `ω₁` and
  `wellOrdering_undefinable`, uncountable-model Scott characterization for `ℕ` in `Type 1`, and
  rigidity of `(ℕ, ≤)`.
-/

public section

open FirstOrder FirstOrder.Language Structure Ordinal

universe u v w w'

section Examples

open TauCeti
open scoped Ordinal

-- On `Language.order` with `.le` interpreted as `<`, `boundedWellOrderSentence` characterizes
-- well-orders of order type below `α`.
example {α : Ordinal.{w}} (hα : α < ω₁) (N : Type w') [LinearOrder N] :
    letI := @orderStructure N ⟨(· < ·)⟩
    SentenceInf.Realize
        (boundedWellOrderSentence (L := Language.order) (leSymb : Language.order.Relations 2) α
          hα)
        N ↔
      ∃ _ : WellFoundedLT N, lift.{w} (typeLT N) < lift.{w'} α := by
  let := @orderStructure N ⟨(· < ·)⟩
  rw [realize_boundedWellOrderSentence_iff]
  change (∃ h : IsWellOrder N (· < ·), lift.{w} (@Ordinal.type N (· < ·) h) < lift.{w'} α) ↔ _
  exact ⟨fun ⟨hwo, hlt⟩ => ⟨hwo.wf, hlt⟩, fun ⟨_, hlt⟩ => ⟨inferInstance, hlt⟩⟩

-- The ordinal `α` itself is not a model of `boundedWellOrderSentence` for `<` below `α`.
example {α : Ordinal.{w}} (hα : α < ω₁) :
    letI := @orderStructure α.ToType ⟨(· < ·)⟩
    ¬ SentenceInf.Realize
        (boundedWellOrderSentence (L := Language.order) (leSymb : Language.order.Relations 2) α
          hα)
        α.ToType := by
  let := @orderStructure α.ToType ⟨(· < ·)⟩
  rw [realize_boundedWellOrderSentence_iff_lt]
  change ¬ ∃ h : IsWellOrder α.ToType (· < ·), @Ordinal.type α.ToType (· < ·) h < α
  rintro ⟨_, hlt⟩
  simp [Ordinal.type_toType] at hlt

-- A rational `lt`-chain makes `lt` ill-founded explicitly via `f (-1), f (-2), …`.
example {L : Language.{u, v}} {M : Type w} [L.Structure M] {lt : L.Relations 2}
    {f : ℚ → M} (hf : RelChain lt f) :
    (∀ n : ℕ, RelMap lt ![f (-((n + 1 : ℕ) + 1 : ℚ)), f (-((n + 1 : ℕ) : ℚ))]) ∧
      ¬ WellFounded (fun x y : M => RelMap lt ![x, y]) := by
  have hstep : ∀ n : ℕ,
      RelMap lt ![f (-((n + 1 : ℕ) + 1 : ℚ)), f (-((n + 1 : ℕ) : ℚ))] :=
    fun n => (relChain_iff.mp hf) _ _ (neg_lt_neg (lt_add_one _))
  refine ⟨hstep, fun hwf => (wellFounded_iff_isEmpty_descending_chain.mp hwf).false
    ⟨fun n : ℕ => f (-(↑(n + 1) : ℚ)), fun n => by push_cast at hstep ⊢; exact hstep n⟩⟩

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
    let lt : Language.order.Relations 2 := .le
    have hω : (ω : Ordinal.{0}) < ω₁ := Ordinal.omega0_lt_omega_one
    letI := @orderStructure (Fin 3) ⟨(· < ·)⟩
    letI := @orderStructure ℕ ⟨(· < ·)⟩
    letI := @orderStructure ℤ ⟨(· < ·)⟩
    letI := @orderStructure ℚ ⟨(· < ·)⟩
    SentenceInf.Realize (boundedWellOrderSentence lt ω hω) (Fin 3) ∧
      SentenceInf.Realize (wellOrderTypeSentence lt ω hω) ℕ ∧
      ¬ SentenceInf.Realize (boundedWellOrderSentence lt ω hω) ℕ ∧
      ¬ SentenceInf.Realize (boundedWellOrderSentence lt ω hω) ℤ ∧
      ¬ SentenceInf.Realize (boundedWellOrderSentence lt ω hω) ℚ := by
  intro lt hω
  let := @orderStructure (Fin 3) ⟨(· < ·)⟩
  let := @orderStructure ℕ ⟨(· < ·)⟩
  let := @orderStructure ℤ ⟨(· < ·)⟩
  let := @orderStructure ℚ ⟨(· < ·)⟩
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
    exact RelChain.not_wellFounded (L := Language.order) (lt := lt) (f := id)
      (relChain_iff.mpr fun _ _ hxy => hxy) hwf
  · intro h
    have hwf : WellFounded (· < · : ℚ → ℚ → Prop) :=
      (isWellOrder_of_realize_boundedWellOrderSentence lt hω h).wf
    exact RelChain.not_wellFounded (L := Language.order) (lt := lt) (f := id)
      (relChain_iff.mpr fun _ _ hxy => hxy) hwf

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

end Examples
