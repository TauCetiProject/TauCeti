/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Presentation
public import TauCeti.ModelTheory.Infinitary.Reindex

/-!
# Infinitary equivalence and the forward direction of Karp's theorem

`InfEquivAt κ M N` says that `M` and `N` satisfy the same `L_{∞ω}` sentences whose conjunctions and
disjunctions are indexed by the carrier `κ`. Agreement transports contravariantly along index
codings: agreement at `κ` gives agreement at every carrier `ι` coded into `κ`, since recoding a
sentence along an `IndexCoding ι κ` preserves its meaning.

The forward direction of Karp's theorem holds at every carrier: potentially isomorphic
structures in a relational language satisfy the same infinitary sentences. The proof passes to a
tuple back-and-forth system and shows, by induction on formulas, that the two tuples of each of
its pairs satisfy the same infinitary formulas. No countability is assumed, and the carrier and
the universes of the two structures are independent.

This is the forward half of Carol Karp, *Finite-quantifier equivalence* (1965). Cameron Freer's
`cameronfreer/infinitary-logic`, `InfinitaryLogic/Karp/CarrierTheorem.lean` at checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, proves both directions at a common carrier.

## Main definitions

* `TauCeti.InfEquivAt`: agreement on all sentences with a given branching carrier.

## Main results

* `TauCeti.InfEquivAt.of_reindex`: agreement transports contravariantly along index codings.
* `TauCeti.IsTupleBFSystem.realize_iff`: the tuples of a pair in a tuple back-and-forth system
  satisfy the same infinitary formulas.
* `TauCeti.PotentialIso.infEquivAt`: potentially isomorphic structures satisfy the same
  infinitary sentences at every carrier.
-/

public section

universe u v w w' uι uκ

namespace TauCeti

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- `M` and `N` satisfy the same `L_{∞ω}` sentences whose conjunctions and disjunctions are indexed
by `κ`. -/
def InfEquivAt (κ : Type uκ) (M : Type w) (N : Type w') [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : L.SentenceInf κ, φ.Realize M ↔ φ.Realize N

/-- Agreement at `κ` means agreement on every sentence with branching carrier `κ`. -/
theorem infEquivAt_iff {κ : Type uκ} :
    InfEquivAt (L := L) κ M N ↔ ∀ φ : L.SentenceInf κ, φ.Realize M ↔ φ.Realize N :=
  Iff.rfl

/-- Agreement at a carrier `κ` gives agreement at every carrier `ι` coded into `κ`. -/
theorem InfEquivAt.of_reindex {ι : Type uι} {κ : Type uκ} (c : IndexCoding ι κ)
    (h : InfEquivAt (L := L) κ M N) : InfEquivAt (L := L) ι M N := by
  intro φ
  have := h (BoundedFormulaInf.reindex c φ)
  simpa only [SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_reindex] using this

variable [L.IsRelational]

/-- **Pairs in a tuple back-and-forth system satisfy the same infinitary formulas**, at every
carrier. -/
theorem IsTupleBFSystem.realize_iff {S : Set (Σ n, (Fin n → M) × (Fin n → N))}
    (hS : IsTupleBFSystem (L := L) S) {κ : Type uκ} :
    ∀ {n} (φ : L.BoundedFormulaInf κ Empty n) {a : Fin n → M} {b : Fin n → N},
      ⟨n, a, b⟩ ∈ S → ∀ (v : Empty → M) (w : Empty → N), φ.Realize v a ↔ φ.Realize w b := by
  -- In a relational language, a term with no free variables is a bound variable.
  have hterm : ∀ {n} (t : L.Term (Empty ⊕ Fin n)), ∃ i, t = Term.var (Sum.inr i) := by
    intro n t
    cases t with
    | var x => rcases x with x | i
               · exact x.elim
               · exact ⟨i, rfl⟩
    | func f _ => exact isEmptyElim f
  intro n φ
  induction φ with
  | falsum => intro _ _ _ _ _; simp only [BoundedFormulaInf.realize_falsum]
  | equal t₁ t₂ =>
    intro a b hab v w
    obtain ⟨i, rfl⟩ := hterm t₁
    obtain ⟨j, rfl⟩ := hterm t₂
    simpa using ((sameAtomicType_iff a b).1 (hS.sameAtomicType hab)).1 i j
  | rel R ts =>
    intro a b hab v w
    choose g hg using fun i => hterm (ts i)
    obtain rfl : ts = fun i => Term.var (Sum.inr (g i)) := funext hg
    simpa [Function.comp_def] using ((sameAtomicType_iff a b).1 (hS.sameAtomicType hab)).2 R g
  | imp φ ψ ihφ ihψ =>
    intro a b hab v w
    simp only [BoundedFormulaInf.realize_imp, ihφ hab v w, ihψ hab v w]
  | all φ ih =>
    intro a b hab v w
    simp only [BoundedFormulaInf.realize_all]
    constructor
    · intro h y
      obtain ⟨x, hx⟩ := hS.back hab y
      exact (ih hx v w).1 (h x)
    · intro h x
      obtain ⟨y, hy⟩ := hS.forth hab x
      exact (ih hy v w).2 (h y)
  | iSup φs ih =>
    intro a b hab v w
    simp only [BoundedFormulaInf.realize_iSup]
    exact exists_congr fun i => ih i hab v w
  | iInf φs ih =>
    intro a b hab v w
    simp only [BoundedFormulaInf.realize_iInf]
    exact forall_congr' fun i => ih i hab v w

/-- **Karp's theorem, forward direction.** Potentially isomorphic structures in a relational
language satisfy the same infinitary sentences, at every carrier. -/
theorem PotentialIso.infEquivAt (h : PotentialIso (L := L) M N) (κ : Type uκ) :
    InfEquivAt (L := L) κ M N := by
  obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
  intro φ
  simp only [SentenceInf.realize_def, FormulaInf.realize_def]
  rw [Subsingleton.elim (default : Fin 0 → M) Fin.elim0,
    Subsingleton.elim (default : Fin 0 → N) Fin.elim0]
  exact hS.realize_iff φ hS.empty_mem _ _

end TauCeti
