/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Countable
public import TauCeti.ModelTheory.BackAndForth.Presentation
public import TauCeti.ModelTheory.Infinitary.Reindex

/-!
# Infinitary equivalence and Karp's theorem

`InfEquivAt κ M N` says that `M` and `N` satisfy the same `L_{∞ω}` sentences whose conjunctions and
disjunctions are indexed by the carrier `κ`. Agreement transports contravariantly along index
codings: agreement at `κ` gives agreement at every carrier `ι` coded into `κ`, since recoding a
sentence along an `IndexCoding ι κ` preserves its meaning.

Karp's theorem says that structures in a relational language are potentially isomorphic exactly
when they satisfy the same infinitary sentences. The forward direction holds at every carrier, and
the converse at any carrier `κ` into which both structures are coded. Full infinitary equivalence
`InfEquivW` quantifies, outside the syntax, over all carriers in the universe of `M ⊕ N`, and the
carrier `M ⊕ N` packages the converse. No countability is assumed, and the carrier and the
universes of the two structures are independent. For countable structures, which are coded into
`ℕ`, agreement on the `L_{ω₁ω}` sentences is therefore isomorphism.

The theorem is Carol Karp's, *Finite-quantifier equivalence* (1965). Cameron Freer's
`cameronfreer/infinitary-logic`, `InfinitaryLogic/Karp/CarrierTheorem.lean` at checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, proves both directions at a common carrier.

## Main definitions

* `TauCeti.InfEquivAt`: agreement on all sentences with a given branching carrier.
* `TauCeti.InfEquivW`: agreement at every carrier in the universe of `M ⊕ N`.

## Main results

* `TauCeti.InfEquivAt.of_reindex`: agreement transports contravariantly along index codings.
* `TauCeti.IsTupleBFSystem.realize_iff`: the tuples of a pair in a tuple back-and-forth system
  satisfy the same infinitary formulas.
* `TauCeti.PotentialIso.infEquivAt`: potentially isomorphic structures satisfy the same
  infinitary sentences at every carrier.
* `TauCeti.exists_forall_realize_snoc_iff_of_forall_realize_iff`: tuples agreeing on every
  formula with a carrier into which the second structure is coded admit matching one-element
  extensions.
* `TauCeti.karp_theorem_at`: Karp's theorem at a common carrier.
* `TauCeti.karp_theorem`: Karp's theorem for full infinitary equivalence.
* `TauCeti.InfEquivAt.infEquivW` and `TauCeti.InfEquivW.infEquivAt`: agreement at one coded
  carrier gives full infinitary equivalence, which gives agreement at carriers in every universe.
* `TauCeti.countable_infEquivAt_nat_iff_iso`: on countable structures, agreement on the
  `L_{ω₁ω}` sentences is isomorphism.
-/

public section

universe u v w w' uι uκ uμ

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

/-- Agreement at `κ` is agreement on the formulas with carrier `κ`, no free variables, and no
bound-variable slots, under the empty valuations. -/
theorem infEquivAt_iff_forall_realize {κ : Type uκ} :
    InfEquivAt (L := L) κ M N ↔ ∀ φ : L.BoundedFormulaInf κ Empty 0,
      φ.Realize Empty.elim (Fin.elim0 : Fin 0 → M) ↔
        φ.Realize Empty.elim (Fin.elim0 : Fin 0 → N) := by
  simp only [infEquivAt_iff, SentenceInf.realize_def, FormulaInf.realize_def,
    Subsingleton.elim (default : Fin 0 → M) Fin.elim0,
    Subsingleton.elim (default : Fin 0 → N) Fin.elim0]

/-- `M` and `N` satisfy the same `L_{∞ω}` sentences at every carrier in the universe of `M ⊕ N`.
The carriers are quantified outside the syntax. -/
def InfEquivW (M : Type w) (N : Type w') [L.Structure M] [L.Structure N] : Prop :=
  ∀ κ : Type (max w w'), InfEquivAt (L := L) κ M N

/-- Full infinitary equivalence is agreement at every carrier in the universe of `M ⊕ N`. -/
theorem infEquivW_iff :
    InfEquivW (L := L) M N ↔ ∀ κ : Type (max w w'), InfEquivAt (L := L) κ M N :=
  Iff.rfl

/-- Agreement at a carrier `κ` gives agreement at every carrier `ι` coded into `κ`. -/
theorem InfEquivAt.of_reindex {ι : Type uι} {κ : Type uκ} (c : IndexCoding ι κ)
    (h : InfEquivAt (L := L) κ M N) : InfEquivAt (L := L) ι M N := by
  intro φ
  have := h (BoundedFormulaInf.reindex c φ)
  simpa only [SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_reindex] using this

/-- Agreement on the infinitary sentences at any carrier implies elementary equivalence, since
first-order sentences embed at every carrier. -/
theorem InfEquivAt.elementarilyEquivalent {κ : Type uκ} (h : InfEquivAt (L := L) κ M N) :
    M ≅[L] N := by
  refine elementarilyEquivalent_iff.mpr fun φ => ?_
  simpa only [SentenceInf.realize_def, FormulaInf.realize_def, BoundedFormula.realize_toInf,
    Sentence.Realize, Formula.Realize, Subsingleton.elim default Empty.elim] using
    h (BoundedFormula.toInf φ)

/-- **Matching one more element.** If two tuples agree on every infinitary formula with carrier
`κ` and the second structure is coded into `κ`, then every one-element extension of the first
tuple is matched by a one-element extension of the second that again agrees on every such
formula. -/
theorem exists_forall_realize_snoc_iff_of_forall_realize_iff {κ : Type uκ} (cN : IndexCoding N κ)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hab : ∀ φ : L.BoundedFormulaInf κ Empty n, φ.Realize Empty.elim a ↔ φ.Realize Empty.elim b)
    (x : M) : ∃ y : N, ∀ φ : L.BoundedFormulaInf κ Empty (n + 1),
      φ.Realize Empty.elim (Fin.snoc a x) ↔ φ.Realize Empty.elim (Fin.snoc b y) := by
  classical
  by_contra hne
  -- Each candidate match `y` is separated from `x` by a formula, oriented to hold at `x`.
  choose φ hφ using fun y => not_forall.1 fun h => hne ⟨y, h⟩
  let ψ (y : N) : L.BoundedFormulaInf κ Empty (n + 1) :=
    if (φ y).Realize Empty.elim (Fin.snoc a x) then φ y else (φ y).not
  have hψa (y : N) : (ψ y).Realize Empty.elim (Fin.snoc a x) := by
    by_cases h : (φ y).Realize Empty.elim (Fin.snoc a x)
    · simp only [ψ, h, ↓reduceIte]
    · simpa only [ψ, h, ↓reduceIte, BoundedFormulaInf.realize_not] using h
  have hψb (y : N) : ¬ (ψ y).Realize Empty.elim (Fin.snoc b y) := by
    by_cases h : (φ y).Realize Empty.elim (Fin.snoc a x)
    · simp only [ψ, h, ↓reduceIte]
      exact fun hb => hφ y (iff_of_true h hb)
    · simp only [ψ, h, ↓reduceIte, BoundedFormulaInf.realize_not, not_not]
      by_contra hb
      exact hφ y (iff_of_false h hb)
  -- Some `x` satisfies every oriented formula, but no candidate match does.
  have := hab (BoundedFormulaInf.iInfAlong cN ψ).ex
  simp only [BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_iInfAlong] at this
  obtain ⟨y, hy⟩ := this.1 ⟨x, hψa⟩
  exact hψb y (hy y)

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
  -- Induct on formulas: atomic formulas use atomic-type agreement, and quantifiers use the forth
  -- and back clauses.
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
  -- Pass to a tuple back-and-forth system, whose empty pair relates the two structures.
  obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
  exact infEquivAt_iff_forall_realize.2 fun φ => hS.realize_iff φ hS.empty_mem _ _

/-! ### The converse -/

variable {κ : Type uκ}

/-- **Karp's theorem, converse direction.** Structures in a relational language that are both coded
into a carrier `κ` and satisfy the same infinitary sentences with carrier `κ` are potentially
isomorphic. -/
theorem InfEquivAt.potentialIso (cM : IndexCoding M κ) (cN : IndexCoding N κ)
    (h : InfEquivAt (L := L) κ M N) : PotentialIso (L := L) M N := by
  -- The pairs of tuples agreeing on every formula with carrier `κ` form a tuple system.
  let S : Set (Σ n, (Fin n → M) × (Fin n → N)) := {p | ∀ φ : L.BoundedFormulaInf κ Empty p.1,
    φ.Realize Empty.elim p.2.1 ↔ φ.Realize Empty.elim p.2.2}
  refine IsTupleBFSystem.potentialIso (S := S) ⟨?_, ?_, ?_, ?_⟩
  · exact infEquivAt_iff_forall_realize.1 h
  · intro n a b hab
    rw [sameAtomicType_iff]
    refine ⟨fun i j => ?_, fun r f => ?_⟩
    · simpa using hab (.equal (Term.var (Sum.inr i)) (Term.var (Sum.inr j)))
    · simpa [Function.comp_def] using hab (.rel r fun k => Term.var (Sum.inr (f k)))
  · intro n a b hab x
    exact exists_forall_realize_snoc_iff_of_forall_realize_iff cN hab x
  · intro n a b hab y
    obtain ⟨x, hx⟩ :=
      exists_forall_realize_snoc_iff_of_forall_realize_iff cM (fun φ => (hab φ).symm) y
    exact ⟨x, fun φ => (hx φ).symm⟩

/-- **Karp's theorem at a common carrier.** Structures in a relational language that are both
coded into `κ` are potentially isomorphic exactly when they satisfy the same infinitary sentences
with carrier `κ`. -/
theorem karp_theorem_at (cM : IndexCoding M κ) (cN : IndexCoding N κ) :
    PotentialIso (L := L) M N ↔ InfEquivAt (L := L) κ M N :=
  ⟨fun h => h.infEquivAt κ, InfEquivAt.potentialIso cM cN⟩

/-- **Karp's theorem.** Structures in a relational language are potentially isomorphic exactly when
they satisfy the same infinitary sentences. The converse uses the carrier `M ⊕ N`. -/
theorem karp_theorem : PotentialIso (L := L) M N ↔ InfEquivW (L := L) M N :=
  ⟨fun h κ => h.infEquivAt κ,
    fun h => (h (M ⊕ N)).potentialIso (IndexCoding.sumInl M N) (IndexCoding.sumInr M N)⟩

/-- Agreement at one carrier into which both structures are coded gives full infinitary
equivalence. -/
theorem InfEquivAt.infEquivW (cM : IndexCoding M κ) (cN : IndexCoding N κ)
    (h : InfEquivAt (L := L) κ M N) : InfEquivW (L := L) M N :=
  karp_theorem.1 (h.potentialIso cM cN)

/-- Full infinitary equivalence gives agreement at a carrier in any universe. -/
theorem InfEquivW.infEquivAt (h : InfEquivW (L := L) M N) (μ : Type uμ) :
    InfEquivAt (L := L) μ M N :=
  (karp_theorem.2 h).infEquivAt μ

/-- **Karp's theorem for countable structures.** Countable structures in a relational language are
isomorphic exactly when they satisfy the same `L_{ω₁ω}` sentences, the infinitary sentences whose
conjunctions and disjunctions are indexed by `ℕ`. -/
theorem countable_infEquivAt_nat_iff_iso [Countable M] [Countable N] :
    InfEquivAt (L := L) ℕ M N ↔ Nonempty (M ≃[L] N) := by
  -- Both structures are coded into `ℕ`, so Karp's theorem applies at that carrier.
  let _ := Encodable.ofCountable M
  let _ := Encodable.ofCountable N
  exact (karp_theorem_at (IndexCoding.ofEncodable M) (IndexCoding.ofEncodable N)).symm.trans
    countable_potentialIso_iff_iso

end TauCeti
