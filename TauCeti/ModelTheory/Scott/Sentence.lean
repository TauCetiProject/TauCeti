/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Scott.Formula
public import TauCeti.ModelTheory.Scott.Stabilization
public import TauCeti.ModelTheory.BackAndForth.TupleSystem
public import TauCeti.ModelTheory.Infinitary.Equiv

/-!
# Scott sentences at stabilizing levels

`scottSentenceAt M α` conjoins the Scott approximation of the empty tuple with the universal
closures of all tuple-upgrade implications from level `α` to level `α + 1`. At a countable
internally stabilizing level, the original structure satisfies this sentence. In every model,
the pairs related at level `α` form a tuple back-and-forth system, and therefore agree at all
ordinal levels. The realizing structure need not be countable.

`scottSentence M` uses the least internal stabilization ordinal. Its construction and the
back-and-forth conclusion are independent of the subsequent passage from a system to an
isomorphism between countable structures.

Isomorphic copies satisfy these sentences by invariance of infinitary satisfaction. This
supplies the isomorphism-to-satisfaction direction of their characterization.

The construction is due to Dana Scott, *Logic with denumerably long formulas and finite strings
of quantifiers* (1965). Unlike the empty-tuple approximation called `scottSentenceAt` in Cameron
Freer's `cameronfreer/infinitary-logic`, `InfinitaryLogic/Scott/Formula.lean` at checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`, this sentence includes the tuple-upgrade clauses.
-/

public section

universe u v w w' o o'

namespace TauCeti

open FirstOrder FirstOrder.Language Fin
open scoped Ordinal

variable {L : Language.{u, v}} [Countable (Σ k, L.Relations k)]
variable (M : Type w) [L.Structure M] [Countable M]

/-- The empty-tuple Scott approximation together with universal tuple-upgrade implications.
At a countable internally stabilizing level it describes a back-and-forth class of structures. -/
noncomputable def scottSentenceAt (α : Ordinal.{o}) : L.Sentenceω :=
  scottFormula (L := L) (Fin.elim0 : Fin 0 → M) α ⊓
    .iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable (Σ n, Fin n → M)))
      (fun p => ((scottFormula p.2 α).imp (scottFormula p.2 (α + 1))).alls)

/-- The defining conjunction of the empty-tuple approximation and the tuple-upgrade clauses. -/
theorem scottSentenceAt_def (α : Ordinal.{o}) :
    scottSentenceAt (L := L) M α =
      scottFormula (L := L) (Fin.elim0 : Fin 0 → M) α ⊓
        .iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable (Σ n, Fin n → M)))
          (fun p => ((scottFormula p.2 α).imp (scottFormula p.2 (α + 1))).alls) := (rfl)

variable [L.IsRelational] {N : Type w'} [L.Structure N]

/-- Satisfaction says that the empty tuples agree at `α` and that every matching tuple
can be upgraded to `α + 1`. This characterization holds for models of any cardinality. -/
@[simp]
theorem realize_scottSentenceAt {α : Ordinal.{o}} (hα : α < ω₁) :
    SentenceInf.Realize (scottSentenceAt (L := L) M α) N ↔
      BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) ∧
        ∀ (n : ℕ) (a : Fin n → M) (b : Fin n → N),
          BFEquiv (L := L) α n a b → BFEquiv (L := L) (α + 1) n a b := by
  have hsucc : α + 1 < ω₁ := (Cardinal.isSuccLimit_omega 1).add_one_lt hα
  simp only [scottSentenceAt_def, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_iInfAlong,
    BoundedFormulaInf.realize_alls, BoundedFormulaInf.realize_imp,
    realize_scottFormula_iff_bfEquiv _ _ hα,
    realize_scottFormula_iff_bfEquiv _ _ hsucc, Sigma.forall]
  rfl

/-- A countable structure satisfies the Scott sentence at each countable internally
stabilizing level. -/
theorem realize_scottSentenceAt_self {α : Ordinal.{o}} (hα : α < ω₁)
    (hs : SelfStabilizesCompletely (L := L) M α) :
    SentenceInf.Realize (scottSentenceAt (L := L) M α) M :=
  (realize_scottSentenceAt M hα).mpr
    ⟨BFEquiv.refl _ _, fun _ _ _ hab => hs.bfEquiv_of_le le_self_add hab⟩

/-- In any model of a Scott sentence, the tuples matching at its level form a back-and-forth
system. No countability or internal-stabilization hypothesis on the model is needed. -/
theorem isTupleBFSystem_of_realize_scottSentenceAt {α : Ordinal.{o}} (hα : α < ω₁)
    (h : SentenceInf.Realize (scottSentenceAt (L := L) M α) N) :
    IsTupleBFSystem (L := L)
      {p : Σ n, (Fin n → M) × (Fin n → N) | BFEquiv (L := L) α p.1 p.2.1 p.2.2} := by
  obtain ⟨hzero, hstep⟩ := (realize_scottSentenceAt M hα).mp h
  exact ⟨hzero, fun hab => hab.sameAtomicType,
    fun {n a b} hab => ((BFEquiv.add_one α a b).mp (hstep n a b hab)).2.1,
    fun {n a b} hab => ((BFEquiv.add_one α a b).mp (hstep n a b hab)).2.2⟩

/-- The Scott sentence using the least internal stabilization ordinal of the structure. -/
noncomputable def scottSentence : L.Sentenceω :=
  scottSentenceAt (L := L) M (selfStabilizationOrdinal (L := L) M)

/-- The canonical Scott sentence uses the least internal stabilization level. -/
theorem scottSentence_def : scottSentence (L := L) M =
    scottSentenceAt (L := L) M (selfStabilizationOrdinal (L := L) M) := (rfl)

/-- Every countable structure satisfies its canonical Scott sentence. -/
@[simp]
theorem realize_scottSentence_self : SentenceInf.Realize (scottSentence (L := L) M) M := by
  rw [scottSentence_def]
  exact realize_scottSentenceAt_self M (selfStabilizationOrdinal_lt_omega_one M)
    (selfStabilizesCompletely_selfStabilizationOrdinal M)

/-- A model of the canonical Scott sentence agrees with the original structure at every
ordinal back-and-forth level. The ordinal universe is independent of the structure universes. -/
theorem bfEquiv_of_realize_scottSentence (h : SentenceInf.Realize (scottSentence (L := L) M) N)
    (β : Ordinal.{o'}) :
    BFEquiv (L := L) β 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  rw [scottSentence_def] at h
  have hs := isTupleBFSystem_of_realize_scottSentenceAt M
    (selfStabilizationOrdinal_lt_omega_one M) h
  exact hs.bfEquiv β hs.empty_mem

end TauCeti

namespace FirstOrder.Language.Equiv

open TauCeti

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ k, L.Relations k)]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] [Countable M]

/-- Every isomorphic copy satisfies the Scott sentence at a countable internally
stabilizing level of the original structure. -/
theorem realize_scottSentenceAt (e : M ≃[L] N) {α : Ordinal.{o}}
    (hα : α < Ordinal.omega 1) (hs : SelfStabilizesCompletely (L := L) M α) :
    SentenceInf.Realize (scottSentenceAt (L := L) M α) N :=
  (StrongHomClass.realize_sentenceInf e _).mp (realize_scottSentenceAt_self M hα hs)

/-- Every isomorphic copy of a countable structure satisfies its canonical Scott sentence. -/
theorem realize_scottSentence (e : M ≃[L] N) :
    SentenceInf.Realize (scottSentence (L := L) M) N :=
  (StrongHomClass.realize_sentenceInf e _).mp (realize_scottSentence_self M)

end FirstOrder.Language.Equiv
