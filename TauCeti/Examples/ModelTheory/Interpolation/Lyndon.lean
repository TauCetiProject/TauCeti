/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.ModelTheory.Graph
import TauCeti.ModelTheory.Interpolation.Lyndon

/-!
# Examples: Lyndon interpolation for `L_{ω₁ω}`

Downstream regression and worked examples exercising the public Lyndon interpolation interface:

* **Degenerate interpolants**: over any language `L` (including function symbols), when `φ` is
  unsatisfiable (`φ ⊨ ⊥`), `⊥` interpolates `φ ⊨ ψ` with empty function and signed relation
  supports; when `ψ` is valid (`⊤ ⊨ ψ`), `⊤` interpolates `φ ⊨ ψ` with empty function and signed
  relation supports; and `lyndon_interpolation` applies in both cases.
* **Strictly polarity-sensitive relational interpolant**: over a language with a shared binary
  relation `R` and side relations `P, Q`, the sentence `(∃ x, R(x, x)) ∧ (∀ x, R(x, x) → P(x, x))`
  uses `R` in both polarities while `(∃ x, R(x, x)) ∨ (∃ x, Q(x, x))` uses `R` only positively.
  Relational Lyndon interpolation produces an interpolant `θ` with `θ.relationsInSigned false = ∅`
  and `θ.relationsInSigned true ⊆ {⟨2, R⟩}` (whereas Craig interpolation only bounds unsigned
  occurrences by `{⟨2, R⟩}`), non-degenerate on `Unit`, and upward monotone in `R` alone on every
  carrier.
* **Function-symbol elimination with polarity preservation**: over `Language.graph[[Unit]]`, the
  finite theory `{adj(c, c), ∀ x, adj(x, c) → x = c}` uses the constant `c` and uses `adj` in both
  polarities, while `∃ x, adj(x, x)` uses no function symbols and uses `adj` only positively.
  `Theoryω.lyndon_interpolation` produces a function-free, negative-free interpolant non-degenerate
  on `Unit`.
-/

universe u v w

namespace TauCeti

open FirstOrder FirstOrder.Language

-- 1. An unsatisfiable antecedent admits `⊥` as a function-free and polarity-free interpolant, and
-- `lyndon_interpolation` applies over an arbitrary language `L`.
example {L : Language.{u, v}} {φ ψ : L.Sentenceω} (hφ : Sentenceω.Entails φ ⊥) :
    (⊥ : L.Sentenceω).functionsIn = ∅ ∧
      (∀ s, (⊥ : L.Sentenceω).relationsInSigned s = ∅) ∧
      Sentenceω.Entails φ ⊥ ∧
      Sentenceω.Entails (⊥ : L.Sentenceω) ψ ∧
      ∃ θ : L.Sentenceω,
        θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
        θ.relationsInSigned true ⊆ φ.relationsInSigned true ∩ ψ.relationsInSigned true ∧
        θ.relationsInSigned false ⊆ φ.relationsInSigned false ∩ ψ.relationsInSigned false ∧
        Sentenceω.Entails φ θ ∧ Sentenceω.Entails θ ψ := by
  have hbot_ψ : Sentenceω.Entails (⊥ : L.Sentenceω) ψ :=
    Sentenceω.entails_iff.2 fun M _ _ hbot => False.elim (SentenceInf.realize_bot.1 hbot)
  exact ⟨BoundedFormulaInf.functionsIn_falsum, BoundedFormulaInf.relationsInSigned_bot,
    hφ, hbot_ψ, lyndon_interpolation φ ψ (hφ.trans hbot_ψ)⟩

-- 2. A valid consequent admits `⊤` as a function-free and polarity-free interpolant, and
-- `lyndon_interpolation` applies over an arbitrary language `L`.
example {L : Language.{u, v}} {φ ψ : L.Sentenceω} (hψ : Sentenceω.Entails ⊤ ψ) :
    (⊤ : L.Sentenceω).functionsIn = ∅ ∧
      (∀ s, (⊤ : L.Sentenceω).relationsInSigned s = ∅) ∧
      Sentenceω.Entails φ ⊤ ∧
      Sentenceω.Entails ⊤ ψ ∧
      ∃ θ : L.Sentenceω,
        θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
        θ.relationsInSigned true ⊆ φ.relationsInSigned true ∩ ψ.relationsInSigned true ∧
        θ.relationsInSigned false ⊆ φ.relationsInSigned false ∩ ψ.relationsInSigned false ∧
        Sentenceω.Entails φ θ ∧ Sentenceω.Entails θ ψ := by
  have hφ_top : Sentenceω.Entails φ ⊤ :=
    Sentenceω.entails_iff.2 fun _ _ _ _ => by simp [SentenceInf.realize_def, FormulaInf.realize_def]
  exact ⟨BoundedFormulaInf.functionsIn_top, BoundedFormulaInf.relationsInSigned_top,
    hφ_top, hψ, lyndon_interpolation φ ψ (hφ_top.trans hψ)⟩

-- 3. Relational Lyndon interpolation eliminates a negative occurrence of a shared relation symbol:
-- `(∃ x, R(x, x)) ∧ (∀ x, R(x, x) → P(x, x))` uses `R` in both polarities while
-- `(∃ x, R(x, x)) ∨ (∃ x, Q(x, x))` uses `R` only positively, yielding an interpolant `θ` with no
-- negative relation occurrences, non-degenerate on `Unit`, and upward monotone in `R` alone.
example :
    let ThreeGraph := Language.graph.sum (Language.graph.sum Language.graph)
    let sharedRel : ThreeGraph.Relations 2 := .inl Language.adj
    let leftRel : ThreeGraph.Relations 2 := .inr (.inl Language.adj)
    let rightRel : ThreeGraph.Relations 2 := .inr (.inr Language.adj)
    let mixedAntecedent : ThreeGraph.Sentenceω :=
      BoundedFormulaInf.ex (BoundedFormulaInf.rel sharedRel ![&0, &0]) ⊓
        BoundedFormulaInf.all
          ((BoundedFormulaInf.rel sharedRel ![&0, &0]).imp
            (BoundedFormulaInf.rel leftRel ![&0, &0]))
    let posConsequent : ThreeGraph.Sentenceω :=
      BoundedFormulaInf.ex (BoundedFormulaInf.rel sharedRel ![&0, &0]) ⊔
        BoundedFormulaInf.ex (BoundedFormulaInf.rel rightRel ![&0, &0])
    ∃ θ : ThreeGraph.Sentenceω,
      θ.relationsInSigned true ⊆ {⟨2, sharedRel⟩} ∧
      θ.relationsInSigned false = ∅ ∧
      Sentenceω.Entails mixedAntecedent θ ∧
      Sentenceω.Entails θ posConsequent ∧
      (∃ S₁ : ThreeGraph.Structure Unit, @SentenceInf.Realize _ ℕ θ Unit S₁) ∧
      (∃ S₀ : ThreeGraph.Structure Unit, ¬ @SentenceInf.Realize _ ℕ θ Unit S₀) ∧
      (∀ (M : Type w) (S S' : ThreeGraph.Structure M),
        (∀ xs, @Structure.RelMap ThreeGraph M S 2 sharedRel xs →
          @Structure.RelMap ThreeGraph M S' 2 sharedRel xs) →
        @SentenceInf.Realize _ ℕ θ M S → @SentenceInf.Realize _ ℕ θ M S') := by
  intro ThreeGraph sharedRel leftRel rightRel mixedAntecedent posConsequent
  have hent : Sentenceω.Entails mixedAntecedent posConsequent := by
    refine Sentenceω.entails_iff.2 fun M _ _ h => ?_
    simp only [mixedAntecedent, posConsequent, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_sup,
      BoundedFormulaInf.realize_ex] at h ⊢
    exact .inl h.1
  obtain ⟨θ, hpos, hneg, h₁, h₂⟩ :=
    lyndon_interpolation_relational mixedAntecedent posConsequent hent
  have hpos_sub : mixedAntecedent.relationsInSigned true ∩
      posConsequent.relationsInSigned true ⊆ {⟨2, sharedRel⟩} := by
    rintro r ⟨hL, hR⟩
    have hL' : r = ⟨2, leftRel⟩ ∨ r = ⟨2, sharedRel⟩ := by simpa [mixedAntecedent] using hL
    have hR' : r = ⟨2, rightRel⟩ ∨ r = ⟨2, sharedRel⟩ := by simpa [posConsequent] using hR
    rcases hR' with rfl | rfl
    · rcases hL' with h | h
      · exact False.elim (Sum.inl_ne_inr
          (Sum.inr.inj (eq_of_heq (Sigma.mk.inj h.symm).2)))
      · exact False.elim (Sum.inl_ne_inr (eq_of_heq (Sigma.mk.inj h.symm).2))
    · exact Set.mem_singleton _
  have hneg_empty : posConsequent.relationsInSigned false = ∅ := by
    simp [posConsequent]
  have hθpos : θ.relationsInSigned true ⊆ {⟨2, sharedRel⟩} := hpos.trans hpos_sub
  have hθneg : θ.relationsInSigned false = ∅ :=
    Set.subset_empty_iff.1 (hneg.trans (Set.inter_subset_right.trans hneg_empty.subset))
  refine ⟨θ, hθpos, hθneg, h₁, h₂, ?_, ?_, ?_⟩
  · let S₁ : ThreeGraph.Structure Unit := ⟨fun f => isEmptyElim f, fun _ _ => True⟩
    let : ThreeGraph.Structure Unit := S₁
    refine ⟨S₁, (Sentenceω.entails_iff.1 h₁) Unit ?_⟩
    simp only [mixedAntecedent, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_all,
      BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_rel]
    exact ⟨⟨(), trivial⟩, fun _ _ => trivial⟩
  · let S₀ : ThreeGraph.Structure Unit := ⟨fun f => isEmptyElim f, fun _ _ => False⟩
    let : ThreeGraph.Structure Unit := S₀
    refine ⟨S₀, fun hθ => ?_⟩
    have hr := (Sentenceω.entails_iff.1 h₂) Unit hθ
    simp only [posConsequent, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_sup, BoundedFormulaInf.realize_ex,
      BoundedFormulaInf.realize_rel] at hr
    rcases hr with ⟨_, hy⟩ | ⟨_, hy⟩ <;> exact hy
  · intro M S S' hshared hθS
    refine SentenceInf.realize_mono_of_signed θ S S' ?_ ?_ hθS
    · intro k R hR
      obtain ⟨rfl, rfl⟩ := Sigma.mk.inj_iff.1 (Set.mem_singleton_iff.1 (hθpos hR))
      exact hshared
    · intro k R hR
      rw [BoundedFormulaInf.negativeRelationsIn, hθneg] at hR
      exact hR.elim

-- 4. `Theoryω.lyndon_interpolation` eliminates both the constant symbol `c` and the negative
-- occurrence of `adj` from `{adj(c, c), ∀ x, adj(x, c) → x = c} ⊨ ∃ x, adj(x, x)` over
-- `Language.graph[[Unit]]`, producing an interpolant non-degenerate on `Unit`.
example :
    let PointedGraph := Language.graph[[Unit]]
    let graphAdj : PointedGraph.Relations 2 :=
      (Language.graph.lhomWithConstants Unit).onRelation Language.adj
    let c₀ : PointedGraph.Term (Empty ⊕ Fin 0) := (Language.graph.con ()).term
    let c₁ : PointedGraph.Term (Empty ⊕ Fin 1) := (Language.graph.con ()).term
    let loopAtBase : PointedGraph.Sentenceω := BoundedFormulaInf.rel graphAdj ![c₀, c₀]
    let uniqueInNeighbor : PointedGraph.Sentenceω :=
      BoundedFormulaInf.all
        ((BoundedFormulaInf.rel graphAdj ![&0, c₁]).imp (BoundedFormulaInf.equal &0 c₁))
    let someLoop : PointedGraph.Sentenceω :=
      BoundedFormulaInf.ex (BoundedFormulaInf.rel graphAdj ![&0, &0])
    let T : PointedGraph.Theoryω := {loopAtBase, uniqueInNeighbor}
    ∃ θ : PointedGraph.Sentenceω,
      θ.functionsIn = ∅ ∧
      θ.relationsInSigned true ⊆ {⟨2, graphAdj⟩} ∧
      θ.relationsInSigned false = ∅ ∧
      T.Entails θ ∧
      Sentenceω.Entails θ someLoop ∧
      (∃ S₁ : PointedGraph.Structure Unit, @SentenceInf.Realize _ ℕ θ Unit S₁) ∧
      (∃ S₀ : PointedGraph.Structure Unit, ¬ @SentenceInf.Realize _ ℕ θ Unit S₀) := by
  intro PointedGraph graphAdj c₀ c₁ loopAtBase uniqueInNeighbor someLoop T
  have hT_cnt : T.Countable := (Set.countable_singleton _).insert _
  have hent : T.Entails someLoop := by
    refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    have hloop := hM.realize_of_mem (Set.mem_insert loopAtBase _)
    simp only [loopAtBase, someLoop, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_rel] at hloop ⊢
    refine ⟨Term.realize (Sum.elim Empty.elim default) c₀, ?_⟩
    convert hloop using 1
    ext ⟨i, hi⟩
    match i, hi with
    | 0, _ => simp [c₀, Fin.snoc]
    | 1, _ => simp [c₀, Fin.snoc]
  obtain ⟨θ, hfun, hpos, hneg, h₁, h₂⟩ := Theoryω.lyndon_interpolation hT_cnt someLoop hent
  have hfun_empty : someLoop.functionsIn = ∅ := by
    ext x
    simp only [someLoop, BoundedFormulaInf.functionsIn_ex, BoundedFormulaInf.functionsIn_rel,
      Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_exists]
    rintro ⟨i, hi⟩
    match i, hi with
    | 0, _ => simp
    | 1, _ => simp
  have hpos_sub : someLoop.relationsInSigned true ⊆ {⟨2, graphAdj⟩} := by simp [someLoop]
  have hneg_empty : someLoop.relationsInSigned false = ∅ := by simp [someLoop]
  refine ⟨θ,
    Set.subset_empty_iff.1 (hfun.trans (Set.inter_subset_right.trans hfun_empty.subset)),
    hpos.trans (Set.inter_subset_right.trans hpos_sub),
    Set.subset_empty_iff.1 (hneg.trans (Set.inter_subset_right.trans hneg_empty.subset)),
    h₁, h₂, ?_, ?_⟩
  · let S₁ : PointedGraph.Structure Unit := ⟨fun _ _ => (), fun _ _ => True⟩
    let : PointedGraph.Structure Unit := S₁
    refine ⟨S₁, (Theoryω.entails_iff.1 h₁) Unit ?_⟩
    rw [Theoryω.model_iff]
    rintro φ (rfl | rfl)
    · simp only [loopAtBase, SentenceInf.realize_def, FormulaInf.realize_def,
        BoundedFormulaInf.realize_rel]
      trivial
    · simp only [uniqueInNeighbor, SentenceInf.realize_def, FormulaInf.realize_def,
        BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_imp,
        BoundedFormulaInf.realize_equal]
      intro _ _
      trivial
  · let S₀ : PointedGraph.Structure Unit := ⟨fun _ _ => (), fun _ _ => False⟩
    let : PointedGraph.Structure Unit := S₀
    refine ⟨S₀, fun hθ => ?_⟩
    have hr := (Sentenceω.entails_iff.1 h₂) Unit hθ
    simp only [someLoop, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_rel] at hr
    obtain ⟨_, hy⟩ := hr
    exact hy

end TauCeti
