/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.ModelTheory.Graph
import TauCeti.ModelTheory.Infinitary.GraphTranslation.Polarity

/-!
# Regression examples: signed relation occurrences and polarity monotonicity

These examples exercise the signed occurrence calculus, polarity monotonicity, non-injective signed
pullback, and graph-translation polarity preservation from a downstream module, through public
statements only:

* **Infinitary graph reachability is upward monotone in the edge relation.** The countable
  disjunction `⋁_{k : ℕ} walkInf k` of `k`-step walks in `Language.graph` has no negative relation
  occurrences (`negativeRelationsIn = ∅`), so `BoundedFormulaInf.realize_mono_of_signed` transfers
  it from `G.structure` to `G'.structure` whenever `G ≤ G'`.
* **Maximum-degree bounds are downward monotone in the edge relation.** The sentence
  `∀ x y z, adj(x, y) → adj(x, z) → y = z` has no positive relation occurrences
  (`positiveRelationsIn = ∅`), so `SentenceInf.realize_mono_of_signed` transfers it from
  `G'.structure` to `G.structure` whenever `G ≤ G'`.
* **Signed separation along a non-injective language homomorphism.** Folding `L.sum L` onto `L`
  via `(LHom.id L).sumElim (LHom.id L)` lets
  `LHom.exists_eq_onBoundedFormulaInf_of_relationsInSigned_subset` split any `L`-formula `φ` into a
  formula of `L.sum L` whose positive relation occurrences lie in the left summand and whose
  negative relation occurrences lie in the right summand.
* **Lyndon's relational-to-functional vocabulary transfer.** Across `relationalize`, `graphAxioms`,
  `relSym_inter`, and `backTranslate`, any graph-language sentence whose signed relation
  occurrences lie in those shared by `(graphAxioms F).conjunction hF ⊓ φ.relationalize` and
  `((graphAxioms F).conjunction hF).imp ψ.relationalize` back-translates to an `L`-sentence whose
  signed relation occurrences lie in `φ.relationsInSigned s ∩ ψ.relationsInSigned s` at both
  polarities.
-/

universe u v uα uι

open FirstOrder FirstOrder.Language

-- 1. Infinitary graph reachability `⋁_{k : ℕ} walkInf k` has no negative relation occurrences, so
-- adding edges (`G ≤ G'`) preserves reachability between any two vertices `x` and `y`.
example {V : Type u} {G G' : SimpleGraph V} (hle : G ≤ G') (x y : V) :
    let walkInf : ℕ → Language.graph.BoundedFormulaω (Fin 2) 0 := fun k =>
      Nat.rec (.equal (.var (.inl 0)) (.var (.inl 1)))
        (fun _ ih => ((BoundedFormulaInf.rel Language.adj ![.var (.inl 0), .var (.inr 0)]) ⊓
          TauCeti.BoundedFormulaInf.relabel ![.inr 0, .inl 1] ih).ex) k
    let reachableInf : Language.graph.BoundedFormulaω (Fin 2) 0 := .iSup walkInf
    @BoundedFormulaInf.Realize Language.graph ℕ (Fin 2) V G.structure 0
      reachableInf ![x, y] default →
    @BoundedFormulaInf.Realize Language.graph ℕ (Fin 2) V G'.structure 0
      reachableInf ![x, y] default := by
  intro walkInf reachableInf hxy
  have hwalk (k : ℕ) : (walkInf k).relationsInSigned false = ∅ := by
    induction k with
    | zero => simp [walkInf]
    | succ k ih => simp [walkInf, ih]
  refine reachableInf.realize_mono_of_signed G.structure G'.structure ?_ ?_ ![x, y] default hxy
  · rintro _ ⟨⟩ _ xs hadj
    exact hle hadj
  · intro k R hR
    simp [reachableInf, BoundedFormulaInf.negativeRelationsIn, hwalk] at hR

-- 2. Maximum degree at most `1` (`∀ x y z, adj(x, y) → adj(x, z) → y = z`) has no positive
-- relation occurrences, so deleting edges (`G ≤ G'`) preserves it from `G'` down to `G`.
example {V : Type u} {G G' : SimpleGraph V} (hle : G ≤ G') :
    let atMostOneNeighbor : Language.graph.Sentenceω :=
      BoundedFormulaInf.alls (n := 3)
        ((BoundedFormulaInf.rel Language.adj ![.var (.inr 0), .var (.inr 1)]).imp
          ((BoundedFormulaInf.rel Language.adj ![.var (.inr 0), .var (.inr 2)]).imp
            (.equal (.var (.inr 1)) (.var (.inr 2)))))
    @SentenceInf.Realize Language.graph ℕ atMostOneNeighbor V G'.structure →
    @SentenceInf.Realize Language.graph ℕ atMostOneNeighbor V G.structure := by
  intro atMostOneNeighbor hG'
  refine SentenceInf.realize_mono_of_signed atMostOneNeighbor G'.structure G.structure ?_ ?_ hG'
  · intro k R hR
    simp [atMostOneNeighbor, BoundedFormulaInf.positiveRelationsIn] at hR
  · rintro _ ⟨⟩ _ xs hadj
    exact hle hadj

-- 3. Folding `L.sum L` onto `L` via `(LHom.id L).sumElim (LHom.id L)` pulls any formula `φ` back to
-- a formula separating positive relation occurrences into `Sum.inl` and negative ones into
-- `Sum.inr`.
example {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) :
    let g : L.sum L →ᴸ L := (LHom.id L).sumElim (LHom.id L)
    ∃ ψ : (L.sum L).BoundedFormulaInf ι α n,
      g.onBoundedFormulaInf ψ = φ ∧
        ψ.positiveRelationsIn ⊆
          (fun r : Σ k, L.Relations k => ⟨r.1, Sum.inl r.2⟩) '' φ.positiveRelationsIn ∧
        ψ.negativeRelationsIn ⊆
          (fun r : Σ k, L.Relations k => ⟨r.1, Sum.inr r.2⟩) '' φ.negativeRelationsIn := by
  intro g
  obtain ⟨ψ, hψ, -, hpos, hneg⟩ :=
    g.exists_eq_onBoundedFormulaInf_of_relationsInSigned_subset
      (F := (fun f : Σ k, L.Functions k => ⟨f.1, Sum.inl f.2⟩) '' φ.functionsIn)
      (P := (fun r : Σ k, L.Relations k => ⟨r.1, Sum.inl r.2⟩) '' φ.positiveRelationsIn)
      (N := (fun r : Σ k, L.Relations k => ⟨r.1, Sum.inr r.2⟩) '' φ.negativeRelationsIn)
      φ
      (fun ⟨k, f⟩ hf => ⟨⟨k, Sum.inl f⟩, ⟨⟨k, f⟩, hf, rfl⟩, rfl⟩)
      (fun ⟨k, R⟩ hR => ⟨⟨k, Sum.inl R⟩, ⟨⟨k, R⟩, hR, rfl⟩, rfl⟩)
      (fun ⟨k, R⟩ hR => ⟨⟨k, Sum.inr R⟩, ⟨⟨k, R⟩, hR, rfl⟩, rfl⟩)
  exact ⟨ψ, hψ, hpos, hneg⟩

-- 4. Any relational Lyndon interpolant `θ` between
-- `(graphAxioms F).conjunction hF ⊓ φ.relationalize` and
-- `((graphAxioms F).conjunction hF).imp ψ.relationalize` back-translates to an `L`-sentence
-- whose signed relation occurrences lie in `φ.relationsInSigned s ∩ ψ.relationsInSigned s`.
example {L : Language.{u, v}} {F : Set (Σ k, L.Functions k)} (hF : (graphAxioms F).Countable)
    (φ ψ : L.Sentenceω) (hφ : φ.functionsIn ⊆ F) (hψ : ψ.functionsIn ⊆ F)
    (θ : L.graphLanguage.Sentenceω)
    (hθ : ∀ s, θ.relationsInSigned s ⊆
      ((graphAxioms F).conjunction hF ⊓ φ.relationalize).relationsInSigned s ∩
        (((graphAxioms F).conjunction hF).imp ψ.relationalize).relationsInSigned s)
    (s : Bool) :
    θ.backTranslate.relationsInSigned s ⊆ φ.relationsInSigned s ∩ ψ.relationsInSigned s := by
  have hsub := Set.preimage_mono (f := (baseRelSym (L := L))) (hθ s)
  rwa [← BoundedFormulaInf.relationsInSigned_backTranslate,
    relationsInSigned_conjunction_graphAxioms_inf_relationalize s hF φ hφ,
    relationsInSigned_conjunction_graphAxioms_imp_relationalize s hF ψ hψ,
    relSym_inter, preimage_baseRelSym_relSym] at hsub
