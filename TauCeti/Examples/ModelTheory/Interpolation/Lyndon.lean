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

Downstream regression and worked examples exercising `lyndon_interpolation_relational`,
`lyndon_interpolation`, and `Theoryω.lyndon_interpolation` through their public interfaces:

* **Degenerate interpolants**: when `φ ⊨ ⊥`, `⊥` interpolates `φ ⊨ ψ` with empty function and
  signed-relation occurrences; when `⊤ ⊨ ψ`, `⊤` does; and `lyndon_interpolation` applies in both
  cases.
* **Recovering Craig's unsigned symbol bound**: joining the positive and negative relation bounds of
  `lyndon_interpolation` via `BoundedFormulaInf.relationsInSigned_union_not` recovers
  `θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn`.
* **Strict refinement of Craig interpolation over `Language.graph`**: the sentence
  `∃ x y, x ≠ y ∧ adj(x, y)` entails `(∃ x y, x ≠ y) ∨ ∀ x y, ¬ adj(x, y)`. Both sentences mention
  `Language.adj`, so Craig's unsigned bound allows `adj`, whereas `adj` occurs only positively on
  the left and only negatively on the right; `lyndon_interpolation_relational` therefore forces a
  pure-equality interpolant (`θ.relationsIn = ∅`) that holds on `Bool` and fails on `Unit`.
* **Upward monotonicity of a positive Lyndon interpolant**: when `φ` and `ψ` have no shared
  negative relation occurrences in `Language.graph`, `lyndon_interpolation_relational` produces an
  interpolant with `negativeRelationsIn = ∅`, which transfers upward along subgraph inclusions
  `G ≤ G'` by `SentenceInf.realize_mono_of_signed`.
* **Function symbols and countable theories (`Theoryω.lyndon_interpolation`)**: over a signature
  with one unary function symbol `f` and one unary relation symbol `R`, the two-sentence theory
  `{∀ x, f (f x) = x, ∃ x, f x ≠ x ∧ R(x)}` entails `(∃ x, f x ≠ x) ∨ ∀ x, ¬ R(x)`. Because `R`
  occurs with opposite polarities on the two sides, `Theoryω.lyndon_interpolation` produces a
  relation-free sentence `θ` in `{f}` that holds on `(Bool, Bool.not)` and fails on `(Bool, id)` —
  forcing `f` to occur in `θ` since both structures share the same two-element carrier.
-/

universe u v

open FirstOrder FirstOrder.Language

-- 1. An unsatisfiable antecedent admits `⊥` with empty occurrence sets, and `lyndon_interpolation`
-- applies directly.
example {L : Language.{u, v}} {φ ψ : L.Sentenceω} (hφ : Sentenceω.Entails φ ⊥) :
    (⊥ : L.Sentenceω).functionsIn = ∅ ∧
      (⊥ : L.Sentenceω).positiveRelationsIn = ∅ ∧
      (⊥ : L.Sentenceω).negativeRelationsIn = ∅ ∧
      ∃ θ : L.Sentenceω,
        θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
        θ.positiveRelationsIn ⊆ φ.positiveRelationsIn ∩ ψ.positiveRelationsIn ∧
        θ.negativeRelationsIn ⊆ φ.negativeRelationsIn ∩ ψ.negativeRelationsIn ∧
        φ.Entails θ ∧ θ.Entails ψ := by
  have hφψ : φ.Entails ψ :=
    Sentenceω.entails_iff.2 fun M _ _ hM => False.elim (by
      have hbot := Sentenceω.entails_iff.1 hφ M hM
      rwa [SentenceInf.realize_bot] at hbot)
  exact ⟨BoundedFormulaInf.functionsIn_bot, BoundedFormulaInf.relationsInSigned_bot true,
    BoundedFormulaInf.relationsInSigned_bot false, lyndon_interpolation φ ψ hφψ⟩

-- 2. A valid consequent admits `⊤` with empty occurrence sets, and `lyndon_interpolation` applies
-- directly.
example {L : Language.{u, v}} {φ ψ : L.Sentenceω} (hψ : Sentenceω.Entails ⊤ ψ) :
    (⊤ : L.Sentenceω).functionsIn = ∅ ∧
      (⊤ : L.Sentenceω).positiveRelationsIn = ∅ ∧
      (⊤ : L.Sentenceω).negativeRelationsIn = ∅ ∧
      ∃ θ : L.Sentenceω,
        θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
        θ.positiveRelationsIn ⊆ φ.positiveRelationsIn ∩ ψ.positiveRelationsIn ∧
        θ.negativeRelationsIn ⊆ φ.negativeRelationsIn ∩ ψ.negativeRelationsIn ∧
        φ.Entails θ ∧ θ.Entails ψ := by
  have hφtop : Sentenceω.Entails φ ⊤ :=
    Sentenceω.entails_iff.2 fun _ _ _ _ => by
      simp [SentenceInf.realize_def, FormulaInf.realize_def]
  exact ⟨BoundedFormulaInf.functionsIn_top, BoundedFormulaInf.relationsInSigned_top true,
    BoundedFormulaInf.relationsInSigned_top false, lyndon_interpolation φ ψ (hφtop.trans hψ)⟩

-- 3. Recovering Craig's unsigned symbol bound from the two signed bounds of `lyndon_interpolation`.
example {L : Language.{u, v}} (φ ψ : L.Sentenceω) (h : φ.Entails ψ) :
    ∃ θ : L.Sentenceω,
      θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
      θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
      φ.Entails θ ∧ θ.Entails ψ := by
  obtain ⟨θ, hfun, hpos, hneg, hφθ, hθψ⟩ := lyndon_interpolation φ ψ h
  refine ⟨θ, hfun, ?_, hφθ, hθψ⟩
  rw [← BoundedFormulaInf.relationsInSigned_union_not true θ]
  refine (Set.union_subset_union hpos hneg).trans ?_
  exact Set.union_subset
    (Set.inter_subset_inter
      (BoundedFormulaInf.relationsInSigned_subset_relationsIn true φ)
      (BoundedFormulaInf.relationsInSigned_subset_relationsIn true ψ))
    (Set.inter_subset_inter
      (BoundedFormulaInf.relationsInSigned_subset_relationsIn false φ)
      (BoundedFormulaInf.relationsInSigned_subset_relationsIn false ψ))

-- 4. Although `adj` occurs in both `∃ x y, x ≠ y ∧ adj(x, y)` and
-- `(∃ x y, x ≠ y) ∨ ∀ x y, ¬ adj(x, y)` over `Language.graph`, it occurs only positively on the
-- left and only negatively on the right, so `lyndon_interpolation_relational` forces a
-- pure-equality interpolant holding on `Bool` and failing on `Unit`.
example :
    let posEdgeTwoElem : Language.graph.Sentenceω :=
      BoundedFormulaInf.ex <| BoundedFormulaInf.ex <|
        (BoundedFormulaInf.equal &0 &1).not ⊓ BoundedFormulaInf.rel Language.adj ![&0, &1]
    let negEdgeOrTwoElem : Language.graph.Sentenceω :=
      (BoundedFormulaInf.ex <| BoundedFormulaInf.ex <| (BoundedFormulaInf.equal &0 &1).not) ⊔
        (BoundedFormulaInf.all <| BoundedFormulaInf.all <|
          (BoundedFormulaInf.rel Language.adj ![&0, &1]).not)
    (⟨2, Language.adj⟩ : Σ n, Language.graph.Relations n) ∈
      posEdgeTwoElem.relationsIn ∩ negEdgeOrTwoElem.relationsIn ∧
    ∃ θ : Language.graph.Sentenceω,
      θ.relationsIn = ∅ ∧
      posEdgeTwoElem.Entails θ ∧
      θ.Entails negEdgeOrTwoElem ∧
      (∀ S : Language.graph.Structure Bool, @SentenceInf.Realize _ ℕ θ Bool S) ∧
      (∀ S : Language.graph.Structure Unit, ¬ @SentenceInf.Realize _ ℕ θ Unit S) := by
  intro posEdgeTwoElem negEdgeOrTwoElem
  have hmem : (⟨2, Language.adj⟩ : Σ n, Language.graph.Relations n) ∈
      posEdgeTwoElem.relationsIn ∩ negEdgeOrTwoElem.relationsIn := by
    simp [posEdgeTwoElem, negEdgeOrTwoElem]
  have hent : posEdgeTwoElem.Entails negEdgeOrTwoElem := by
    refine Sentenceω.entails_iff.2 fun M _ _ h => ?_
    simp only [posEdgeTwoElem, negEdgeOrTwoElem, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_sup, BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_inf,
      BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal] at h ⊢
    obtain ⟨x, y, hxy, -⟩ := h
    exact .inl ⟨x, y, hxy⟩
  obtain ⟨θ, hpos, hneg, h₁, h₂⟩ :=
    lyndon_interpolation_relational posEdgeTwoElem negEdgeOrTwoElem hent
  have hpos_empty : θ.positiveRelationsIn = ∅ :=
    Set.subset_empty_iff.1 (hpos.trans (by simp [posEdgeTwoElem, negEdgeOrTwoElem]))
  have hneg_empty : θ.negativeRelationsIn = ∅ :=
    Set.subset_empty_iff.1 (hneg.trans (by simp [posEdgeTwoElem, negEdgeOrTwoElem]))
  have hrel_empty : θ.relationsIn = ∅ := by
    simp only [BoundedFormulaInf.positiveRelationsIn, BoundedFormulaInf.negativeRelationsIn]
      at hpos_empty hneg_empty
    simp [← BoundedFormulaInf.relationsInSigned_union_not true θ, hpos_empty, hneg_empty]
  refine ⟨hmem, θ, hrel_empty, h₁, h₂, ?_, ?_⟩
  · intro S
    -- Since `θ` mentions no relations, truth on `S` agrees with truth on the full relation on
    -- `Bool`, which satisfies `posEdgeTwoElem`.
    let Sfull : Language.graph.Structure Bool := ⟨fun f => isEmptyElim f, fun _ _ => True⟩
    have hSfull : @SentenceInf.Realize _ ℕ θ Bool Sfull := by
      let : Language.graph.Structure Bool := Sfull
      refine (Sentenceω.entails_iff.1 h₁) Bool ?_
      simp only [posEdgeTwoElem, SentenceInf.realize_def, FormulaInf.realize_def,
        BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_not,
        BoundedFormulaInf.realize_equal, BoundedFormulaInf.realize_rel]
      exact ⟨false, true, Bool.false_ne_true, trivial⟩
    exact SentenceInf.realize_mono_of_signed θ Sfull S
      (fun _ hR => False.elim (by simp [hpos_empty] at hR))
      (fun _ hR => False.elim (by simp [hneg_empty] at hR)) hSfull
  · intro S hθ
    -- On `Unit`, transferring to the full relation `S₁` (where `adj () ()` holds) refutes
    -- `negEdgeOrTwoElem`.
    let S₁ : Language.graph.Structure Unit := ⟨fun f => isEmptyElim f, fun _ _ => True⟩
    have hθ₁ : @SentenceInf.Realize _ ℕ θ Unit S₁ :=
      SentenceInf.realize_mono_of_signed θ S S₁
        (fun _ hR => False.elim (by simp [hpos_empty] at hR))
        (fun _ hR => False.elim (by simp [hneg_empty] at hR)) hθ
    let : Language.graph.Structure Unit := S₁
    have hr := (Sentenceω.entails_iff.1 h₂) Unit hθ₁
    simp only [negEdgeOrTwoElem, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_sup, BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_all,
      BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal,
      BoundedFormulaInf.realize_rel] at hr
    rcases hr with ⟨_, _, hxy⟩ | hall
    · exact hxy trivial
    · exact hall () () trivial

-- 5. When `φ` and `ψ` have no shared negative relation occurrences in `Language.graph`, any Lyndon
-- interpolant `θ` is upward monotone along subgraph inclusions `G ≤ G'`.
example (φ ψ : Language.graph.Sentenceω) (h : φ.Entails ψ)
    (hneg₀ : φ.negativeRelationsIn ∩ ψ.negativeRelationsIn = ∅) :
    ∃ θ : Language.graph.Sentenceω,
      φ.Entails θ ∧ θ.Entails ψ ∧
      ∀ {V : Type u} {G G' : SimpleGraph V}, G ≤ G' →
        @SentenceInf.Realize Language.graph ℕ θ V G.structure →
        @SentenceInf.Realize Language.graph ℕ θ V G'.structure := by
  obtain ⟨θ, -, hneg, hφθ, hθψ⟩ := lyndon_interpolation_relational φ ψ h
  have hθneg : θ.negativeRelationsIn = ∅ := Set.subset_empty_iff.1 (hneg₀ ▸ hneg)
  refine ⟨θ, hφθ, hθψ, fun {V G G'} hle hG => ?_⟩
  refine SentenceInf.realize_mono_of_signed θ G.structure G'.structure ?_ ?_ hG
  · rintro _ ⟨⟩ _ xs hadj
    exact hle hadj
  · intro _ R hR
    simp [hθneg] at hR

-- 6. Over a language with one unary function symbol `f` and one unary relation symbol `R`,
-- countable-theory Lyndon interpolation eliminates `R` (opposite polarities) while retaining `f`
-- (forced to occur because `θ` distinguishes `Bool.not` from `id` on the same carrier `Bool`).
example :
    let Lfun : Language.{0, 0} :=
      ⟨fun | 1 => Unit | _ => Empty, fun | 1 => Unit | _ => Empty⟩
    let fTerm (t : Lfun.Term (Empty ⊕ Fin 1)) : Lfun.Term (Empty ⊕ Fin 1) :=
      Term.func (l := 1) () ![t]
    let rAtom : Lfun.BoundedFormulaω Empty 1 :=
      BoundedFormulaInf.rel (n := 1) (l := 1) () ![&0]
    let involutiveAxiom : Lfun.Sentenceω :=
      BoundedFormulaInf.all (.equal (fTerm (fTerm &0)) &0)
    let movedWitnessPos : Lfun.Sentenceω :=
      BoundedFormulaInf.ex ((BoundedFormulaInf.equal (fTerm &0) &0).not ⊓ rAtom)
    let movedOrNoRelNeg : Lfun.Sentenceω :=
      BoundedFormulaInf.ex (BoundedFormulaInf.equal (fTerm &0) &0).not ⊔
        BoundedFormulaInf.all rAtom.not
    let mkStruct (f : Bool → Bool) (P : Bool → Prop) : Lfun.Structure Bool :=
      { funMap := fun {k} sym xs => match k, sym with | 1, () => f (xs 0)
        RelMap := fun {k} sym xs => match k, sym with | 1, () => P (xs 0) }
    let T : Lfun.Theoryω := {involutiveAxiom, movedWitnessPos}
    ∃ θ : Lfun.Sentenceω,
      θ.relationsIn = ∅ ∧
      θ.functionsIn = {⟨1, ()⟩} ∧
      T.Entails θ ∧
      θ.Entails movedOrNoRelNeg ∧
      @SentenceInf.Realize _ ℕ θ Bool (mkStruct Bool.not fun _ => False) ∧
      ¬ @SentenceInf.Realize _ ℕ θ Bool (mkStruct id fun _ => True) := by
  intro Lfun fTerm rAtom involutiveAxiom movedWitnessPos movedOrNoRelNeg mkStruct T
  have hT : T.Countable := (Set.countable_singleton _).insert _
  have hent : T.Entails movedOrNoRelNeg := by
    refine Theoryω.entails_iff.2 fun M _ _ hM => ?_
    have hm := hM.realize_of_mem (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    simp only [movedWitnessPos, movedOrNoRelNeg, SentenceInf.realize_def, FormulaInf.realize_def,
      BoundedFormulaInf.realize_sup, BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_inf,
      BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal] at hm ⊢
    obtain ⟨x, hfx, -⟩ := hm
    exact .inl ⟨x, hfx⟩
  obtain ⟨θ, hfun, hpos, hneg, hTθ, hθψ⟩ := Theoryω.lyndon_interpolation hT movedOrNoRelNeg hent
  have hpos_empty : θ.positiveRelationsIn = ∅ :=
    Set.subset_empty_iff.1 (hpos.trans (by simp [movedOrNoRelNeg, rAtom]))
  have hneg_empty : θ.negativeRelationsIn = ∅ :=
    Set.subset_empty_iff.1 (hneg.trans (by simp [T, involutiveAxiom, movedWitnessPos, rAtom]))
  have hrel_empty : θ.relationsIn = ∅ := by
    simp only [BoundedFormulaInf.positiveRelationsIn, BoundedFormulaInf.negativeRelationsIn]
      at hpos_empty hneg_empty
    simp [← BoundedFormulaInf.relationsInSigned_union_not true θ, hpos_empty, hneg_empty]
  have hfun_sub : θ.functionsIn ⊆ {⟨1, ()⟩} := by
    refine hfun.trans (Set.inter_subset_right.trans ?_)
    rintro ⟨(_ | _ | k), fk⟩ _
    · exact fk.elim
    · cases fk; rfl
    · exact fk.elim
  have hreal_not : @SentenceInf.Realize _ ℕ θ Bool (mkStruct Bool.not fun _ => False) := by
    let S_true := mkStruct Bool.not fun _ => True
    let S_false := mkStruct Bool.not fun _ => False
    have hT_true : @Theoryω.Model _ T Bool S_true := by
      let : Lfun.Structure Bool := S_true
      rw [Theoryω.model_iff]
      rintro φ (rfl | rfl)
      · simp only [involutiveAxiom, fTerm, SentenceInf.realize_def, FormulaInf.realize_def,
          BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_equal, Fin.snoc_zero]
        intro b; cases b <;> rfl
      · simp only [movedWitnessPos, fTerm, rAtom, S_true, mkStruct, SentenceInf.realize_def,
          FormulaInf.realize_def, BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_inf,
          BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_equal,
          BoundedFormulaInf.realize_rel, Fin.snoc_zero]
        exact ⟨false, Bool.false_ne_true.symm, trivial⟩
    have hθ_true : @SentenceInf.Realize _ ℕ θ Bool S_true := by
      let : Lfun.Structure Bool := S_true
      exact Theoryω.entails_iff.1 hTθ Bool hT_true
    exact SentenceInf.realize_mono_of_agreeOn_functionsIn θ S_true S_false
      (fun _ _ _ => rfl)
      (fun _ hR => False.elim (by simp [hpos_empty] at hR))
      (fun _ hR => False.elim (by simp [hneg_empty] at hR)) hθ_true
  have hnreal_id : ¬ @SentenceInf.Realize _ ℕ θ Bool (mkStruct id fun _ => True) := by
    let S_id := mkStruct id fun _ => True
    let : Lfun.Structure Bool := S_id
    intro hθ_id
    have hψ_id := Sentenceω.entails_iff.1 hθψ Bool hθ_id
    simp only [movedOrNoRelNeg, fTerm, rAtom, SentenceInf.realize_def,
      FormulaInf.realize_def, BoundedFormulaInf.realize_sup, BoundedFormulaInf.realize_ex,
      BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_not,
      BoundedFormulaInf.realize_equal, Fin.snoc_zero] at hψ_id
    rcases hψ_id with ⟨x, hxx⟩ | hall
    · exact hxx rfl
    · exact hall false trivial
  have hfun_eq : θ.functionsIn = {⟨1, ()⟩} := by
    refine Set.Subset.antisymm hfun_sub (Set.singleton_subset_iff.2 ?_)
    by_contra hnf
    have hfun_empty : θ.functionsIn = ∅ :=
      Set.subset_empty_iff.1 fun x hx =>
        hnf ((Set.mem_singleton_iff.1 (hfun_sub hx)) ▸ hx)
    exact hnreal_id (SentenceInf.realize_mono_of_agreeOn_functionsIn θ
      (mkStruct Bool.not fun _ => False) (mkStruct id fun _ => True)
      (fun _ hf => False.elim (by simp [hfun_empty] at hf))
      (fun _ hR => False.elim (by simp [hpos_empty] at hR))
      (fun _ hR => False.elim (by simp [hneg_empty] at hR)) hreal_not)
  exact ⟨θ, hrel_empty, hfun_eq, hTθ, hθψ, hreal_not, hnreal_id⟩
