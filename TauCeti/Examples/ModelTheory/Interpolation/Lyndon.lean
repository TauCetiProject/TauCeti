/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Graph
public import TauCeti.ModelTheory.Interpolation.Lyndon

/-!
# Examples: Lyndon interpolation for `L_{ω₁ω}`

Downstream worked examples exercising `FirstOrder.Language.lyndon_interpolation_relational`,
`FirstOrder.Language.lyndon_interpolation`, and
`FirstOrder.Language.Theoryω.lyndon_interpolation`:

* **Opposite-polarity cancellation (`lyndon_interpolation_relational`).** Over `Language.graph`,
  the sentence `∃ x y, x ≠ y ∧ adj(x, y)` entails `(∃ x y, x ≠ y) ∨ ∀ x y, ¬ adj(x, y)`. The unique
  relation symbol `Language.adj` occurs in both sentences, so unsigned Craig interpolation places no
  restriction on the interpolant's vocabulary; because `adj` occurs only positively on the left and
  only negatively on the right, relational Lyndon interpolation produces a pure-equality sentence
  (`θ.relationsIn = ∅`) satisfied on a two-element graph and refuted on a one-element graph.
* **Function-symbol and opposite-polarity elimination (`lyndon_interpolation`).** Over
  `TauCeti.LyndonExample.FuncRelLang` (one constant `constSym`, one unary function `unarySym`, and
  two unary relations `rel true` and `rel false`), the sentence `P(f(c)) ∧ ∀ x, Q(x)` entails
  `(∃ x, P(f(x))) ∨ ∃ x, ¬ Q(x)`. Lyndon interpolation eliminates both the unshared constant `c`
  (`θ.functionsIn ⊆ {⟨1, unarySym⟩}`) and the shared opposite-polarity relation `Q`
  (`θ.positiveRelationsIn ⊆ {⟨1, rel true⟩}`, `θ.negativeRelationsIn = ∅`);
  `SentenceInf.realize_mono_of_agreeOn_functionsIn` then transfers `θ` across structures that alter
  both `c` and `Q`.
* **Countable-theory Lyndon interpolation (`Theoryω.lyndon_interpolation`).** The countable orbit
  theory `{P(f^[n](c)) | n : ℕ}` entails the infinitary conjunction `⋀_{n : ℕ} ∃ x, P(f^[n](x))`;
  `Theoryω.lyndon_interpolation` compresses the entailment through a single `{f, +P}`-sentence
  eliminating the constant `c`.
-/

public section

namespace TauCeti

open FirstOrder FirstOrder.Language BoundedFormulaInf

/-! ### Opposite-polarity cancellation in `Language.graph` -/

section OppositePolarity

-- `∃ x y, x ≠ y ∧ adj(x, y)` in `Language.graph` (`adj` occurs only positively).
private def posAdjTwoElem : Language.graph.Sentenceω :=
  BoundedFormulaInf.ex <| BoundedFormulaInf.ex <|
    (BoundedFormulaInf.equal &0 &1).not ⊓
      BoundedFormulaInf.rel Language.adj ![&0, &1]

-- `(∃ x y, x ≠ y) ∨ ∀ x y, ¬ adj(x, y)` in `Language.graph` (`adj` occurs only negatively).
private def negAdjOrTwoElem : Language.graph.Sentenceω :=
  (BoundedFormulaInf.ex <| BoundedFormulaInf.ex <| (BoundedFormulaInf.equal &0 &1).not) ⊔
    (BoundedFormulaInf.all <| BoundedFormulaInf.all <|
      (BoundedFormulaInf.rel Language.adj ![&0, &1]).not)

-- Unsigned `relationsIn` contains `Language.adj` on both sides, yet relational Lyndon interpolation
-- eliminates `Language.adj` completely and produces a non-degenerate pure-equality interpolant.
example :
    (⟨2, Language.adj⟩ : Σ k, Language.graph.Relations k) ∈
      posAdjTwoElem.relationsIn ∩ negAdjOrTwoElem.relationsIn ∧
    ∃ θ : Language.graph.Sentenceω,
      θ.relationsIn = ∅ ∧
      posAdjTwoElem.Entails θ ∧
      θ.Entails negAdjOrTwoElem ∧
      (∃ S₂ : Language.graph.Structure Bool, @SentenceInf.Realize _ ℕ θ Bool S₂) ∧
      (∃ S₁ : Language.graph.Structure Unit, ¬ @SentenceInf.Realize _ ℕ θ Unit S₁) := by
  have hmem : (⟨2, Language.adj⟩ : Σ k, Language.graph.Relations k) ∈
      posAdjTwoElem.relationsIn ∩ negAdjOrTwoElem.relationsIn := by
    simp [posAdjTwoElem, negAdjOrTwoElem]
  have hent : posAdjTwoElem.Entails negAdjOrTwoElem := by
    refine Sentenceω.entails_iff.2 fun M _ _ h => ?_
    simp only [posAdjTwoElem, negAdjOrTwoElem, SentenceInf.realize_def, FormulaInf.realize_def,
      realize_sup, realize_ex, realize_inf, realize_not, realize_equal] at h ⊢
    obtain ⟨x, y, hxy, -⟩ := h
    exact .inl ⟨x, y, hxy⟩
  obtain ⟨θ, hpos, hneg, h₁, h₂⟩ :=
    lyndon_interpolation_relational posAdjTwoElem negAdjOrTwoElem hent
  have hpos_empty : θ.relationsInSigned true = ∅ :=
    Set.subset_empty_iff.1 (by simpa [posAdjTwoElem, negAdjOrTwoElem] using hpos)
  have hneg_empty : θ.relationsInSigned false = ∅ :=
    Set.subset_empty_iff.1 (by simpa [posAdjTwoElem, negAdjOrTwoElem] using hneg)
  have hrel : θ.relationsIn = ∅ := by
    rw [← θ.relationsInSigned_union_not true, Bool.not_true, hpos_empty, hneg_empty,
      Set.empty_union]
  refine ⟨hmem, θ, hrel, h₁, h₂, ?_, ?_⟩
  · let S₂ : Language.graph.Structure Bool := ⟨fun f => isEmptyElim f, fun _ _ => True⟩
    let : Language.graph.Structure Bool := S₂
    refine ⟨S₂, h₁.realize Bool ?_⟩
    simp only [posAdjTwoElem, SentenceInf.realize_def, FormulaInf.realize_def, realize_ex,
      realize_inf, realize_not, realize_equal, realize_rel]
    exact ⟨false, true, Bool.false_ne_true, trivial⟩
  · let S₁ : Language.graph.Structure Unit := ⟨fun f => isEmptyElim f, fun _ _ => True⟩
    let : Language.graph.Structure Unit := S₁
    refine ⟨S₁, fun hθ => ?_⟩
    have hr := h₂.realize Unit hθ
    simp only [negAdjOrTwoElem, SentenceInf.realize_def, FormulaInf.realize_def, realize_sup,
      realize_ex, realize_all, realize_not, realize_equal, realize_rel] at hr
    exact hr.elim (fun ⟨_, _, hxy⟩ => hxy trivial) (fun hall => hall () () trivial)

end OppositePolarity

/-! ### Function-symbol and opposite-polarity elimination -/

namespace LyndonExample

/-- Function symbols of `FuncRelLang`: one constant symbol and one unary function symbol. -/
inductive FuncSym : ℕ → Type
  | constSym : FuncSym 0
  | unarySym : FuncSym 1

/-- Relation symbols of `FuncRelLang`: two unary predicates indexed by `Bool`. -/
inductive RelSym : ℕ → Type
  | rel (b : Bool) : RelSym 1

/-- Concrete language with one constant `constSym`, one unary function `unarySym`, and two unary
relations `rel true` and `rel false`. -/
abbrev FuncRelLang : Language.{0, 0} where
  Functions := FuncSym
  Relations := RelSym

private abbrev cSym : FuncRelLang.Functions 0 := .constSym

private abbrev fSym : FuncRelLang.Functions 1 := .unarySym

private abbrev pRel : FuncRelLang.Relations 1 := .rel true

private abbrev qRel : FuncRelLang.Relations 1 := .rel false

private def cTerm {α : Type} : FuncRelLang.Term α := .func cSym ![]

private def fTerm {α : Type} (t : FuncRelLang.Term α) : FuncRelLang.Term α := .func fSym ![t]

/-- Antecedent `P(f(c)) ∧ ∀ x, Q(x)` in `FuncRelLang`. -/
def antFuncRel : FuncRelLang.Sentenceω :=
  BoundedFormulaInf.rel pRel ![fTerm cTerm] ⊓
    BoundedFormulaInf.all (BoundedFormulaInf.rel qRel ![&0])

/-- Consequent `(∃ x, P(f(x))) ∨ ∃ x, ¬ Q(x)` in `FuncRelLang`. -/
def conFuncRel : FuncRelLang.Sentenceω :=
  BoundedFormulaInf.ex (BoundedFormulaInf.rel pRel ![fTerm &0]) ⊔
    BoundedFormulaInf.ex (BoundedFormulaInf.rel qRel ![&0]).not

/-- `FuncRelLang`-structure on `Bool` interpreting `constSym` as `c`, `unarySym` as `id`,
`rel true` as constant `p`, and `rel false` as constant `q`. -/
@[instance_reducible]
def boolStructure (c : Bool) (p q : Prop) : FuncRelLang.Structure Bool where
  funMap
    | .constSym, _ => c
    | .unarySym, xs => xs 0
  RelMap
    | .rel true, _ => p
    | .rel false, _ => q

private theorem relMap_boolStructure_true (c : Bool) (p q : Prop) (xs : Fin 1 → Bool) :
    @Structure.RelMap FuncRelLang Bool (boolStructure c p q) 1 pRel xs ↔ p :=
  Iff.rfl

private theorem relMap_boolStructure_false (c : Bool) (p q : Prop) (xs : Fin 1 → Bool) :
    @Structure.RelMap FuncRelLang Bool (boolStructure c p q) 1 qRel xs ↔ q :=
  Iff.rfl

private theorem functionsIn_fTerm_var {n : ℕ} (i : Fin n) :
    (fTerm (Term.var (.inr i) : FuncRelLang.Term (Empty ⊕ Fin n))).functionsIn = {⟨1, fSym⟩} := by
  simp [fTerm, Term.functionsIn_func]

private theorem functionsIn_conFuncRel_subset :
    conFuncRel.functionsIn ⊆ {⟨1, fSym⟩} := by
  simp [conFuncRel, Function.comp_apply, functionsIn_fTerm_var]

private theorem relationsInSigned_antFuncRel_conFuncRel :
    antFuncRel.relationsInSigned true ∩ conFuncRel.relationsInSigned true ⊆ {⟨1, pRel⟩} ∧
    antFuncRel.relationsInSigned false ∩ conFuncRel.relationsInSigned false = ∅ := by
  constructor
  · rintro s ⟨_, hR⟩
    simpa [conFuncRel] using hR
  · refine Set.eq_empty_of_forall_notMem fun s ⟨hL, _⟩ => ?_
    simp [antFuncRel] at hL

private theorem antFuncRel_entails_conFuncRel : antFuncRel.Entails conFuncRel := by
  refine Sentenceω.entails_iff.2 fun M _ _ h => ?_
  obtain ⟨hP, -⟩ := SentenceInf.realize_inf.1 h
  refine SentenceInf.realize_sup.2 (.inl ?_)
  rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_ex]
  rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_rel] at hP
  refine ⟨Structure.funMap cSym ![], ?_⟩
  rw [realize_rel]
  refine Eq.mp (congrArg (Structure.RelMap pRel) ?_) hP
  ext i
  rw [Subsingleton.elim i 0]
  simp only [fTerm, cTerm, Matrix.cons_val_zero, Term.realize_func, Function.comp_apply,
    Fin.snoc_zero]
  refine congrArg (Structure.funMap fSym) ?_
  ext j
  rw [Subsingleton.elim j 0]
  exact congrArg (Structure.funMap cSym) (Subsingleton.elim _ _)

/-- Lyndon interpolation on `antFuncRel ⊨ conFuncRel` eliminates both `constSym` and the shared
opposite-polarity relation `rel false`, and `SentenceInf.realize_mono_of_agreeOn_functionsIn`
transfers the interpolant across simultaneous changes to `constSym` and `rel false`. -/
theorem exists_lyndon_interpolant_funcRel :
    (⟨1, RelSym.rel false⟩ : Σ k, FuncRelLang.Relations k) ∈
      antFuncRel.relationsIn ∩ conFuncRel.relationsIn ∧
    ∃ θ : FuncRelLang.Sentenceω,
      θ.functionsIn ⊆ {⟨1, FuncSym.unarySym⟩} ∧
      θ.positiveRelationsIn ⊆ {⟨1, RelSym.rel true⟩} ∧
      θ.negativeRelationsIn = ∅ ∧
      antFuncRel.Entails θ ∧
      θ.Entails conFuncRel ∧
      @SentenceInf.Realize _ ℕ θ Bool (boolStructure true True False) ∧
      ¬ @SentenceInf.Realize _ ℕ θ Bool (boolStructure false False True) := by
  have hQ : (⟨1, qRel⟩ : Σ k, FuncRelLang.Relations k) ∈
      antFuncRel.relationsIn ∩ conFuncRel.relationsIn := by
    simp [antFuncRel, conFuncRel]
  obtain ⟨θ, hfun, hpos, hneg, h₁, h₂⟩ :=
    lyndon_interpolation antFuncRel conFuncRel antFuncRel_entails_conFuncRel
  obtain ⟨hpos_sub, hneg_eq⟩ := relationsInSigned_antFuncRel_conFuncRel
  have hθfun : θ.functionsIn ⊆ {⟨1, fSym⟩} :=
    hfun.trans (Set.inter_subset_right.trans functionsIn_conFuncRel_subset)
  have hθpos : θ.positiveRelationsIn ⊆ {⟨1, pRel⟩} := hpos.trans hpos_sub
  have hθneg : θ.negativeRelationsIn = ∅ := Set.subset_empty_iff.1 (hneg_eq ▸ hneg)
  refine ⟨hQ, θ, hθfun, hθpos, hθneg, h₁, h₂, ?_, ?_⟩
  · have hTT : @SentenceInf.Realize _ ℕ θ Bool (boolStructure false True True) := by
      let : FuncRelLang.Structure Bool := boolStructure false True True
      refine h₁.realize Bool (SentenceInf.realize_inf.2 ⟨?_, ?_⟩)
      · simp [SentenceInf.realize_def, FormulaInf.realize_def, relMap_boolStructure_true]
      · simp [SentenceInf.realize_def, FormulaInf.realize_def, relMap_boolStructure_false]
    refine SentenceInf.realize_mono_of_agreeOn_functionsIn θ
      (boolStructure false True True) (boolStructure true True False) ?_ ?_ ?_ hTT
    · intro k f hf xs
      obtain ⟨rfl, hsym⟩ := Sigma.mk.inj (Set.mem_singleton_iff.1 (hθfun hf))
      cases eq_of_heq hsym
      rfl
    · intro k R hR _ hp
      obtain ⟨rfl, hsym⟩ := Sigma.mk.inj (Set.mem_singleton_iff.1 (hθpos hR))
      cases eq_of_heq hsym
      exact hp
    · intro k R hR
      exact False.elim (by simp [hθneg] at hR)
  · let : FuncRelLang.Structure Bool := boolStructure false False True
    intro hθ
    rcases SentenceInf.realize_sup.1 (h₂.realize Bool hθ) with hP | hQ'
    · simp [SentenceInf.realize_def, FormulaInf.realize_def, relMap_boolStructure_true] at hP
    · simp [SentenceInf.realize_def, FormulaInf.realize_def, relMap_boolStructure_false] at hQ'

/-! ### Countable-theory Lyndon interpolation -/

private def iterConst : ℕ → FuncRelLang.Term (Empty ⊕ Fin 0)
  | 0 => cTerm
  | n + 1 => fTerm (iterConst n)

private def iterVar : ℕ → FuncRelLang.Term (Empty ⊕ Fin 1)
  | 0 => &0
  | n + 1 => fTerm (iterVar n)

private theorem functionsIn_iterVar_subset (n : ℕ) :
    (iterVar n).functionsIn ⊆ {⟨1, fSym⟩} := by
  induction n with
  | zero => simp [iterVar]
  | succ n ih =>
    rintro s hs
    simp only [iterVar, fTerm, Term.functionsIn_func, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_iUnion, Fin.exists_fin_one, Matrix.cons_val_zero] at hs
    exact hs.elim Set.mem_singleton_of_eq fun h => ih h

private theorem realize_iterConst_eq_iterVar {M : Type} [FuncRelLang.Structure M] (n : ℕ) :
    Term.realize (Sum.elim Empty.elim default) (iterConst n) =
      Term.realize (Sum.elim Empty.elim
        (Fin.snoc (α := fun _ => M) default (Structure.funMap cSym ![]))) (iterVar n) := by
  induction n with
  | zero =>
    rw [iterConst, iterVar, cTerm, Term.realize_func, Function.comp_apply, Term.realize_var,
      Sum.elim_inr, Fin.snoc_zero]
    exact congrArg (Structure.funMap cSym) (Subsingleton.elim _ _)
  | succ n ih =>
    rw [iterConst, iterVar, fTerm, fTerm, Term.realize_func, Term.realize_func]
    exact congrArg (Structure.funMap fSym) (by ext i; rw [Subsingleton.elim i 0]; exact ih)

/-- Countably infinite orbit theory `{P(f^[n](c)) | n : ℕ}` in `FuncRelLang`. -/
def orbitTheory : FuncRelLang.Theoryω :=
  Set.range fun n : ℕ => BoundedFormulaInf.rel pRel ![iterConst n]

/-- Consequence `⋀_{n : ℕ} ∃ x, P(f^[n](x))` of `orbitTheory`. -/
def orbitConseq : FuncRelLang.Sentenceω :=
  BoundedFormulaInf.iInf fun n : ℕ =>
    BoundedFormulaInf.ex (BoundedFormulaInf.rel pRel ![iterVar n])

end LyndonExample

open LyndonExample

-- `Theoryω.lyndon_interpolation` interpolates the countable theory `orbitTheory` and `orbitConseq`
-- by a single sentence mentioning at most `unarySym` and positive `rel true`.
example :
    ∃ θ : FuncRelLang.Sentenceω,
      θ.functionsIn ⊆ {⟨1, FuncSym.unarySym⟩} ∧
      θ.positiveRelationsIn ⊆ {⟨1, RelSym.rel true⟩} ∧
      θ.negativeRelationsIn = ∅ ∧
      orbitTheory.Entails θ ∧
      θ.Entails orbitConseq ∧
      @SentenceInf.Realize _ ℕ θ Bool (boolStructure false True False) ∧
      ¬ @SentenceInf.Realize _ ℕ θ Bool (boolStructure false False True) := by
  have hent : orbitTheory.Entails orbitConseq := by
    refine Theoryω.entails_iff.2 fun M _ _ hM => SentenceInf.realize_iInf.2 fun n => ?_
    have hn :
        (BoundedFormulaInf.rel (ι := ℕ) pRel ![iterConst n]).Realize
          Empty.elim (default : Fin 0 → M) := by
      simpa [SentenceInf.realize_def, FormulaInf.realize_def] using
        hM.realize_of_mem (φ := BoundedFormulaInf.rel pRel ![iterConst n]) ⟨n, rfl⟩
    rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_ex]
    rw [realize_rel] at hn
    refine ⟨Structure.funMap cSym ![], ?_⟩
    rw [realize_rel]
    refine Eq.mp (congrArg (Structure.RelMap pRel) ?_) hn
    ext i
    rw [Subsingleton.elim i 0, Matrix.cons_val_zero, Matrix.cons_val_zero]
    exact realize_iterConst_eq_iterVar (M := M) n
  obtain ⟨θ, hfun, hpos, hneg, h₁, h₂⟩ :=
    Theoryω.lyndon_interpolation (Set.countable_range _) orbitConseq hent
  have hfun' : θ.functionsIn ⊆ {⟨1, FuncSym.unarySym⟩} := by
    refine hfun.trans (Set.inter_subset_right.trans ?_)
    simp only [orbitConseq, functionsIn_iInf, functionsIn_ex, functionsIn_rel,
      Set.iUnion_subset_iff, Fin.forall_fin_one, Matrix.cons_val_zero]
    exact functionsIn_iterVar_subset
  have hpos' : θ.positiveRelationsIn ⊆ {⟨1, RelSym.rel true⟩} := by
    refine hpos.trans (Set.inter_subset_right.trans ?_)
    simp [orbitConseq]
  have hneg' : θ.negativeRelationsIn = ∅ := by
    refine Set.subset_empty_iff.1 (hneg.trans (Set.inter_subset_right.trans ?_))
    simp [orbitConseq]
  refine ⟨θ, hfun', hpos', hneg', h₁, h₂, ?_, ?_⟩
  · let : FuncRelLang.Structure Bool := boolStructure false True False
    refine (Theoryω.entails_iff.1 h₁) Bool (Theoryω.model_iff.2 ?_)
    rintro _ ⟨n, rfl⟩
    simp [SentenceInf.realize_def, FormulaInf.realize_def, relMap_boolStructure_true]
  · let : FuncRelLang.Structure Bool := boolStructure false False True
    intro hθ
    have hr := SentenceInf.realize_iInf.1 (h₂.realize Bool hθ) 0
    simp [SentenceInf.realize_def, FormulaInf.realize_def, relMap_boolStructure_true] at hr

end TauCeti

end
