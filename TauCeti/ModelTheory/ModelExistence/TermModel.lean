/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Quotients
public import TauCeti.ModelTheory.ModelExistence.ConsistencyProperty

/-!
# Henkin-complete sets and their term models

A set `S` of `L_{ω₁ω}` sentences of the Henkin expansion `L[[ℕ]]` is **Henkin complete** when it
contains the target of every clause of a consistency property: an implication in `S` brings the
negation of its hypothesis or its conclusion into `S`, a universal sentence in `S` brings all of
its instances at Henkin constants, a negated universal sentence brings a counterexample at some
Henkin constant, equality is reflexive and substitutive into atomic formulas, every closed term is
equal to some Henkin constant, and so on. The model existence theorem produces such a set as the
union of a fair enumeration of members of a consistency property.

A Henkin-complete set has a **term model**: the Henkin constants modulo the equalities asserted in
`S`. A function symbol applied to classes is the class of a constant that `S` asserts to be equal
to the corresponding closed term, and a relation holds of classes when `S` contains the
corresponding relational sentence. Every element of the term model is the interpretation of a
Henkin constant, and the term model is countable.

Suppose in addition that `S` contains neither `⊥` nor a sentence together with its negation.
The **truth lemma** then consists of two forward implications, for every formula `φ` with `n`
bound positions and every tuple `c` of `n` Henkin constants: if `S` contains the instance `φ[c]`
then `φ` holds of the constants `c` in the term model, and if `S` contains `¬φ[c]` then it does
not. No maximality of `S` and no decision between `φ` and `¬φ` is needed. Under the same
hypotheses the term model is a model of `S` (`ConsistencyProperty.HenkinComplete.model`).

## Main definitions

* `FirstOrder.Language.ConsistencyProperty.HenkinComplete`: sets of `L[[ℕ]]` sentences that
  contain the target of every clause of a consistency property.
* `FirstOrder.Language.ConsistencyProperty.HenkinComplete.TermModel`: the Henkin constants modulo
  the equalities asserted in a Henkin-complete set, with its `L[[ℕ]]`-structure.

## Main results

* `FirstOrder.Language.ConsistencyProperty.HenkinComplete.eq_congr`: substitution of equals into
  atomic formulas at any number of bound positions, with `eq_symm` and `eq_trans`.
* `FirstOrder.Language.ConsistencyProperty.HenkinComplete.con_surjective`: every element of the
  term model is named by a Henkin constant.
* `FirstOrder.Language.ConsistencyProperty.HenkinComplete.realize_eq_con_of_mem`: a closed term
  denotes the class of any Henkin constant that `S` asserts to be equal to it.
* `FirstOrder.Language.ConsistencyProperty.HenkinComplete.realize_iff_mem_of_isAtomic`: an atomic
  sentence holds in the term model exactly when it belongs to `S`.
* `FirstOrder.Language.ConsistencyProperty.HenkinComplete.truth_pos` and
  `FirstOrder.Language.ConsistencyProperty.HenkinComplete.truth_neg`: the truth lemma.
* `FirstOrder.Language.ConsistencyProperty.HenkinComplete.model`: the term model of a
  Henkin-complete set containing no contradiction is a model of it.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, §4.1.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.
* `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Methods/Henkin/CountableCompletion/ConsistencyPropertyEqOn.lean`,
  `QuotientTermModel.lean` and `QuotientTruthLemma.lean`, which formalize a Henkin-completeness
  predicate, a quotient term model and the two-polarity forward truth lemma. Divergences from
  that source: the clauses are those of `FirstOrder.Language.ConsistencyProperty`, with function
  symbols, substitution of equals into all atomic formulas and a naming clause for closed terms;
  the absence of `⊥` and of contradictions is kept out of the predicate; the term model is a
  quotient of the Henkin constants rather than of the closed terms; and the truth lemma is a
  structural induction over formulas with bound positions instantiated by tuples of constants.
-/

public section

universe u v

namespace FirstOrder

namespace Language

open BoundedFormulaInf Term

namespace ConsistencyProperty

variable {L : Language.{u, v}}

/-- A set `S` of `L[[ℕ]]` sentences is **Henkin complete** when it contains the target of every
clause of a consistency property: one chosen component of each disjunctive sentence in `S`, every
component of each conjunctive one, every instance at a Henkin constant of each universal sentence,
a counterexample at some Henkin constant to each negated universal sentence, every reflexive
equation of closed terms, the result of substituting equals into each atomic sentence, and an
equation naming each closed term by a Henkin constant. -/
structure HenkinComplete (S : L[[ℕ]].Theoryω) : Prop where
  /-- An implication brings the negation of its hypothesis or its conclusion. -/
  imp : ∀ φ ψ : L[[ℕ]].Sentenceω, φ.imp ψ ∈ S → φ.not ∈ S ∨ ψ ∈ S
  /-- A negated implication brings its hypothesis and the negation of its conclusion. -/
  not_imp : ∀ φ ψ : L[[ℕ]].Sentenceω, (φ.imp ψ).not ∈ S → φ ∈ S ∧ ψ.not ∈ S
  /-- A countable conjunction brings each of its conjuncts. -/
  iInf : ∀ φs : ℕ → L[[ℕ]].Sentenceω, BoundedFormulaInf.iInf φs ∈ S → ∀ k, φs k ∈ S
  /-- A negated countable conjunction brings the negation of some conjunct. -/
  not_iInf : ∀ φs : ℕ → L[[ℕ]].Sentenceω, (BoundedFormulaInf.iInf φs).not ∈ S →
    ∃ k, (φs k).not ∈ S
  /-- A countable disjunction brings some disjunct. -/
  iSup : ∀ φs : ℕ → L[[ℕ]].Sentenceω, BoundedFormulaInf.iSup φs ∈ S → ∃ k, φs k ∈ S
  /-- A negated countable disjunction brings the negation of each disjunct. -/
  not_iSup : ∀ φs : ℕ → L[[ℕ]].Sentenceω, (BoundedFormulaInf.iSup φs).not ∈ S →
    ∀ k, (φs k).not ∈ S
  /-- A universal sentence brings its instance at every Henkin constant. -/
  all : ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1, φ.all ∈ S → ∀ c : ℕ, φ.inst (L.con c).term ∈ S
  /-- A negated universal sentence brings a counterexample at some Henkin constant. -/
  not_all : ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1, φ.all.not ∈ S →
    ∃ c : ℕ, (φ.inst (L.con c).term).not ∈ S
  /-- Every closed term equals itself. -/
  eq_refl : ∀ t : L[[ℕ]].Term (Empty ⊕ Fin 0), (equal t t : L[[ℕ]].Sentenceω) ∈ S
  /-- Equals can be substituted for equals in an atomic formula. -/
  eq_subst : ∀ (t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)) (φ : L[[ℕ]].BoundedFormulaω Empty 1),
    φ.IsAtomic → (equal t t' : L[[ℕ]].Sentenceω) ∈ S → φ.inst t ∈ S → φ.inst t' ∈ S
  /-- Every closed term equals some Henkin constant. -/
  eq_name : ∀ t : L[[ℕ]].Term (Empty ⊕ Fin 0),
    ∃ c : ℕ, (equal (L.con c).term t : L[[ℕ]].Sentenceω) ∈ S

namespace HenkinComplete

variable {S : L[[ℕ]].Theoryω} (hS : HenkinComplete S)
include hS

/-! ### Equality -/

/-- Substitution of equals at a single bound position of an atomic formula. -/
private theorem substBounds_update_mem {n : ℕ} {φ : L[[ℕ]].BoundedFormulaω Empty n}
    (hφ : φ.IsAtomic) {u : Fin n → L[[ℕ]].Term (Empty ⊕ Fin 0)} {j : Fin n}
    {t : L[[ℕ]].Term (Empty ⊕ Fin 0)} (ht : (equal (u j) t : L[[ℕ]].Sentenceω) ∈ S)
    (hu : substBounds u φ ∈ S) : substBounds (Function.update u j t) φ ∈ S := by
  -- `ψ` instantiates every bound position of `φ` except `j`, which becomes the bound position
  -- of a formula with one bound position; its instances are the instances of `φ` at `u`
  -- updated at `j`.
  have hψ : ∀ s : L[[ℕ]].Term (Empty ⊕ Fin 0),
      (substBounds (Function.update (fun i => (u i).relabel (Sum.map id finZeroElim)) j
        (var (Sum.inr 0))) φ).inst s = substBounds (Function.update u j s) φ := by
    intro s
    rw [inst_def, substBounds_substBounds]
    congr 1
    funext i
    rcases eq_or_ne i j with rfl | hi
    · simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi, subst_relabel]
      conv_rhs => rw [← subst_var (u i)]
      congr 1
      funext x
      rcases x with x | x
      · exact x.elim
      · exact x.elim0
  rw [← hψ]
  exact hS.eq_subst _ _ _ (hφ.substBounds _) ht (by rwa [hψ, Function.update_eq_self])

/-- **Substitution of equals** into an atomic formula at any number of bound positions: if `S`
contains `sᵢ = tᵢ` for every bound position `i` of the atomic formula `φ`, then `S` contains
`φ[t]` as soon as it contains `φ[s]`. -/
theorem eq_congr {n : ℕ} {φ : L[[ℕ]].BoundedFormulaω Empty n} (hφ : φ.IsAtomic)
    {s t : Fin n → L[[ℕ]].Term (Empty ⊕ Fin 0)}
    (hst : ∀ i, (equal (s i) (t i) : L[[ℕ]].Sentenceω) ∈ S) (hs : substBounds s φ ∈ S) :
    substBounds t φ ∈ S := by
  classical
  -- replace the bound positions in `A` by `t`, one at a time
  have key : ∀ A : Finset (Fin n), substBounds (fun i => if i ∈ A then t i else s i) φ ∈ S := by
    intro A
    induction A using Finset.induction_on with
    | empty => simpa using hs
    | insert a A ha ih =>
      convert hS.substBounds_update_mem hφ (j := a) (t := t a) (by simpa [ha] using hst a) ih
        using 2
      funext i
      rcases eq_or_ne i a with rfl | hi
      · simp
      · simp [hi]
  simpa using key Finset.univ

/-- Equality of closed terms in a Henkin-complete set is symmetric. -/
theorem eq_symm {t t' : L[[ℕ]].Term (Empty ⊕ Fin 0)}
    (h : (equal t t' : L[[ℕ]].Sentenceω) ∈ S) : (equal t' t : L[[ℕ]].Sentenceω) ∈ S := by
  have := hS.eq_congr (IsAtomic.equal (ι := ℕ) (var (Sum.inr 1)) (var (Sum.inr 0)))
    (s := ![t, t]) (t := ![t, t'])
    (Fin.forall_fin_two.2 ⟨by simpa using hS.eq_refl t, by simpa using h⟩)
    (by simpa using hS.eq_refl t)
  simpa using this

/-- Equality of closed terms in a Henkin-complete set is transitive. -/
theorem eq_trans {t t' t'' : L[[ℕ]].Term (Empty ⊕ Fin 0)}
    (h : (equal t t' : L[[ℕ]].Sentenceω) ∈ S) (h' : (equal t' t'' : L[[ℕ]].Sentenceω) ∈ S) :
    (equal t t'' : L[[ℕ]].Sentenceω) ∈ S := by
  have := hS.eq_congr (IsAtomic.equal (ι := ℕ) (var (Sum.inr 0)) (var (Sum.inr 1)))
    (s := ![t, t']) (t := ![t, t''])
    (Fin.forall_fin_two.2 ⟨by simpa using hS.eq_refl t, by simpa using h'⟩)
    (by simpa using h)
  simpa using this

/-- Substitution of equals into the arguments of a function symbol. -/
private theorem eq_func_mem {l : ℕ} {f : L[[ℕ]].Functions l}
    {s t : Fin l → L[[ℕ]].Term (Empty ⊕ Fin 0)} {x : L[[ℕ]].Term (Empty ⊕ Fin 0)}
    (hst : ∀ i, (equal (s i) (t i) : L[[ℕ]].Sentenceω) ∈ S)
    (h : (equal x (func f s) : L[[ℕ]].Sentenceω) ∈ S) :
    (equal x (func f t) : L[[ℕ]].Sentenceω) ∈ S := by
  have := hS.eq_congr
    (IsAtomic.equal (ι := ℕ) (var (Sum.inr (Fin.last l)))
      (func f fun i => var (Sum.inr i.castSucc)))
    (s := Fin.snoc s x) (t := Fin.snoc t x)
    (fun i => by induction i using Fin.lastCases <;> simp [hS.eq_refl, hst])
    (by simpa using h)
  simpa using this

/-- Substitution of equals into the arguments of a relation symbol. -/
private theorem rel_mem_of_eq {l : ℕ} {R : L[[ℕ]].Relations l}
    {s t : Fin l → L[[ℕ]].Term (Empty ⊕ Fin 0)}
    (hst : ∀ i, (equal (s i) (t i) : L[[ℕ]].Sentenceω) ∈ S)
    (h : (rel R s : L[[ℕ]].Sentenceω) ∈ S) : (rel R t : L[[ℕ]].Sentenceω) ∈ S := by
  have := hS.eq_congr (IsAtomic.rel (ι := ℕ) R fun i => var (Sum.inr i)) hst (by simpa using h)
  simpa using this

/-! ### The term model -/

/-- Henkin constants are equivalent modulo `S` when `S` asserts that they are equal. -/
private def setoid : Setoid ℕ where
  r c d := (equal (L.con c).term (L.con d).term : L[[ℕ]].Sentenceω) ∈ S
  iseqv := ⟨fun _ => hS.eq_refl _, hS.eq_symm, hS.eq_trans⟩

/-- The **term model** of a Henkin-complete set `S`: the Henkin constants modulo the equalities
asserted in `S`. A function symbol applied to classes is the class of a constant that `S` asserts
to be equal to the corresponding closed term, and a relation holds of classes when `S` contains
the corresponding relational sentence. -/
def TermModel : Type :=
  Quotient hS.setoid

/-- The class of a Henkin constant in the term model. -/
private def cls (c : ℕ) : hS.TermModel :=
  Quotient.mk hS.setoid c

/-- The constant naming a closed term in `S`. -/
private noncomputable def name (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) : ℕ :=
  (hS.eq_name t).choose

private theorem name_mem (t : L[[ℕ]].Term (Empty ⊕ Fin 0)) :
    (equal (L.con (hS.name t)).term t : L[[ℕ]].Sentenceω) ∈ S :=
  (hS.eq_name t).choose_spec

/-- The `L[[ℕ]]`-structure on Henkin constants underlying the term model: a function symbol applied
to constants is the constant naming the corresponding closed term, and a relation holds of
constants when `S` contains the corresponding relational sentence. Both respect the equalities
asserted in `S`. -/
@[instance_reducible]
private noncomputable def prestructure : L[[ℕ]].Prestructure hS.setoid where
  toStructure :=
    { funMap := fun f c => hS.name (func f fun i => (L.con (c i)).term)
      RelMap := fun R c => (rel R fun i => (L.con (c i)).term : L[[ℕ]].Sentenceω) ∈ S }
  fun_equiv _ _ h :=
    hS.eq_trans (hS.eq_func_mem h (hS.name_mem _)) (hS.eq_symm (hS.name_mem _))
  rel_equiv _ _ h :=
    propext ⟨hS.rel_mem_of_eq h, hS.rel_mem_of_eq fun i => hS.eq_symm (h i)⟩

/-- The `L[[ℕ]]`-structure of the term model: a function symbol applied to classes of constants is
the class of the constant naming the corresponding closed term, and a relation holds of classes of
constants when `S` contains the corresponding relational sentence. -/
@[instance_reducible]
noncomputable def termModelStructure : L[[ℕ]].Structure hS.TermModel :=
  quotientStructure (ps := hS.prestructure)

noncomputable instance : L[[ℕ]].Structure hS.TermModel :=
  hS.termModelStructure

private theorem cls_eq_cls_iff {c d : ℕ} :
    hS.cls c = hS.cls d ↔ (equal (L.con c).term (L.con d).term : L[[ℕ]].Sentenceω) ∈ S :=
  Quotient.eq (r := hS.setoid)

private theorem cls_surjective : Function.Surjective hS.cls :=
  Quotient.mk_surjective (s := hS.setoid)

private theorem funMap_cls {l : ℕ} (f : L[[ℕ]].Functions l) (c : Fin l → ℕ) :
    Structure.funMap f (fun i => hS.cls (c i)) =
      hS.cls (hS.name (func f fun i => (L.con (c i)).term)) :=
  funMap_quotient_mk' (ps := hS.prestructure) hS.setoid f c

private theorem relMap_cls {l : ℕ} (R : L[[ℕ]].Relations l) (c : Fin l → ℕ) :
    Structure.RelMap R (fun i => hS.cls (c i)) ↔
      (rel R fun i => (L.con (c i)).term : L[[ℕ]].Sentenceω) ∈ S :=
  relMap_quotient_mk' (ps := hS.prestructure) hS.setoid R c

/-- Evaluation in the term model, stated with the classes of constants. -/
private theorem realize_eq_cls_of_mem {t : L[[ℕ]].Term (Empty ⊕ Fin 0)} {c : ℕ}
    (h : (equal (L.con c).term t : L[[ℕ]].Sentenceω) ∈ S)
    (v : Empty ⊕ Fin 0 → hS.TermModel) : t.realize v = hS.cls c := by
  induction t generalizing c with
  | var x =>
    rcases x with x | x
    · exact x.elim
    · exact x.elim0
  | func f ts ih =>
    have hts (i) : (ts i).realize v = hS.cls (hS.name (ts i)) :=
      ih i (hS.name_mem (ts i))
    rw [realize_func]
    simp only [hts, funMap_cls]
    exact (hS.cls_eq_cls_iff).2
      (hS.eq_trans (hS.eq_func_mem (fun i => hS.name_mem (ts i)) (hS.name_mem _)) (hS.eq_symm h))

/-- A Henkin constant denotes its own class in the term model. -/
private theorem con_eq_cls (c : ℕ) : (L.con c : hS.TermModel) = hS.cls c :=
  (realize_constants (v := fun _ : Empty ⊕ Fin 0 => hS.cls 0)).symm.trans
    (hS.realize_eq_cls_of_mem (hS.eq_refl _) _)

/-- **Every element of the term model is named by a Henkin constant.** -/
theorem con_surjective : Function.Surjective fun c : ℕ => (L.con c : hS.TermModel) := by
  simpa only [con_eq_cls] using hS.cls_surjective

instance : Countable hS.TermModel :=
  hS.con_surjective.countable

instance : Nonempty hS.TermModel :=
  ⟨L.con 0⟩

/-- Two Henkin constants denote the same element of the term model exactly when `S` asserts that
they are equal. -/
theorem con_eq_con_iff {c d : ℕ} :
    (L.con c : hS.TermModel) = L.con d ↔
      (equal (L.con c).term (L.con d).term : L[[ℕ]].Sentenceω) ∈ S := by
  rw [con_eq_cls, con_eq_cls, cls_eq_cls_iff]

/-- **Evaluation in the term model**: a closed term denotes the interpretation of any Henkin
constant that `S` asserts to be equal to it. -/
theorem realize_eq_con_of_mem {t : L[[ℕ]].Term (Empty ⊕ Fin 0)} {c : ℕ}
    (h : (equal (L.con c).term t : L[[ℕ]].Sentenceω) ∈ S)
    (v : Empty ⊕ Fin 0 → hS.TermModel) : t.realize v = L.con c := by
  rw [con_eq_cls]
  exact hS.realize_eq_cls_of_mem h v

/-- **Atomic semantics of the term model**: an atomic sentence holds in the term model exactly
when it belongs to `S`. -/
theorem realize_iff_mem_of_isAtomic {φ : L[[ℕ]].Sentenceω} (hφ : φ.IsAtomic) :
    SentenceInf.Realize φ hS.TermModel ↔ φ ∈ S := by
  cases hφ with
  | equal t₁ t₂ =>
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_equal,
      hS.realize_eq_cls_of_mem (hS.name_mem t₁), hS.realize_eq_cls_of_mem (hS.name_mem t₂),
      cls_eq_cls_iff]
    exact ⟨fun h => hS.eq_trans (hS.eq_symm (hS.name_mem t₁)) (hS.eq_trans h (hS.name_mem t₂)),
      fun h => hS.eq_trans (hS.name_mem t₁) (hS.eq_trans h (hS.eq_symm (hS.name_mem t₂)))⟩
  | rel R ts =>
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_rel,
      fun i => hS.realize_eq_cls_of_mem (hS.name_mem (ts i)), relMap_cls]
    exact ⟨hS.rel_mem_of_eq fun i => hS.name_mem (ts i),
      hS.rel_mem_of_eq fun i => hS.eq_symm (hS.name_mem (ts i))⟩

/-! ### The truth lemma -/

/-- Both halves of the truth lemma, by one simultaneous induction. -/
private theorem truth (hbot : (⊥ : L[[ℕ]].Sentenceω) ∉ S)
    (hcon : ∀ φ ∈ S, φ.not ∉ S) {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n) (c : Fin n → ℕ) :
    (substBounds (fun i => (L.con (c i)).term) φ ∈ S →
      φ.Realize Empty.elim fun i => (L.con (c i) : hS.TermModel)) ∧
    ((substBounds (fun i => (L.con (c i)).term) φ).not ∈ S →
      ¬φ.Realize Empty.elim fun i => (L.con (c i) : hS.TermModel)) := by
  -- atomic formulas are decided by the atomic semantics of the term model
  have atomic {n : ℕ} {φ : L[[ℕ]].BoundedFormulaω Empty n} (hφ : φ.IsAtomic) (c : Fin n → ℕ) :
      (substBounds (fun i => (L.con (c i)).term) φ ∈ S →
        φ.Realize Empty.elim fun i => (L.con (c i) : hS.TermModel)) ∧
      ((substBounds (fun i => (L.con (c i)).term) φ).not ∈ S →
        ¬φ.Realize Empty.elim fun i => (L.con (c i) : hS.TermModel)) := by
    have hr := hS.realize_iff_mem_of_isAtomic (hφ.substBounds fun i => (L.con (c i)).term)
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_substBounds,
      realize_constants] at hr
    exact ⟨hr.2, fun h h' => hcon _ (hr.1 h') h⟩
  -- extending the tuple of constants extends the tuples of their terms and interpretations
  have hterm {n : ℕ} (c : Fin n → ℕ) (d : ℕ) :
      (fun i => (L.con (Fin.snoc (α := fun _ => ℕ) c d i)).term : _ → L[[ℕ]].Term (Empty ⊕ Fin 0)) =
        Fin.snoc (fun i => (L.con (c i)).term) (L.con d).term :=
    Fin.comp_snoc (fun k : ℕ => (L.con k).term) c d
  have hsnoc {n : ℕ} (c : Fin n → ℕ) (d : ℕ) :
      (fun i => (L.con (Fin.snoc (α := fun _ => ℕ) c d i) : hS.TermModel)) =
        Fin.snoc (fun i => (L.con (c i) : hS.TermModel)) (L.con d) :=
    Fin.comp_snoc (fun k : ℕ => (L.con k : hS.TermModel)) c d
  induction φ with
  | falsum =>
    refine ⟨fun h => (hbot ?_).elim, fun _ h => h⟩
    rwa [substBounds_falsum, ← bot_def] at h
  | equal t₁ t₂ => exact atomic (.equal t₁ t₂) c
  | rel R ts => exact atomic (.rel R ts) c
  | imp φ ψ ihφ ihψ =>
    simp only [substBounds_imp, realize_imp]
    refine ⟨fun h hφ => ?_, fun h hφψ => ?_⟩
    · rcases hS.imp _ _ h with h | h
      · exact ((ihφ c).2 h hφ).elim
      · exact (ihψ c).1 h
    · obtain ⟨h₁, h₂⟩ := hS.not_imp _ _ h
      exact (ihψ c).2 h₂ (hφψ ((ihφ c).1 h₁))
  | all φ ih =>
    simp only [substBounds_all, realize_all]
    refine ⟨fun h y => ?_, fun h hall => ?_⟩
    · obtain ⟨d, rfl⟩ := hS.con_surjective y
      have := (ih (Fin.snoc c d)).1
        (by rw [hterm, ← inst_substBounds_liftSubst]; exact hS.all _ h d)
      rwa [hsnoc] at this
    · obtain ⟨d, hd⟩ := hS.not_all _ h
      have := (ih (Fin.snoc c d)).2 (by rw [hterm, ← inst_substBounds_liftSubst]; exact hd)
      rw [hsnoc] at this
      exact this (hall _)
  | iSup φs ih =>
    simp only [substBounds_iSup, realize_iSup]
    refine ⟨fun h => ?_, fun h ⟨k, hk⟩ => (ih k c).2 (hS.not_iSup _ h k) hk⟩
    obtain ⟨k, hk⟩ := hS.iSup _ h
    exact ⟨k, (ih k c).1 hk⟩
  | iInf φs ih =>
    simp only [substBounds_iInf, realize_iInf]
    refine ⟨fun h k => (ih k c).1 (hS.iInf _ h k), fun h hall => ?_⟩
    obtain ⟨k, hk⟩ := hS.not_iInf _ h
    exact (ih k c).2 hk (hall k)

/-- **Truth lemma, positive half**: if a Henkin-complete set `S` containing neither `⊥` nor a
sentence together with its negation contains the instance of `φ` at the Henkin constants `c`,
then `φ` holds of the interpretations of `c` in the term model. -/
theorem truth_pos (hbot : (⊥ : L[[ℕ]].Sentenceω) ∉ S) (hcon : ∀ φ ∈ S, φ.not ∉ S) {n : ℕ}
    {φ : L[[ℕ]].BoundedFormulaω Empty n} {c : Fin n → ℕ}
    (h : substBounds (fun i => (L.con (c i)).term) φ ∈ S) :
    φ.Realize Empty.elim fun i => (L.con (c i) : hS.TermModel) :=
  (hS.truth hbot hcon φ c).1 h

/-- **Truth lemma, negative half**: if a Henkin-complete set `S` containing neither `⊥` nor a
sentence together with its negation contains the negated instance of `φ` at the Henkin constants
`c`, then `φ` fails of the interpretations of `c` in the term model. -/
theorem truth_neg (hbot : (⊥ : L[[ℕ]].Sentenceω) ∉ S) (hcon : ∀ φ ∈ S, φ.not ∉ S) {n : ℕ}
    {φ : L[[ℕ]].BoundedFormulaω Empty n} {c : Fin n → ℕ}
    (h : (substBounds (fun i => (L.con (c i)).term) φ).not ∈ S) :
    ¬φ.Realize Empty.elim fun i => (L.con (c i) : hS.TermModel) :=
  (hS.truth hbot hcon φ c).2 h

/-- **The term model is a model**: a Henkin-complete set containing neither `⊥` nor a sentence
together with its negation is satisfied by its term model. -/
theorem model (hbot : (⊥ : L[[ℕ]].Sentenceω) ∉ S) (hcon : ∀ φ ∈ S, φ.not ∉ S) :
    S.Model hS.TermModel := by
  refine Theoryω.model_iff.2 fun φ hφ => ?_
  -- an instance at the empty tuple of constants is the sentence itself
  have hφ' : substBounds (fun i => (L.con (Fin.elim0 i : ℕ)).term) φ ∈ S := by
    rwa [Subsingleton.elim (fun i => (L.con (Fin.elim0 i : ℕ)).term) fun i => var (Sum.inr i),
      substBounds_var]
  have := hS.truth_pos hbot hcon hφ'
  rw [SentenceInf.realize_def, FormulaInf.realize_def]
  convert this

end HenkinComplete

end ConsistencyProperty

end Language

end FirstOrder
