/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.FormationClosed
public import TauCeti.ModelTheory.Infinitary.SubstBounds
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Instances of infinitary formulas at constants

For an infinitary formula `φ` of `L` with `n` bound positions and a tuple `c : Fin n → γ`, the
**instance** `φ.instConstants c` is the formula of the constant expansion `L[[γ]]` obtained by
substituting the constant `L.con (c i)` for the bound position `i`. In an expansion of an
`L`-structure it holds exactly when `φ` holds at the values of the constants
(`BoundedFormulaInf.realize_instConstants`).

The instances of the members of a fragment `A` at tuples of constants form the set of sentences
`A.instances γ`. Every component of an instance is again an instance: the components of an
implication, of a countable conjunction or disjunction, and the instantiation of a universal
sentence at a constant. When `A` is formation-closed, the negation of an instance is an
instance, and every atomic sentence of `L[[γ]]` is an instance, since the finitely many constants
of an atomic sentence can be abstracted into bound positions.

These are the sentences a consistency property built from satisfiable sets of sentences works
with: a sentence is true at a tuple of constants exactly when the formula it instantiates holds at
their values, so changing the interpretation of a constant outside the tuple does not change its
truth value.

## Main definitions

* `FirstOrder.Language.BoundedFormulaInf.instConstants`: the instance of a formula at a tuple of
  constants.
* `FirstOrder.Language.Fragment.instances`: the instances of the members of a fragment.

## Main results

* `FirstOrder.Language.BoundedFormulaInf.realize_instConstants`: an instance holds exactly when
  the formula holds at the values of the constants.
* `FirstOrder.Language.BoundedFormulaInf.instConstants_eq_imp_iff` and its companions: the
  instances of the components of a formula are the components of its instance.
* `FirstOrder.Language.Term.exists_onTerm_subst_eq`: every term of `L[[γ]]` without bound
  positions is obtained from a term of `L` by substituting constants for its bound positions.
* `FirstOrder.Language.BoundedFormulaInf.IsAtomic.exists_instConstants_eq`: every atomic formula
  of `L[[γ]]` without bound positions is the instance of an atomic formula of `L`.
* `FirstOrder.Language.Fragment.FormationClosed.mem_instances_of_isAtomic`: every atomic sentence
  of `L[[γ]]` is an instance of a member of a formation-closed fragment.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, §4.1.
-/

public section

universe u v w uι uα

namespace FirstOrder

namespace Language

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {γ : Type w}

open Term

/-- The **instance** of `φ` at the tuple `c` of constants: the formula of `L[[γ]]` obtained by
substituting the constant `L.con (c i)` for the bound position `i` of `φ`. -/
def instConstants {n : ℕ} (φ : L.BoundedFormulaInf ι α n) (c : Fin n → γ) :
    L[[γ]].FormulaInf ι α :=
  substBounds (fun i => (L.con (c i)).term) ((L.lhomWithConstants γ).onBoundedFormulaInf φ)

/-- Unfolding lemma for `BoundedFormulaInf.instConstants`. -/
theorem instConstants_def {n : ℕ} (φ : L.BoundedFormulaInf ι α n) (c : Fin n → γ) :
    φ.instConstants c =
      substBounds (fun i => (L.con (c i)).term) ((L.lhomWithConstants γ).onBoundedFormulaInf φ) :=
  (rfl)

section ConstructorEqs

variable {n : ℕ} (c : Fin n → γ)

/-- The instance of `⊥` is `⊥`. -/
@[simp]
theorem instConstants_falsum : (falsum : L.BoundedFormulaInf ι α n).instConstants c = falsum := by
  simp [instConstants_def]

/-- The instance of `⊥` is `⊥`. -/
@[simp]
theorem instConstants_bot : (⊥ : L.BoundedFormulaInf ι α n).instConstants c = ⊥ := by
  simp [instConstants_def]

/-- Instances commute with implication. -/
@[simp]
theorem instConstants_imp (φ ψ : L.BoundedFormulaInf ι α n) :
    (φ.imp ψ).instConstants c = (φ.instConstants c).imp (ψ.instConstants c) := by
  simp [instConstants_def]

/-- Instances commute with negation. -/
@[simp]
theorem instConstants_not (φ : L.BoundedFormulaInf ι α n) :
    φ.not.instConstants c = (φ.instConstants c).not := by
  simp [instConstants_def]

/-- Instances commute with disjunctions over the carrier. -/
@[simp]
theorem instConstants_iSup (φs : ι → L.BoundedFormulaInf ι α n) :
    (iSup φs).instConstants c = iSup fun i => (φs i).instConstants c := by
  simp [instConstants_def]

/-- Instances commute with conjunctions over the carrier. -/
@[simp]
theorem instConstants_iInf (φs : ι → L.BoundedFormulaInf ι α n) :
    (iInf φs).instConstants c = iInf fun i => (φs i).instConstants c := by
  simp [instConstants_def]

/-- The instance of an equation substitutes the constants into the images of both sides. -/
@[simp]
theorem instConstants_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).instConstants c =
      equal (((L.lhomWithConstants γ).onTerm t₁).subst
          (Sum.elim (var ∘ Sum.inl) fun i => (L.con (c i)).term))
        (((L.lhomWithConstants γ).onTerm t₂).subst
          (Sum.elim (var ∘ Sum.inl) fun i => (L.con (c i)).term)) := by
  rw [instConstants_def, LHom.onBoundedFormulaInf_equal, substBounds_equal]

/-- The instance of a relational atom substitutes the constants into the images of its
terms. -/
@[simp]
theorem instConstants_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaInf ι α n).instConstants c =
      rel (Sum.inl R) fun i => ((L.lhomWithConstants γ).onTerm (ts i)).subst
        (Sum.elim (var ∘ Sum.inl) fun i => (L.con (c i)).term) := by
  rw [instConstants_def, LHom.onBoundedFormulaInf_rel, substBounds_rel,
    lhomWithConstants_onRelation]
  -- The two sides differ only in the ascription of `Sum.inl R` to `L.sum (constantsOn γ)`, which
  -- is `L[[γ]]` by definition.
  rfl

end ConstructorEqs

/-- An instance at the empty tuple is the image of the formula in `L[[γ]]`. -/
@[simp]
theorem instConstants_zero (φ : L.BoundedFormulaInf ι α 0) (c : Fin 0 → γ) :
    φ.instConstants c = (L.lhomWithConstants γ).onBoundedFormulaInf φ := by
  have hc : (fun i => (L.con (c i)).term : Fin 0 → L[[γ]].Term (α ⊕ Fin 0)) =
      fun i => var (Sum.inr i) :=
    funext fun i => i.elim0
  rw [instConstants_def, hc, substBounds_var]

/-- **An instance holds at the values of its constants**: in an expansion of an `L`-structure to
`L[[γ]]`, the instance of `φ` at `c` is realized exactly when `φ` is realized at the values of the
constants `L.con (c i)`. -/
@[simp]
theorem realize_instConstants {M : Type*} [L.Structure M] [L[[γ]].Structure M]
    [(L.lhomWithConstants γ).IsExpansionOn M] {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (c : Fin n → γ) (v : α → M) :
    (φ.instConstants c).Realize v ↔ φ.Realize v fun i => (L.con (c i) : M) := by
  simp only [instConstants_def, FormulaInf.realize_def, realize_substBounds, Term.realize_constants,
    LHom.realize_onBoundedFormulaInf]

/-! ### Inversion -/

section Inversion

variable {n : ℕ} {φ : L.BoundedFormulaInf ι α n} {c : Fin n → γ}

/-- An instance is `⊥` exactly when the formula is. -/
@[simp]
theorem instConstants_eq_falsum_iff : φ.instConstants c = falsum ↔ φ = falsum := by
  refine ⟨fun h => ?_, by rintro rfl; simp⟩
  cases φ <;> simp at h ⊢
  simp [instConstants_def] at h

/-- An instance is an implication exactly when the formula is an implication whose sides have
the two sides of the instance as their instances. -/
theorem instConstants_eq_imp_iff {ψ₁ ψ₂ : L[[γ]].FormulaInf ι α} :
    φ.instConstants c = ψ₁.imp ψ₂ ↔
      ∃ φ₁ φ₂ : L.BoundedFormulaInf ι α n,
        φ = φ₁.imp φ₂ ∧ φ₁.instConstants c = ψ₁ ∧ φ₂.instConstants c = ψ₂ := by
  refine ⟨fun h => ?_, by rintro ⟨φ₁, φ₂, rfl, rfl, rfl⟩; simp⟩
  cases φ with
  | imp φ₁ φ₂ =>
    simp only [instConstants_imp, imp.injEq] at h
    exact ⟨φ₁, φ₂, rfl, h⟩
  | all => simp [instConstants_def] at h
  | _ => simp at h

/-- An instance is a countable disjunction exactly when the formula is a countable disjunction
whose disjuncts have the disjuncts of the instance as their instances. -/
theorem instConstants_eq_iSup_iff {ψs : ι → L[[γ]].FormulaInf ι α} :
    φ.instConstants c = iSup ψs ↔ ∃ φs, φ = iSup φs ∧ ∀ i, (φs i).instConstants c = ψs i := by
  refine ⟨fun h => ?_, by rintro ⟨φs, rfl, hs⟩; simp [hs]⟩
  cases φ with
  | iSup φs =>
    simp only [instConstants_iSup, iSup.injEq] at h
    exact ⟨φs, rfl, fun i => congrFun h i⟩
  | all => simp [instConstants_def] at h
  | _ => simp at h

/-- An instance is a countable conjunction exactly when the formula is a countable conjunction
whose conjuncts have the conjuncts of the instance as their instances. -/
theorem instConstants_eq_iInf_iff {ψs : ι → L[[γ]].FormulaInf ι α} :
    φ.instConstants c = iInf ψs ↔ ∃ φs, φ = iInf φs ∧ ∀ i, (φs i).instConstants c = ψs i := by
  refine ⟨fun h => ?_, by rintro ⟨φs, rfl, hs⟩; simp [hs]⟩
  cases φ with
  | iInf φs =>
    simp only [instConstants_iInf, iInf.injEq] at h
    exact ⟨φs, rfl, fun i => congrFun h i⟩
  | all => simp [instConstants_def] at h
  | _ => simp at h

/-- If an instance is a universal formula `∀ ψ`, the formula is a universal formula `∀ φ'`, and
instantiating `ψ` at a constant `d` gives the instance of `φ'` at the extended tuple. -/
theorem exists_eq_all_of_instConstants_eq_all {ψ : L[[γ]].BoundedFormulaInf ι α 1}
    (h : φ.instConstants c = ψ.all) :
    ∃ φ' : L.BoundedFormulaInf ι α (n + 1), φ = φ'.all ∧
      ∀ d : γ, ψ.inst (L.con d).term = φ'.instConstants (Fin.snoc c d) := by
  cases φ with
  | all φ' =>
    simp only [instConstants_def, LHom.onBoundedFormulaInf_all, substBounds_all, all.injEq] at h
    refine ⟨φ', rfl, fun d => ?_⟩
    rw [← h, inst_substBounds_liftSubst, instConstants_def]
    congr 1
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  | _ => simp at h

end Inversion

/-! ### Atomic formulas over the constant expansion -/

/-- Every term of `L[[γ]]` whose variables are free variables abstracts to a term of `L`: there is
a finite set of constants such that, at every tuple listing them, the term is obtained from a
term of `L` by substituting the constants of the tuple for its bound positions. -/
private theorem exists_finite_subst_con (t : L[[γ]].Term (α ⊕ Fin 0)) :
    ∃ S : Set γ, S.Finite ∧ ∀ {n : ℕ} (c : Fin n → γ), S ⊆ Set.range c →
      ∃ s : L.Term (α ⊕ Fin n), ((L.lhomWithConstants γ).onTerm s).subst
        (Sum.elim (var ∘ Sum.inl) fun i => (L.con (c i)).term) = t := by
  induction t with
  | var a =>
    rcases a with a | i
    · exact ⟨∅, Set.finite_empty, fun _ _ => ⟨var (Sum.inl a), rfl⟩⟩
    · exact i.elim0
  | @func l f ts ih =>
    rcases f with f | k
    · choose S hS hs using ih
      refine ⟨⋃ i, S i, Set.finite_iUnion hS, fun c hc => ?_⟩
      choose s hs using fun i => hs i c ((Set.subset_iUnion S i).trans hc)
      refine ⟨func f s, ?_⟩
      simp only [LHom.onTerm, Term.subst, lhomWithConstants_onFunction, hs]
      rfl
    · cases l with
      | zero =>
        refine ⟨{k}, Set.finite_singleton k, fun c hc => ?_⟩
        obtain ⟨i, hi⟩ := hc rfl
        refine ⟨var (Sum.inr i), ?_⟩
        simp only [LHom.onTerm, Term.subst, Sum.elim_inr, hi, Constants.term, Language.con]
        congr
        exact funext fun i => i.elim0
      | succ l => exact isEmptyElim k

/-- **Terms abstract their constants**: a term of `L[[γ]]` whose variables are free variables is
obtained from a term of `L` by substituting a tuple of constants for its bound positions. -/
theorem _root_.FirstOrder.Language.Term.exists_onTerm_subst_eq (t : L[[γ]].Term (α ⊕ Fin 0)) :
    ∃ (n : ℕ) (s : L.Term (α ⊕ Fin n)) (c : Fin n → γ), ((L.lhomWithConstants γ).onTerm s).subst
      (Sum.elim (var ∘ Sum.inl) fun i => (L.con (c i)).term) = t := by
  obtain ⟨S, hS, hs⟩ := exists_finite_subst_con t
  obtain ⟨n, c, hc⟩ := Set.Finite.fin_embedding hS
  obtain ⟨s, hs⟩ := hs c hc.ge
  exact ⟨n, s, c, hs⟩

/-- The value of a term of `L` with constants substituted for its bound positions, in an expansion
of an `L`-structure, is its value at the values of the constants. -/
theorem _root_.FirstOrder.Language.Term.realize_onTerm_subst_con {M : Type*} [L.Structure M]
    [L[[γ]].Structure M] [(L.lhomWithConstants γ).IsExpansionOn M] {n : ℕ}
    (s : L.Term (α ⊕ Fin n)) (c : Fin n → γ) (v : α → M) (xs : Fin 0 → M) :
    (((L.lhomWithConstants γ).onTerm s).subst
        (Sum.elim (var ∘ Sum.inl) fun i => (L.con (c i)).term)).realize (Sum.elim v xs) =
      s.realize (Sum.elim v fun i => (L.con (c i) : M)) := by
  rw [Term.realize_subst, LHom.realize_onTerm]
  congr 1
  funext x
  rcases x with a | i
  · rfl
  · exact Term.realize_constants

/-- **Atomic formulas abstract their constants**: an atomic formula of `L[[γ]]` without bound
positions is the instance of an atomic formula of `L` at a tuple of constants. -/
theorem IsAtomic.exists_instConstants_eq {φ : L[[γ]].FormulaInf ι α} (h : φ.IsAtomic) :
    ∃ (n : ℕ) (ψ : L.BoundedFormulaInf ι α n) (c : Fin n → γ),
      ψ.IsAtomic ∧ ψ.instConstants c = φ := by
  cases h with
  | equal t₁ t₂ =>
    obtain ⟨S₁, hS₁, hs₁⟩ := exists_finite_subst_con t₁
    obtain ⟨S₂, hS₂, hs₂⟩ := exists_finite_subst_con t₂
    obtain ⟨n, c, hc⟩ := Set.Finite.fin_embedding (hS₁.union hS₂)
    obtain ⟨s₁, rfl⟩ := hs₁ c (hc ▸ Set.subset_union_left)
    obtain ⟨s₂, rfl⟩ := hs₂ c (hc ▸ Set.subset_union_right)
    exact ⟨n, BoundedFormulaInf.equal s₁ s₂, c, .equal _ _, by simp⟩
  | @rel l R ts =>
    rcases R with R | R
    · choose S hS hs using fun i => exists_finite_subst_con (ts i)
      obtain ⟨n, c, hc⟩ := Set.Finite.fin_embedding (Set.finite_iUnion hS)
      choose s hs using fun i => hs i c (hc ▸ Set.subset_iUnion S i)
      refine ⟨n, BoundedFormulaInf.rel R s, c, .rel _ _, ?_⟩
      simp only [instConstants_rel, hs]
    · exact isEmptyElim R

end BoundedFormulaInf

namespace Fragment

open BoundedFormulaInf

variable {L : Language.{u, v}} (A : Fragment L) (γ : Type w)

/-- The **instances** of a fragment `A` at constants indexed by `γ`: the sentences of `L[[γ]]`
that are the instance of a member of `A` at a tuple of constants. -/
def instances : Set L[[γ]].Sentenceω :=
  {φ | ∃ (n : ℕ) (ψ : L.BoundedFormulaω Empty n) (c : Fin n → γ),
    (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧ ψ.instConstants c = φ}

variable {A γ}

/-- Membership in the instances of a fragment. -/
theorem mem_instances {φ : L[[γ]].Sentenceω} :
    φ ∈ A.instances γ ↔ ∃ (n : ℕ) (ψ : L.BoundedFormulaω Empty n) (c : Fin n → γ),
      (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧ ψ.instConstants c = φ :=
  Iff.rfl

/-- The instance of a member at a tuple of constants is an instance. -/
theorem instConstants_mem_instances {n : ℕ} {ψ : L.BoundedFormulaω Empty n}
    (h : (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) (c : Fin n → γ) :
    ψ.instConstants c ∈ A.instances γ :=
  ⟨n, ψ, c, h, rfl⟩

/-- The image in `L[[γ]]` of a member sentence is an instance. -/
theorem onBoundedFormulaInf_mem_instances {φ : L.Sentenceω}
    (h : (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    (L.lhomWithConstants γ).onBoundedFormulaInf φ ∈ A.instances γ :=
  ⟨0, φ, Fin.elim0, h, instConstants_zero φ _⟩

/-- The antecedent of an instance implication is an instance. -/
theorem imp_left_mem_instances {φ ψ : L[[γ]].Sentenceω} (h : φ.imp ψ ∈ A.instances γ) :
    φ ∈ A.instances γ := by
  obtain ⟨n, χ, c, hχ, hc⟩ := h
  obtain ⟨χ₁, χ₂, rfl, rfl, -⟩ := instConstants_eq_imp_iff.1 hc
  exact instConstants_mem_instances (A.imp_left_mem hχ) c

/-- The consequent of an instance implication is an instance. -/
theorem imp_right_mem_instances {φ ψ : L[[γ]].Sentenceω} (h : φ.imp ψ ∈ A.instances γ) :
    ψ ∈ A.instances γ := by
  obtain ⟨n, χ, c, hχ, hc⟩ := h
  obtain ⟨χ₁, χ₂, rfl, -, rfl⟩ := instConstants_eq_imp_iff.1 hc
  exact instConstants_mem_instances (A.imp_right_mem hχ) c

/-- Every conjunct of an instance countable conjunction is an instance. -/
theorem iInf_mem_instances {φs : ℕ → L[[γ]].Sentenceω} (h : iInf φs ∈ A.instances γ) (k : ℕ) :
    φs k ∈ A.instances γ := by
  obtain ⟨n, χ, c, hχ, hc⟩ := h
  obtain ⟨χs, rfl, hs⟩ := instConstants_eq_iInf_iff.1 hc
  exact hs k ▸ instConstants_mem_instances (A.iInf_mem hχ k) c

/-- Every disjunct of an instance countable disjunction is an instance. -/
theorem iSup_mem_instances {φs : ℕ → L[[γ]].Sentenceω} (h : iSup φs ∈ A.instances γ) (k : ℕ) :
    φs k ∈ A.instances γ := by
  obtain ⟨n, χ, c, hχ, hc⟩ := h
  obtain ⟨χs, rfl, hs⟩ := instConstants_eq_iSup_iff.1 hc
  exact hs k ▸ instConstants_mem_instances (A.iSup_mem hχ k) c

/-- Instantiating an instance universal sentence at a constant gives an instance. -/
theorem inst_mem_instances {φ : L[[γ]].BoundedFormulaω Empty 1} (h : φ.all ∈ A.instances γ)
    (d : γ) : φ.inst (L.con d).term ∈ A.instances γ := by
  obtain ⟨n, χ, c, hχ, hc⟩ := h
  obtain ⟨χ', rfl, hd⟩ := exists_eq_all_of_instConstants_eq_all hc
  exact hd d ▸ instConstants_mem_instances (A.all_mem hχ) _

namespace FormationClosed

variable (hA : A.FormationClosed)
include hA

/-- Over a formation-closed fragment, a negation is an instance exactly when the negated sentence
is. -/
@[simp]
theorem not_mem_instances_iff {φ : L[[γ]].Sentenceω} :
    φ.not ∈ A.instances γ ↔ φ ∈ A.instances γ := by
  refine ⟨imp_left_mem_instances, fun ⟨n, χ, c, hχ, hc⟩ => ?_⟩
  exact hc ▸ instConstants_not c χ ▸ instConstants_mem_instances (hA.not_mem_iff.2 hχ) c

/-- **Atomic sentences are instances**: over a formation-closed fragment, every atomic sentence of
`L[[γ]]` is an instance. -/
theorem mem_instances_of_isAtomic {φ : L[[γ]].Sentenceω} (h : φ.IsAtomic) :
    φ ∈ A.instances γ := by
  obtain ⟨n, ψ, c, hψ, rfl⟩ := h.exists_instConstants_eq
  exact instConstants_mem_instances (hA.atomic_mem hψ) c

end FormationClosed

end Fragment

end Language

end FirstOrder
