/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Lemmas
import TauCeti.ModelTheory.Syntax

/-!
# Abstracting constants out of terms

A term of the constant expansion `L[[γ]]` mentions only finitely many of the new constants, so it
is obtained from a term of `L` by substituting a tuple of constants for its bound positions. In an
expansion of an `L`-structure, such a term evaluates to the value of the term of `L` at the
values of the constants.

## Main results

* `FirstOrder.Language.Term.exists_finite_forall_onTerm_subst_eq`: the constants of a term of
  `L[[γ]]` lie in a finite set, and the term abstracts over every tuple listing that set.
* `FirstOrder.Language.Term.exists_onTerm_subst_eq`: every term of `L[[γ]]` without bound
  positions is obtained from a term of `L` by substituting constants for its bound positions.
* `FirstOrder.Language.Term.realize_onTerm_subst_con`: the value of such a term in an expansion.
* `FirstOrder.Language.Term.exists_eq_con_of_isRelational`: over a relational language, a closed
  term of `L[[γ]]` is a constant.
* `FirstOrder.Language.coe_con_constantsOn_structure`: in the expansion interpreting each
  constant `c` as `e c`, the constant `L.con c` is interpreted as `e c`.
-/

public section

universe u v w uα

namespace FirstOrder.Language

variable {L : Language.{u, v}} {α : Type uα} {γ : Type w}

/-- In the expansion of an `L`-structure interpreting each constant `c` of `constantsOn γ` as
`e c`, the constant `L.con c` of `L[[γ]]` is interpreted as `e c`. -/
@[simp]
theorem coe_con_constantsOn_structure {M : Type*} [L.Structure M] (e : γ → M) (c : γ) :
    letI := constantsOn.structure e; (L.con c : M) = e c :=
  -- `L.con c` is the constant symbol `c` of `constantsOn γ`, and `constantsOn.structure e`
  -- interprets it as `e c`.
  rfl

namespace Term

/-- Every term of `L[[γ]]` whose variables are free variables abstracts to a term of `L`: there is
a finite set of constants such that, at every tuple listing them, the term is obtained from a
term of `L` by substituting the constants of the tuple for its bound positions. -/
theorem exists_finite_forall_onTerm_subst_eq (t : L[[γ]].Term (α ⊕ Fin 0)) :
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
      -- The two sides differ only in the ascription of `Sum.inl f` to `L.sum (constantsOn γ)`,
      -- which is `L[[γ]]` by definition.
      rfl
    · cases l with
      | zero =>
        refine ⟨{k}, Set.finite_singleton k, fun c hc => ?_⟩
        obtain ⟨i, hi⟩ := hc rfl
        refine ⟨var (Sum.inr i), ?_⟩
        simp only [LHom.onTerm, Term.subst, Sum.elim_inr, hi, Constants.term, Language.con]
        -- Unfolded, `L.con k` is the function symbol `Sum.inr k` of `L.sum (constantsOn γ)`, which
        -- is `L[[γ]]` by definition, so the two sides differ only in their empty argument tuples.
        congr
        exact funext fun i => i.elim0
      | succ l => exact isEmptyElim k

/-- **Terms abstract their constants**: a term of `L[[γ]]` whose variables are free variables is
obtained from a term of `L` by substituting a tuple of constants for its bound positions. -/
theorem exists_onTerm_subst_eq (t : L[[γ]].Term (α ⊕ Fin 0)) :
    ∃ (n : ℕ) (s : L.Term (α ⊕ Fin n)) (c : Fin n → γ), ((L.lhomWithConstants γ).onTerm s).subst
      (Sum.elim (var ∘ Sum.inl) fun i => (L.con (c i)).term) = t := by
  obtain ⟨S, hS, hs⟩ := exists_finite_forall_onTerm_subst_eq t
  obtain ⟨n, c, hc⟩ := Set.Finite.fin_embedding hS
  obtain ⟨s, hs⟩ := hs c hc.ge
  exact ⟨n, s, c, hs⟩

/-- Over a relational language, a term of `L[[γ]]` without variables is one of the constants. -/
theorem exists_eq_con_of_isRelational [L.IsRelational] [IsEmpty α]
    (t : L[[γ]].Term (α ⊕ Fin 0)) : ∃ c, t = (L.con c).term := by
  obtain ⟨n, s, c, rfl⟩ := exists_onTerm_subst_eq t
  obtain ⟨i, rfl⟩ := s.exists_eq_var_inr_of_isRelational
  exact ⟨c i, by simp [LHom.onTerm]⟩

/-- The value of a term of `L` with constants substituted for its bound positions, in an expansion
of an `L`-structure, is its value at the values of the constants. -/
theorem realize_onTerm_subst_con {M : Type*} [L.Structure M]
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

end Term

end FirstOrder.Language
