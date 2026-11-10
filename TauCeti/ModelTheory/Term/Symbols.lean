/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Function symbols occurring in a term

`Term.functionsIn` records function symbols together with their arities. The set is finite,
unchanged by relabelling variables, bounded under substitution by the symbols of the substituted
terms, mapped to its image under a language homomorphism (with
`LHom.exists_eq_onTerm_of_functionsIn_subset` pulling back terms whose occurring symbols lie in the
image of a given set), and determines which interpretations a term can observe.
These facts supply the term cases of symbol locality for infinitary formulas.
-/

public section

universe u v uα uβ u' v' w

namespace FirstOrder.Language.Term

variable {L : FirstOrder.Language.{u, v}} {α : Type uα} {β : Type uβ}

/-- The function symbols occurring in a term, tagged by arity. -/
def functionsIn : L.Term α → Set (Σ n, L.Functions n)
  | .var _ => ∅
  | .func f ts => {⟨_, f⟩} ∪ ⋃ i, functionsIn (ts i)

@[simp]
theorem functionsIn_var (a : α) : (var a : L.Term α).functionsIn = ∅ := (rfl)

@[simp]
theorem functionsIn_func {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term α) :
    (func f ts).functionsIn = {⟨n, f⟩} ∪ ⋃ i, (ts i).functionsIn := (rfl)

/-- Every term mentions only finitely many function symbols, even over an arbitrary language. -/
theorem functionsIn_finite (t : L.Term α) : t.functionsIn.Finite := by
  induction t with
  | var => simp
  | func f ts ih =>
    exact (Set.finite_singleton _).union (Set.finite_iUnion ih)

/-- Relabelling variables does not change the function symbols of a term. -/
@[simp]
theorem functionsIn_relabel (t : L.Term α) (g : α → β) :
    (t.relabel g).functionsIn = t.functionsIn := by
  induction t with
  | var => simp
  | func f ts ih => simp [ih]

/-- Substitution keeps every function symbol of the original term. -/
theorem functionsIn_subset_functionsIn_subst (t : L.Term α) (f : α → L.Term β) :
    t.functionsIn ⊆ (t.subst f).functionsIn := by
  induction t with
  | var => simp
  | func F ts ih =>
    simp only [functionsIn_func, subst]
    exact Set.union_subset_union_right _ (Set.iUnion_mono ih)

/-- Substitution adds at most the function symbols of the substituted terms. -/
theorem functionsIn_subst_subset (t : L.Term α) (f : α → L.Term β) :
    (t.subst f).functionsIn ⊆ t.functionsIn ∪ ⋃ a, (f a).functionsIn := by
  induction t with
  | var a =>
    exact Set.subset_union_of_subset_right (Set.subset_iUnion (fun a => (f a).functionsIn) a) _
  | func F ts ih =>
    simp only [functionsIn_func, subst]
    refine Set.union_subset (fun x hx => Or.inl (Or.inl hx)) (Set.iUnion_subset fun i => ?_)
    refine (ih i).trans (Set.union_subset_union_left _ ?_)
    exact Set.subset_union_of_subset_right (Set.subset_iUnion (fun i => (ts i).functionsIn) i) _

/-- Two substitutions either give a term the same image, or they differ at a variable whose
substituted term has all its function symbols in the image of the term. -/
theorem subst_eq_or_exists_functionsIn_subset (t : L.Term α) (f g : α → L.Term β) :
    t.subst f = t.subst g ∨ ∃ a, f a ≠ g a ∧ (f a).functionsIn ⊆ (t.subst f).functionsIn := by
  induction t with
  | var a => exact (em (f a = g a)).imp id fun h => ⟨a, h, subset_rfl⟩
  | func F ts ih =>
    by_cases h : ∀ i, (ts i).subst f = (ts i).subst g
    · exact .inl (by simp only [subst, h])
    · obtain ⟨i, hi⟩ := not_forall.1 h
      obtain ⟨a, hfa, ha⟩ := (ih i).resolve_left hi
      refine .inr ⟨a, hfa, ha.trans ?_⟩
      simp only [subst, functionsIn_func]
      exact (Set.subset_iUnion (fun i => ((ts i).subst f).functionsIn) i).trans
        Set.subset_union_right

/-- A language map sends the occurring function symbols to their images. -/
@[simp]
theorem functionsIn_onTerm (t : L.Term α) {L' : FirstOrder.Language.{u', v'}} (g : L →ᴸ L') :
    (g.onTerm t).functionsIn = (fun f => ⟨f.1, g.onFunction f.2⟩) '' t.functionsIn := by
  induction t with
  | var => simp [LHom.onTerm]
  | func f ts ih => simp [LHom.onTerm, ih, Set.image_iUnion]

/-- Interpretations agreeing on the occurring symbols give the same value to a term. -/
theorem realize_congr_of_agreeOn {M : Type w} (t : L.Term α) (S S' : L.Structure M)
    (h : ∀ {n} (f : L.Functions n), ⟨n, f⟩ ∈ t.functionsIn →
      ∀ xs, @Structure.funMap L M S n f xs = @Structure.funMap L M S' n f xs)
    (v : α → M) : @realize L M S α v t = @realize L M S' α v t := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [realize_func]
    rw [h f (by simp)]
    congr 1
    funext i
    exact ih i (fun g hg => h g (by
      simp only [functionsIn_func]
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, hg⟩)))

end FirstOrder.Language.Term

namespace FirstOrder.Language.LHom

variable {L : FirstOrder.Language.{u, v}} {L' : FirstOrder.Language.{u', v'}} {α : Type uα}

/-- A term of `L'` whose occurring function symbols lie in the image of a set `F` under a language
homomorphism `g : L →ᴸ L'` is the image under `g` of a term of `L` whose occurring function symbols
lie in `F`. No injectivity of `g` is needed. -/
theorem exists_eq_onTerm_of_functionsIn_subset (g : L →ᴸ L') {F : Set (Σ k, L.Functions k)}
    (t : L'.Term α)
    (hF : t.functionsIn ⊆ (fun f : Σ k, L.Functions k => ⟨f.1, g.onFunction f.2⟩) '' F) :
    ∃ t₀ : L.Term α, g.onTerm t₀ = t ∧ t₀.functionsIn ⊆ F := by
  induction t with
  | var b => exact ⟨.var b, rfl, by simp⟩
  | @func k f ts ih =>
    rw [Term.functionsIn_func] at hF
    obtain ⟨⟨k₀, f₀⟩, hf₀F, hfk⟩ := hF (Or.inl rfl)
    cases hfk
    have hts : ∀ i, ∃ t₀ : L.Term α, g.onTerm t₀ = ts i ∧ t₀.functionsIn ⊆ F := fun i =>
      ih i ((Set.subset_union_of_subset_right
        (Set.subset_iUnion (fun j => (ts j).functionsIn) i) _).trans hF)
    choose ts₀ hts₀ hts₀F using hts
    refine ⟨.func f₀ ts₀, by simp [LHom.onTerm, hts₀], ?_⟩
    rw [Term.functionsIn_func]
    exact Set.union_subset (Set.singleton_subset_iff.mpr hf₀F) (Set.iUnion_subset hts₀F)

end FirstOrder.Language.LHom
