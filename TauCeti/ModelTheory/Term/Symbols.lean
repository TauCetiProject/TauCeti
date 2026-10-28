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
unchanged by relabelling variables, and determines which interpretations a term can observe.
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
