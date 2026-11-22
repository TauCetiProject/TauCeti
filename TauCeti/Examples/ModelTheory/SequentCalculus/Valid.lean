/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.SequentCalculus.Valid

/-!
# Examples: valid formulas, disjunctions and tautologies

* For a nullary relation atom `p`, the disjunction of `p` and `¬p` is a tautology, hence valid.
* For a term `t`, the equation `t = t` is valid, while the one-element disjunction of `t = t` is
  not a tautology: a truth assignment may make the atom `t = t` false. So the equivalence of
  validity and tautology for quantifier-free formulas needs them to be equality-free.
* The empty disjunction is `⊥`, which is not valid.
-/

public section

universe u v

namespace TauCeti

open FirstOrder FirstOrder.Language BoundedFormula

variable {L : Language.{u, v}}

-- The excluded middle for a nullary relation atom is a tautology, and so is valid.
example (p : L.Relations 0) :
    (disjunction [p.formula Fin.elim0, (p.formula Fin.elim0).not] : L.Formula ℕ).IsTautology ∧
      (disjunction [p.formula Fin.elim0, (p.formula Fin.elim0).not] : L.Formula ℕ).IsValid := by
  have h : (disjunction [p.formula Fin.elim0, (p.formula Fin.elim0).not] :
      L.Formula ℕ).IsTautology := isTautology_iff.2 fun τ => by
    simp only [propRealize_disjunction, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left, propRealize_not]
    exact em _
  exact ⟨h, h.isValid⟩

-- An equation `t = t` is valid but not a tautology, even as a one-element disjunction.
example (t : L.Term ℕ) :
    (t.equal t).IsValid ∧ ¬(disjunction [t.equal t] : L.Formula ℕ).IsTautology := by
  refine ⟨isValid_iff.2 fun _ _ _ => Formula.realize_equal.2 rfl, fun h => ?_⟩
  -- The truth assignment making every formula false falsifies the atom `t = t`.
  simpa [Term.equal] using isTautology_iff.1 h fun _ _ => False

-- The empty disjunction is `⊥`, which is not valid.
example : disjunction ([] : List (L.Formula ℕ)) = ⊥ ∧
    ¬(disjunction ([] : List (L.Formula ℕ))).IsValid :=
  ⟨disjunction_nil, disjunction_nil (L := L) ▸ not_isValid_bot⟩

end TauCeti
