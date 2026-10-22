/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Scott.AtomicDiagram
public import TauCeti.ModelTheory.BackAndForth.Equivalence
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Canonical Scott formulas

For a tuple `a` in a countable relational structure, `scottFormula a α` describes its
back-and-forth class at every countable ordinal `α`. The realizing structure can have arbitrary
cardinality and lie in an independent universe. The tuple occupies bound-variable slots.

At a successor the formula retains the previous approximation and requires matching
one-element extensions in both directions. At a countable limit it conjoins all earlier
approximations. The limit clause at uncountable ordinals is assigned the true formula;
the characteristic theorem is asserted only below the first uncountable ordinal.
These formulas are the ingredients for sentences characterizing countable structures.

The construction follows Dana Scott, *Logic with denumerably long formulas and finite strings
of quantifiers* (1965), and Cameron Freer's `cameronfreer/infinitary-logic`,
`InfinitaryLogic/Scott/Formula.lean` at checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`. Here tuples occupy bound positions rather than
free variables, and the ordinal universe is independent of the structure universes.
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder FirstOrder.Language Fin Ordinal
open scoped Ordinal

variable {L : Language.{u, v}} [Countable (Σ k, L.Relations k)]
variable {M : Type w} [L.Structure M] [Countable M]

/-- The canonical Scott approximation of a tuple in a relational language. At countable ordinals
it characterizes back-and-forth equivalence; uncountable limit stages are assigned the true formula.
The construction uses equality and relation tests and is defined for every language. -/
noncomputable def scottFormula {n : ℕ} (a : Fin n → M) (α : Ordinal.{o}) :
    L.BoundedFormulaω Empty n := by
  classical
  exact Ordinal.limitRecOn
    (motive := fun _ => (k : ℕ) → (Fin k → M) → L.BoundedFormulaω Empty k) α
    (fun _ a => atomicDiagram a)
    (fun _ ih k a => ih k a ⊓
      (.iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable M))
        (fun x => (ih (k + 1) (snoc a x)).ex) ⊓
      (BoundedFormulaInf.iSupAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable M))
        (fun x => ih (k + 1) (snoc a x))).all))
    (fun β _ ih k a => if hβ : β < ω₁ then
      letI := (Cardinal.countable_Iio_of_lt_omega_one hβ).to_subtype
      .iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable (Set.Iio β)))
        (fun γ => ih γ γ.prop k a)
      else ⊤)
    n a

variable {n : ℕ}

/-- The zero approximation is the atomic diagram. -/
@[simp]
theorem scottFormula_zero (a : Fin n → M) :
    scottFormula (L := L) a (0 : Ordinal.{o}) = atomicDiagram a := by
  simp [scottFormula]

/-- A successor approximation retains the preceding formula and adds forth and back clauses. -/
theorem scottFormula_add_one (a : Fin n → M) (α : Ordinal.{o}) :
    scottFormula (L := L) a (α + 1) = scottFormula a α ⊓
      (.iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable M))
        (fun x => (scottFormula (snoc a x) α).ex) ⊓
      (BoundedFormulaInf.iSupAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable M))
        (fun x => scottFormula (snoc a x) α)).all) := by
  simp [scottFormula]

/-- At a countable limit, the approximation conjoins all previous approximations. -/
theorem scottFormula_limit (a : Fin n → M) {α : Ordinal.{o}}
    (hlim : Order.IsSuccLimit α) (hα : α < ω₁) :
    scottFormula (L := L) a α =
      .iInfAlong (IndexCoding.ofEncodableWith
        (letI := (Cardinal.countable_Iio_of_lt_omega_one hα).to_subtype;
          Encodable.ofCountable (Set.Iio α)))
        (fun β => scottFormula a β) := by
  classical
  simp [scottFormula, Ordinal.limitRecOn_limit _ _ _ _ hlim, hα]

/-- A tuple in any structure satisfies the canonical Scott formula exactly when it is
back-and-forth equivalent to the original tuple at that countable ordinal. -/
@[simp]
theorem realize_scottFormula_iff_bfEquiv [L.IsRelational] {N : Type w'} [L.Structure N]
    (a : Fin n → M) (b : Fin n → N) {α : Ordinal.{o}} (hα : α < ω₁) :
    (scottFormula (L := L) a α).Realize Empty.elim b ↔ BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => simp
  | add_one α ih =>
    have hα' : α < ω₁ := lt_trans (lt_add_one α) hα
    simp only [scottFormula_add_one, BoundedFormulaInf.realize_inf,
      BoundedFormulaInf.realize_iInfAlong, BoundedFormulaInf.realize_ex,
      BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_iSupAlong,
      ih _ _ hα', BFEquiv.add_one]
  | limit α hlim ih =>
    simp only [scottFormula_limit a hlim hα, BoundedFormulaInf.realize_iInfAlong,
      BFEquiv.limit hlim]
    exact Subtype.forall.trans (forall_congr' fun β =>
      forall_congr' fun hβ => ih β hβ a b (lt_trans hβ hα))

end TauCeti
