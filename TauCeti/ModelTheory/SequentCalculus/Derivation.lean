/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.SequentCalculus.Instance

/-!
# Derivations of the sequent calculus `LK` with equality

A sequent `Γ ⇒ Δ` of first-order formulas is a pair of finite sets of formulas whose free variables
are natural numbers, read as "the conjunction of `Γ` implies the disjunction of `Δ`". This file
defines the derivations of Gentzen's sequent calculus `LK` for classical first-order logic with
equality, over Mathlib's first-order formulas with `⊥`, implication and the universal quantifier
as primitives, together with the three measures of a derivation that cut elimination works with:
its height, its cut rank and the set of formulas occurring in it.

The rules are these, writing `Γ, φ` for `insert φ Γ`.

* Initial sequents: `Γ ⇒ Δ` when an atomic formula lies in both `Γ` and `Δ` (`ax`), and when
  `⊥ ∈ Γ` (`botL`).
* Implication: if `φ → ψ ∈ Γ`, from `Γ ⇒ Δ, φ` and `Γ, ψ ⇒ Δ` infer `Γ ⇒ Δ` (`impL`); if
  `φ → ψ ∈ Δ`, from `Γ, φ ⇒ Δ, ψ` infer `Γ ⇒ Δ` (`impR`).
* Universal quantifier: if `∀'φ ∈ Γ`, from `Γ, φ[t] ⇒ Δ` infer `Γ ⇒ Δ`, for any term `t`
  (`allL`); if `∀'φ ∈ Δ` and the variable `y` occurs free in no formula of `Γ ∪ Δ`, from
  `Γ ⇒ Δ, φ[y]` infer `Γ ⇒ Δ` (`allR`).
* Equality: from `Γ, t = t ⇒ Δ` infer `Γ ⇒ Δ` (`ref`); if `s = t ∈ Γ` and `φ` is atomic with one
  bound position and `φ[s] ∈ Γ`, from `Γ, φ[t] ⇒ Δ` infer `Γ ⇒ Δ` (`repl`).
* Cut: from `Γ ⇒ Δ, φ` and `Γ, φ ⇒ Δ` infer `Γ ⇒ Δ` (`cut`).

Here `φ[t]` is the instance `φ.inst ![t]` of a formula `φ` with one bound position.

Since sequents are sets, exchange and contraction are built in, and the principal formula of every
logical rule stays available in the premises; weakening is then admissible rather than a rule.
Initial sequents share an *atomic* formula, not an arbitrary one, so that the logical rules can be
inverted. The sets are finite, so that a fresh eigenvariable for the right universal rule always
exists. Insertion of a formula uses classical decidable equality.

The *height* of a derivation counts rules along its longest branch, initial sequents having height
`0`. Its *cut rank* is the largest value of `depth φ + 1` over its cut formulas `φ`, and `0` when
it has no cut, so a derivation is cut-free exactly when its cut rank is `0`. Its *formulas* are the
formulas of all the sequents occurring in it.

## Main definitions

* `TauCeti.SequentCalculus.LKDerivation`: the derivations of a sequent `Γ ⇒ Δ`.
* `TauCeti.SequentCalculus.LKDerivation.height`: the height of a derivation.
* `TauCeti.SequentCalculus.LKDerivation.cutRank`: the cut rank of a derivation.
* `TauCeti.SequentCalculus.LKDerivation.formulas`: the formulas occurring in a derivation.

## References

* Samuel R. Buss, *An introduction to proof theory*, in *Handbook of Proof Theory*, Elsevier,
  1998, §1.2 (the propositional rules) and Definition 2.3.2 (the quantifier rules of `LK`).
* Jean H. Gallier, *Logic for Computer Science: Foundations of Automatic Theorem Proving*, second
  edition, Dover, 2015, Definition 6.4.2 (the calculus `G1nnf` on sets of formulas, whose
  principal formulas may stay in the premises) and Definitions 6.4.3 and 6.4.4 (degree and cut
  rank).
* S. Negri and J. von Plato, *Cut elimination in the presence of axioms*, Bulletin of Symbolic
  Logic 4 (1998): the reflexivity and replacement rules for equality.
-/

public section

universe u v

open FirstOrder Language BoundedFormula

namespace TauCeti.SequentCalculus

variable {L : Language.{u, v}}

open Classical in
/-- The derivations of a sequent `Γ ⇒ Δ` in Gentzen's sequent calculus `LK` with equality, where
`Γ` and `Δ` are finite sets of first-order formulas with free variables in `ℕ`. There is one
constructor per rule; the principal formula of a logical rule stays in the premises, initial
sequents share an atomic formula or have `⊥` in the antecedent, the eigenvariable `y` of the right
universal rule occurs free in no formula of the conclusion, and the equality rules are reflexivity
and replacement in atomic formulas, both acting on the antecedent. -/
inductive LKDerivation : Finset (L.Formula ℕ) → Finset (L.Formula ℕ) → Type (max u v)
  /-- An initial sequent: an atomic formula lies in the antecedent and in the succedent. -/
  | ax {Γ Δ : Finset (L.Formula ℕ)} (φ : L.Formula ℕ) (hφ : φ.IsAtomic) (hΓ : φ ∈ Γ)
      (hΔ : φ ∈ Δ) : LKDerivation Γ Δ
  /-- An initial sequent: `⊥` lies in the antecedent. -/
  | botL {Γ Δ : Finset (L.Formula ℕ)} (h : (⊥ : L.Formula ℕ) ∈ Γ) : LKDerivation Γ Δ
  /-- Left implication: if `φ → ψ ∈ Γ`, from `Γ ⇒ Δ, φ` and `Γ, ψ ⇒ Δ` infer `Γ ⇒ Δ`. -/
  | impL {Γ Δ : Finset (L.Formula ℕ)} (φ ψ : L.Formula ℕ) (h : φ.imp ψ ∈ Γ)
      (d₁ : LKDerivation Γ (insert φ Δ)) (d₂ : LKDerivation (insert ψ Γ) Δ) : LKDerivation Γ Δ
  /-- Right implication: if `φ → ψ ∈ Δ`, from `Γ, φ ⇒ Δ, ψ` infer `Γ ⇒ Δ`. -/
  | impR {Γ Δ : Finset (L.Formula ℕ)} (φ ψ : L.Formula ℕ) (h : φ.imp ψ ∈ Δ)
      (d : LKDerivation (insert φ Γ) (insert ψ Δ)) : LKDerivation Γ Δ
  /-- Left universal quantifier: if `∀'φ ∈ Γ`, from `Γ, φ[t] ⇒ Δ` infer `Γ ⇒ Δ`. -/
  | allL {Γ Δ : Finset (L.Formula ℕ)} (φ : L.BoundedFormula ℕ 1) (t : L.Term ℕ) (h : φ.all ∈ Γ)
      (d : LKDerivation (insert (φ.inst ![t]) Γ) Δ) : LKDerivation Γ Δ
  /-- Right universal quantifier: if `∀'φ ∈ Δ` and the eigenvariable `y` occurs free in no
  formula of `Γ ∪ Δ`, from `Γ ⇒ Δ, φ[y]` infer `Γ ⇒ Δ`. -/
  | allR {Γ Δ : Finset (L.Formula ℕ)} (φ : L.BoundedFormula ℕ 1) (y : ℕ) (h : φ.all ∈ Δ)
      (hy : ∀ ψ ∈ Γ ∪ Δ, y ∉ ψ.freeVarFinset)
      (d : LKDerivation Γ (insert (φ.inst ![Term.var y]) Δ)) : LKDerivation Γ Δ
  /-- Reflexivity of equality: from `Γ, t = t ⇒ Δ` infer `Γ ⇒ Δ`. -/
  | ref {Γ Δ : Finset (L.Formula ℕ)} (t : L.Term ℕ) (d : LKDerivation (insert (t.equal t) Γ) Δ) :
      LKDerivation Γ Δ
  /-- Replacement of equals in atomic formulas: if `s = t ∈ Γ` and `φ[s] ∈ Γ` for an atomic `φ`
  with one bound position, from `Γ, φ[t] ⇒ Δ` infer `Γ ⇒ Δ`. -/
  | repl {Γ Δ : Finset (L.Formula ℕ)} (φ : L.BoundedFormula ℕ 1) (hφ : φ.IsAtomic)
      (s t : L.Term ℕ) (h₁ : s.equal t ∈ Γ) (h₂ : φ.inst ![s] ∈ Γ)
      (d : LKDerivation (insert (φ.inst ![t]) Γ) Δ) : LKDerivation Γ Δ
  /-- Cut: from `Γ ⇒ Δ, φ` and `Γ, φ ⇒ Δ` infer `Γ ⇒ Δ`. -/
  | cut {Γ Δ : Finset (L.Formula ℕ)} (φ : L.Formula ℕ) (d₁ : LKDerivation Γ (insert φ Δ))
      (d₂ : LKDerivation (insert φ Γ) Δ) : LKDerivation Γ Δ

namespace LKDerivation

variable {Γ Δ : Finset (L.Formula ℕ)}

/-! ### Height -/

/-- The height of a derivation: `0` for an initial sequent, and one more than the largest height of
the premises for every other rule. -/
noncomputable def height : {Γ Δ : Finset (L.Formula ℕ)} → LKDerivation Γ Δ → ℕ
  | _, _, ax .. => 0
  | _, _, botL _ => 0
  | _, _, impL _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, _, impR _ _ _ d => d.height + 1
  | _, _, allL _ _ _ d => d.height + 1
  | _, _, allR _ _ _ _ d => d.height + 1
  | _, _, ref _ d => d.height + 1
  | _, _, repl _ _ _ _ _ _ d => d.height + 1
  | _, _, cut _ d₁ d₂ => max d₁.height d₂.height + 1

@[simp]
theorem height_ax (φ : L.Formula ℕ) (hφ : φ.IsAtomic) (hΓ : φ ∈ Γ) (hΔ : φ ∈ Δ) :
    (ax φ hφ hΓ hΔ).height = 0 :=
  (rfl)

@[simp]
theorem height_botL (h : (⊥ : L.Formula ℕ) ∈ Γ) : (botL h : LKDerivation Γ Δ).height = 0 :=
  (rfl)

open Classical in
@[simp]
theorem height_impL (φ ψ : L.Formula ℕ) (h : φ.imp ψ ∈ Γ) (d₁ : LKDerivation Γ (insert φ Δ))
    (d₂ : LKDerivation (insert ψ Γ) Δ) :
    (impL φ ψ h d₁ d₂).height = max d₁.height d₂.height + 1 :=
  (rfl)

open Classical in
@[simp]
theorem height_impR (φ ψ : L.Formula ℕ) (h : φ.imp ψ ∈ Δ)
    (d : LKDerivation (insert φ Γ) (insert ψ Δ)) : (impR φ ψ h d).height = d.height + 1 :=
  (rfl)

open Classical in
@[simp]
theorem height_allL (φ : L.BoundedFormula ℕ 1) (t : L.Term ℕ) (h : φ.all ∈ Γ)
    (d : LKDerivation (insert (φ.inst ![t]) Γ) Δ) : (allL φ t h d).height = d.height + 1 :=
  (rfl)

open Classical in
@[simp]
theorem height_allR (φ : L.BoundedFormula ℕ 1) (y : ℕ) (h : φ.all ∈ Δ)
    (hy : ∀ ψ ∈ Γ ∪ Δ, y ∉ ψ.freeVarFinset)
    (d : LKDerivation Γ (insert (φ.inst ![Term.var y]) Δ)) :
    (allR φ y h hy d).height = d.height + 1 :=
  (rfl)

open Classical in
@[simp]
theorem height_ref (t : L.Term ℕ) (d : LKDerivation (insert (t.equal t) Γ) Δ) :
    (ref t d).height = d.height + 1 :=
  (rfl)

open Classical in
@[simp]
theorem height_repl (φ : L.BoundedFormula ℕ 1) (hφ : φ.IsAtomic) (s t : L.Term ℕ)
    (h₁ : s.equal t ∈ Γ) (h₂ : φ.inst ![s] ∈ Γ) (d : LKDerivation (insert (φ.inst ![t]) Γ) Δ) :
    (repl φ hφ s t h₁ h₂ d).height = d.height + 1 :=
  (rfl)

open Classical in
@[simp]
theorem height_cut (φ : L.Formula ℕ) (d₁ : LKDerivation Γ (insert φ Δ))
    (d₂ : LKDerivation (insert φ Γ) Δ) :
    (cut φ d₁ d₂).height = max d₁.height d₂.height + 1 :=
  (rfl)

/-- A derivation of height `0` is an initial sequent: its antecedent and succedent share an
atomic formula, or its antecedent contains `⊥`. -/
theorem exists_isAtomic_or_bot_mem_of_height_eq_zero (d : LKDerivation Γ Δ) (hd : d.height = 0) :
    (∃ φ, φ.IsAtomic ∧ φ ∈ Γ ∧ φ ∈ Δ) ∨ (⊥ : L.Formula ℕ) ∈ Γ := by
  cases d with
  | ax φ hφ hΓ hΔ => exact Or.inl ⟨φ, hφ, hΓ, hΔ⟩
  | botL h => exact Or.inr h
  | _ => simp at hd

/-! ### Cut rank -/

/-- The cut rank of a derivation: the largest value of `depth φ + 1` over the cut formulas `φ` of
its cuts, and `0` when it has no cut. -/
noncomputable def cutRank : {Γ Δ : Finset (L.Formula ℕ)} → LKDerivation Γ Δ → ℕ
  | _, _, ax .. => 0
  | _, _, botL _ => 0
  | _, _, impL _ _ _ d₁ d₂ => max d₁.cutRank d₂.cutRank
  | _, _, impR _ _ _ d => d.cutRank
  | _, _, allL _ _ _ d => d.cutRank
  | _, _, allR _ _ _ _ d => d.cutRank
  | _, _, ref _ d => d.cutRank
  | _, _, repl _ _ _ _ _ _ d => d.cutRank
  | _, _, cut φ d₁ d₂ => max (φ.depth + 1) (max d₁.cutRank d₂.cutRank)

@[simp]
theorem cutRank_ax (φ : L.Formula ℕ) (hφ : φ.IsAtomic) (hΓ : φ ∈ Γ) (hΔ : φ ∈ Δ) :
    (ax φ hφ hΓ hΔ).cutRank = 0 :=
  (rfl)

@[simp]
theorem cutRank_botL (h : (⊥ : L.Formula ℕ) ∈ Γ) : (botL h : LKDerivation Γ Δ).cutRank = 0 :=
  (rfl)

open Classical in
@[simp]
theorem cutRank_impL (φ ψ : L.Formula ℕ) (h : φ.imp ψ ∈ Γ) (d₁ : LKDerivation Γ (insert φ Δ))
    (d₂ : LKDerivation (insert ψ Γ) Δ) :
    (impL φ ψ h d₁ d₂).cutRank = max d₁.cutRank d₂.cutRank :=
  (rfl)

open Classical in
@[simp]
theorem cutRank_impR (φ ψ : L.Formula ℕ) (h : φ.imp ψ ∈ Δ)
    (d : LKDerivation (insert φ Γ) (insert ψ Δ)) : (impR φ ψ h d).cutRank = d.cutRank :=
  (rfl)

open Classical in
@[simp]
theorem cutRank_allL (φ : L.BoundedFormula ℕ 1) (t : L.Term ℕ) (h : φ.all ∈ Γ)
    (d : LKDerivation (insert (φ.inst ![t]) Γ) Δ) : (allL φ t h d).cutRank = d.cutRank :=
  (rfl)

open Classical in
@[simp]
theorem cutRank_allR (φ : L.BoundedFormula ℕ 1) (y : ℕ) (h : φ.all ∈ Δ)
    (hy : ∀ ψ ∈ Γ ∪ Δ, y ∉ ψ.freeVarFinset)
    (d : LKDerivation Γ (insert (φ.inst ![Term.var y]) Δ)) :
    (allR φ y h hy d).cutRank = d.cutRank :=
  (rfl)

open Classical in
@[simp]
theorem cutRank_ref (t : L.Term ℕ) (d : LKDerivation (insert (t.equal t) Γ) Δ) :
    (ref t d).cutRank = d.cutRank :=
  (rfl)

open Classical in
@[simp]
theorem cutRank_repl (φ : L.BoundedFormula ℕ 1) (hφ : φ.IsAtomic) (s t : L.Term ℕ)
    (h₁ : s.equal t ∈ Γ) (h₂ : φ.inst ![s] ∈ Γ) (d : LKDerivation (insert (φ.inst ![t]) Γ) Δ) :
    (repl φ hφ s t h₁ h₂ d).cutRank = d.cutRank :=
  (rfl)

open Classical in
@[simp]
theorem cutRank_cut (φ : L.Formula ℕ) (d₁ : LKDerivation Γ (insert φ Δ))
    (d₂ : LKDerivation (insert φ Γ) Δ) :
    (cut φ d₁ d₂).cutRank = max (φ.depth + 1) (max d₁.cutRank d₂.cutRank) :=
  (rfl)

open Classical in
/-! ### Formulas of a derivation -/

/-- The formulas occurring in a derivation: those of its end sequent together with those occurring
in the derivations of its premises. -/
noncomputable def formulas : {Γ Δ : Finset (L.Formula ℕ)} → LKDerivation Γ Δ → Set (L.Formula ℕ)
  | Γ, Δ, ax .. => ↑Γ ∪ ↑Δ
  | Γ, Δ, botL _ => ↑Γ ∪ ↑Δ
  | Γ, Δ, impL _ _ _ d₁ d₂ => ↑Γ ∪ ↑Δ ∪ d₁.formulas ∪ d₂.formulas
  | Γ, Δ, impR _ _ _ d => ↑Γ ∪ ↑Δ ∪ d.formulas
  | Γ, Δ, allL _ _ _ d => ↑Γ ∪ ↑Δ ∪ d.formulas
  | Γ, Δ, allR _ _ _ _ d => ↑Γ ∪ ↑Δ ∪ d.formulas
  | Γ, Δ, ref _ d => ↑Γ ∪ ↑Δ ∪ d.formulas
  | Γ, Δ, repl _ _ _ _ _ _ d => ↑Γ ∪ ↑Δ ∪ d.formulas
  | Γ, Δ, cut _ d₁ d₂ => ↑Γ ∪ ↑Δ ∪ d₁.formulas ∪ d₂.formulas

@[simp]
theorem formulas_ax (φ : L.Formula ℕ) (hφ : φ.IsAtomic) (hΓ : φ ∈ Γ) (hΔ : φ ∈ Δ) :
    (ax φ hφ hΓ hΔ).formulas = ↑Γ ∪ ↑Δ :=
  (rfl)

@[simp]
theorem formulas_botL (h : (⊥ : L.Formula ℕ) ∈ Γ) :
    (botL h : LKDerivation Γ Δ).formulas = ↑Γ ∪ ↑Δ :=
  (rfl)

open Classical in
@[simp]
theorem formulas_impL (φ ψ : L.Formula ℕ) (h : φ.imp ψ ∈ Γ) (d₁ : LKDerivation Γ (insert φ Δ))
    (d₂ : LKDerivation (insert ψ Γ) Δ) :
    (impL φ ψ h d₁ d₂).formulas = ↑Γ ∪ ↑Δ ∪ d₁.formulas ∪ d₂.formulas :=
  (rfl)

open Classical in
@[simp]
theorem formulas_impR (φ ψ : L.Formula ℕ) (h : φ.imp ψ ∈ Δ)
    (d : LKDerivation (insert φ Γ) (insert ψ Δ)) :
    (impR φ ψ h d).formulas = ↑Γ ∪ ↑Δ ∪ d.formulas :=
  (rfl)

open Classical in
@[simp]
theorem formulas_allL (φ : L.BoundedFormula ℕ 1) (t : L.Term ℕ) (h : φ.all ∈ Γ)
    (d : LKDerivation (insert (φ.inst ![t]) Γ) Δ) :
    (allL φ t h d).formulas = ↑Γ ∪ ↑Δ ∪ d.formulas :=
  (rfl)

open Classical in
@[simp]
theorem formulas_allR (φ : L.BoundedFormula ℕ 1) (y : ℕ) (h : φ.all ∈ Δ)
    (hy : ∀ ψ ∈ Γ ∪ Δ, y ∉ ψ.freeVarFinset)
    (d : LKDerivation Γ (insert (φ.inst ![Term.var y]) Δ)) :
    (allR φ y h hy d).formulas = ↑Γ ∪ ↑Δ ∪ d.formulas :=
  (rfl)

open Classical in
@[simp]
theorem formulas_ref (t : L.Term ℕ) (d : LKDerivation (insert (t.equal t) Γ) Δ) :
    (ref t d).formulas = ↑Γ ∪ ↑Δ ∪ d.formulas :=
  (rfl)

open Classical in
@[simp]
theorem formulas_repl (φ : L.BoundedFormula ℕ 1) (hφ : φ.IsAtomic) (s t : L.Term ℕ)
    (h₁ : s.equal t ∈ Γ) (h₂ : φ.inst ![s] ∈ Γ) (d : LKDerivation (insert (φ.inst ![t]) Γ) Δ) :
    (repl φ hφ s t h₁ h₂ d).formulas = ↑Γ ∪ ↑Δ ∪ d.formulas :=
  (rfl)

open Classical in
@[simp]
theorem formulas_cut (φ : L.Formula ℕ) (d₁ : LKDerivation Γ (insert φ Δ))
    (d₂ : LKDerivation (insert φ Γ) Δ) :
    (cut φ d₁ d₂).formulas = ↑Γ ∪ ↑Δ ∪ d₁.formulas ∪ d₂.formulas :=
  (rfl)

/-- The formulas of the end sequent occur in the derivation. -/
theorem union_subset_formulas (d : LKDerivation Γ Δ) : ↑Γ ∪ ↑Δ ⊆ d.formulas := by
  intro x hx
  cases d <;> simp only [formulas_ax, formulas_botL, formulas_impL, formulas_impR, formulas_allL,
    formulas_allR, formulas_ref, formulas_repl, formulas_cut, Set.mem_union] at hx ⊢ <;> tauto

/-- The formulas of the antecedent of the end sequent occur in the derivation. -/
theorem coe_subset_formulas_left (d : LKDerivation Γ Δ) : ↑Γ ⊆ d.formulas :=
  Set.subset_union_left.trans d.union_subset_formulas

/-- The formulas of the succedent of the end sequent occur in the derivation. -/
theorem coe_subset_formulas_right (d : LKDerivation Γ Δ) : ↑Δ ⊆ d.formulas :=
  Set.subset_union_right.trans d.union_subset_formulas

end LKDerivation

end TauCeti.SequentCalculus
