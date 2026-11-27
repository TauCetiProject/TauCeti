/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.SequentCalculus.Soundness

/-!
# Examples: derivations of the sequent calculus `LK` and their soundness

These examples exercise the derivations of `LK` with equality, their height and cut rank, and
soundness, from a downstream module through public statements only.

* For atomic `p` and `q`, the sequent `p → q ⇒ p → q` is not an initial sequent, since initial
  sequents share an atomic formula; it has a derivation without cuts of height `2`, by right and
  then left implication.
* `⇒ t = t` has a derivation of height `1` (`ref`, then an initial sequent), and the symmetry of
  equality `s = t ⇒ t = s` one of height `2`: `ref` adds `s = s`, and `repl` with
  `φ = (#0 = s)` rewrites `s = s` to `t = s`.
* A derivation whose only cut is on `p → q` has cut rank `2`, and one whose only cut is on an atom
  has cut rank `1`.
* The eigenvariable condition matters: `P(x₀) ⇒ ∀y P(y), P(x₀)` is an initial sequent, but `x₀`
  occurs free in its antecedent, so the right universal rule at `y = x₀` does not apply to it;
  and indeed `P(x₀) ⇒ ∀y P(y)` is not valid (carrier `{0, 1}`, `P = {0}`, every variable sent to
  `0`), so by soundness it has no derivation.
* `⇒ x₀ = x₁` is not valid, so it has no derivation.
* `⇒ ∃x (x = x)`, that is `⇒ ¬∀x ¬(x = x)`, has a derivation of height `4`: right implication,
  left universal at `x₀`, left implication, and `ref` before the initial sequent
  `x₀ = x₀ ⇒ x₀ = x₀`.
-/

public section

universe u v

open FirstOrder FirstOrder.Language BoundedFormula TauCeti.SequentCalculus LKDerivation

variable {L : Language.{u, v}}

/-! ### Implication -/

-- `p → q ⇒ p → q` has a derivation without cuts of height `2`.
example {p q : L.Formula ℕ} (hp : p.IsAtomic) (hq : q.IsAtomic) :
    ∃ d : LKDerivation {p.imp q} {p.imp q}, d.cutRank = 0 ∧ d.height = 2 :=
  ⟨impR p q (by simp) <| impL p q (by simp) (ax p hp (by simp) (by simp))
    (ax q hq (by simp) (by simp)), by simp, by simp⟩

-- `p → q ⇒ p → q` is not an initial sequent: no derivation of it has height `0`.
example (p q : L.Formula ℕ) (d : LKDerivation {p.imp q} {p.imp q}) : d.height ≠ 0 := by
  intro hd
  rcases d.exists_isAtomic_or_bot_mem_of_height_eq_zero hd with ⟨φ, hφ, hφΓ, -⟩ | h
  · rw [Finset.mem_singleton.1 hφΓ] at hφ
    cases hφ
  · cases Finset.mem_singleton.1 h

/-! ### Equality -/

-- `⇒ t = t` has a derivation of height `1`.
example (t : L.Term ℕ) : ∃ d : LKDerivation ∅ {t.equal t}, d.cutRank = 0 ∧ d.height = 1 :=
  ⟨ref t (ax (t.equal t) (Formula.isAtomic_equal _ _) (by simp) (by simp)),
    by simp only [cutRank_ref, cutRank_ax], by simp only [height_ref, height_ax]⟩

-- The symmetry of equality `s = t ⇒ t = s` has a derivation of height `2`.
example (s t : L.Term ℕ) :
    ∃ d : LKDerivation {s.equal t} {t.equal s}, d.cutRank = 0 ∧ d.height = 2 := by
  -- The atomic formula `#0 = s` with one bound position, and its instances.
  have hinst (u : L.Term ℕ) : ((&0).bdEqual (s.relabel Sum.inl)).inst ![u] = u.equal s := by
    simp [Term.subst_relabel, Function.comp_def, Term.subst_var]
  refine ⟨ref s <| repl ((&0).bdEqual (s.relabel Sum.inl)) (IsAtomic.equal _ _) s t (by simp)
    (by rw [hinst]; simp) <|
      ax (t.equal s) (Formula.isAtomic_equal _ _) (by rw [hinst]; simp) (by simp), by simp, by simp⟩

/-! ### Cut rank -/

open Classical in
-- A derivation whose only cut is on an implication of atoms has cut rank `2`.
example {Γ Δ : Finset (L.Formula ℕ)} {p q : L.Formula ℕ} (hp : p.IsAtomic) (hq : q.IsAtomic)
    (d₁ : LKDerivation Γ (insert (p.imp q) Δ)) (d₂ : LKDerivation (insert (p.imp q) Γ) Δ)
    (h₁ : d₁.cutRank = 0) (h₂ : d₂.cutRank = 0) : (cut _ d₁ d₂).cutRank = 2 := by
  simp [h₁, h₂, hp.depth_eq_zero, hq.depth_eq_zero]

open Classical in
-- A derivation whose only cut is on an atom has cut rank `1`.
example {Γ Δ : Finset (L.Formula ℕ)} {p : L.Formula ℕ} (hp : p.IsAtomic)
    (d₁ : LKDerivation Γ (insert p Δ)) (d₂ : LKDerivation (insert p Γ) Δ)
    (h₁ : d₁.cutRank = 0) (h₂ : d₂.cutRank = 0) : (cut _ d₁ d₂).cutRank = 1 := by
  simp [h₁, h₂, hp.depth_eq_zero]

/-! ### The eigenvariable condition -/

section Eigenvariable

variable (P : L.Relations 1)

/-- The structure on `{0, 1}`, written `ULift Bool` with `0` as `false`, in which every relation
holds exactly of the tuples of zeros and every function is constantly zero. -/
local instance allFalseStructure : L.Structure (ULift.{max u v} Bool) where
  funMap _ _ := ⟨false⟩
  RelMap _ xs := ∀ i, xs i = ⟨false⟩

-- `P(x₀)` is an instance of `P(#0)` at `x₀`.
example : (P.boundedFormula₁ &0).inst ![Term.var 0] = P.formula₁ (Term.var 0) := by
  simp only [Relations.boundedFormula₁, Relations.formula₁, inst_boundedFormula]
  congr 1
  funext i
  simp [Matrix.cons_val_fin_one, Term.subst]

open Classical in
-- `P(x₀) ⇒ ∀y P(y), P(x₀)` is an initial sequent.
example : Nonempty (LKDerivation {P.formula₁ (Term.var 0)}
    {(P.boundedFormula₁ &0).all, P.formula₁ (Term.var 0)}) :=
  ⟨ax (P.formula₁ (Term.var 0)) (IsAtomic.rel _ _) (by simp) (by simp)⟩

open Classical in
-- The variable `x₀` occurs free in `P(x₀)`, so it is not an eigenvariable for the right universal
-- rule on `P(x₀) ⇒ ∀y P(y)`.
example : ¬∀ ψ ∈ ({P.formula₁ (Term.var 0)} ∪ {(P.boundedFormula₁ &0).all} :
    Finset (L.Formula ℕ)), 0 ∉ ψ.freeVarFinset := by
  simp [Relations.formula₁, Relations.formula, Relations.boundedFormula, freeVarFinset]

-- `P(x₀) ⇒ ∀y P(y)` is not valid, so it has no derivation.
example : ¬Valid {P.formula₁ (Term.var 0)} {(P.boundedFormula₁ &0).all} ∧
    IsEmpty (LKDerivation {P.formula₁ (Term.var 0)} {(P.boundedFormula₁ &0).all}) := by
  have h : ¬Valid {P.formula₁ (Term.var 0)} {(P.boundedFormula₁ &0).all} := fun h => by
    obtain ⟨ψ, hψ, hψv⟩ := valid_iff.1 h (ULift.{max u v} Bool) (fun _ => ⟨false⟩) (by
      simp [Structure.RelMap])
    rw [Finset.mem_singleton.1 hψ, Formula.realize_all] at hψv
    simpa [Relations.boundedFormula₁, Structure.RelMap] using hψv ⟨true⟩
  exact ⟨h, isEmpty_lkDerivation_of_not_valid h⟩

-- `⇒ x₀ = x₁` is not valid, so it has no derivation.
example : IsEmpty (LKDerivation (∅ : Finset (L.Formula ℕ)) {(Term.var 0).equal (Term.var 1)}) :=
  isEmpty_lkDerivation_of_not_valid fun h => by
    obtain ⟨ψ, hψ, hψv⟩ := valid_iff.1 h (ULift.{max u v} Bool) (fun n => ⟨n = 0⟩) (by simp)
    rw [Finset.mem_singleton.1 hψ, Formula.realize_equal] at hψv
    simp at hψv

end Eigenvariable

/-! ### `∃x (x = x)` -/

open Classical in
-- `⇒ ∃x (x = x)` has a derivation without cuts of height `4`.
example : ∃ d : LKDerivation ∅ {((&0).bdEqual (&0) : L.BoundedFormula ℕ 1).ex},
    d.cutRank = 0 ∧ d.height = 4 := by
  -- The instance of `¬(#0 = #0)` at `x₀` is `¬(x₀ = x₀)`.
  have hinst : ((&0).bdEqual (&0) : L.BoundedFormula ℕ 1).not.inst ![Term.var 0] =
      ((Term.var 0).equal (Term.var 0)).not := by
    simp
  refine ⟨impR _ ⊥ (Finset.mem_singleton.2 rfl) <|
    allL ((&0).bdEqual (&0) : L.BoundedFormula ℕ 1).not (Term.var 0) (by simp) <|
    impL ((Term.var 0).equal (Term.var 0)) ⊥ (by rw [hinst]; exact Finset.mem_insert.2 (Or.inl rfl))
      (ref (Term.var 0) <|
        ax ((Term.var 0).equal (Term.var 0)) (Formula.isAtomic_equal _ _) (by simp) (by simp))
      (botL (by simp)), ?_, ?_⟩
  · simp only [cutRank_impR, cutRank_allL, cutRank_impL, cutRank_ref, cutRank_ax, cutRank_botL,
      max_self]
  · simp only [height_impR, height_allL, height_impL, height_ref, height_ax, height_botL]
    rfl
