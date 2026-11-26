/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Logic.Propositional.Clause
import Mathlib.Data.Finset.Piecewise

/-!
# Restriction and splitting of clausal formulas

Restricting a formula by a finite set of literals deletes the clauses made true and removes
the literals made false. The variables assigned by the restriction disappear from the result.
For a consistent set of literals, the restricted formula is satisfiable exactly when the original
formula has a model making those literals true. Restriction by a singleton gives the splitting,
unit clause, and pure literal rules of propositional search.
-/

public section

open Std.Sat (Literal)

namespace TauCeti.Propositional

variable {V : Type*} [DecidableEq V] {F : CNF V} {M : Clause V} {l : Literal V} {τ : V → Bool}

namespace CNF

/-- Restrict a clausal formula by setting every literal in `M` to true. Keep the clauses
disjoint from `M` and erase from each the negations of the literals in `M`. -/
def restrict (F : CNF V) (M : Clause V) : CNF V :=
  (F.filter (Disjoint · M)).image (· \ M.image Literal.negate)

@[simp]
theorem mem_restrict {D : Clause V} :
    D ∈ F.restrict M ↔ ∃ C ∈ F, Disjoint C M ∧ C \ M.image Literal.negate = D := by
  simp [restrict, and_assoc]

@[simp]
theorem restrict_empty (F : CNF V) : F.restrict ∅ = F := by
  simp [restrict]

@[simp]
theorem empty_restrict (M : Clause V) : (∅ : CNF V).restrict M = ∅ := by
  simp [restrict]

/-- Setting `l` to true deletes the clauses containing it and erases its negation from the rest. -/
theorem restrict_singleton (F : CNF V) (l : Literal V) :
    F.restrict {l} = (F.filter (l ∉ ·)).image (·.erase l.negate) := by
  simp [restrict, Finset.sdiff_singleton_eq_erase]

/-- No variable assigned by the restriction occurs in the residual formula. -/
@[simp]
theorem disjoint_vars_restrict (F : CNF V) (M : Clause V) :
    Disjoint (F.restrict M).vars M.vars := by
  refine Finset.disjoint_left.mpr fun v hv hM ↦ ?_
  obtain ⟨D, hD, hvD⟩ := mem_vars.mp hv
  obtain ⟨C, _, hd, rfl⟩ := mem_restrict.mp hD
  obtain ⟨b, hb⟩ := Clause.mem_vars.mp hvD
  obtain ⟨c, hc⟩ := Clause.mem_vars.mp hM
  obtain ⟨hbC, hbM⟩ := Finset.mem_sdiff.mp hb
  by_cases h : c = b
  · exact Finset.disjoint_left.mp hd hbC (h ▸ hc)
  · exact hbM (Finset.mem_image.mpr ⟨(v, c), hc, Prod.ext rfl (Bool.not_eq.mpr h)⟩)

/-- If the opposite polarity is absent, restricting by `l` simply deletes its clauses. -/
theorem restrict_singleton_eq_filter (h : ∀ C ∈ F, l.negate ∉ C) :
    F.restrict {l} = F.filter (l ∉ ·) := by
  rw [restrict_singleton]
  refine (Finset.image_congr (g := id) ?_).trans Finset.image_id
  intro C hC
  exact Finset.erase_eq_of_notMem (h C (Finset.mem_filter.mp hC).1)

end CNF

/-- An assignment making every literal in `M` true models the restriction exactly when it
models the original formula. -/
@[simp]
theorem models_restrict_iff (hM : ∀ k ∈ M, τ k.1 = k.2) :
    Models τ (F.restrict M) ↔ Models τ F := by
  constructor
  · intro h
    apply models_iff.mpr
    intro C hC
    by_cases hd : Disjoint C M
    · exact (h.satisfies (CNF.mem_restrict.mpr ⟨C, hC, hd, rfl⟩)).mono Finset.sdiff_subset
    · obtain ⟨k, hkC, hkM⟩ := Finset.not_disjoint_iff.mp hd
      exact satisfies_of_mem hkC (hM k hkM)
  · intro h
    apply models_iff.mpr
    intro D hD
    obtain ⟨C, hC, _, rfl⟩ := CNF.mem_restrict.mp hD
    obtain ⟨k, hk, hτ⟩ := satisfies_iff.mp (h.satisfies hC)
    refine satisfies_of_mem (Finset.mem_sdiff.mpr ⟨hk, ?_⟩) hτ
    intro hkM
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hkM
    simp [hM j hj] at hτ

/-- A model of the restriction by consistent literals extends to a model of the original formula
that makes the literals true and agrees with the given model on all other variables. -/
theorem Models.exists_extension_of_restrict (hτ : Models τ (F.restrict M)) (hM : ¬M.IsTautology) :
    ∃ σ, Models σ F ∧ (∀ k ∈ M, σ k.1 = k.2) ∧ ∀ v ∉ M.vars, σ v = τ v := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ¬Satisfies ρ M := by
    simpa only [Clause.isTautology_iff_forall_satisfies, not_forall] using hM
  -- The complement of an assignment falsifying M makes all of its literals true.
  let σ := M.vars.piecewise (fun v ↦ !(ρ v)) τ
  have hσ : ∀ k ∈ M, σ k.1 = k.2 := by
    intro k hk
    dsimp only [σ]
    rw [Finset.piecewise_eq_of_mem _ _ _ (Clause.mem_vars_of_mem hk)]
    exact Bool.not_eq.mpr fun h ↦ hρ (satisfies_of_mem hk h)
  have hoff : ∀ v ∉ M.vars, σ v = τ v := fun _ hv ↦ Finset.piecewise_eq_of_notMem _ _ _ hv
  refine ⟨σ, (models_restrict_iff hσ).mp ?_, hσ, hoff⟩
  apply (models_congr _).mpr hτ
  exact fun v hv ↦ hoff v (Finset.disjoint_left.mp (F.disjoint_vars_restrict M) hv)

/-- Restriction by consistent literals is satisfiable exactly when some model of the original
formula makes all those literals true. -/
theorem satisfiable_restrict_iff (hM : ¬M.IsTautology) :
    Satisfiable (F.restrict M : Set (Clause V)) ↔ ∃ τ, Models τ F ∧ ∀ k ∈ M, τ k.1 = k.2 := by
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := satisfiable_iff.mp h
    obtain ⟨σ, hF, hσ, _⟩ := hτ.exists_extension_of_restrict hM
    exact ⟨σ, hF, hσ⟩
  · rintro ⟨τ, hτ, hMτ⟩
    exact ((models_restrict_iff hMτ).mpr hτ).satisfiable

/-- Restricting by one literal tests for a model in which that literal is true. -/
theorem satisfiable_restrict_singleton_iff :
    Satisfiable (F.restrict {l} : Set (Clause V)) ↔ ∃ τ, Models τ F ∧ τ l.1 = l.2 := by
  rw [satisfiable_restrict_iff]
  · simp
  · simp [Clause.isTautology_iff, Literal.negate, Prod.ext_iff]

/-- Splitting on either polarity of a variable preserves satisfiability. -/
theorem satisfiable_iff_restrict_or_restrict_negate :
    Satisfiable (F : Set (Clause V)) ↔
      Satisfiable (F.restrict {l} : Set (Clause V)) ∨
        Satisfiable (F.restrict {l.negate} : Set (Clause V)) := by
  rw [satisfiable_iff]
  simp [satisfiable_restrict_singleton_iff, Bool.eq_not, ← exists_or, ← and_or_left, em]

/-- A unit clause forces the choice of polarity in the splitting rule. -/
theorem satisfiable_iff_restrict_of_singleton_mem (hl : {l} ∈ F) :
    Satisfiable (F : Set (Clause V)) ↔ Satisfiable (F.restrict {l} : Set (Clause V)) := by
  rw [satisfiable_restrict_singleton_iff, satisfiable_iff]
  exact ⟨fun ⟨τ, hτ⟩ ↦ ⟨τ, hτ, satisfies_singleton.mp (hτ.satisfies hl)⟩,
    fun ⟨τ, hτ, _⟩ ↦ ⟨τ, hτ⟩⟩

/-- Deleting all clauses containing a pure literal preserves satisfiability. -/
theorem satisfiable_iff_filter_of_pure (hl : ∀ C ∈ F, l.negate ∉ C) :
    Satisfiable (F : Set (Clause V)) ↔ Satisfiable (F.filter (l ∉ ·) : Set (Clause V)) := by
  refine ⟨fun h ↦ h.mono (Finset.filter_subset _ _), ?_⟩
  rw [← CNF.restrict_singleton_eq_filter hl, satisfiable_restrict_singleton_iff]
  exact fun ⟨_, hτ, _⟩ ↦ hτ.satisfiable

end TauCeti.Propositional
