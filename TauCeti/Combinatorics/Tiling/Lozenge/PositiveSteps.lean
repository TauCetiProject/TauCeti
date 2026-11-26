/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Positive steps of walks in the edge graph of a region

A step from `u` to `u'` of the triangular lattice is positive when `u' = u + e_k` for one of the
three positive directions `e₁ = (1, 0)`, `e₂ = (0, 1)`, `e₃ = (1, 1)`. Every dart of the edge graph
`regionGraph R` of a region goes from some `u` to `u + e_k` or to `u − e_k`, and exactly one of a
dart and its reverse is positive. The number of positive steps of a walk, `positiveSteps p`, is
additive under concatenation, and a walk and its reverse together have as many positive steps as
the walk has darts. The least number of positive steps of a walk from `u` to `v` is the oriented
distance `ρ_R(u, v)` of Thurston's tileability criterion.

## Main definitions

* `TauCeti.IsPositiveStep u u'`: `u' = u + e_k` for some direction `k`.
* `TauCeti.positiveSteps p`: the number of darts of a walk `p` in `regionGraph R` that are
  positive steps.

## Main statements

* `TauCeti.isPositiveStep_add_latticeDir`, `TauCeti.not_isPositiveStep_sub_latticeDir`: every step
  `u → u + e_k` is positive and no step `u → u − e_k` is.
* `TauCeti.exists_eq_add_or_eq_sub_of_regionGraph_adj`: every dart of `regionGraph R` goes from
  some `u` to `u + e_k` or to `u − e_k`.
* `TauCeti.isPositiveStep_iff_not_isPositiveStep_of_regionGraph_adj`: exactly one of a dart and
  its reverse is a positive step.
* `TauCeti.ite_isPositiveStep_add_ite_isPositiveStep_of_regionGraph_adj`: a dart and its reverse
  together contribute exactly one positive step.
* `TauCeti.positiveSteps_nil`, `TauCeti.positiveSteps_cons`, `TauCeti.positiveSteps_append`:
  `positiveSteps` vanishes on the empty walk and is additive under concatenation.
* `TauCeti.positiveSteps_add_positiveSteps_reverse`: `positiveSteps p` plus `positiveSteps` of
  the reversed walk is the length of `p`.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Theorem 1.4. Gorin states the criterion for the height `x + y − 3H` and the oriented distance
  along the directions `(1, 0)`, `(0, 1)`, `(−1, −1)`; here the positive directions are `e₁`, `e₂`,
  `e₃`. Both forms characterise tileability of simply connected regions.
* W. P. Thurston, *Conway's tiling groups*, Amer. Math. Monthly 97 (1990), 757–773.
-/

public section

namespace TauCeti

/-- A step from `u` to `u'` is positive when `u' = u + e_k` for one of the three positive
directions `e₁ = (1, 0)`, `e₂ = (0, 1)`, `e₃ = (1, 1)`. -/
def IsPositiveStep (u u' : ℤ × ℤ) : Prop :=
  ∃ k : Fin 3, u' = u + latticeDir k

variable {R : Set TriFace} {u u' v w : ℤ × ℤ}

theorem isPositiveStep_def : IsPositiveStep u u' ↔ ∃ k : Fin 3, u' = u + latticeDir k := Iff.rfl

/-- A step is positive when its displacement is `(1, 0)`, `(0, 1)` or `(1, 1)`. -/
theorem isPositiveStep_iff :
    IsPositiveStep u u' ↔ u' - u = (1, 0) ∨ u' - u = (0, 1) ∨ u' - u = (1, 1) := by
  simp only [isPositiveStep_def, Fin.exists_fin_succ, Fin.exists_fin_zero, sub_eq_iff_eq_add']
  simp

/-- Every step `u → u + e_k` is positive. -/
@[simp] theorem isPositiveStep_add_latticeDir (u : ℤ × ℤ) (k : Fin 3) :
    IsPositiveStep u (u + latticeDir k) :=
  ⟨k, rfl⟩

/-- No step `u → u − e_k` is positive. -/
@[simp] theorem not_isPositiveStep_sub_latticeDir (u : ℤ × ℤ) (k : Fin 3) :
    ¬ IsPositiveStep u (u - latticeDir k) := by
  rw [isPositiveStep_iff, sub_sub_cancel_left]
  revert k
  simp [Fin.forall_fin_succ, Prod.ext_iff]

instance instDecidableRelIsPositiveStep : DecidableRel IsPositiveStep := fun _ _ =>
  decidable_of_iff _ isPositiveStep_iff.symm

/-- A positive step reversed is not a positive step: the coordinates of `e_k + e_j` are not both
zero. -/
theorem IsPositiveStep.asymm (h : IsPositiveStep u u') : ¬ IsPositiveStep u' u := by
  rw [isPositiveStep_iff] at h ⊢
  rcases u with ⟨x, y⟩
  rcases u' with ⟨x', y'⟩
  simp only [Prod.mk_sub_mk, Prod.mk.injEq] at h ⊢
  omega

/-- **Darts of the edge graph.** Every dart of `regionGraph R` goes from some `u` to `u + e_k` or
to `u − e_k`. -/
theorem exists_eq_add_or_eq_sub_of_regionGraph_adj (h : (regionGraph R).Adj u u') :
    ∃ k : Fin 3, u' = u + latticeDir k ∨ u' = u - latticeDir k := by
  obtain ⟨⟨v, k⟩, -, he⟩ := regionGraph_adj.1 h
  rw [TriEdge.endpoints_def, TriEdge.target_mk, Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨k, Or.inl rfl⟩
  · exact ⟨k, Or.inr (add_sub_cancel_right _ _).symm⟩

/-- Exactly one of a dart of `regionGraph R` and its reverse is a positive step. -/
theorem isPositiveStep_iff_not_isPositiveStep_of_regionGraph_adj
    (h : (regionGraph R).Adj u u') :
    IsPositiveStep u u' ↔ ¬ IsPositiveStep u' u := by
  obtain ⟨k, rfl | rfl⟩ := exists_eq_add_or_eq_sub_of_regionGraph_adj h
  · simpa using IsPositiveStep.asymm (isPositiveStep_add_latticeDir u k)
  · simpa using isPositiveStep_add_latticeDir (u - latticeDir k) k

/-- For a dart of `regionGraph R`, the dart and its reverse together contribute exactly one
positive step. -/
theorem ite_isPositiveStep_add_ite_isPositiveStep_of_regionGraph_adj
    (h : (regionGraph R).Adj u u') :
    ((if IsPositiveStep u u' then 1 else 0) + if IsPositiveStep u' u then 1 else 0) = 1 := by
  have := isPositiveStep_iff_not_isPositiveStep_of_regionGraph_adj h
  split_ifs <;> simp_all

/-- The number of positive steps of a walk in the edge graph of a region: its darts from some `u`
to `u + e_k`. -/
def positiveSteps {u v : ℤ × ℤ} (p : (regionGraph R).Walk u v) : ℕ :=
  p.darts.countP fun d => IsPositiveStep d.fst d.snd

theorem positiveSteps_def {u v : ℤ × ℤ} (p : (regionGraph R).Walk u v) :
    positiveSteps p = p.darts.countP fun d => IsPositiveStep d.fst d.snd := (rfl)

/-- A walk with no darts has no positive steps. -/
@[simp] theorem positiveSteps_nil :
    positiveSteps (SimpleGraph.Walk.nil : (regionGraph R).Walk u u) = 0 :=
  (rfl)

@[simp] theorem positiveSteps_cons (h : (regionGraph R).Adj u v) (p : (regionGraph R).Walk v w) :
    positiveSteps (.cons h p) = positiveSteps p + if IsPositiveStep u v then 1 else 0 := by
  simp only [positiveSteps_def, SimpleGraph.Walk.darts_cons, List.countP_cons,
    decide_eq_true_eq]

/-- **Additivity.** The positive steps of a concatenation are those of the two walks. -/
@[simp] theorem positiveSteps_append (p : (regionGraph R).Walk u v) (q : (regionGraph R).Walk v w) :
    positiveSteps (p.append q) = positiveSteps p + positiveSteps q := by
  simp only [positiveSteps_def, SimpleGraph.Walk.darts_append, List.countP_append]

theorem positiveSteps_le_length (p : (regionGraph R).Walk u v) : positiveSteps p ≤ p.length := by
  rw [positiveSteps_def, ← SimpleGraph.Walk.length_darts]
  exact List.countP_le_length

/-- **A walk and its reverse.** `positiveSteps p` plus the positive steps of the reversed walk is
the length of `p`: every dart of `p` is positive in exactly one direction. -/
theorem positiveSteps_add_positiveSteps_reverse (p : (regionGraph R).Walk u v) :
    positiveSteps p + positiveSteps p.reverse = p.length := by
  induction p with
  | nil => rfl
  | @cons a b _ hab p ih =>
    have := ite_isPositiveStep_add_ite_isPositiveStep_of_regionGraph_adj hab
    simp [SimpleGraph.Walk.reverse_cons, ← ih]
    omega

end TauCeti
