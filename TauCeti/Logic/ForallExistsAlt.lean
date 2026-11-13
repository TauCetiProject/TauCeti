/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation

/-!
# Alternating universal and existential quantifiers

For a relation `P` between `k`-tuples, `TauCeti.ForallExistsAlt k P` is the statement
`∀ x₀ ∃ y₀ ∀ x₁ ∃ y₁ … ∀ x_{k-1} ∃ y_{k-1}, P x y` with `k` alternations of quantifiers. This is
the prefix of a positive sentence in prenex form, where each existential witness may depend on
the universal variables to its left and on no others.

That dependence is made explicit by Skolem functions: the alternation holds exactly when there is
a function `f` from tuples `x` to tuples `y` with `P x (f x)` for all `x`, such that the `i`-th
coordinate of `f x` depends only on the coordinates `x j` with `j ≤ i`.

## Main definitions

* `TauCeti.ForallExistsAlt k P`: the alternation `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1}, P x y`.

## Main results

* `TauCeti.forallExistsAlt_iff_exists_skolem`: the alternation holds exactly when it has
  Skolem functions respecting the order of the quantifiers.
-/

public section

namespace TauCeti

variable {α β : Type*} {k : ℕ}

/-- The alternation of quantifiers `∀ x₀ ∃ y₀ ∀ x₁ ∃ y₁ … ∀ x_{k-1} ∃ y_{k-1}, P x y`, for a
relation `P` between the tuple `x` of universally quantified values and the tuple `y` of
existentially quantified ones. -/
def ForallExistsAlt : (k : ℕ) → ((Fin k → α) → (Fin k → β) → Prop) → Prop
  | 0, P => P ![] ![]
  | k + 1, P => ∀ x, ∃ y, ForallExistsAlt k fun xs ys => P (Fin.cons x xs) (Fin.cons y ys)

/-- With no quantifiers, the alternation is the relation at the empty tuples. -/
@[simp]
theorem forallExistsAlt_zero {P : (Fin 0 → α) → (Fin 0 → β) → Prop} :
    ForallExistsAlt 0 P ↔ P ![] ![] :=
  Iff.rfl

/-- The outermost pair of quantifiers of an alternation. -/
theorem forallExistsAlt_succ {P : (Fin (k + 1) → α) → (Fin (k + 1) → β) → Prop} :
    ForallExistsAlt (k + 1) P ↔
      ∀ x, ∃ y, ForallExistsAlt k fun xs ys => P (Fin.cons x xs) (Fin.cons y ys) :=
  Iff.rfl

/-- A single alternation is `∀ x ∃ y, P x y`. -/
theorem forallExistsAlt_one {P : (Fin 1 → α) → (Fin 1 → β) → Prop} :
    ForallExistsAlt 1 P ↔ ∀ x, ∃ y, P ![x] ![y] :=
  Iff.rfl

/-- The innermost pair of quantifiers of an alternation. -/
theorem forallExistsAlt_succ' {P : (Fin (k + 1) → α) → (Fin (k + 1) → β) → Prop} :
    ForallExistsAlt (k + 1) P ↔
      ForallExistsAlt k fun xs ys => ∀ x, ∃ y, P (Fin.snoc xs x) (Fin.snoc ys y) := by
  induction k with
  | zero => simp [forallExistsAlt_one]
  | succ k ih =>
    rw [forallExistsAlt_succ, forallExistsAlt_succ]
    simp only [ih, Fin.cons_snoc_eq_snoc_cons]

/-- An alternation of quantifiers is monotone in the quantified relation. -/
theorem ForallExistsAlt.mono {P Q : (Fin k → α) → (Fin k → β) → Prop}
    (h : ForallExistsAlt k P) (hPQ : ∀ x y, P x y → Q x y) : ForallExistsAlt k Q := by
  induction k with
  | zero => exact hPQ _ _ h
  | succ k ih => exact fun x => (h x).imp fun y hy => ih hy fun xs ys => hPQ _ _

/-- Skolem functions respecting the order of the quantifiers witness an alternation: if the
`i`-th coordinate of `f x` depends only on the coordinates `x j` with `j ≤ i`, and `P x (f x)`
holds for every `x`, then `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1}, P x y`. -/
theorem forallExistsAlt_of_skolem {P : (Fin k → α) → (Fin k → β) → Prop}
    (f : (Fin k → α) → Fin k → β)
    (hf : ∀ i x x', (∀ j ≤ i, x j = x' j) → f x i = f x' i) (hP : ∀ x, P x (f x)) :
    ForallExistsAlt k P := by
  induction k with
  | zero => simpa [Subsingleton.elim (f ![]) ![]] using hP ![]
  | succ k ih =>
    intro x
    refine ⟨f (fun _ => x) 0, ih (fun xs i => f (Fin.cons x xs) i.succ) ?_ fun xs => ?_⟩
    · intro i xs xs' h
      refine hf i.succ _ _ fun j hj => ?_
      cases j using Fin.cases with
      | zero => rfl
      | succ j => simpa using h j (Fin.succ_le_succ_iff.mp hj)
    · have h0 : f (fun _ => x) 0 = f (Fin.cons x xs) 0 :=
        hf 0 _ _ fun j hj => by simp [Fin.le_zero_iff.mp hj]
      have hx := hP (Fin.cons x xs)
      rw [← Fin.cons_self_tail (f (Fin.cons x xs))] at hx
      rwa [h0]

/-- An alternation of quantifiers has Skolem functions respecting the order of the quantifiers:
a function `f` with `P x (f x)` for every `x` such that the `i`-th coordinate of `f x` depends
only on the coordinates `x j` with `j ≤ i`. -/
theorem ForallExistsAlt.exists_skolem {P : (Fin k → α) → (Fin k → β) → Prop}
    (h : ForallExistsAlt k P) :
    ∃ f : (Fin k → α) → Fin k → β,
      (∀ i x x', (∀ j ≤ i, x j = x' j) → f x i = f x' i) ∧ ∀ x, P x (f x) := by
  induction k with
  | zero =>
    exact ⟨fun _ => ![], fun i => i.elim0, fun x => by rwa [Subsingleton.elim x ![]]⟩
  | succ k ih =>
    choose y hy using h
    choose g hg hgP using fun x => ih (hy x)
    refine ⟨fun x => Fin.cons (y (x 0)) (g (x 0) (Fin.tail x)), fun i x x' hxx' => ?_,
      fun x => ?_⟩
    · have h0 : x 0 = x' 0 := hxx' 0 (Fin.zero_le _)
      cases i using Fin.cases with
      | zero => simp [h0]
      | succ i =>
        simp only [Fin.cons_succ, ← h0]
        exact hg (x 0) i _ _ fun j hj => hxx' j.succ (Fin.succ_le_succ_iff.mpr hj)
    · simpa using hgP (x 0) (Fin.tail x)

/-- An alternation `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1}, P x y` holds exactly when it has Skolem
functions respecting the order of the quantifiers: a function `f` with `P x (f x)` for every `x`
such that the `i`-th coordinate of `f x` depends only on the coordinates `x j` with `j ≤ i`. -/
theorem forallExistsAlt_iff_exists_skolem {P : (Fin k → α) → (Fin k → β) → Prop} :
    ForallExistsAlt k P ↔
      ∃ f : (Fin k → α) → Fin k → β,
        (∀ i x x', (∀ j ≤ i, x j = x' j) → f x i = f x' i) ∧ ∀ x, P x (f x) :=
  ⟨ForallExistsAlt.exists_skolem, fun ⟨f, hf, hP⟩ => forallExistsAlt_of_skolem f hf hP⟩

end TauCeti
