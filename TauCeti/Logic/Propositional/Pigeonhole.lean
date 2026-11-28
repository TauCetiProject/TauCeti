/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Logic.Propositional.Clause
public import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Pigeonhole

/-!
# Pigeonhole formulas

The pigeonhole formula `pigeonhole m n` over the variables `Fin m × Fin n`, with the variable
`(i, j)` read as "pigeon `i` sits in hole `j`", says that every pigeon sits in some hole and that
no two pigeons share a hole. It is satisfiable exactly when `m ≤ n`, so for `n < m` it is an
unsatisfiable formula. It is a standard example formula in the study of resolution proofs.

## Main definitions

* `TauCeti.Propositional.pigeonhole m n`: the pigeonhole formula for `m` pigeons and `n` holes.

## Main results

* `TauCeti.Propositional.mem_pigeonhole`: the clauses of the pigeonhole formula.
* `TauCeti.Propositional.models_pigeonhole_iff`: the models of the pigeonhole formula.
* `TauCeti.Propositional.satisfiable_pigeonhole_iff`: the pigeonhole formula is satisfiable
  exactly when `m ≤ n`.
* `TauCeti.Propositional.pigeonhole_zero_left`, `TauCeti.Propositional.pigeonhole_zero_right`:
  with no pigeons the formula is empty, and with no holes it is the empty clause alone.
* `TauCeti.Propositional.card_pigeonhole`: for `n ≠ 0` the pigeonhole formula has
  `m + n * m.choose 2` clauses.
-/

public section

namespace TauCeti.Propositional

variable {m n : ℕ}

/-- The **pigeonhole formula** for `m` pigeons and `n` holes, over the variables `(i, j)` read as
"pigeon `i` sits in hole `j`". It has the clause `{(i, j) | j}` for each pigeon `i` and the clause
`{¬(i, j), ¬(i', j)}` for each hole `j` and each pair of pigeons `i < i'`. -/
def pigeonhole (m n : ℕ) : CNF (Fin m × Fin n) :=
  (Finset.univ.image fun i : Fin m ↦ Finset.univ.image fun j : Fin n ↦ ((i, j), true)) ∪
    ((Finset.univ : Finset (Fin m × Fin m × Fin n)).filter fun t ↦ t.1 < t.2.1).image fun t ↦
      {((t.1, t.2.2), false), ((t.2.1, t.2.2), false)}

/-- A clause of the pigeonhole formula says that the pigeon `i` sits in some hole, or that the
pigeons `i < i'` do not both sit in the hole `j`. -/
@[simp]
theorem mem_pigeonhole {C : Clause (Fin m × Fin n)} :
    C ∈ pigeonhole m n ↔
      (∃ i : Fin m, C = Finset.univ.image fun j : Fin n ↦ ((i, j), true)) ∨
        ∃ (i i' : Fin m) (j : Fin n), i < i' ∧ C = {((i, j), false), ((i', j), false)} := by
  simp only [pigeonhole, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_filter, Prod.exists, eq_comm]

/-- With no pigeons, the pigeonhole formula is empty. -/
@[simp]
theorem pigeonhole_zero_left (n : ℕ) : pigeonhole 0 n = ∅ := by
  simp [pigeonhole]

/-- With no holes and at least one pigeon, the pigeonhole formula is the empty clause alone. -/
theorem pigeonhole_zero_right (hm : m ≠ 0) : pigeonhole m 0 = {∅} := by
  have : NeZero m := ⟨hm⟩
  ext C
  simp

/-- For at least one hole, the pigeonhole formula has `m` pigeon clauses and `m.choose 2` hole
clauses for each of the `n` holes. -/
theorem card_pigeonhole (hn : n ≠ 0) : (pigeonhole m n).card = m + n * m.choose 2 := by
  have j₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  rw [pigeonhole, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_image_of_injOn, Finset.card_univ, Fintype.card_fin]
  · rw [Finset.card_nbij' (fun t ↦ ((t.1, t.2.1), t.2.2)) (fun t ↦ (t.1.1, t.1.2, t.2))
      (t := (Finset.univ.filter fun x : Fin m × Fin m ↦ x.1 < x.2) ×ˢ Finset.univ)
      (fun t ht ↦ by simpa using ht) (fun t ht ↦ by simpa using ht) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl), Finset.card_product, Fintype.card_product_filter_lt, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin, mul_comm]
  · rintro ⟨i, i', j⟩ hi ⟨k, k', l⟩ hk heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi hk
    have := Finset.coe_inj.mpr heq
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.pair_eq_pair_iff, Prod.mk.injEq,
      and_true] at this
    grind
  · intro i i' h
    have := Finset.mem_image_of_mem (fun j : Fin n ↦ ((i, j), true)) (Finset.mem_univ j₀)
    exact (by simpa [h] using this : i' = i).symm
  · refine Finset.disjoint_left.mpr fun C hC hC' ↦ ?_
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter] at hC hC'
    obtain ⟨i, rfl⟩ := hC
    obtain ⟨⟨k, k', l⟩, -, h⟩ := hC'
    have := Finset.mem_image_of_mem (fun j : Fin n ↦ ((i, j), true)) (Finset.mem_univ j₀)
    simp [← h] at this

/-- An assignment is a model of the pigeonhole formula exactly when it puts every pigeon in some
hole and no two pigeons in the same hole. -/
theorem models_pigeonhole_iff {τ : Fin m × Fin n → Bool} :
    Models τ (pigeonhole m n : Set (Clause (Fin m × Fin n))) ↔
      (∀ i, ∃ j, τ (i, j) = true) ∧ ∀ i i' j, i < i' → τ (i, j) = false ∨ τ (i', j) = false := by
  simp only [pigeonhole, models_iff, Finset.coe_union, Set.mem_union, Finset.mem_coe, or_imp,
    forall_and, Finset.forall_mem_image, Finset.mem_univ, Finset.mem_filter, true_and,
    forall_const, Prod.forall, satisfies_insert, satisfies_singleton]
  simp [satisfies_iff]

/-- The pigeonhole formula is satisfiable exactly when the `m` pigeons fit injectively into the
`n` holes, that is when `m ≤ n`. -/
theorem satisfiable_pigeonhole_iff (m n : ℕ) :
    Satisfiable (pigeonhole m n : Set (Clause (Fin m × Fin n))) ↔ m ≤ n := by
  refine ⟨fun hS ↦ ?_, fun h ↦ Models.satisfiable (τ := fun p ↦ decide (p.1.val = p.2.val)) ?_⟩
  · obtain ⟨τ, hτ⟩ := satisfiable_iff.mp hS
    obtain ⟨hpig, hhole⟩ := models_pigeonhole_iff.mp hτ
    choose f hf using hpig
    have hne : ∀ i i', i < i' → f i ≠ f i' := fun i i' hlt heq ↦ by
      have := hhole i i' (f i) hlt
      rw [hf, heq, hf] at this
      simp at this
    refine Fin.le_of_injective f fun i i' h ↦ ?_
    rcases lt_trichotomy i i' with hlt | rfl | hlt
    exacts [(hne _ _ hlt h).elim, rfl, (hne _ _ hlt h.symm).elim]
  · refine models_pigeonhole_iff.mpr ⟨fun i ↦ ⟨⟨i, i.isLt.trans_le h⟩, by simp⟩, ?_⟩
    intro i i' j hii'
    rw [Fin.lt_def] at hii'
    simp only [decide_eq_false_iff_not]
    omega

end TauCeti.Propositional
