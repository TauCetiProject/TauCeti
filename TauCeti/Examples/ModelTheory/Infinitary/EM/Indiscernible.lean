/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.EM.Indiscernible
import TauCeti.ModelTheory.Order

/-!
# Regression examples: indiscernible sequences

* In `(ℕ, <)`, the identity sequence is indiscernible for `x₀ < x₁`: the formula holds at every
  increasing pair.
* In `(ℤ, <)`, the sequence `n ↦ (-1)ⁿ n`, with values `0, -1, 2, -3, …`, is not: `x₀ < x₁` holds
  at the index pair `(0, 2)` and fails at `(0, 1)`.
* Every sequence, over every index order, is indiscernible for every set of sentences: there is
  exactly one increasing `0`-tuple.
-/

open FirstOrder FirstOrder.Language

-- In `(ℕ, <)`, the identity sequence is indiscernible for `x₀ < x₁`.
example :
    letI := Language.orderStructure ℕ
    let lt : Language.order.BoundedFormulaω Empty 2 :=
      ((Term.var (Sum.inr 0)).lt (Term.var (Sum.inr 1)) :
        Language.order.BoundedFormula Empty 2).toInf
    IsIndiscernibleOn (id : ℕ → ℕ) {⟨2, lt⟩} := by
  let _ := Language.orderStructure ℕ
  intro lt
  rw [isIndiscernibleOn_iff]
  intro n ψ hψ s t
  cases hψ
  simp [lt, s.strictMono (show (0 : Fin 2) < 1 by decide),
    t.strictMono (show (0 : Fin 2) < 1 by decide)]

-- In `(ℤ, <)`, the sequence `0, -1, 2, -3, …` is not indiscernible for `x₀ < x₁`.
example :
    letI := Language.orderStructure ℤ
    let lt : Language.order.BoundedFormulaω Empty 2 :=
      ((Term.var (Sum.inr 0)).lt (Term.var (Sum.inr 1)) :
        Language.order.BoundedFormula Empty 2).toInf
    ¬ IsIndiscernibleOn (fun n : ℕ => (-1) ^ n * (n : ℤ)) {⟨2, lt⟩} := by
  let _ := Language.orderStructure ℤ
  intro lt h
  rw [isIndiscernibleOn_iff] at h
  have h02 := h rfl (OrderEmbedding.ofStrictMono ![0, 2] (Fin.strictMono_iff_lt_succ.2 (by decide)))
    (OrderEmbedding.ofStrictMono ![0, 1] (Fin.strictMono_iff_lt_succ.2 (by decide)))
  simp [lt] at h02

-- Every sequence is indiscernible for every set of sentences.
example {L : Language} {J M : Type*} [LE J] [L.Structure M] (a : J → M)
    (Δ : Set (Σ n, L.BoundedFormulaω Empty n)) (hΔ : ∀ p ∈ Δ, p.1 = 0) :
    IsIndiscernibleOn a Δ := by
  rw [isIndiscernibleOn_iff]
  intro n ψ hψ s t
  obtain rfl : n = 0 := hΔ _ hψ
  rw [Subsingleton.elim (a ∘ s) (a ∘ t)]
