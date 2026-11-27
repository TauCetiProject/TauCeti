/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.EM.SkolemTower
import TauCeti.ModelTheory.Order

/-!
# Regression examples: one step of the Skolem tower

The arity convention at `n = 0`: a one-variable formula `ψ(x₀)` gets a constant symbol, and its
witness axiom says that the constant witnesses `∃y ψ(y)` when that holds. In `(ℕ, ≤)`, with `ψ(x₀)`
the formula `∀y (x₀ ≤ y)` saying that `x₀` is least, the witness axiom holds when the constant is
`0` and fails when it is `1`.
-/

open FirstOrder FirstOrder.Language

-- At `n = 0` the witness axiom says that the constant witnesses `∃y ψ(y)` when that holds.
example {L : Language} {M : Type*} [L.Structure M] {Γ : Set (Σ n, L.BoundedFormulaω Empty n)}
    [(skolemLanguage Γ).Structure M] (f : (skolemLanguage Γ).Functions 0) :
    SentenceInf.Realize (skolemWitnessAxiom f) M ↔
      ((∃ y : M, f.val.Realize Empty.elim ![y]) →
        f.val.Realize Empty.elim ![Structure.funMap f (default : Fin 0 → M)]) := by
  have h (y : M) : Fin.snoc (default : Fin 0 → M) y = ![y] :=
    funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl
  rw [realize_skolemWitnessAxiom, Unique.forall_iff]
  simp only [h]

-- In `(ℕ, ≤)`, the constant `0` witnesses the least-element formula `∀y (x₀ ≤ y)`.
example :
    let ψ : Language.order.BoundedFormulaω Empty 1 :=
      (((Term.var (Sum.inr 0)).le (Term.var (Sum.inr 1)) :
        Language.order.BoundedFormula Empty 2).all).toInf
    let f : (skolemLanguage {⟨1, ψ⟩}).Functions 0 := ⟨ψ, rfl⟩
    letI := Language.orderStructure ℕ
    letI : (skolemLanguage {⟨1, ψ⟩}).Structure ℕ := ⟨fun _ _ => 0, fun r => isEmptyElim r⟩
    SentenceInf.Realize (skolemWitnessAxiom f) ℕ := by
  intro ψ f
  let _ := Language.orderStructure ℕ
  let _ : (skolemLanguage {⟨1, ψ⟩}).Structure ℕ := ⟨fun _ _ => 0, fun r => isEmptyElim r⟩
  rw [realize_skolemWitnessAxiom]
  intro xs _
  simp only [f, ψ, BoundedFormula.realize_toInf, BoundedFormula.realize_all,
    Term.realize_le]
  exact fun y => Nat.zero_le y

-- The constant `1` does not: `0` is least, but `1` is not.
example :
    let ψ : Language.order.BoundedFormulaω Empty 1 :=
      (((Term.var (Sum.inr 0)).le (Term.var (Sum.inr 1)) :
        Language.order.BoundedFormula Empty 2).all).toInf
    let f : (skolemLanguage {⟨1, ψ⟩}).Functions 0 := ⟨ψ, rfl⟩
    letI := Language.orderStructure ℕ
    letI : (skolemLanguage {⟨1, ψ⟩}).Structure ℕ := ⟨fun _ _ => 1, fun r => isEmptyElim r⟩
    ¬ SentenceInf.Realize (skolemWitnessAxiom f) ℕ := by
  intro ψ f
  let _ := Language.orderStructure ℕ
  let _ : (skolemLanguage {⟨1, ψ⟩}).Structure ℕ := ⟨fun _ _ => 1, fun r => isEmptyElim r⟩
  rw [realize_skolemWitnessAxiom]
  intro h
  have := h default ⟨0, by
    simp only [f, ψ, BoundedFormula.realize_toInf, BoundedFormula.realize_all,
      Term.realize_le]
    exact fun y => Nat.zero_le y⟩
  simp only [f, ψ, BoundedFormula.realize_toInf, BoundedFormula.realize_all,
    Term.realize_le] at this
  exact absurd (this 0 : 1 ≤ 0) (by decide)
