/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Entrywise maps and extensionality of matrices

This file complements `Matrix.map_injective` from Mathlib with its surjective counterpart, and
adds an extensionality lemma for matrices indexed by `Fin (m + 1)` and `Fin (n + 1)`.

## Main results

* `Matrix.map_map_surjInv`, `Matrix.map_surjective`: applying a surjective function entrywise is
  surjective on matrices. The lift by the chosen section `Function.surjInv` commutes with
  transposition, so it lifts symmetric matrices to symmetric matrices.
* `Matrix.ext_fin_succ`: matrices indexed by `Fin (m + 1)` and `Fin (n + 1)` are equal when their
  four blocks agree.
-/

public section

namespace Matrix

variable {m n α β : Type*}

/-- Lifting a matrix entrywise along the section `Function.surjInv hf` of a surjective `f` and
applying `f` again gives back the matrix. -/
theorem map_map_surjInv {f : α → β} (hf : Function.Surjective f) (M : Matrix m n β) :
    (M.map (Function.surjInv hf)).map f = M :=
  ext fun i j => Function.surjInv_eq hf (M i j)

/-- Applying a surjective function entrywise is surjective on matrices. -/
theorem map_surjective {f : α → β} (hf : Function.Surjective f) :
    Function.Surjective fun M : Matrix m n α => M.map f := fun M =>
  ⟨_, map_map_surjInv hf M⟩

/-- Two matrices indexed by `Fin (m + 1)` and `Fin (n + 1)` are equal when their four blocks
agree: the corner `(0, 0)`, the rest of row `0`, the rest of column `0`, and the indices
`(Fin.succ, Fin.succ)`. -/
theorem ext_fin_succ {m n : ℕ} {M N : Matrix (Fin (m + 1)) (Fin (n + 1)) α}
    (h₀₀ : M 0 0 = N 0 0) (h₀ₛ : ∀ j : Fin n, M 0 j.succ = N 0 j.succ)
    (hₛ₀ : ∀ i : Fin m, M i.succ 0 = N i.succ 0)
    (hₛₛ : ∀ (i : Fin m) (j : Fin n), M i.succ j.succ = N i.succ j.succ) :
    M = N := by
  ext p q
  induction p using Fin.cases <;> induction q using Fin.cases
  exacts [h₀₀, h₀ₛ _, hₛ₀ _, hₛₛ _ _]

end Matrix
