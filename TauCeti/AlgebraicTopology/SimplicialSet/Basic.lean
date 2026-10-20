/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Simplicial identities with indices given by their values

Mathlib states the elementwise simplicial identities `SSet.δ_comp_σ_of_le_apply`,
`SSet.δ_comp_σ_of_gt_apply` and `SSet.δ_comp_δ_apply` with indices of the form `Fin.castSucc i`
and `Fin.succ i`. This file restates them with all indices as independent elements of `Fin`,
related only by equations between their values. This lets inductive arguments name indices such
as `⟨j.val - 1, _⟩` directly, without first rewriting them as successors.
-/

public section

universe u

open CategoryTheory Simplicial

namespace SSet

variable {X : SSet.{u}} {n : ℕ}

/-- `SSet.δ_comp_σ_of_le_apply` with indices given by their values: if `a < b`, then
`δ a ∘ σ b = σ (b - 1) ∘ δ a`. -/
lemma δ_comp_σ_of_val_lt_apply (a : Fin (n + 3)) (b : Fin (n + 2)) (a' : Fin (n + 2))
    (b' : Fin (n + 1)) (hab : a.val < b.val) (ha' : a'.val = a.val) (hb' : b'.val + 1 = b.val)
    (x : X _⦋n + 1⦌) :
    X.δ a (X.σ b x) = X.σ b' (X.δ a' x) := by
  obtain rfl : a = a'.castSucc := Fin.ext ha'.symm
  obtain rfl : b = b'.succ := Fin.ext (by simpa using hb'.symm)
  exact δ_comp_σ_of_le_apply (by rw [Fin.le_def]; simp at hab ⊢; omega) x

/-- `SSet.δ_comp_σ_of_gt_apply` with indices given by their values: if `b + 1 < a`, then
`δ a ∘ σ b = σ b ∘ δ (a - 1)`. -/
lemma δ_comp_σ_of_val_gt_apply (a : Fin (n + 3)) (b : Fin (n + 2)) (a' : Fin (n + 2))
    (b' : Fin (n + 1)) (hab : b.val + 1 < a.val) (ha' : a'.val + 1 = a.val)
    (hb' : b'.val = b.val) (x : X _⦋n + 1⦌) :
    X.δ a (X.σ b x) = X.σ b' (X.δ a' x) := by
  obtain rfl : a = a'.succ := Fin.ext (by simpa using ha'.symm)
  obtain rfl : b = b'.castSucc := Fin.ext hb'.symm
  exact δ_comp_σ_of_gt_apply (by rw [Fin.lt_def]; simp at hab ⊢; omega) x

/-- `SSet.δ_comp_δ_apply` with indices given by their values: if `a < b`, then
`δ a ∘ δ b = δ (b - 1) ∘ δ a`. -/
lemma δ_comp_δ_of_val_lt_apply (a b : Fin (n + 3)) (a' b' : Fin (n + 2)) (hab : a.val < b.val)
    (ha' : a'.val = a.val) (hb' : b'.val + 1 = b.val) (x : X _⦋n + 2⦌) :
    X.δ a' (X.δ b x) = X.δ b' (X.δ a x) := by
  obtain rfl : a = a'.castSucc := Fin.ext ha'.symm
  obtain rfl : b = b'.succ := Fin.ext (by simpa using hb'.symm)
  exact δ_comp_δ_apply (by rw [Fin.le_def]; simp at hab ⊢; omega) x

end SSet
