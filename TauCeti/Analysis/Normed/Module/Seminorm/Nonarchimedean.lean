/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Operations preserving nonarchimedean seminorms

Basic algebraic and lattice operations on seminorms that preserve the ultrametric inequality
`p (x + y) ≤ max (p x) (p y)`.

## Main results

* `IsNonarchimedean.smul_seminorm`: nonnegative scalar multiples of a nonarchimedean seminorm are
  nonarchimedean.
* `IsNonarchimedean.sup_seminorm`: binary suprema of nonarchimedean seminorms are nonarchimedean.
* `TauCeti.isNonarchimedean_finsetSup`: finite suprema of nonarchimedean seminorms are
  nonarchimedean.
-/

public section

open scoped NNReal

section Operations

variable {R V : Type*} [SeminormedRing R] [AddGroup V] [SMul R V]

namespace IsNonarchimedean

/-- Scaling a nonarchimedean seminorm by a nonnegative real preserves the ultrametric
inequality. -/
theorem smul_seminorm {p : Seminorm R V} (hp : IsNonarchimedean p) (c : ℝ≥0) :
    IsNonarchimedean (c • p) := fun x y ↦ by
  simp only [FunLike.coe_smul, Pi.smul_apply, NNReal.smul_def, smul_eq_mul]
  exact (mul_le_mul_of_nonneg_left (hp x y) c.property).trans_eq (mul_max_of_nonneg _ _ c.property)

/-- The pointwise supremum of two nonarchimedean seminorms is nonarchimedean. -/
theorem sup_seminorm {p q : Seminorm R V} (hp : IsNonarchimedean p) (hq : IsNonarchimedean q) :
    IsNonarchimedean (p ⊔ q) := fun x y ↦ by
  simp only [Pi.sup_apply, sup_le_iff]
  exact ⟨(hp x y).trans (max_le_max le_sup_left le_sup_left),
    (hq x y).trans (max_le_max le_sup_right le_sup_right)⟩

end IsNonarchimedean

end Operations

section FinsetSup

variable {R V ι : Type*} [SeminormedRing R] [AddCommGroup V] [Module R V]

/-- A finite supremum of nonarchimedean seminorms is nonarchimedean. -/
theorem TauCeti.isNonarchimedean_finsetSup {p : ι → Seminorm R V} {s : Finset ι}
    (hp : ∀ i ∈ s, IsNonarchimedean (p i)) : IsNonarchimedean (s.sup p : Seminorm R V) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x y
    simp [Seminorm.bot_eq_zero]
  | insert a t _ ih =>
    rw [Finset.sup_insert]
    exact (hp a (Finset.mem_insert_self a t)).sup_seminorm
      (ih fun i hi ↦ hp i (Finset.mem_insert_of_mem hi))

end FinsetSup
