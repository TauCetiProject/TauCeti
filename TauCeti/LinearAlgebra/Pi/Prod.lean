/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import TauCeti.Algebra.Group.Equiv.Pi

/-!
# Families of pairs as pairs of families

A family of pairs `x : ∀ i, M i × N i` is the pair of families `(fun i ↦ (x i).1, fun i ↦ (x i).2)`.
This is the additive equivalence `TauCeti.AddEquiv.arrowProdEquivProdArrow`, which is also linear:
`(∀ i, M i × N i) ≃ₗ[R] (∀ i, M i) × (∀ i, N i)` (`TauCeti.LinearEquiv.arrowProdEquivProdArrow`).
-/

public section

namespace TauCeti.LinearEquiv

variable (R : Type*) [Semiring R] {ι : Type*} (M N : ι → Type*) [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- `TauCeti.AddEquiv.arrowProdEquivProdArrow` as a linear equivalence: a family of pairs is a pair
of families. -/
def arrowProdEquivProdArrow : ((i : ι) → M i × N i) ≃ₗ[R] ((i : ι) → M i) × ((i : ι) → N i) :=
  (TauCeti.AddEquiv.arrowProdEquivProdArrow M N).toLinearEquiv fun _ _ ↦ by
    ext <;> simp

variable {R M N}

@[simp]
theorem arrowProdEquivProdArrow_apply (x : (i : ι) → M i × N i) :
    arrowProdEquivProdArrow R M N x = (fun i ↦ (x i).1, fun i ↦ (x i).2) := by
  simp [arrowProdEquivProdArrow]

@[simp]
theorem arrowProdEquivProdArrow_symm_apply (y : ((i : ι) → M i) × ((i : ι) → N i)) :
    (arrowProdEquivProdArrow R M N).symm y = fun i ↦ (y.1 i, y.2 i) := by
  simp [arrowProdEquivProdArrow]

variable (R M N) in
@[simp]
theorem toAddEquiv_arrowProdEquivProdArrow :
    (arrowProdEquivProdArrow R M N).toAddEquiv = TauCeti.AddEquiv.arrowProdEquivProdArrow M N :=
  AddEquiv.ext fun _ ↦ by simp

end TauCeti.LinearEquiv
