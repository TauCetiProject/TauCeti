/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Decreasing filtrations by two-sided ideals

An `AlgFiltration` is a multiplicative decreasing family of two-sided ideals,
starting with the whole semiring. Multiplication may be noncommutative. For rings,
these are the filtrations used to form inverse limits of quotient rings.

The same family carries Mathlib's `IsRingFiltration` on the order dual of the
natural numbers; its strict part at `k` is the ideal at `k + 1`.

Adapted from `yuma-mizuno-lean/Mei`, commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`,
`Mei/RingTheory/FilteredAlgebra/Basic.lean` (Apache 2.0).
-/

public section

namespace TauCeti

/-- A decreasing multiplicative filtration of an associative semiring by two-sided ideals. -/
@[ext]
structure AlgFiltration (A : Type*) [Semiring A] where
  /-- Terms of filtration order at least `k`. -/
  ideal : ℕ → Ideal A
  /-- Every term is two-sided, so ring quotients inherit multiplication. -/
  isTwoSided : ∀ k, (ideal k).IsTwoSided
  /-- Higher orders give smaller ideals. -/
  antitone : Antitone ideal
  /-- Every element has order at least zero. -/
  ideal_zero : ideal 0 = ⊤
  /-- Multiplication adds filtration orders. -/
  mul_mem : ∀ {a b : ℕ} {x y : A}, x ∈ ideal a → y ∈ ideal b → x * y ∈ ideal (a + b)

namespace AlgFiltration

variable {A : Type*} [Semiring A] (F : AlgFiltration A)

attribute [instance] isTwoSided
attribute [simp] ideal_zero

/-- The decreasing family, viewed with increasing order-dual indices. -/
def orderDual : ℕᵒᵈ → Ideal A := fun k => F.ideal k.ofDual

/-- Evaluation of the order-dual family. -/
@[simp]
theorem orderDual_apply (k : ℕᵒᵈ) : F.orderDual k = F.ideal k.ofDual := (rfl)

/-- The ideal filtration is a ring filtration in Mathlib's sense. -/
instance instIsRingFiltration :
    IsRingFiltration F.orderDual (fun k => F.ideal (k.ofDual + 1)) where
  mono _ _ h := F.antitone h
  is_le := by
    intro i j h
    exact F.antitone (Nat.succ_le_of_lt h)
  is_sup B j h := h (OrderDual.toDual (j.ofDual + 1)) (Nat.lt_succ_self _)
  one_mem := by simp
  mul_mem := fun {_ _ _ _} hx hy => F.mul_mem hx hy

end AlgFiltration
end TauCeti

namespace Ideal

variable {A : Type*} [Semiring A]

/-- Powers of a two-sided ideal give a decreasing multiplicative filtration. -/
def algFiltration (I : Ideal A) [I.IsTwoSided] : TauCeti.AlgFiltration A where
  ideal k := I ^ k
  isTwoSided _ := inferInstance
  antitone := fun _ _ h => Ideal.pow_le_pow_right h
  ideal_zero := by simp
  mul_mem {a b} {x y} hx hy := by
    rw [Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul hx hy

/-- The terms of the ideal-adic filtration are the powers of its ideal. -/
@[simp]
theorem algFiltration_ideal (I : Ideal A) [I.IsTwoSided] (k : ℕ) :
    I.algFiltration.ideal k = I ^ k := (rfl)

end Ideal
