/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Quantale
public import TauCeti.Data.EReal.Operations
import Mathlib.Order.GaloisConnection.Basic

/-!
# Additive residuation on extended real numbers

Extended real addition distributes over arbitrary suprema, including the empty supremum:
Mathlib's convention makes `⊥` absorbing. Thus `EReal` is an additive quantale, and Mathlib's
`AddQuantale.rightAddResiduation a c` is the largest `b` with `a + b ≤ c`.

This residual is safe subtraction for extended-cost dual constraints. It agrees with `c - a`
except that it is `⊤` when `c = ⊤` or `a = ⊥`. In particular the residual of `⊤` by `⊤`
is `⊤`, whereas ordinary `EReal` subtraction gives `⊥`.

The construction uses Mathlib's additive quantale and Galois connection APIs.
-/

public section

namespace EReal

/-- Extended real addition distributes over all suprema; its residual therefore gives a
right adjoint to addition without finiteness hypotheses. -/
instance instIsAddQuantale : IsAddQuantale EReal :=
  have hadd (a : EReal) (s : Set EReal) : a + sSup s = ⨆ b ∈ s, a + b :=
    GaloisConnection.l_sSup fun _ _ ↦ add_le_iff_le_ite (a := a)
  ⟨hadd, fun s a ↦ by simpa only [add_comm] using hadd a s⟩

/-- Additive residuation is ordinary subtraction except at the two unrestricted cases:
an infinite upper bound or an absorbing summand. -/
theorem rightAddResiduation_eq (a c : EReal) :
    AddQuantale.rightAddResiduation a c = if c = ⊤ ∨ a = ⊥ then ⊤ else c - a :=
  eq_of_forall_le_iff fun b ↦ by
    rw [AddQuantale.rightAddResiduation_le_iff_add_le, add_le_iff_le_ite]

/-- Subtracting an extended potential from a finite cost requires no exceptional convention. -/
@[simp]
theorem rightAddResiduation_coe (a : EReal) (c : ℝ) :
    AddQuantale.rightAddResiduation a (c : EReal) = (c : EReal) - a := by
  rw [rightAddResiduation_eq]
  by_cases ha : a = ⊥ <;> simp [ha]

/-- Shifting the summand by a real constant shifts its residual by the opposite constant. -/
theorem rightAddResiduation_add_coe (a c : EReal) (r : ℝ) :
    AddQuantale.rightAddResiduation (a + (r : EReal)) c =
      AddQuantale.rightAddResiduation a c - (r : EReal) := by
  apply eq_of_forall_le_iff
  intro b
  rw [AddQuantale.rightAddResiduation_le_iff_add_le,
    le_sub_iff_add_le (.inl (coe_ne_bot r)) (.inl (coe_ne_top r)),
    AddQuantale.rightAddResiduation_le_iff_add_le, add_right_comm, add_assoc]

end EReal
