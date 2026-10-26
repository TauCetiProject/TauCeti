/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Quantale
public import Mathlib.Data.EReal.Operations
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

noncomputable section

namespace TauCeti

/-- Extended real addition distributes over all suprema; its residual therefore gives a
right adjoint to addition without finiteness hypotheses. -/
instance : IsAddQuantale EReal := by
  have hadd (a : EReal) (s : Set EReal) : a + sSup s = ⨆ b ∈ s, a + b := by
    induction a with
    | bot => simp
    | coe a =>
      have hgc : GaloisConnection (fun b : EReal ↦ (a : EReal) + b)
          (fun c : EReal ↦ c - (a : EReal)) := fun b c ↦ by
        simp only [add_comm]
        exact (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot a))
          (.inl (EReal.coe_ne_top a))).symm
      exact hgc.l_sSup
    | top =>
      by_cases hs : sSup s = ⊥
      · have hmem := sSup_eq_bot.mp hs
        rw [hs]
        simp only [EReal.add_bot]
        symm
        exact iSup_eq_bot.mpr fun b ↦ iSup_eq_bot.mpr fun hb ↦ by simp [hmem b hb]
      · rw [EReal.top_add_of_ne_bot hs]
        obtain ⟨b, hb, hb'⟩ := not_forall₂.mp (mt sSup_eq_bot.mpr hs)
        symm
        apply top_unique
        calc (⊤ : EReal) = ⊤ + b := (EReal.top_add_of_ne_bot hb').symm
             _ ≤ ⨆ y ∈ s, (⊤ : EReal) + y := le_iSup_of_le b (le_iSup_of_le hb le_rfl)
  exact ⟨hadd, fun s a ↦ by simpa only [add_comm] using hadd a s⟩

/-- Additive residuation is ordinary subtraction except at the two unrestricted cases:
an infinite upper bound or an absorbing summand. -/
theorem _root_.EReal.rightAddResiduation_eq (a c : EReal) :
    AddQuantale.rightAddResiduation a c = if c = ⊤ ∨ a = ⊥ then ⊤ else c - a := by
  apply le_antisymm
  · by_cases h : c = ⊤ ∨ a = ⊥
    · simp [h]
    · rw [ite_eq_right h, EReal.le_sub_iff_add_le (Or.inl (not_or.mp h).2)
        (Or.inr (not_or.mp h).1), add_comm]
      exact AddQuantale.rightAddResiduation_le_iff_add_le.mp le_rfl
  · rw [AddQuantale.rightAddResiduation_le_iff_add_le]
    by_cases h : c = ⊤ ∨ a = ⊥
    · rcases h with rfl | rfl <;> simp
    · simp only [ite_eq_right h]
      rw [add_comm]
      exact EReal.add_le_of_le_sub le_rfl

/-- Subtracting an extended potential from a finite cost requires no exceptional convention. -/
@[simp]
theorem _root_.EReal.rightAddResiduation_coe (a : EReal) (c : ℝ) :
    AddQuantale.rightAddResiduation a (c : EReal) = (c : EReal) - a := by
  rw [EReal.rightAddResiduation_eq]
  by_cases ha : a = ⊥ <;> simp [ha]

/-- An infinite cost imposes no bound on the other potential, even if this potential is `⊤`. -/
@[simp]
theorem _root_.EReal.rightAddResiduation_top (a : EReal) :
    AddQuantale.rightAddResiduation a (⊤ : EReal) = ⊤ := by
  simp [EReal.rightAddResiduation_eq]

/-- The absorbing summand `⊥` imposes no bound on the other summand. -/
@[simp]
theorem _root_.EReal.rightAddResiduation_bot (c : EReal) :
    AddQuantale.rightAddResiduation (⊥ : EReal) c = ⊤ := by
  simp [EReal.rightAddResiduation_eq]

/-- Shifting the summand by a real constant shifts its residual by the opposite constant. -/
theorem _root_.EReal.rightAddResiduation_add_coe (a c : EReal) (r : ℝ) :
    AddQuantale.rightAddResiduation (a + (r : EReal)) c =
      AddQuantale.rightAddResiduation a c - (r : EReal) := by
  apply eq_of_forall_le_iff
  intro b
  rw [AddQuantale.rightAddResiduation_le_iff_add_le,
    EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot r)) (.inl (EReal.coe_ne_top r)),
    AddQuantale.rightAddResiduation_le_iff_add_le, add_right_comm, add_assoc]

end TauCeti
