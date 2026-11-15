/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Gluing periods on integer intervals

A sequence with period `p` on one closed interval and positive period `q` on another retains
period `p` on their union if the overlap contains at least `p + q` integer points. The periods
need not be coprime, and either interval may contain the other. This allows local periods to be
propagated along overlapping windows without replacing them by growing common multiples.

The supporting congruence lemma identifies values at any two congruent indices inside a
single interval. The gluing theorem counts both endpoints of the overlap.

## References

Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem* (2018), Lemma 7.
-/

public section

namespace TauCeti.Nat

/-- A sequence periodic on a closed interval has equal values at congruent indices in that
interval. The period may be zero, in which case congruence means equality. -/
theorem apply_eq_of_modEq_of_period_on_Icc {α : Type*} {f : ℕ → α} {p l r a b : ℕ}
    (h : ∀ t, l ≤ t → t + p ≤ r → f (t + p) = f t)
    (ha : a ∈ Set.Icc l r) (hb : b ∈ Set.Icc l r) (hab : a ≡ b [MOD p]) :
    f a = f b := by
  suffices ∀ a b, l ≤ a → b ≤ r → a ≤ b → a ≡ b [MOD p] → f a = f b by
    rcases le_total a b with hab' | hba'
    · exact this a b ha.1 hb.2 hab' hab
    · exact (this b a hb.1 ha.2 hba' hab.symm).symm
  intro a b hal hbr hab' hab
  obtain ⟨k, rfl⟩ := (Nat.modEq_iff_exists_eq_add hab').mp hab
  suffices ∀ k, a + p * k ≤ r → f (a + p * k) = f a by
    exact (this k hbr).symm
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc]
    intro hk
    exact (h _ (by omega) hk).trans (ih (by omega))

/-- If the overlap of two closed integer intervals contains at least the sum of their
periods, with the second period positive, the first period extends to the entire union.
In particular, the periods need not be coprime and nested intervals are allowed. -/
theorem period_on_Icc_min_max {α : Type*} {f : ℕ → α} {p q l r L R : ℕ}
    (hq : 0 < q)
    (h₁ : ∀ t, l ≤ t → t + p ≤ r → f (t + p) = f t)
    (h₂ : ∀ t, L ≤ t → t + q ≤ R → f (t + q) = f t)
    (hoverlap : p + q ≤ (Finset.Icc (max l L) (min r R)).card) :
    ∀ t, min l L ≤ t → t + p ≤ max r R → f (t + p) = f t := by
  rw [Nat.card_Icc] at hoverlap
  intro t ht htp
  by_cases hfirst : l ≤ t ∧ t + p ≤ r
  · exact h₁ t hfirst.1 hfirst.2
  have ht₂ : L ≤ t ∧ t + p ≤ R := by omega
  -- The overlap contains a whole block of q possible starting points for a p-step.
  have hmem : t % q ∈ (Finset.Ico (max l L) (max l L + q)).image (· % q) := by
    rw [Nat.image_Ico_mod]
    exact Finset.mem_range.mpr (Nat.mod_lt t hq)
  obtain ⟨y, hy, hyt⟩ := Finset.mem_image.mp hmem
  obtain ⟨hyl, hyq⟩ := Finset.mem_Ico.mp hy
  have hyr : y + p ≤ min r R := by omega
  have hty : t ≡ y [MOD q] := hyt.symm
  calc
    f (t + p) = f (y + p) := apply_eq_of_modEq_of_period_on_Icc h₂
      (by constructor <;> omega) (by constructor <;> omega) (hty.add_right p)
    _ = f y := h₁ y (by omega) (by omega)
    _ = f t := apply_eq_of_modEq_of_period_on_Icc h₂
      (by constructor <;> omega) (by constructor <;> omega) hty.symm

-- Two shared integer points suffice when both periods are one.
example {α : Type*} {f : ℕ → α}
    (h₁ : ∀ t, 2 ≤ t → t + 1 ≤ 5 → f (t + 1) = f t)
    (h₂ : ∀ t, 4 ≤ t → t + 1 ≤ 8 → f (t + 1) = f t) :
    ∀ t, 2 ≤ t → t + 1 ≤ 8 → f (t + 1) = f t := by
  exact period_on_Icc_min_max (by decide) h₁ h₂ (by decide)

-- A nested interval may carry a different, non-coprime period.
example {α : Type*} {f : ℕ → α}
    (h₁ : ∀ t, 6 ≤ t → t + 2 ≤ 12 → f (t + 2) = f t)
    (h₂ : ∀ t, 2 ≤ t → t + 4 ≤ 20 → f (t + 4) = f t) :
    ∀ t, 2 ≤ t → t + 2 ≤ 20 → f (t + 2) = f t := by
  exact period_on_Icc_min_max (by decide) h₁ h₂ (by decide)

-- Disjoint constant intervals do not determine one period on their union.
example :
    (∀ t, 0 ≤ t → t + 1 ≤ 2 → (if t + 1 ≤ 2 then 0 else 1 : ℕ) =
      (if t ≤ 2 then 0 else 1)) ∧
    (∀ t, 4 ≤ t → t + 1 ≤ 6 → (if t + 1 ≤ 2 then 0 else 1 : ℕ) =
      (if t ≤ 2 then 0 else 1)) ∧
    ¬ (∀ t, 0 ≤ t → t + 1 ≤ 6 → (if t + 1 ≤ 2 then 0 else 1 : ℕ) =
      (if t ≤ 2 then 0 else 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t _ ht
    split_ifs <;> omega
  · intro t ht _
    split_ifs <;> omega
  · intro h
    have := h 2 (by omega) (by omega)
    simp at this

end TauCeti.Nat
