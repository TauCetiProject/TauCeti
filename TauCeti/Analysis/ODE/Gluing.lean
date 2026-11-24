/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Gluing solutions of an ODE across a window

A solution of `Θ' = v t (Θ t)` is often built from three pieces: a solution on `t ≤ a`, one on a
compact window `[a, b]` (for instance from the Picard–Lindelöf theorem, which only gives a
one-sided derivative at the ends of the window), and one on `t ≥ b`. If the pieces agree at the
junctions, the glued function solves the equation with a two-sided derivative everywhere, because
the one-sided derivatives at `a` and `b` are both `v t (Θ t)`.

## Main results

* `TauCeti.exists_eq_hasDerivAt_of_hasDerivWithinAt_Icc`: the glued function solves the
  equation at every parameter where the pieces do.
-/

public section

open Set Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Gluing solutions across a window.** Let `a ≤ b`, let `W` solve `Θ' = v t (Θ t)` on the
window `[a, b]`, let `E₀` solve it within `t ≤ a` at the parameters `t ∈ I` with `t ≤ a`, and
let `E₁` solve it within `t ≥ b` at those with `t ≥ b`, with `E₀ a = W a` and `W b = E₁ b`. Then
the function equal to `E₀` for `t ≤ a`, to `W` on the window and to `E₁` for `t ≥ b` solves the
equation at every parameter in `I`: the one-sided derivatives match at the junctions. -/
theorem exists_eq_hasDerivAt_of_hasDerivWithinAt_Icc {v : ℝ → F → F} {a b : ℝ}
    {E₀ W E₁ : ℝ → F} {I : Set ℝ} (hab : a ≤ b) (ha : E₀ a = W a) (hb : W b = E₁ b)
    (hE₀ : ∀ t ∈ I, t ≤ a → HasDerivWithinAt E₀ (v t (E₀ t)) (Iic a) t)
    (hW : ∀ t ∈ Icc a b, HasDerivWithinAt W (v t (W t)) (Icc a b) t)
    (hE₁ : ∀ t ∈ I, b ≤ t → HasDerivWithinAt E₁ (v t (E₁ t)) (Ici b) t) :
    ∃ Θ : ℝ → F, (∀ t ≤ a, Θ t = E₀ t) ∧ (∀ t ∈ Icc a b, Θ t = W t) ∧
      (∀ t, b ≤ t → Θ t = E₁ t) ∧ ∀ t ∈ I, HasDerivAt Θ (v t (Θ t)) t := by
  set Θ : ℝ → F := fun t ↦ if t ≤ a then E₀ t else if t ≤ b then W t else E₁ t
  have hΘ₀ : ∀ t ≤ a, Θ t = E₀ t := fun t ht ↦ by simp only [Θ, ht, ↓reduceIte]
  have hΘW : ∀ t ∈ Icc a b, Θ t = W t := fun t ht ↦ by
    rcases ht.1.eq_or_lt with rfl | h
    · rw [hΘ₀ _ le_rfl, ha]
    · simp only [Θ, not_le.2 h, ht.2, ↓reduceIte]
  have hΘ₁ : ∀ t, b ≤ t → Θ t = E₁ t := fun t ht ↦ by
    rcases ht.eq_or_lt with rfl | h
    · rw [hΘW _ ⟨hab, le_rfl⟩, hb]
    · simp only [Θ, not_le.2 (hab.trans_lt h), not_le.2 h, ↓reduceIte]
  -- The derivatives of the three pieces, as derivatives of `Θ` within their intervals.
  have hleft : ∀ t ∈ I, t ≤ a → HasDerivWithinAt Θ (v t (Θ t)) (Iic a) t := fun t ht hta ↦ by
    rw [hΘ₀ t hta]
    exact (hE₀ t ht hta).congr (fun y hy ↦ hΘ₀ y hy) (hΘ₀ t hta)
  have hmid : ∀ t ∈ Icc a b, HasDerivWithinAt Θ (v t (Θ t)) (Icc a b) t := fun t ht ↦ by
    rw [hΘW t ht]
    exact (hW t ht).congr (fun y hy ↦ hΘW y hy) (hΘW t ht)
  have hright : ∀ t ∈ I, b ≤ t → HasDerivWithinAt Θ (v t (Θ t)) (Ici b) t := fun t ht htb ↦ by
    rw [hΘ₁ t htb]
    exact (hE₁ t ht htb).congr (fun y hy ↦ hΘ₁ y hy) (hΘ₁ t htb)
  refine ⟨Θ, hΘ₀, hΘW, hΘ₁, fun t ht ↦ ?_⟩
  rcases lt_trichotomy t a with h | rfl | h
  · exact (hleft t ht h.le).hasDerivAt (Iic_mem_nhds h)
  · rw [← hasDerivWithinAt_univ, ← Iic_union_Ici]
    rcases hab.eq_or_lt with rfl | hab'
    · exact (hleft t ht le_rfl).union (hright t ht le_rfl)
    · exact (hleft t ht le_rfl).union
        ((hmid t ⟨le_rfl, hab⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab'))
  rcases lt_trichotomy t b with h' | rfl | h'
  · exact (hmid t ⟨h.le, h'.le⟩).hasDerivAt (Icc_mem_nhds h h')
  · rw [← hasDerivWithinAt_univ, ← Iic_union_Ici]
    exact ((hmid t ⟨hab, le_rfl⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE h)).union (hright t ht le_rfl)
  · exact (hright t ht h'.le).hasDerivAt (Ici_mem_nhds h')

end TauCeti
