/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Gluing solutions of an ODE across a window

A solution of `Θ' = v t (Θ t)` is often built from three pieces: a solution on `t ≤ a`, one on a
compact window `[a, b]` (for instance from the Picard–Lindelöf theorem, which only gives a
one-sided derivative at the ends of the window), and one on `t ≥ b`. If the pieces agree at the
junctions, the glued function solves the equation with a two-sided derivative everywhere, because
the one-sided derivatives at `a` and `b` are both `v t (Θ t)`. Similarly, an autonomous integral
curve on `[a, s]` can be concatenated with a translated integral curve on `[0, b)` at the matching
time `s`.

## Main results

* `TauCeti.exists_eq_hasDerivAt_of_hasDerivWithinAt_Icc`: the glued function solves the
  equation at every parameter where the pieces do.
* `TauCeti.hasDerivWithinAt_ite_Ico`: concatenation of an integral curve on `[a, s]` with a
  translated integral curve on `[0, b)` into an integral curve on `[a, s + b)`.
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

/-- Concatenating an integral curve `γ₁` of `X` on `[a, s]` with an integral curve `γ₂` of `X` on
`[0, b)` starting at `γ₂ 0 = γ₁ s` yields an integral curve of `X` on `[a, s + b)`. -/
theorem hasDerivWithinAt_ite_Ico (X : F → F) {γ₁ γ₂ : ℝ → F} {a s b u : ℝ}
    (h0₂ : γ₂ 0 = γ₁ s)
    (hγ₁' : ∀ t ∈ Icc a s, HasDerivWithinAt γ₁ (X (γ₁ t)) (Icc a s) t)
    (hγ₂' : ∀ t ∈ Ico 0 b, HasDerivWithinAt γ₂ (X (γ₂ t)) (Ico 0 b) t)
    (hu : u ∈ Ico a (s + b)) :
    HasDerivWithinAt (fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s))
      (X ((fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s)) u)) (Ico a (s + b)) u := by
  set γ : ℝ → F := fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s)
  rcases lt_trichotomy u s with hus | rfl | hsu
  · have hγu : γ u = γ₁ u := ite_eq_left hus.le
    have hd := (hγ₁' u ⟨hu.1, hus.le⟩).mono_of_mem_nhdsWithin (s := Ico a (s + b))
      (mem_nhdsWithin.mpr ⟨Iio s, isOpen_Iio, hus, fun _ hr ↦ ⟨hr.2.1, hr.1.le⟩⟩)
    exact (hγu ▸ hd).congr_of_eventuallyEq
      (Filter.mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds hus))
        fun _ hr ↦ ite_eq_left (mem_Iio.mp hr).le) hγu
  · have hγs : γ u = γ₁ u := ite_eq_left le_rfl
    have hb : 0 < b := by linarith [hu.2]
    have hleft : HasDerivWithinAt γ (X (γ u)) (Icc a u) u :=
      (hγs ▸ hγ₁' u ⟨hu.1, le_rfl⟩).congr (fun _ hr ↦ ite_eq_left hr.2) hγs
    have hright : HasDerivWithinAt γ (X (γ u)) (Ico u (u + b)) u := by
      have hd₂ := HasDerivWithinAt.scomp_of_eq (s := Ico u (u + b)) u
        (hγ₂' 0 ⟨le_rfl, hb⟩) ((hasDerivAt_id u).sub_const u).hasDerivWithinAt
        (fun _ hr ↦ ⟨sub_nonneg.mpr hr.1, sub_lt_iff_lt_add'.mpr hr.2⟩) (sub_self u).symm
      simp only [Function.comp_def, id_eq, h0₂, one_smul, ← hγs] at hd₂
      refine hd₂.congr (fun r hr ↦ ?_) (by simp [γ, h0₂])
      rcases hr.1.eq_or_lt with rfl | hsr
      · simp [γ, h0₂]
      · exact ite_eq_right (not_le_of_gt hsr)
    have hboth : HasDerivWithinAt γ (X (γ u)) (Icc a u ∪ Ico u (u + b)) u :=
      hleft.union hright
    rwa [Icc_union_Ico_eq_Ico hu.1 hu.2] at hboth
  · have hγu : γ u = γ₂ (u - s) := ite_eq_right (not_le_of_gt hsu)
    have hd₂ := ((hγ₂' (u - s) ⟨by linarith, by linarith [hu.2]⟩).hasDerivAt
      (Ico_mem_nhds (by linarith) (by linarith [hu.2]))).comp_sub_const u s
    exact (hγu ▸ hd₂.hasDerivWithinAt).congr_of_eventuallyEq
      (Filter.mem_of_superset (nhdsWithin_le_nhds (Ioi_mem_nhds hsu))
        fun _ hr ↦ ite_eq_right (not_le_of_gt (mem_Ioi.mp hr))) hγu

end TauCeti
