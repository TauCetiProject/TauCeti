/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.MeasureTheory.Covering.EssentialBoundary
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Sets stable under a half-space of translations

Let `ν` be a vector of a real inner product space `E`. A set `S ⊆ E` with `S + h ⊆ S` for every
`h` with `⟪h, ν⟫ ≤ 0` is determined by the values of `⟪·, ν⟫` on it, and these form a lower set of
`ℝ`. Hence `S` is empty, the whole space, an open half-space `{y | ⟪y, ν⟫ < c}` or a closed
half-space `{y | ⟪y, ν⟫ ≤ c}` (`TauCeti.eq_setOf_inner_lt_or_le_of_forall_inner_nonpos`).

The measure-theoretic form holds against an additive Haar measure `μ` on a finite-dimensional
space. If a null-measurable set `s` satisfies `x + h ∈ s` for `μ`-almost every `x ∈ s`, for each
such `h` separately, then `s` agrees almost everywhere with `∅`, with `univ` or with an open
half-space `{y | ⟪y, ν⟫ < c}` (`TauCeti.ae_eq_setOf_inner_lt_of_forall_inner_nonpos`). The
exceptional null sets may depend on `h`. The proof replaces `s` by its essential interior, which is
a.e. equal to `s` by Lebesgue's density theorem and commutes with translations, so it is stable
under the translations exactly. A hyperplane is null, so the open and closed half-spaces agree
almost everywhere.

This is how a set of locally finite perimeter with a constant outer normal is identified with a
half-space, the rigidity step in the blow-up of sets of finite perimeter at points of the
reduced boundary.

## Main declarations

* `TauCeti.eq_setOf_inner_lt_or_le_of_forall_inner_nonpos`: the exact classification.
* `TauCeti.ae_eq_setOf_inner_lt_of_forall_inner_nonpos`: the almost-everywhere classification.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.2.
-/

public section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ν : E}

/-- **Sets stable under a half-space of translations.** If `x + h ∈ S` whenever `x ∈ S` and
`⟪h, ν⟫ ≤ 0`, then `S` is empty, the whole space, or a half-space `{y | ⟪y, ν⟫ < c}` or
`{y | ⟪y, ν⟫ ≤ c}`. -/
theorem eq_setOf_inner_lt_or_le_of_forall_inner_nonpos {S : Set E}
    (hS : ∀ h, ⟪h, ν⟫ ≤ 0 → ∀ x ∈ S, x + h ∈ S) :
    S = ∅ ∨ S = univ ∨ ∃ c, S = {y | ⟪y, ν⟫ < c} ∨ S = {y | ⟪y, ν⟫ ≤ c} := by
  rcases eq_or_ne ν 0 with rfl | hν
  · -- For `ν = 0` every translation preserves `S`, so it is empty or the whole space.
    rcases S.eq_empty_or_nonempty with hS0 | ⟨x, hx⟩
    · exact Or.inl hS0
    · exact Or.inr (Or.inl (eq_univ_of_forall fun y => by simpa using hS (y - x) (by simp) x hx))
  set T := (fun y => ⟪y, ν⟫) '' S
  have hν2 : ⟪ν, ν⟫ ≠ 0 := inner_self_ne_zero.2 hν
  -- Membership in `S` only depends on `⟪·, ν⟫`, whose values on `S` form a lower set.
  have hmem (y : E) : y ∈ S ↔ ⟪y, ν⟫ ∈ T := by
    refine ⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxy⟩
    simpa using hS (y - x) (by simp [inner_sub_left, ← hxy]) x hx
  have hlow {t t' : ℝ} (htt' : t ≤ t') (ht' : t' ∈ T) : t ∈ T := by
    obtain ⟨x, hx, rfl⟩ := ht'
    refine ⟨x + ((t - ⟪x, ν⟫) / ⟪ν, ν⟫) • ν, hS _ ?_ x hx, ?_⟩
    · rw [real_inner_smul_left, div_mul_cancel₀ _ hν2]
      linarith
    · simp only [inner_add_left, real_inner_smul_left, div_mul_cancel₀ _ hν2]
      ring
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact Or.inl (eq_empty_of_forall_notMem fun y hy => by simpa [hT] using (hmem y).1 hy)
  by_cases hbdd : BddAbove T
  · refine Or.inr (Or.inr ⟨sSup T, ?_⟩)
    by_cases hc : sSup T ∈ T
    · refine Or.inr (ext fun y => ?_)
      rw [hmem, mem_ofPred_eq]
      exact ⟨fun h => le_csSup hbdd h, fun h => hlow h hc⟩
    · refine Or.inl (ext fun y => ?_)
      rw [hmem, mem_ofPred_eq]
      refine ⟨fun h => (le_csSup hbdd h).lt_of_ne fun he => hc (he ▸ h), fun h => ?_⟩
      obtain ⟨t, ht, hlt⟩ := exists_lt_of_lt_csSup hT h
      exact hlow hlt.le ht
  · refine Or.inr (Or.inl (eq_univ_of_forall fun y => (hmem y).2 ?_))
    obtain ⟨t, ht, hlt⟩ := not_bddAbove_iff.1 hbdd ⟪y, ν⟫
    exact hlow hlt.le ht

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- For `ν ≠ 0`, a closed half-space agrees almost everywhere with the open one, since the
hyperplane `{y | ⟪y, ν⟫ = c}` is null for an additive Haar measure. -/
theorem setOf_inner_le_ae_eq_setOf_inner_lt (hν : ν ≠ 0) (c : ℝ) :
    {y : E | ⟪y, ν⟫ ≤ c} =ᵐ[μ] {y | ⟪y, ν⟫ < c} := by
  refine ae_eq_set.2 ⟨measure_mono_null (fun y hy => ?_) (Measure.addHaar_setOf_inner_eq μ hν c),
    measure_mono_null (fun y hy => ?_) measure_empty⟩
  · exact le_antisymm hy.1 (not_lt.1 hy.2)
  · simp only [mem_sdiff, mem_ofPred_eq, not_le] at hy
    linarith [hy.1, hy.2]

/-- **Sets almost stable under a half-space of translations.** Let `μ` be an additive Haar
measure and `s` a null-measurable set such that, for every `h` with `⟪h, ν⟫ ≤ 0`, almost every
`x ∈ s` has `x + h ∈ s`. Then `s` agrees almost everywhere with `∅`, with `univ` or with an open
half-space `{y | ⟪y, ν⟫ < c}`. -/
theorem ae_eq_setOf_inner_lt_of_forall_inner_nonpos {s : Set E} (hs : NullMeasurableSet s μ)
    (H : ∀ h, ⟪h, ν⟫ ≤ 0 → ∀ᵐ x ∂μ, x ∈ s → x + h ∈ s) :
    s =ᵐ[μ] (∅ : Set E) ∨ s =ᵐ[μ] (univ : Set E) ∨ ∃ c : ℝ, s =ᵐ[μ] {y | ⟪y, ν⟫ < c} := by
  set S := essentialInterior μ s
  have hSs : s =ᵐ[μ] S := (essentialInterior_ae_eq hs).symm
  -- The essential interior is stable under these translations, without exceptional sets.
  have hS (h : E) (hh : ⟪h, ν⟫ ≤ 0) (x : E) (hx : x ∈ S) : x + h ∈ S := by
    have hle : s ≤ᵐ[μ] (· + h) ⁻¹' s := H h hh
    simpa [S, essentialInterior_preimage_add_right] using essentialInterior_mono_ae hle hx
  rcases eq_setOf_inner_lt_or_le_of_forall_inner_nonpos hS with h0 | h1 | ⟨c, hc | hc⟩
  · exact Or.inl (hSs.trans (h0 ▸ Filter.EventuallyEq.rfl))
  · exact Or.inr (Or.inl (hSs.trans (h1 ▸ Filter.EventuallyEq.rfl)))
  · exact Or.inr (Or.inr ⟨c, hSs.trans (hc ▸ Filter.EventuallyEq.rfl)⟩)
  rcases eq_or_ne ν 0 with rfl | hν
  · -- For `ν = 0` the closed half-space `{y | 0 ≤ c}` is empty or the whole space.
    by_cases hc0 : 0 ≤ c
    · exact Or.inr (Or.inl (hSs.trans (by simp [hc, hc0])))
    · exact Or.inl (hSs.trans (by simp [hc, hc0]))
  · exact Or.inr (Or.inr ⟨c, (hSs.trans (hc ▸ Filter.EventuallyEq.rfl)).trans
      (setOf_inner_le_ae_eq_setOf_inner_lt hν c)⟩)

end TauCeti
