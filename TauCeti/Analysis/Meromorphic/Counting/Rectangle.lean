/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Exact additivity of counts in imaginary height

Rectangles are closed in their real coordinate and half open in their imaginary coordinate.
Thus a zero on a splitting edge contributes to precisely one of the two pieces. Meromorphy
on the containing closed rectangle supplies finite divisor support, including at its edges.
-/

public section

open Set Complex

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {U : Set ℂ} {σ₁ σ₂ t₁ t₂ t₃ : ℝ}

private theorem rectangle_partition (hf : MeromorphicOn f U)
    (ht12 : t₁ ≤ t₂) (ht23 : t₂ ≤ t₃)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₃ ⊆ U) :
    ((Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) ∪ (Icc σ₁ σ₂ ×ℂ Ioc t₂ t₃) =
      Icc σ₁ σ₂ ×ℂ Ioc t₁ t₃) ∧
    Disjoint (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) (Icc σ₁ σ₂ ×ℂ Ioc t₂ t₃) ∧
    ((Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) ∩ Function.support (MeromorphicOn.divisor f U)).Finite ∧
    ((Icc σ₁ σ₂ ×ℂ Ioc t₂ t₃) ∩ Function.support (MeromorphicOn.divisor f U)).Finite := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [← preimage_equivRealProd_prod, ← preimage_union, ← prod_union,
      Ioc_union_Ioc_eq_Ioc ht12 ht23]
  · exact disjoint_left.mpr fun z hz hz' ↦
      disjoint_left.mp (Ioc_disjoint_Ioc_of_le le_rfl) hz.2 hz'.2
  · apply hf.divisor_finite_inter_support_of_isCompact
      (isCompact_Icc.reProdIm isCompact_Icc) hU
    intro z hz
    exact ⟨hz.1, le_of_lt hz.2.1, hz.2.2.trans ht23⟩
  · apply hf.divisor_finite_inter_support_of_isCompact
      (isCompact_Icc.reProdIm isCompact_Icc) hU
    intro z hz
    exact ⟨hz.1, ht12.trans (le_of_lt hz.2.1), hz.2.2⟩

/-- Splitting a half-open rectangle in imaginary height adds the signed counts exactly.
Meromorphy on the containing closed rectangle suffices; no boundary nonvanishing is required. -/
theorem divisorCount_reProdIm_Ioc_eq_add (hf : MeromorphicOn f U)
    (ht12 : t₁ ≤ t₂) (ht23 : t₂ ≤ t₃)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₃ ⊆ U) :
    divisorCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₃) =
      divisorCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) +
        divisorCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₂ t₃) := by
  obtain ⟨hsplit, hdisjoint, hfirst, hsecond⟩ := rectangle_partition hf ht12 ht23 hU
  rw [← hsplit]
  exact divisorCount_union hdisjoint hfirst hsecond

/-- Splitting a half-open rectangle in imaginary height adds the natural zero counts exactly.
Zeros on the splitting edge belong to the lower piece and are counted only once. -/
theorem zeroCount_reProdIm_Ioc_eq_add (hf : MeromorphicOn f U)
    (ht12 : t₁ ≤ t₂) (ht23 : t₂ ≤ t₃)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₃ ⊆ U) :
    zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₃) =
      zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) +
        zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₂ t₃) := by
  obtain ⟨hsplit, hdisjoint, hfirst, hsecond⟩ := rectangle_partition hf ht12 ht23 hU
  rw [← hsplit]
  exact zeroCount_union hdisjoint hfirst hsecond

end TauCeti
