/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Transport of integrals over the range of a map along a measure-preserving equivalence

If `e : α ≃ᵐ β` is measure preserving, then integrability and the value of the integral of `g`
over the range of `f : γ → β` are those of `g ∘ e` over the range of `e.symm ∘ f`.
-/

public section

open Set MeasureTheory

variable {α β γ F : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Transport along a measure-preserving measurable equivalence `e` of integrability and of the
integral over the range of `f`: the range of `e.symm ∘ f` is the preimage under `e` of the range of
`f`. No measurability of the range is needed. -/
theorem MeasureTheory.MeasurePreserving.integrableOn_range_and_setIntegral_range
    {e : α ≃ᵐ β} (h : MeasurePreserving e μ ν) {f : γ → β} (g : β → F)
    (hgi : IntegrableOn (g ∘ e) (range (e.symm ∘ f)) μ) :
    IntegrableOn g (range f) ν ∧
      ∫ y in range (e.symm ∘ f), g (e y) ∂μ = ∫ z in range f, g z ∂ν := by
  rw [range_comp, e.image_symm] at hgi ⊢
  exact ⟨(h.integrableOn_comp_preimage e.measurableEmbedding).mp hgi,
    h.setIntegral_preimage_emb e.measurableEmbedding g _⟩
