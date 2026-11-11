/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm

/-!
# The trace against a bounded coefficient field in `Lᵖ`

Let `V` be a finite-dimensional inner product space. For an `Lᵖ` field `G` of endomorphisms of
`V` vanishing off a set `K`, and an almost everywhere strongly measurable coefficient field `A`
with `‖A x‖ ≤ Λ` on `K`, the trace `tr (A ∘ G)` lies in `Lᵖ` with norm at most
`dim V * Λ * ‖G‖_{Lᵖ}` (`TauCeti.exists_lp_traceCLM_comp_le`). This applies the pointwise bound
`‖tr T‖ ≤ dim V * ‖T‖` (`ContinuousLinearMap.norm_traceCLM_le`).

This is how the lower-order terms produced by localizing a non-divergence-form equation
`tr (A ∘ D²u) = f` with a cutoff are controlled in `Lᵖ`.
-/

public section

namespace TauCeti

open Module MeasureTheory
open scoped ENNReal

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **The trace against a bounded coefficient field is bounded in `Lᵖ`.** Let `G` be an `Lᵖ` field
of endomorphisms of `V` vanishing off a set `K`, and let `A` be an almost everywhere strongly
measurable field of endomorphisms with `‖A x‖ ≤ Λ` almost everywhere on `K`. Then `tr (A ∘ G)`
lies in `Lᵖ`, with norm at most `dim V * Λ * ‖G‖`. -/
theorem exists_lp_traceCLM_comp_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {K : Set α} {A : α → V →L[𝕜] V} {Λ : ℝ}
    (hA : AEStronglyMeasurable A μ) (hAΛ : ∀ᵐ x ∂μ, x ∈ K → ‖A x‖ ≤ Λ) (G : Lp (V →L[𝕜] V) p μ)
    (hG : ∀ᵐ x ∂μ, x ∉ K → G x = 0) :
    ∃ g : Lp 𝕜 p μ, (∀ᵐ x ∂μ, g x = traceCLM 𝕜 V (A x ∘L G x)) ∧
      ‖g‖ ≤ finrank 𝕜 V * Λ * ‖G‖ := by
  have hmeas : AEStronglyMeasurable (fun x => traceCLM 𝕜 V (A x ∘L G x)) μ :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun B M : V →L[𝕜] V => traceCLM 𝕜 V (B ∘L M))
      ((traceCLM 𝕜 V).continuous.comp (continuous_fst.clm_comp continuous_snd)) hA
      (Lp.aestronglyMeasurable G)
  have hle : ∀ᵐ x ∂μ, ‖traceCLM 𝕜 V (A x ∘L G x)‖ ≤ finrank 𝕜 V * Λ * ‖G x‖ := by
    filter_upwards [hG, hAΛ] with x h1 h2
    by_cases hx : x ∈ K
    · calc ‖traceCLM 𝕜 V (A x ∘L G x)‖ ≤ finrank 𝕜 V * ‖A x ∘L G x‖ :=
            ContinuousLinearMap.norm_traceCLM_le _
        _ ≤ finrank 𝕜 V * (Λ * ‖G x‖) := by
            gcongr
            exact ((A x).opNorm_comp_le (G x)).trans (by gcongr; exact h2 hx)
        _ = finrank 𝕜 V * Λ * ‖G x‖ := by ring
    · rw [h1 hx, ContinuousLinearMap.comp_zero, map_zero, norm_zero, norm_zero, mul_zero]
  have hmem := (Lp.memLp G).of_le_mul hmeas hle
  exact ⟨hmem.toLp _, hmem.coeFn_toLp, Lp.norm_le_mul_norm_of_ae_le_mul
    (by filter_upwards [hmem.coeFn_toLp, hle] with x h1 h2; rwa [h1])⟩

end TauCeti
