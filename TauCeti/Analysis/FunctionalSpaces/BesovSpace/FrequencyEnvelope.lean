/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Basic
public import TauCeti.Analysis.SpecificLimits.FrequencyEnvelope

/-!
# Frequency envelopes in homogeneous Besov spaces

The weighted block sizes `a_k = 2^{ks} ‖P_k u‖_{Lᵖ}`, `k ∈ ℤ`, of an element `u` of the
homogeneous Besov space `\dot B^s_{p,2}` form a square-summable sequence whose `ℓ²` norm is
`‖u‖_{\dot B^s_{p,2}}`. The construction `TauCeti.exists_isFrequencyEnvelope_of_summable_sq` of
admissible frequency envelopes for `ℓ²` sequences therefore applies to them. For `p = 2` this is
the homogeneous Sobolev space `\dot H^s = \dot B^s_{2,2}`.

## Main results

* `TauCeti.HomogeneousBesovSpace.exists_isFrequencyEnvelope`: for every `u ∈ \dot B^s_{p,2}` the
  weighted block sizes `2^{ks} ‖P_k u‖_{Lᵖ}` have a frequency envelope `c` that is
  `(-σ₁, σ₂)`-admissible, with `‖c‖_{ℓ²} ≲ ‖u‖_{\dot B^s_{p,2}}` and a constant independent of
  `u`.

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436
  (2022), arXiv:1709.08599, Section 3 (frequency envelopes).
-/

public section

open scoped ENNReal

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Admissible envelopes in `\dot B^s_{p,2}`.** For rates `δ > 0`, `σ₁(1 - ε) > 0` and
`σ₂(1 - ε) > 0` there is a constant `C` such that the weighted block sizes `2^{ks} ‖P_k u‖_{Lᵖ}`
of every `u ∈ \dot B^s_{p,2}` have a frequency envelope `c` with rate `δ` that is
`(-σ₁, σ₂)`-admissible and has `‖c‖_{ℓ²}² ≤ C ‖u‖_{\dot B^s_{p,2}}²`. For `p = 2` this covers
`\dot H^s = \dot B^s_{2,2}`. -/
theorem HomogeneousBesovSpace.exists_isFrequencyEnvelope {δ σ₁ σ₂ ε : ℝ} (hδ : 0 < δ)
    (h₁ : 0 < σ₁ * (1 - ε)) (h₂ : 0 < σ₂ * (1 - ε)) :
    ∃ C, ∀ u : HomogeneousBesovSpace F φ s p 2, ∃ c,
      IsFrequencyEnvelope δ (fun k ↦ 2 ^ (s * k) * ‖u.block k‖) c ∧
        IsAdmissibleEnvelope σ₁ σ₂ ε c ∧ Summable (fun k ↦ c k ^ 2) ∧
          ∑' k, c k ^ 2 ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨C, hC⟩ := exists_isFrequencyEnvelope_of_summable_sq hδ h₁ h₂
  refine ⟨C, fun u ↦ ?_⟩
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsq : ∀ k : ℤ, (2 : ℝ) ^ (s * k) * ‖u.block k‖ = ‖u.weightedBlocks k‖ := fun k ↦
    (u.norm_weightedBlocks_apply k).symm
  have hsum := (lp.memℓp u.weightedBlocks).summable h2
  have hnorm := lp.norm_rpow_eq_tsum h2 u.weightedBlocks
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_weightedBlocks] at hsum hnorm
  simp only [hsq]
  rw [hnorm]
  exact hC _ hsum

end TauCeti
