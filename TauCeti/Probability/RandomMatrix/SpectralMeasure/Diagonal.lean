/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Diagonal
public import TauCeti.Probability.StrongLaw

/-!
# Weak spectral limits under a random diagonal perturbation

Adding a real i.i.d. diagonal divided by a normalization tending to infinity preserves almost
sure weak spectral limits of Hermitian matrix families. Pairwise independence of the diagonal
coordinates suffices. No diagonal moment, centering, or independence from the matrix family is
required. The full-measure event works for every limiting probability measure at once.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), proof of Theorem 2.1.
-/

public section

open Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- Adding an identically distributed, pairwise independent real diagonal divided by any
normalization tending to infinity preserves weak spectral limits almost surely. There is no
moment assumption on the diagonal and no independence assumption involving the matrices. -/
theorem ae_tendsto_spectralMeasure_add_diagonal_div_iff {𝕜 : Type*} [RCLike 𝕜]
    (A : (n : ℕ) → Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)
    (hA : ∀ n ω, (A n ω).IsHermitian) (η : ℕ → Ω → ℝ)
    (hindep : Pairwise fun i j ↦ IndepFun (η i) (η j) P)
    (hid : ∀ i, IdentDistrib (η i) (η 0) P P)
    (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) :
    ∀ᵐ ω ∂P, ∀ μ : ProbabilityMeasure ℝ,
      Tendsto (fun n ↦
        (A n ω + diagonal (fun i : Fin (n + 1) ↦ ((η i ω / b (n + 1) : ℝ) : 𝕜))).spectralMeasure
          ((hA n ω).add (isHermitian_diagonal_ofReal _)))
        atTop (𝓝 μ) ↔
      Tendsto (fun n ↦ (A n ω).spectralMeasure (hA n ω)) atTop (𝓝 μ) := by
  classical
  filter_upwards [ae_tendsto_card_filter_norm_gt_div η hindep hid] with ω hω
  intro μ
  apply Matrix.tendsto_spectralMeasure_add_diagonal_iff
  intro ε hε
  have hlarge := hω (fun n ↦ ε * b n) (hb.const_mul_atTop hε)
  have hshift := hlarge.comp (tendsto_add_atTop_nat 1)
  apply hshift.congr'
  filter_upwards [((hb.comp (tendsto_add_atTop_nat 1)).eventually
    (eventually_gt_atTop 0))] with n hn
  simp only [Function.comp_apply] at hn
  simp only [Function.comp_apply, Fintype.card_fin, Real.norm_eq_abs]
  congr 1
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.1 hi, abs_div, abs_of_pos hn, lt_div_iff₀ hn]

end TauCeti.Probability
