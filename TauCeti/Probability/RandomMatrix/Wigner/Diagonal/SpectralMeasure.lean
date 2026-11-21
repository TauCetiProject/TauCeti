/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.SpectralMeasure.Diagonal
public import TauCeti.Probability.RandomMatrix.Wigner.Basic

/-!
# Weak spectral limits of Wigner corners with a random diagonal

Wigner matrices and their zero-diagonal versions have the same almost-sure weak spectral
limits when the diagonal entries are identically distributed and pairwise independent.
This separates the diagonal law from the finite-second-moment off-diagonal hypotheses
in the semicircle law.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), proof of Theorem 2.1.
-/

public section

open Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- A Wigner family with an identically distributed, pairwise independent real diagonal has
the same weak spectral limits as its zero-diagonal version, almost surely, without any
diagonal moment assumption. The upper entries may be arbitrary and may depend on the diagonal. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix_zero_iff
    (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    (hindep : Pairwise fun i j ↦ IndepFun (η i) (η j) P)
    (hid : ∀ i, IdentDistrib (η i) (η 0) P P) :
    ∀ᵐ ω ∂P, ∀ μ : ProbabilityMeasure ℝ,
      Tendsto (fun n ↦ (wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1))) atTop (𝓝 μ) ↔
      Tendsto (fun n ↦ (wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1))) atTop (𝓝 μ) := by
  have h := ae_tendsto_spectralMeasure_add_diagonal_div_iff
    (fun n ω ↦ wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω)
    (fun n ω ↦ wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1))
    η hindep hid (fun n ↦ Real.sqrt n)
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [h] with ω hω
  simpa only [wignerMatrix_eq_add_diagonal ξ η, RCLike.ofReal_eq_complex_ofReal] using
    fun μ ↦ (hω μ).symm

end TauCeti.Probability
