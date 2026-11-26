/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.Conjugation
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Conjugation on the Besov spaces

A continuous conjugate-linear map `L : F →L⋆[ℂ] G`, for instance complex conjugation on `ℂ`, acts
on `F`-valued tempered distributions by `(L u) ψ = L (u (conj ψ))`
(`TemperedDistribution.conjPostcompCLM`). The `j`-th Littlewood–Paley block `Δⱼ` is the Fourier
multiplier by the `j`-th piece `ψⱼ` of the inhomogeneous Littlewood–Paley partition, a real and
even function, so it commutes with this action
(`TemperedDistribution.littlewoodPaleyBlock_conjPostcompCLM`). On `Lᵖ` functions the action is
`f ↦ L ∘ f`, of norm at most `‖L‖`. Hence `L` maps the Besov space `B^s_{p,q}(E, F)` into
`B^s_{p,q}(E, G)` (`TemperedDistribution.MemBesov.conjPostcompCLM`): the blocks of `L u` are the
`Lᵖ` functions `L ∘ Δⱼ u`.

In particular the complex conjugate and the real part of a scalar tempered distribution in
`B^s_{p,q}` are again in `B^s_{p,q}`. This is the input for describing the Besov spaces of
sections of real vector bundles, whose chart components are real parts of complex tempered
distributions.

## Main declarations

* `TemperedDistribution.littlewoodPaleyBlock_conjPostcompCLM`: `Δⱼ (L u) = L (Δⱼ u)`.
* `TemperedDistribution.MemBesov.conjPostcompCLM`: conjugate-linear maps preserve `B^s_{p,q}`.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap ComplexConjugate

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

namespace TemperedDistribution

/-- **The Littlewood–Paley blocks commute with conjugate-linear maps.** The symbol `ψⱼ` of the
block `Δⱼ` is real and even, so `Δⱼ (L u) = L (Δⱼ u)`. -/
@[simp]
theorem littlewoodPaleyBlock_conjPostcompCLM (φ : ContDiffBump (0 : E)) (j : ℕ)
    (L : F →L⋆[ℂ] G) (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock G φ j (conjPostcompCLM L u) =
      conjPostcompCLM L (littlewoodPaleyBlock F φ j u) := by
  rw [littlewoodPaleyBlock_apply, littlewoodPaleyBlock_apply,
    fourierMultiplierCLM_conjPostcompCLM L
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j)]
  simp [φ.inhomogeneousLittlewoodPaley_neg]

variable [CompleteSpace F] [CompleteSpace G]

/-- **Conjugate-linear maps preserve the Besov spaces.** If `u ∈ B^s_{p,q}(E, F)` and
`L : F →L⋆[ℂ] G` is a continuous conjugate-linear map, then `L u ∈ B^s_{p,q}(E, G)`: its blocks are
the `Lᵖ` functions `L ∘ Δⱼ u`. -/
theorem MemBesov.conjPostcompCLM {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (L : F →L⋆[ℂ] G) :
    (conjPostcompCLM L u).MemBesov φ s p q := by
  obtain ⟨f, hf, hmem⟩ := memBesov_iff.1 hu
  refine memBesov_iff.2 ⟨fun j ↦ L.compLp (f j), fun j ↦ ?_,
    (hmem.const_mul ‖L‖).mono fun j ↦ ?_⟩
  · rw [littlewoodPaleyBlock_conjPostcompCLM, hf j, conjPostcompCLM_toTemperedDistribution_eq]
  · rw [Real.norm_of_nonneg (by positivity), mul_left_comm]
    gcongr
    exact L.norm_compLp_le (f j)

end TemperedDistribution
