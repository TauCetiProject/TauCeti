/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus
public import TauCeti.Analysis.Sobolev.Torus.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.DyadicSymbol

/-!
# Periodic Bessel-potential spaces between periodic Besov spaces

On the torus `𝕋ᵈ = UnitAddTorus d` the Bessel potential `J^s` of order `s : ℝ` multiplies the
Fourier coefficients by `⟨n⟩^s = (1 + ‖n‖²)^{s/2}`. For `1 ≤ p ≤ ∞`, a formal Fourier series
`c : ℤᵈ → ℂ` lies in the **periodic Bessel-potential space** `H^{s,p}(𝕋ᵈ)`
(`TauCeti.UnitAddTorus.MemSobolev s p c`) when `J^s c` is the Fourier series of a function in
`Lᵖ(𝕋ᵈ)`: some `f ∈ Lᵖ(𝕋ᵈ)` has `f̂(n) = ⟨n⟩^s c(n)` for every `n`. At `s = 0` these are the
coefficient sequences of the functions in `Lᵖ(𝕋ᵈ)` (`TauCeti.UnitAddTorus.memSobolev_zero_iff`).
The predicate and its linear structure are in `TauCeti.Analysis.Sobolev.Torus.Basic`.

This file proves that `H^{s,p}(𝕋ᵈ)` lies between two periodic Besov spaces with the same
smoothness and integrability,

`B^s_{p,1}(𝕋ᵈ) ⊆ H^{s,p}(𝕋ᵈ) ⊆ B^s_{p,∞}(𝕋ᵈ)`,

for every bump function `φ` defining the blocks `Δⱼ` of `TauCeti.UnitAddTorus.MemBesov`, every
`s : ℝ` and every `1 ≤ p ≤ ∞`, with norm bounds. This is the periodic counterpart of
`TemperedDistribution.MemBesov.memSobolev` and `TemperedDistribution.MemSobolev.memBesov` on `ℝᵈ`.

## The argument

Both inclusions rest on the localized estimate `‖J^s Δⱼ c‖_p ≤ C 2^{js} ‖Δⱼ c‖_p`, with `C`
independent of `j`, `p` and `c`. On the support of the piece `ψⱼ` the symbol `⟨ξ⟩^s` agrees with a
Schwartz function `σⱼ` whose kernel has `‖𝓕⁻ σⱼ‖_{L¹(ℝᵈ)} ≤ C 2^{js}`
(`ContDiffBump.exists_mul_inhomogeneousLittlewoodPaley_eq_one_add_norm_sq_rpow_mul`), and the
Fourier multiplier on `𝕋ᵈ` with the symbol `σⱼ` sampled on `ℤᵈ` is bounded on `Lᵖ(𝕋ᵈ)` by
`‖𝓕⁻ σⱼ‖_{L¹(ℝᵈ)}` (`TauCeti.UnitAddTorus.eLpNorm_tsum_mul_mFourierCoeff_mul_mFourier_le`).

* If `f̂ = ⟨·⟩^s c` with `f ∈ Lᵖ(𝕋ᵈ)`, then `Δⱼ c` is the multiplier with the symbol `⟨·⟩^{-s}`,
  localized to the piece `ψⱼ`, applied to the block `Δⱼ f̂`. The blocks are bounded on `Lᵖ(𝕋ᵈ)`
  uniformly in `j` (`TauCeti.UnitAddTorus.exists_norm_littlewoodPaleyBlockLp_mFourierCoeff_le`),
  so `2^{js} ‖Δⱼ c‖_p ≤ C ‖f‖_p` for every `j`: this is `c ∈ B^s_{p,∞}(𝕋ᵈ)`.
* If the weighted block norms `2^{js} ‖Δⱼ c‖_p` are summable, then by the localized estimate the
  trigonometric polynomials `gⱼ = J^s Δⱼ c` are summable in `Lᵖ(𝕋ᵈ)`, which is complete. Every
  Fourier coefficient is a continuous functional on `Lᵖ(𝕋ᵈ)`, so the sum `f = ∑ⱼ gⱼ` has
  `f̂(n) = ∑ⱼ ψⱼ(n) ⟨n⟩^s c(n) = ⟨n⟩^s c(n)`, since the pieces `ψⱼ` sum to one: this is
  `c ∈ H^{s,p}(𝕋ᵈ)`.

Composing the two inclusions with the strict monotonicity of the Besov scale shows that
`H^{s,p}(𝕋ᵈ)` decreases in `s` (`TauCeti.UnitAddTorus.MemSobolev.of_le`).

As in `TauCeti.UnitAddTorus.MemBesov`, `Lᵖ(𝕋ᵈ)` is taken for the product of the Haar probability
measures on the circle factors.

## Main declarations

* `TauCeti.UnitAddTorus.memSobolev_of_finite_support`: the trigonometric polynomials lie in
  `H^{s,p}(𝕋ᵈ)`.
* `TauCeti.UnitAddTorus.exists_rpow_mul_norm_littlewoodPaleyBlockLp_le_of_mFourierCoeff_eq` and
  `TauCeti.UnitAddTorus.MemSobolev.memBesov`: `H^{s,p}(𝕋ᵈ) ⊆ B^s_{p,∞}(𝕋ᵈ)`.
* `TauCeti.UnitAddTorus.exists_mFourierCoeff_eq_and_norm_le_tsum_of_memBesov` and
  `TauCeti.UnitAddTorus.MemBesov.memSobolev`: `B^s_{p,1}(𝕋ᵈ) ⊆ H^{s,p}(𝕋ᵈ)`.
* `TauCeti.UnitAddTorus.MemSobolev.of_le`: `H^{s,p}(𝕋ᵈ) ⊆ H^{s',p}(𝕋ᵈ)` for `s' ≤ s`.

## References

* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (the periodic Besov and Bessel-potential spaces).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Theorem 6.2.4 (the inclusions
  on `ℝᵈ`, whose proof is followed here).
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- The periodic Littlewood–Paley blocks and `H^{s,p}(𝕋ᵈ)` live on `Lᵖ` for the product of the Haar
-- probability measures on the circle factors, given by this instance.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

variable {s : ℝ} {p : ℝ≥0∞} {c : (d → ℤ) → ℂ} {φ : ContDiffBump (0 : EuclideanSpace ℝ d)}

/-! ### `H^{s,p}(𝕋ᵈ) ⊆ B^s_{p,∞}(𝕋ᵈ)` -/

variable (φ) in
/-- **`H^{s,p}(𝕋ᵈ) ⊆ B^s_{p,∞}(𝕋ᵈ)`, quantitatively.** There is `C ≥ 0`, depending only on `φ` and
`s`, such that for every `1 ≤ p ≤ ∞`: if the Fourier coefficients of `f ∈ Lᵖ(𝕋ᵈ)` are
`f̂(n) = (1 + ‖n‖²)^{s/2} c(n)`, then `2^{js} ‖Δⱼ c‖_p ≤ C ‖f‖_p` for every `j`. -/
theorem exists_rpow_mul_norm_littlewoodPaleyBlockLp_le_of_mFourierCoeff_eq (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : (d → ℤ) → ℂ)
      (f : Lp ℂ p (volume : Measure (UnitAddTorus d))),
      (∀ n, mFourierCoeff f n = (((1 + ‖latticePoint n‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * c n) →
      ∀ j : ℕ, 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j c‖ ≤ C * ‖f‖ := by
  obtain ⟨C₁, hC₁, hblock⟩ := exists_norm_littlewoodPaleyBlockLp_mFourierCoeff_le φ
  obtain ⟨C₂, hC₂⟩ := φ.exists_mul_inhomogeneousLittlewoodPaley_eq_one_add_norm_sq_rpow_mul (-s)
  choose σ hσ hσC using hC₂
  refine ⟨max C₂ 0 * C₁, by positivity, fun p _ c f hf j ↦ ?_⟩
  -- `Δⱼ c` is the multiplier with the symbol `σⱼ`, equal to `⟨ξ⟩^{-s}` near the support of `ψⱼ`,
  -- applied to the block `Δⱼ f̂`.
  have h := norm_littlewoodPaleyBlockLp_le_of_mul_eq (c := c) (σ j) j
    (littlewoodPaleyBlockLp φ p j (mFourierCoeff f)) fun n ↦ by
      -- The Bessel weights of orders `-s` and `s` are inverse to each other.
      have hw : (((1 + ‖latticePoint n‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) *
          (((1 + ‖latticePoint n‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity), neg_div, neg_add_cancel,
          Real.rpow_zero, Complex.ofReal_one]
      rw [mFourierCoeff_littlewoodPaleyBlockLp, hf n, ← mul_assoc, hσ j]
      linear_combination (-(φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n) * hw
  -- `2^{js} 2^{-js} = 1`.
  have h2 : (2 : ℝ) ^ (s * j) * ((2 : ℝ) ^ j) ^ (-s) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos]
    simp [mul_comm]
  calc 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j c‖
      ≤ 2 ^ (s * j) * ((max C₂ 0 * ((2 : ℝ) ^ j) ^ (-s)) * (C₁ * ‖f‖)) := by
        gcongr
        refine h.trans ?_
        gcongr
        · exact (hσC j).trans (by gcongr; exact le_max_left _ _)
        · exact hblock p j f
    _ = max C₂ 0 * C₁ * ‖f‖ := by
        linear_combination (max C₂ 0 * C₁ * ‖f‖) * h2

/-- **`H^{s,p}(𝕋ᵈ) ⊆ B^s_{p,∞}(𝕋ᵈ)`.** -/
theorem MemSobolev.memBesov [Fact (1 ≤ p)] (hc : MemSobolev s p c)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ d)) : MemBesov φ s p ∞ c := by
  obtain ⟨C, -, hC⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_le_of_mFourierCoeff_eq φ s
  obtain ⟨f, hf⟩ := memSobolev_def.1 hc
  refine memBesov_def.2 (memℓp_infty_iff.2 ⟨C * ‖f‖, ?_⟩)
  rintro _ ⟨j, rfl⟩
  dsimp only
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC p c f hf j

/-! ### `B^s_{p,1}(𝕋ᵈ) ⊆ H^{s,p}(𝕋ᵈ)` -/

variable (φ) in
/-- **`B^s_{p,1}(𝕋ᵈ) ⊆ H^{s,p}(𝕋ᵈ)`, quantitatively.** There is `C ≥ 0`, depending only on `φ` and
`s`, such that for every `1 ≤ p ≤ ∞` and every `c ∈ B^s_{p,1}(𝕋ᵈ)` some `f ∈ Lᵖ(𝕋ᵈ)` has the
Fourier coefficients `f̂(n) = (1 + ‖n‖²)^{s/2} c(n)` and

`‖f‖_p ≤ C ∑ⱼ 2^{js} ‖Δⱼ c‖_p`. -/
theorem exists_mFourierCoeff_eq_and_norm_le_tsum_of_memBesov (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : (d → ℤ) → ℂ), MemBesov φ s p 1 c →
      ∃ f : Lp ℂ p (volume : Measure (UnitAddTorus d)),
        (∀ n, mFourierCoeff f n = (((1 + ‖latticePoint n‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * c n) ∧
          ‖f‖ ≤ C * ∑' j : ℕ, 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j c‖ := by
  obtain ⟨C, hC⟩ := φ.exists_mul_inhomogeneousLittlewoodPaley_eq_one_add_norm_sq_rpow_mul s
  choose σ hσ hσC using hC
  refine ⟨max C 0, le_max_right _ _, fun p _ c hc ↦ ?_⟩
  -- The pieces `gⱼ = J^s Δⱼ c`, the blocks of `σⱼ c`.
  set g : ℕ → Lp ℂ p (volume : Measure (UnitAddTorus d)) := fun j ↦
    littlewoodPaleyBlockLp φ p j (fun n ↦ σ j (latticePoint n) * c n)
  have h2 (j : ℕ) : ((2 : ℝ) ^ j) ^ s = 2 ^ (s * j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, mul_comm]
  have hg (j : ℕ) : ‖g j‖ ≤ max C 0 * (2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j c‖) := by
    refine (norm_littlewoodPaleyBlockLp_le_of_mul_eq (σ j) j (littlewoodPaleyBlockLp φ p j c)
      fun n ↦ by rw [mFourierCoeff_littlewoodPaleyBlockLp]; ring).trans ?_
    rw [← mul_assoc]
    gcongr
    exact (hσC j).trans (by rw [h2]; gcongr; exact le_max_left _ _)
  have hsum : Summable fun j : ℕ ↦ 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j c‖ := by
    have h := (memℓp_gen_iff (by simp : 0 < (1 : ℝ≥0∞).toReal)).1 (memBesov_def.1 hc)
    simp only [ENNReal.toReal_one, Real.rpow_one] at h
    exact h.congr fun j ↦ Real.norm_of_nonneg (by positivity)
  refine ⟨∑' j, g j, fun n ↦ ?_, tsum_of_norm_bounded (hsum.hasSum.mul_left (max C 0)) hg⟩
  -- The coefficients of `∑ⱼ gⱼ` are `∑ⱼ ψⱼ(n) ⟨n⟩^s c(n) = ⟨n⟩^s c(n)`.
  have hψ : HasSum (fun j ↦ (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ)) 1 := by
    have h := Complex.hasSum_ofReal.2 (φ.hasSum_inhomogeneousLittlewoodPaley (latticePoint n))
    rwa [Complex.ofReal_one] at h
  rw [← mFourierCoeffCLM_apply,
    (mFourierCoeffCLM p n).map_tsum (Summable.of_norm_bounded (hsum.mul_left (max C 0)) hg)]
  refine ((hψ.mul_left ((((1 + ‖latticePoint n‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * c n)).congr_fun
    fun j ↦ ?_).tsum_eq.trans (mul_one _)
  simp only [g, mFourierCoeffCLM_apply, mFourierCoeff_littlewoodPaleyBlockLp]
  linear_combination (c n) * hσ j (latticePoint n)

/-- **`B^s_{p,1}(𝕋ᵈ) ⊆ H^{s,p}(𝕋ᵈ)`.** -/
theorem MemBesov.memSobolev [Fact (1 ≤ p)] (hc : MemBesov φ s p 1 c) : MemSobolev s p c := by
  obtain ⟨C, -, hC⟩ := exists_mFourierCoeff_eq_and_norm_le_tsum_of_memBesov φ s
  obtain ⟨f, hf, -⟩ := hC p c hc
  exact memSobolev_def.2 ⟨f, hf⟩

/-! ### Consequences -/

/-- **Trigonometric polynomials lie in every periodic Bessel-potential space.** -/
theorem memSobolev_of_finite_support [Fact (1 ≤ p)] (hc : (Function.support c).Finite) :
    MemSobolev s p c :=
  (memBesov_of_finite_support (φ := (default : ContDiffBump (0 : EuclideanSpace ℝ d)))
    (q := 1) hc).memSobolev

/-- **Monotonicity of the periodic Bessel-potential scale.** `H^{s,p}(𝕋ᵈ) ⊆ H^{s',p}(𝕋ᵈ)` for
`s' ≤ s`: for `s' < s` this is `H^{s,p} ⊆ B^s_{p,∞} ⊆ B^{s'}_{p,1} ⊆ H^{s',p}`. -/
theorem MemSobolev.of_le [Fact (1 ≤ p)] (hc : MemSobolev s p c) {s' : ℝ} (hs : s' ≤ s) :
    MemSobolev s' p c := by
  rcases hs.eq_or_lt with rfl | hs
  · exact hc
  · exact ((hc.memBesov default).of_lt hs one_ne_zero).memSobolev

end TauCeti.UnitAddTorus
