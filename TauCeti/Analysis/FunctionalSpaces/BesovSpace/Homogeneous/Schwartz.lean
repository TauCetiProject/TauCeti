/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Basic
public import TauCeti.Analysis.Fourier.L2Multiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.Bernstein
import TauCeti.Analysis.Sobolev.BesselPotential.Besov

/-!
# Schwartz functions in the homogeneous Besov spaces `\dot B^s_{2,∞}`

Let `Pⱼ`, `j ∈ ℤ`, be the homogeneous Littlewood–Paley blocks built from a bump function `φ` on a
real inner product space `E` of dimension `n`. For a Schwartz function `f` the blocks `Pⱼ f` are
`L²` functions with two kinds of control:

* at high frequencies they decay faster than every power of `2^{-j}`, because `f` lies in every
  inhomogeneous Besov space `B^s_{2,∞}` (`SchwartzMap.memBesov`), whose blocks agree with the
  homogeneous ones for `j ≥ 1`;
* at low frequencies Bernstein's inequality from `L¹` to `L²`
  (`ContDiffBump.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le`) and the uniform `L¹`
  bound of the blocks give `‖Pⱼ f‖₂ ≤ C 2^{jn/2} ‖f‖₁`.

So `2^{js} ‖Pⱼ f‖₂` is bounded over `j ∈ ℤ` exactly when the low-frequency weight `2^{j(s + n/2)}`
stays bounded as `j → -∞`, that is for `s ≥ -n/2`
(`SchwartzMap.exists_two_rpow_mul_norm_fourierMultiplierCLM_littlewoodPaley_le`): every Schwartz
function lies in `\dot B^s_{2,∞}` for `s ≥ -n/2` (`SchwartzMap.memHomogeneousBesov`). The bound
`s ≥ -n/2` cannot be lowered in general, since `‖Pⱼ f‖₂` is comparable to `2^{jn/2} |𝓕 f (0)|`
as `j → -∞`.

With `σ = -s ≤ n/2` the bound reads `‖Pⱼ f‖₂ ≤ C 2^{jσ}`. Against the blocks of an element of
`\dot B^σ_{2,1}` it makes the pairings with a Schwartz test function absolutely summable, which is
how test functions are paired with dyadic series of evolutions of homogeneous Besov data.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Lemma 2.1
  (Bernstein) and Section 2.3.
-/

public section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace SchwartzMap

/-- **The homogeneous blocks of a Schwartz function are bounded in `\dot B^s_{2,∞}`.** Let `n` be
the dimension of `E` and `s ≥ -n/2`. For every Schwartz function `f` there is `C` such that
`2^{js} ‖Pⱼ f‖₂ ≤ C` for every `j ∈ ℤ`, where `Pⱼ` is the `L²` Fourier multiplier with any symbol
in `L^∞` almost everywhere equal to `ψⱼ`. -/
theorem exists_two_rpow_mul_norm_fourierMultiplierCLM_littlewoodPaley_le (f : 𝓢(E, F))
    (φ : ContDiffBump (0 : E)) {s : ℝ} (hs : -((Module.finrank ℝ E : ℝ) / 2) ≤ s) :
    ∃ C : ℝ, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
        (2 : ℝ) ^ (s * j) * ‖Lp.fourierMultiplierCLM F m (f.toLp 2)‖ ≤ C := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  -- High frequencies: the blocks of `f ∈ B^{s'}_{2,∞} ⊆ \dot B^{s'}_{2,∞}` for `s' = max s 1 > 0`.
  set s' : ℝ := max s 1
  obtain ⟨g, hg, hmem⟩ := memHomogeneousBesov_iff.1 ((f.memBesov φ s' 2 (q := ∞)
    ENNReal.top_ne_zero).memHomogeneousBesov (lt_max_of_lt_right one_pos) ENNReal.top_ne_zero)
  obtain ⟨K, hK⟩ := memℓp_infty_iff.1 hmem
  have hgm (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E))
      (hm : m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))) :
      Lp.fourierMultiplierCLM F m (f.toLp 2) = g j :=
    Lp.toTemperedDistribution_injective <| by
      dsimp only
      rw [← hg, ← homogeneousLittlewoodPaleyBlock_toTemperedDistribution φ hm,
        Lp.toTemperedDistribution_toLp_eq]
  -- Low frequencies: Bernstein's inequality from `L¹`, `‖Pⱼ f‖₂ ≤ C 2^{jn/2} ‖f‖₁`.
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le_eLpNorm (F := F)
    le_rfl one_le_two
  set A : ℝ≥0∞ := C * eLpNorm f 1 volume
  have hlow (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E))
      (hm : m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))) :
      ‖Lp.fourierMultiplierCLM F m (f.toLp 2)‖ ≤ A.toReal * (2 : ℝ) ^ (n / 2 * j) := by
    have hexp : ((2 : ℝ) ^ j) ^ (n * ((1 : ℝ≥0∞).toReal⁻¹ - (2 : ℝ≥0∞).toReal⁻¹)) =
        (2 : ℝ) ^ (n / 2 * j) := by
      rw [← Real.rpow_intCast, ← Real.rpow_mul zero_le_two]
      norm_num
      ring_nf
    have h := hC j m hm (f.toLp 2)
    rw [eLpNorm_congr_ae (f.coeFn_toLp 2 volume), hexp, mul_right_comm] at h
    rw [Lp.norm_def, ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 ^ (n / 2 * j)),
      ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (f.memLp 1 volume).eLpNorm_ne_top) ENNReal.ofReal_ne_top) h
  refine ⟨max K A.toReal, fun j m hm ↦ ?_⟩
  rcases le_or_gt 0 j with hj | hj
  · -- For `j ≥ 0`, `2^{js} ≤ 2^{js'}`.
    refine le_max_of_le_left ((mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le
      one_le_two (mul_le_mul_of_nonneg_right (le_max_left s 1) (Int.cast_nonneg_iff.2 hj)))
      (norm_nonneg _)).trans ?_)
    rw [hgm j m hm]
    simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (s' * j))] using
      hK ⟨j, rfl⟩
  · -- For `j < 0`, `2^{js} 2^{jn/2} = 2^{j(s + n/2)} ≤ 1`.
    refine le_max_of_le_right ((mul_le_mul_of_nonneg_left (hlow j m hm) (by positivity)).trans ?_)
    rw [mul_left_comm, ← Real.rpow_add two_pos]
    refine mul_le_of_le_one_right ENNReal.toReal_nonneg (Real.rpow_le_one_of_one_le_of_nonpos
      one_le_two ?_)
    nlinarith [(Int.cast_lt_zero.2 hj : (j : ℝ) < 0)]

/-- **Schwartz functions lie in `\dot B^s_{2,∞}` for `s ≥ -n/2`**, where `n` is the dimension of
`E`: the weighted blocks `2^{js} ‖Pⱼ f‖₂` of a Schwartz function `f` are bounded over `j ∈ ℤ`. -/
theorem memHomogeneousBesov (f : 𝓢(E, F)) (φ : ContDiffBump (0 : E)) {s : ℝ}
    (hs : -((Module.finrank ℝ E : ℝ) / 2) ≤ s) :
    (f : 𝓢'(E, F)).MemHomogeneousBesov φ s 2 ∞ := by
  obtain ⟨C, hC⟩ := f.exists_two_rpow_mul_norm_fourierMultiplierCLM_littlewoodPaley_le φ hs
  set m : ℤ → Lp ℂ ∞ (volume : Measure E) := fun j ↦ (φ.memLp_ofReal_littlewoodPaley j ∞).toLp _
  have hm (j : ℤ) : m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) :=
    (φ.memLp_ofReal_littlewoodPaley j ∞).coeFn_toLp
  refine (memHomogeneousBesov_iff_memℓp (f := fun j ↦ Lp.fourierMultiplierCLM F (m j) (f.toLp 2))
    fun j ↦ ?_).2 (memℓp_infty_iff.2 ⟨C, ?_⟩)
  · rw [← homogeneousLittlewoodPaleyBlock_toTemperedDistribution φ (hm j),
      Lp.toTemperedDistribution_toLp_eq]
  · rintro _ ⟨j, rfl⟩
    dsimp only
    rw [Real.norm_of_nonneg (by positivity)]
    exact hC j (m j) (hm j)

end SchwartzMap
