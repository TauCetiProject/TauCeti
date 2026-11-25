/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Probability.Concentration.Poincare.Herbst
public import TauCeti.Probability.RandomMatrix.Wigner.Basic
import TauCeti.Analysis.Matrix.HoffmanWielandt
import TauCeti.Probability.Concentration.SubgaussianTail

/-!
# Concentration of Wigner linear spectral statistics

On the unscaled Hilbert space of upper-triangular Wigner coordinates, integrating a
`K`-Lipschitz test against the empirical spectral measure is `√2 K / n`-Lipschitz.
The factor `√2` accounts for the two matrix entries contributed by each strictly upper
coordinate. A joint coordinate law with logarithmic Sobolev constant `C` therefore gives
sub-Gaussian fluctuations with variance proxy `2 C K² / n²`.

The argument follows Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*,
§2.3, especially Lemma 2.3.1 and Theorem 2.3.5. The logarithmic Sobolev hypothesis is on the
joint law, so the concentration transfer also applies to dependent coordinates.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Frobenius NNReal

namespace TauCeti

/-- Wigner coordinates carry the usual norm on their real or complex values. -/
instance wignerCoordinateNormedAddCommGroup {n : ℕ} (k : WignerCoordinateIndex n) :
    NormedAddCommGroup (WignerCoordinateType k) := by
  cases k <;> infer_instance

/-- Wigner coordinates are real inner product spaces, including the complex coordinates. -/
instance wignerCoordinateInnerProductSpace {n : ℕ} (k : WignerCoordinateIndex n) :
    InnerProductSpace ℝ (WignerCoordinateType k) := by
  cases k <;> infer_instance

/-- Every Wigner coordinate space is finite-dimensional over the reals. -/
instance wignerCoordinateFiniteDimensional {n : ℕ} (k : WignerCoordinateIndex n) :
    FiniteDimensional ℝ (WignerCoordinateType k) := by
  cases k <;> infer_instance

/-- The norm topology on each Wigner coordinate space is second countable. -/
instance wignerCoordinateSecondCountableTopology {n : ℕ} (k : WignerCoordinateIndex n) :
    SecondCountableTopology (WignerCoordinateType k) := by
  cases k <;> infer_instance

/-- Each Wigner coordinate has its Borel σ-algebra. -/
instance wignerCoordinateBorelSpace {n : ℕ} (k : WignerCoordinateIndex n) :
    BorelSpace (WignerCoordinateType k) := by
  cases k <;> infer_instance

variable {n : ℕ} {K C : ℝ≥0} {f : ℝ → ℝ}

private theorem exists_wignerCoordinates_eq
    (x : (k : WignerCoordinateIndex n) → WignerCoordinateType k) :
    ∃ (ξ : StrictUpper → Unit → ℂ) (η : ℕ → Unit → ℝ),
      wignerCoordinates ξ η n () = x := by
  refine ⟨Function.extend FinStrictUpper.toStrictUpper (fun u _ ↦ x (.inl u)) 0,
    Function.extend Fin.val (fun i _ ↦ x (.inr i)) 0, ?_⟩
  funext k
  cases k with
  | inl u => rw [wignerCoordinates_inl, FinStrictUpper.toStrictUpper_injective.extend_apply]
  | inr i => rw [wignerCoordinates_inr, Fin.val_injective.extend_apply]

/-- A matrix constructed from finite Wigner coordinates is Hermitian. -/
theorem wignerMatrixOfCoordinates_isHermitian
    (x : (k : WignerCoordinateIndex n) → WignerCoordinateType k) :
    (wignerMatrixOfCoordinates x).IsHermitian := by
  obtain ⟨ξ, η, rfl⟩ := exists_wignerCoordinates_eq x
  rw [← wignerMatrix_eq_wignerMatrixOfCoordinates]
  exact wignerMatrix_isHermitian ξ η () n

/-- The squared Frobenius distance of two normalized Wigner matrices counts the squared
diagonal errors once and the squared strictly upper errors twice, with an overall factor
`1/n`. -/
theorem norm_wignerMatrixOfCoordinates_sub_sq
    (x y : (k : WignerCoordinateIndex n) → WignerCoordinateType k) :
    ‖wignerMatrixOfCoordinates x - wignerMatrixOfCoordinates y‖ ^ 2 =
      (n : ℝ)⁻¹ * ((∑ i : Fin n, (x (.inr i) - y (.inr i)) ^ 2) +
        2 * ∑ u : FinStrictUpper n, ‖x (.inl u) - y (.inl u)‖ ^ 2) := by
  obtain ⟨ξ, η, rfl⟩ := exists_wignerCoordinates_eq x
  obtain ⟨ξ', η', rfl⟩ := exists_wignerCoordinates_eq y
  rw [← wignerMatrix_eq_wignerMatrixOfCoordinates, ← wignerMatrix_eq_wignerMatrixOfCoordinates,
    wignerMatrix_sub, Matrix.frobenius_norm_sq_eq_sum_norm_sq, sum_norm_wignerMatrix_apply_sq]
  simp only [wignerCoordinates_inl, wignerCoordinates_inr]

/-- With the Frobenius norm, the normalized Wigner constructor is `√2 / √n`-Lipschitz on
the unscaled Hilbert coordinates. -/
theorem lipschitzWith_wignerMatrixOfCoordinates :
    LipschitzWith (NNReal.sqrt 2 / NNReal.sqrt n)
      (fun x : PiLp 2 (@WignerCoordinateType n) ↦ wignerMatrixOfCoordinates x.ofLp) := by
  refine lipschitzWith_iff_norm_sub_le.mpr fun x y ↦ le_of_sq_le_sq ?_ (by positivity)
  push_cast
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [norm_wignerMatrixOfCoordinates_sub_sq, mul_pow, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hn,
    PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  let diagSq := ∑ i : Fin n, (x (.inr i) - y (.inr i)) ^ 2
  let upperSq := ∑ i : FinStrictUpper n, ‖x (.inl i) - y (.inl i)‖ ^ 2
  have hdiag : 0 ≤ diagSq := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  calc
    _ ≤ (n : ℝ)⁻¹ * (2 * (upperSq + diagSq)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hdiag]) (inv_nonneg.2 hn)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- A `K`-Lipschitz test integrated against the empirical spectral measure of a normalized
Wigner matrix is `√2 K / n`-Lipschitz in its unscaled Hilbert coordinates. -/
theorem lipschitzWith_integral_spectralMeasure_wignerMatrixOfCoordinates [NeZero n] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E} (hg : LipschitzWith K g) :
    LipschitzWith (NNReal.sqrt 2 * K / n)
      (fun x : PiLp 2 (@WignerCoordinateType n) ↦
        ∫ z, g z ∂((wignerMatrixOfCoordinates x.ofLp).spectralMeasure
          (wignerMatrixOfCoordinates_isHermitian x.ofLp) : Measure ℝ)) := by
  refine lipschitzWith_iff_norm_sub_le.mpr fun x y ↦ ?_
  by_cases hE : CompleteSpace E
  swap
  · simp only [integral_of_not_completeSpace hE, sub_self, norm_zero]
    positivity
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn
  have hmatrix := lipschitzWith_iff_norm_sub_le.mp lipschitzWith_wignerMatrixOfCoordinates x y
  push_cast at hmatrix
  calc
    _ ≤ K * ‖wignerMatrixOfCoordinates x.ofLp - wignerMatrixOfCoordinates y.ofLp‖ /
        √(n : ℝ) := by
      simpa only [Fintype.card_fin] using
        Matrix.norm_integral_spectralMeasure_sub_integral_spectralMeasure_le
          (wignerMatrixOfCoordinates_isHermitian x.ofLp)
          (wignerMatrixOfCoordinates_isHermitian y.ofLp) hg
    _ ≤ K * (√2 / √(n : ℝ) * ‖x - y‖) / √(n : ℝ) := by gcongr
    _ = _ := by
      push_cast
      field_simp [hs.ne', hn.ne']
      rw [Real.sq_sqrt hn.le]
      ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (PiLp 2 (@WignerCoordinateType n))}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Under a logarithmic Sobolev inequality for the joint law of the unscaled Wigner
coordinates, a centered Lipschitz spectral statistic is sub-Gaussian with variance proxy
`2 C K² / n²`. -/
theorem hasSubgaussianMGF_integral_spectralMeasure_wignerMatrix [NeZero n]
    (hμ : μ.LogSobolevInequality C)
    (hcoords : HasLaw (fun ω ↦ WithLp.toLp 2 (wignerCoordinates ξ η n ω)) μ P)
    (hf : LipschitzWith K f) :
    HasSubgaussianMGF
      (fun ω ↦
        (∫ z, f z ∂((wignerMatrix ξ η n ω).spectralMeasure
          (wignerMatrix_isHermitian ξ η ω n) : Measure ℝ)) -
        ∫ ω', ∫ z, f z ∂((wignerMatrix ξ η n ω').spectralMeasure
          (wignerMatrix_isHermitian ξ η ω' n) : Measure ℝ) ∂P)
      (2 * C * K ^ 2 / (n : ℝ≥0) ^ 2) P := by
  let := hcoords.isProbabilityMeasure_iff.mp (inferInstance : IsProbabilityMeasure P)
  have hL := lipschitzWith_integral_spectralMeasure_wignerMatrixOfCoordinates (n := n) hf
  have hsub := hμ.hasSubgaussianMGF_of_lipschitzWith hL
  have hproxy : (C : ℝ).toNNReal * (NNReal.sqrt 2 * K / n) ^ 2 =
      2 * C * K ^ 2 / (n : ℝ≥0) ^ 2 := by
    rw [Real.toNNReal_coe, div_pow, mul_pow, NNReal.sq_sqrt, ← mul_div_assoc]
    ring
  rw [hproxy] at hsub
  have hmean := hcoords.integral_comp hL.continuous.aestronglyMeasurable
  rw [← hcoords.map_eq] at hmean
  have hsub' := HasSubgaussianMGF.of_map hcoords.aemeasurable (hcoords.map_eq.symm ▸ hsub)
  simpa only [← hmean, Function.comp_def, WithLp.ofLp_toLp,
    ← wignerMatrix_eq_wignerMatrixOfCoordinates] using hsub'

/-- A Lipschitz Wigner spectral statistic has a two-sided Gaussian tail at speed `n²`
under the logarithmic Sobolev inequality for the joint coordinate law. -/
theorem measureReal_abs_integral_spectralMeasure_wignerMatrix_sub_ge_le [NeZero n]
    (hμ : μ.LogSobolevInequality C)
    (hcoords : HasLaw (fun ω ↦ WithLp.toLp 2 (wignerCoordinates ξ η n ω)) μ P)
    (hf : LipschitzWith K f) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω |
      t ≤ |(∫ z, f z ∂((wignerMatrix ξ η n ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω n) : Measure ℝ)) -
        ∫ ω', ∫ z, f z ∂((wignerMatrix ξ η n ω').spectralMeasure
          (wignerMatrix_isHermitian ξ η ω' n) : Measure ℝ) ∂P|} ≤
      2 * Real.exp (-((n : ℝ) ^ 2 * t ^ 2) / (4 * C * K ^ 2)) := by
  have hsub := hasSubgaussianMGF_integral_spectralMeasure_wignerMatrix hμ hcoords hf
  convert hsub.measureReal_abs_ge_le ht using 3
  push_cast
  simp only [← mul_div_assoc, div_div_eq_mul_div]
  ring

end TauCeti
