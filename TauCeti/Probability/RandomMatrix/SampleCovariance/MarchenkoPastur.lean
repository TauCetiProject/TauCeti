/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MarchenkoPastur.Stability
public import TauCeti.Probability.RandomMatrix.QuadraticForm
public import TauCeti.Probability.RandomMatrix.SampleCovariance.ZeroMass
import TauCeti.Analysis.Matrix.SampleCovariance.SelfConsistency
import TauCeti.Analysis.Matrix.SpectralMeasure.Scaling
import TauCeti.Probability.RandomMatrix.SampleCovariance.Approximation
import TauCeti.Probability.RandomMatrix.SampleCovariance.ExpectedSpectralMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.ProductMeasure

/-!
# The Marchenko–Pastur law

Sample covariance matrices with independent, unit second moment entries and a uniform
directional sub-Gaussian bound have almost surely convergent empirical spectral measures
when the row-to-column ratio tends to a positive constant. The entry laws may vary with
dimension and position. For varying sample spaces, bounded continuous spectral statistics
converge in mean absolute error and in probability. The proof uses uniform leave-one-column-out
concentration, the rank-one resolvent estimate and stability of the Marchenko–Pastur equation.

For the corners of one infinite array of i.i.d. complex entries with mean zero and unit second
absolute moment, `marchenkoPastur_ae` removes the sub-Gaussian assumption.
`ae_tendsto_spectralMeasure_sampleCovariance_of_bounded` gives the bounded case, and
the bounded-entry reduction `ae_tendsto_spectralMeasure_sampleCovariance_of_bounded_entries`
transfers it to finite variance. Real entries are the case of an entry law supported on `ℝ`.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.
* Z. D. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*, 2nd ed.,
  Springer, 2010, §3.3.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {p : ℕ → ℕ} [∀ m, NeZero (p m)]
  {X : (m : ℕ) → Ω → Matrix (Fin (p m)) (Fin (m + 1)) ℂ} {K y : ℝ≥0}

private theorem tendsto_covariance_quadratic_of_tendsto_columnErrors
    (M : (m : ℕ) → Matrix (Fin (p m)) (Fin (m + 1)) ℂ)
    (hy : Tendsto (fun m : ℕ ↦ (p m : ℝ≥0) / (m + 1)) atTop (𝓝 y)) (hy₀ : y ≠ 0)
    {z : ℂ} (hz : z.im ≠ 0)
    (herror : Tendsto (fun m ↦ ‖fun k ↦ (M m).sampleCovarianceResolventColumnError z k‖)
      atTop (𝓝 0)) :
    let y' := fun m : ℕ ↦ (p m : ℝ≥0) / (m + 1)
    let w := fun m ↦ resolventTransform
      ((sampleCovariance (M m)).spectralMeasure (isHermitian_sampleCovariance _) : Measure ℝ) z
    Tendsto (fun m ↦ (y' m : ℂ) * z * (w m * w m) + (z + y' m - 1) * w m + 1)
      atTop (𝓝 0) := by
  intro y' w
  have hratio : Tendsto (fun m : ℕ ↦ (m + 1 : ℝ) / p m) atTop (𝓝 (y : ℝ)⁻¹) := by
    simpa only [Function.comp_def, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_one, inv_div] using
      ((NNReal.continuous_coe.tendsto y).comp hy).inv₀ (by exact_mod_cast hy₀)
  have hinv : Tendsto (fun m : ℕ ↦ ((m + 1 : ℝ) * |z.im|)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_inv, one_div, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (|z.im|⁻¹)
  have hlim := (hratio.mul_const (‖z‖ / |z.im|)).mul (herror.add hinv)
  simp only [add_zero, mul_zero] at hlim
  refine squeeze_zero_norm (fun m ↦ ?_) hlim
  have haspect : (y' m : ℂ) =
      (Fintype.card (Fin (p m)) : ℂ) / Fintype.card (Fin (m + 1)) := by
    simp [y', NNReal.coe_div]
  rw [haspect]
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    norm_sampleCovariance_resolvent_quadratic_le (M m) hz

/-- **Marchenko–Pastur law for uniformly sub-Gaussian entries.** With independent entries
within each matrix, unit second absolute moments and a common directional sub-Gaussian
proxy, the empirical covariance spectral measures converge almost surely if the aspect
ratio tends to a positive number. Matrices at different sizes may have arbitrary coupling. -/
theorem ae_tendsto_spectralMeasure_sampleCovariance_of_hasSubgaussianMGF
    (hind : ∀ m, iIndepFun (fun ij : Fin (p m) × Fin (m + 1) ↦
      fun ω ↦ X m ω ij.1 ij.2) P)
    (hX : ∀ m i j (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * X m ω i j).re)
      (‖u‖₊ ^ 2 * K) P)
    (hunit : ∀ m i j, ∫ ω, ‖X m ω i j‖ ^ 2 ∂P = 1)
    (hy : Tendsto (fun m : ℕ ↦ (p m : ℝ≥0) / (m + 1)) atTop (𝓝 y)) (hy₀ : y ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (fun m ↦ (sampleCovariance (X m ω)).spectralMeasure
      (isHermitian_sampleCovariance _)) atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure) := by
  have hdim : ∃ C : ℝ, 0 < C ∧ ∀ᶠ m in atTop, (p m : ℝ) ≤ C * (m + 1) := by
    refine ⟨(y : ℝ) + 1, by positivity, ?_⟩
    have h := (NNReal.continuous_coe.tendsto y).comp hy
    filter_upwards [h.eventually_lt_const (lt_add_one (y : ℝ))] with m hm
    apply (div_le_iff₀ (by positivity : 0 < (m + 1 : ℝ))).mp
    simpa only [Function.comp_def, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_one] using hm.le
  apply (ae_tendsto_marchenkoPastur_iff_ae_quadratic_tendsto_zero hy).2
  intro z hz
  filter_upwards [ae_tendsto_norm_star_dotProduct_sampleCovariance_resolvent_mulVec_sub_trace
    hind hX hunit hdim hz.ne'] with ω hω
  refine tendsto_covariance_quadratic_of_tendsto_columnErrors (fun m ↦ X m ω) hy hy₀ hz.ne' ?_
  simpa only [sampleCovarianceResolventColumnError_def, Fintype.card_fin, Matrix.col_apply']
    using hω

/-- Under the sub-Gaussian Marchenko–Pastur hypotheses, the proportion of sample covariance
eigenvalues equal to zero converges almost surely to the limiting atom at zero. -/
theorem ae_tendsto_spectralMeasure_sampleCovariance_singleton_zero
    (hind : ∀ m, iIndepFun (fun ij : Fin (p m) × Fin (m + 1) ↦
      fun ω ↦ X m ω ij.1 ij.2) P)
    (hX : ∀ m i j (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * X m ω i j).re)
      (‖u‖₊ ^ 2 * K) P)
    (hunit : ∀ m i j, ∫ ω, ‖X m ω i j‖ ^ 2 ∂P = 1)
    (hy : Tendsto (fun m : ℕ ↦ (p m : ℝ≥0) / (m + 1)) atTop (𝓝 y)) (hy₀ : y ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (fun m ↦ ((sampleCovariance (X m ω)).spectralMeasure
      (isHermitian_sampleCovariance _) : Measure ℝ) {0})
      atTop (𝓝 (marchenkoPastur y {0})) := by
  filter_upwards [ae_tendsto_spectralMeasure_sampleCovariance_of_hasSubgaussianMGF
    hind hX hunit hy hy₀] with ω hω
  exact tendsto_spectralMeasure_sampleCovariance_singleton_zero (fun m ↦ X m ω)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hy) hω

/-- **Marchenko–Pastur law for bounded complex entries.** Independent centered entries with
unit second absolute moments and a common almost-sure bound suffice. -/
theorem ae_tendsto_spectralMeasure_sampleCovariance_of_bounded
    (hind : ∀ m, iIndepFun (fun ij : Fin (p m) × Fin (m + 1) ↦
      fun ω ↦ X m ω ij.1 ij.2) P)
    (hm : ∀ m, AEMeasurable (X m) P) {b : ℝ≥0}
    (hb : ∀ m i j, ∀ᵐ ω ∂P, ‖X m ω i j‖ ≤ b)
    (hmean : ∀ m i j, ∫ ω, X m ω i j ∂P = 0)
    (hunit : ∀ m i j, ∫ ω, ‖X m ω i j‖ ^ 2 ∂P = 1)
    (hy : Tendsto (fun m : ℕ ↦ (p m : ℝ≥0) / (m + 1)) atTop (𝓝 y)) (hy₀ : y ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (fun m ↦ (sampleCovariance (X m ω)).spectralMeasure
      (isHermitian_sampleCovariance _)) atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure) := by
  have : IsProbabilityMeasure P := (hind 0).isProbabilityMeasure
  exact ae_tendsto_spectralMeasure_sampleCovariance_of_hasSubgaussianMGF hind
    (fun m i j ↦ hasSubgaussianMGF_re_star_mul_of_norm_le ((hm m).eval i |>.eval j)
      (hb m i j) (hmean m i j)) hunit hy hy₀

/-- The bounded-entry Marchenko–Pastur law for real data. The real sample covariance
spectral measure is preserved on entrywise embedding into the complex matrices. -/
theorem ae_tendsto_spectralMeasure_sampleCovariance_of_bounded_real
    {Xr : (m : ℕ) → Ω → Matrix (Fin (p m)) (Fin (m + 1)) ℝ}
    (hind : ∀ m, iIndepFun (fun ij : Fin (p m) × Fin (m + 1) ↦
      fun ω ↦ Xr m ω ij.1 ij.2) P)
    (hm : ∀ m, AEMeasurable (Xr m) P) {b : ℝ≥0}
    (hb : ∀ m i j, ∀ᵐ ω ∂P, ‖Xr m ω i j‖ ≤ b)
    (hmean : ∀ m i j, ∫ ω, Xr m ω i j ∂P = 0)
    (hunit : ∀ m i j, ∫ ω, ‖Xr m ω i j‖ ^ 2 ∂P = 1)
    (hy : Tendsto (fun m : ℕ ↦ (p m : ℝ≥0) / (m + 1)) atTop (𝓝 y)) (hy₀ : y ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (fun m ↦ (sampleCovariance (Xr m ω)).spectralMeasure
      (isHermitian_sampleCovariance _)) atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure) := by
  let Y m (ω : Ω) := (Xr m ω).map Complex.ofReal
  have hindY m := (hind m).comp (fun _ ↦ Complex.ofReal) (fun _ ↦ Complex.measurable_ofReal)
  have hmY m : AEMeasurable (Y m) P := .of_eval fun i ↦ .of_eval fun j ↦
    Complex.measurable_ofReal.comp_aemeasurable ((hm m).eval i |>.eval j)
  have hbY m i j : ∀ᵐ ω ∂P, ‖Y m ω i j‖ ≤ b := by
    simpa only [Y, Matrix.map_apply, Complex.norm_real] using hb m i j
  have hmeanY m i j : ∫ ω, Y m ω i j ∂P = 0 := by
    simp only [Y, Matrix.map_apply, integral_complex_ofReal, hmean, Complex.ofReal_zero]
  have hunitY m i j : ∫ ω, ‖Y m ω i j‖ ^ 2 ∂P = 1 := by
    simpa only [Y, Matrix.map_apply, Complex.norm_real] using hunit m i j
  have hL (m : ℕ) (ω : Ω) :
      (sampleCovariance (Y m ω)).spectralMeasure (isHermitian_sampleCovariance _) =
        (sampleCovariance (Xr m ω)).spectralMeasure (isHermitian_sampleCovariance _) := by
    have he := sampleCovariance_map (Xr m ω) (RCLike.ofRealStarAlgHom ℂ)
    have hA : ((sampleCovariance (Xr m ω)).map Complex.ofReal).IsHermitian :=
      (isHermitian_sampleCovariance (Xr m ω)).map _
        (fun x ↦ map_star (RCLike.ofRealStarAlgHom ℂ) x)
    have hEq := spectralMeasure_eq_of_charpoly_eq
      (isHermitian_sampleCovariance (Y m ω)) hA (congrArg Matrix.charpoly he)
    exact hEq.trans (spectralMeasure_map_ofReal _ hA)
  simpa only [hL] using
    ae_tendsto_spectralMeasure_sampleCovariance_of_bounded hindY hmY hbY hmeanY hunitY hy hy₀

/-- **Marchenko–Pastur law, almost surely.** Let `x` be an array, indexed by `ℕ × ℕ`, of independent
complex entries with common law `ν` of mean zero and unit second absolute moment, let `p(n) ≥ 1`
with `p(n) / n → y > 0`, and let `Xₙ` be the top-left `p(n) × n` corner of the array. Then almost
surely the empirical spectral measures of the sample covariances `Xₙ Xₙᴴ / n` converge weakly to
the Marchenko–Pastur law `MP_y`. -/
theorem marchenkoPastur_ae {x : ℕ × ℕ → Ω → ℂ} {ν : Measure ℂ}
    (hx : ∀ ij, HasLaw (x ij) ν P) (hindep : iIndepFun x P)
    (hmean : ∫ z, z ∂ν = 0) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1) (hy : 0 < y)
    (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 y)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      (sampleCovariance (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω)).spectralMeasure
        (isHermitian_sampleCovariance _)) atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have : IsProbabilityMeasure ν := (hx (0, 0)).isProbabilityMeasure_iff.1 ‹_›
  -- Work with the corners of size `p (m + 1) × (m + 1)`, which have a nonempty column type.
  have hp' : Tendsto (fun m : ℕ ↦ (p (m + 1) : ℝ) / (m + 1)) atTop (𝓝 y) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (tendsto_add_atTop_iff_nat 1).2 hp
  have hdim : ∀ᶠ m : ℕ in atTop, (y / 2 : ℝ) * m ≤ Fintype.card (Fin (p (m + 1))) := by
    filter_upwards [hp'.eventually (lt_mem_nhds (half_lt_self (by exact_mod_cast hy)))] with m hm
    rw [Fintype.card_fin]
    have := (lt_div_iff₀ (by positivity)).1 hm
    nlinarith [NNReal.coe_nonneg y]
  have hind (m : ℕ) : iIndepFun (fun ij : Fin (p (m + 1)) × Fin (m + 1) ↦
      fun ω ↦ x (ij.1, ij.2) ω) P :=
    hindep.precomp (Fin.val_injective.prodMap Fin.val_injective)
  have h := ae_tendsto_spectralMeasure_sampleCovariance_of_bounded_entries
    (X := fun m ω ↦ Matrix.of fun (i : Fin (p (m + 1))) (j : Fin (m + 1)) ↦ x (i, j) ω)
    (μ := (marchenkoPastur y).toProbabilityMeasure) hind (fun _ _ _ ↦ hx _) hmean hvar
    (by positivity) hdim ?_
  · filter_upwards [h] with ω hω
    exact (tendsto_add_atTop_iff_nat 1).1 hω
  intro Y hY ρ hYind hYlaw ⟨B, hB⟩ hρmean hρunit
  apply tendsto_expectedCovarianceSpectralMeasure_of_ae_tendsto hY
  refine ae_tendsto_spectralMeasure_sampleCovariance_of_bounded hYind hY (b := B.toNNReal)
    (fun m i j ↦ ?_) (fun m i j ↦ (hYlaw m i j).integral_eq.trans hρmean)
    (fun m i j ↦ ((hYlaw m i j).integral_comp (by fun_prop)).trans hρunit)
    (NNReal.tendsto_coe.1 (by simpa using hp')) hy.ne'
  exact ((hYlaw m i j).ae_iff (p := fun x ↦ ‖x‖ ≤ B.toNNReal)
    (measurableSet_setOfPred.1 (measurableSet_le measurable_norm measurable_const))).2
    (hB.mono fun _ h ↦ h.trans (Real.le_coe_toNNReal B))

/-- For i.i.d. complex entries with positive finite variance `v` and arbitrary mean, the
empirical spectral measures of the entrywise centered sample covariances converge weakly
almost surely to the Marchenko–Pastur law at the limiting positive aspect ratio `y`, scaled
by `v`. -/
theorem ae_tendsto_spectralMeasure_centered_sampleCovariance_of_pos_variance
    {x : ℕ × ℕ → Ω → ℂ} {ν : Measure ℂ}
    (hx : ∀ ij, HasLaw (x ij) ν P) (hindep : iIndepFun x P) (hy : 0 < y)
    (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 y))
    (hv : 0 < ∫ z, ‖z - ∫ w, w ∂ν‖ ^ 2 ∂ν) :
    let b := ∫ z, z ∂ν
    let v := ∫ z, ‖z - b‖ ^ 2 ∂ν
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (sampleCovariance (Matrix.of
      fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω - b)).spectralMeasure
        (isHermitian_sampleCovariance _)) atTop
      (𝓝 ((marchenkoPastur y).toProbabilityMeasure.map (v * ·))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have : IsProbabilityMeasure ν := (hx (0, 0)).isProbabilityMeasure_iff.1 ‹_›
  let b := ∫ z, z ∂ν
  let v := ∫ z, ‖z - b‖ ^ 2 ∂ν
  have hv' : 0 < v := hv
  let Z (z : ℂ) := (√v)⁻¹ • (z - b)
  have hZ : Measurable Z := by fun_prop
  have hmean : ∫ z, z ∂(ν.map Z) = 0 := by
    have hsq : Integrable (fun z ↦ ‖z - b‖ ^ 2) ν := by
      by_contra h
      exact hv'.ne' (integral_undef h)
    have hLp : MemLp (fun z ↦ z - b) 2 ν :=
      (memLp_two_iff_integrable_sq_norm
        (measurable_id.sub measurable_const).aestronglyMeasurable).mpr hsq
    have hid : Integrable (fun z : ℂ ↦ z) ν := by
      simpa only [sub_eq_add_neg, integrable_add_const_iff] using hLp.integrable one_le_two
    rw [integral_map hZ.aemeasurable (by fun_prop)]
    simp only [Z, integral_smul]
    rw [integral_sub hid (integrable_const b)]
    simp [b]
  have hvar : ∫ z, ‖z‖ ^ 2 ∂(ν.map Z) = 1 := by
    rw [integral_map hZ.aemeasurable (by fun_prop)]
    simp only [Z, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (√v)⁻¹),
      mul_pow, integral_const_mul, inv_pow, Real.sq_sqrt hv'.le]
    exact inv_mul_cancel₀ hv'.ne'
  filter_upwards [marchenkoPastur_ae (fun ij ↦ (hasLaw_map hZ.aemeasurable).fun_comp (hx ij))
    (hindep.comp (fun _ ↦ Z) (fun _ ↦ hZ)) hmean hvar hy hp]
    with ω hMP
  let A (n : ℕ) := Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω - b
  let B (n : ℕ) := Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ Z (x (i, j) ω)
  have hA (n : ℕ) : A n = √v • B n := by
    ext i j
    simp only [A, B, Matrix.smul_apply, Matrix.of_apply, Z, smul_smul,
      mul_inv_cancel₀ (Real.sqrt_pos.2 hv').ne', one_smul]
  have hmap (n : ℕ) : ((sampleCovariance (B n)).spectralMeasure
      (isHermitian_sampleCovariance _)).map (v * ·) =
        (sampleCovariance (A n)).spectralMeasure (isHermitian_sampleCovariance _) := by
    rw [map_spectralMeasure_mul]
    apply spectralMeasure_eq_of_charpoly_eq
    rw [hA n, sampleCovariance_real_smul, Real.sq_sqrt hv'.le]
  exact ((ProbabilityMeasure.continuous_map (continuous_const.mul continuous_id)).tendsto _
    |>.comp hMP).congr hmap

section VaryingSpaces

variable {Ωs : ℕ → Type*} [∀ m, MeasurableSpace (Ωs m)] {Ps : ∀ m, Measure (Ωs m)}
  {Xs : (m : ℕ) → Ωs m → Matrix (Fin (p m)) (Fin (m + 1)) ℂ}

omit [∀ m, NeZero (p m)] in
private theorem aemeasurable_of_directional_subgaussian
    (hX : ∀ m i j (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Xs m ω i j).re)
      (‖u‖₊ ^ 2 * K) (Ps m)) (m : ℕ) : AEMeasurable (Xs m) (Ps m) :=
  .of_eval fun i ↦ .of_eval fun j ↦
    (integrable_of_hasSubgaussianMGF_re_star_mul (hX m i j)).aemeasurable

private theorem ae_tendsto_spectralMeasure_sampleCovariance_infinitePi
    (hind : ∀ m, iIndepFun (fun ij : Fin (p m) × Fin (m + 1) ↦
      fun ω ↦ Xs m ω ij.1 ij.2) (Ps m))
    (hX : ∀ m i j (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Xs m ω i j).re)
      (‖u‖₊ ^ 2 * K) (Ps m))
    (hunit : ∀ m i j, ∫ ω, ‖Xs m ω i j‖ ^ 2 ∂Ps m = 1)
    (hy : Tendsto (fun m : ℕ ↦ (p m : ℝ≥0) / (m + 1)) atTop (𝓝 y)) (hy₀ : y ≠ 0) :
    haveI : ∀ m, IsProbabilityMeasure (Ps m) := fun m ↦ (hind m).isProbabilityMeasure
    ∀ᵐ ω ∂Measure.infinitePi Ps, Tendsto (fun m ↦ (sampleCovariance (Xs m (ω m))).spectralMeasure
      (isHermitian_sampleCovariance _)) atTop (𝓝 (marchenkoPastur y).toProbabilityMeasure) := by
  have : ∀ m, IsProbabilityMeasure (Ps m) := fun m ↦ (hind m).isProbabilityMeasure
  let Q := Measure.infinitePi Ps
  let Y (m : ℕ) (ω : ∀ m, Ωs m) := Xs m (ω m)
  have he m := measurePreserving_eval_infinitePi Ps m
  have hcoord (m : ℕ) (ij : Fin (p m) × Fin (m + 1)) :
      AEMeasurable (fun ω ↦ Xs m ω ij.1 ij.2) (Ps m) :=
    ((aemeasurable_of_directional_subgaussian hX m).eval ij.1).eval ij.2
  refine ae_tendsto_spectralMeasure_sampleCovariance_of_hasSubgaussianMGF
    (P := Q) (X := Y) (K := K) ?_ ?_ ?_ hy hy₀
  · intro m
    -- Pull back the joint product law and all its marginals along the same projection.
    have hL := fun ij ↦ hasLaw_map (hcoord m ij)
    exact (iIndepFun_iff_hasLaw_pi_pi (fun ij ↦ (hL ij).fun_comp (he m).hasLaw)).2
      (((hind m).hasLaw_pi hL).fun_comp (he m).hasLaw)
  · intro m i j u
    have hL := hasLaw_map (hX m i j u).aemeasurable
    exact (hX m i j u).congr_identDistrib (hL.identDistrib (hL.fun_comp (he m).hasLaw))
  · intro m i j
    exact ((he m).hasLaw.integral_comp
      ((hcoord m (i, j)).norm.pow_const 2).aestronglyMeasurable).trans (hunit m i j)

/-- On possibly different probability spaces, every bounded continuous spectral statistic
converges in mean absolute error to its Marchenko–Pastur integral. Each matrix has independent
entries of unit second moment with a common directional sub-Gaussian proxy. -/
theorem tendsto_integral_norm_integral_spectralMeasure_sampleCovariance_sub
    (hind : ∀ m, iIndepFun (fun ij : Fin (p m) × Fin (m + 1) ↦
      fun ω ↦ Xs m ω ij.1 ij.2) (Ps m))
    (hX : ∀ m i j (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Xs m ω i j).re)
      (‖u‖₊ ^ 2 * K) (Ps m))
    (hunit : ∀ m i j, ∫ ω, ‖Xs m ω i j‖ ^ 2 ∂Ps m = 1)
    (hy : Tendsto (fun m : ℕ ↦ (p m : ℝ≥0) / (m + 1)) atTop (𝓝 y)) (hy₀ : y ≠ 0)
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun m ↦ ∫ ω, ‖(∫ x, f x ∂((sampleCovariance (Xs m ω)).spectralMeasure
      (isHermitian_sampleCovariance _) : Measure ℝ)) - ∫ x, f x ∂marchenkoPastur y‖ ∂Ps m)
      atTop (𝓝 0) := by
  have : ∀ m, IsProbabilityMeasure (Ps m) := fun m ↦ (hind m).isProbabilityMeasure
  let Q := Measure.infinitePi Ps
  set c := ∫ x, f x ∂marchenkoPastur y
  set F := fun m (ω : Ωs m) ↦ ∫ x, f x ∂((sampleCovariance (Xs m ω)).spectralMeasure
    (isHermitian_sampleCovariance _) : Measure ℝ)
  have hm m : AEStronglyMeasurable (F m) (Ps m) :=
    aestronglyMeasurable_integral_spectralMeasure_sampleCovariance
      (aemeasurable_of_directional_subgaussian hX m) f
  have hme m := ((hm m).sub (aestronglyMeasurable_const (b := c))).norm
  have hF m : (∫ ω : ∀ m, Ωs m, ‖F m (ω m) - c‖ ∂Q) = ∫ ω, ‖F m ω - c‖ ∂Ps m :=
    (measurePreserving_eval_infinitePi Ps m).hasLaw.integral_comp (hme m)
  -- Name the inner integral with `F` so that the projection identity rewrites under `Tendsto`.
  change Tendsto (fun m ↦ ∫ ω, ‖F m ω - c‖ ∂Ps m) atTop (𝓝 0)
  simp_rw [← hF]
  rw [← integral_zero (α := ∀ m, Ωs m) (μ := Q) (G := ℝ)]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖f‖ + ‖f‖)
    (fun m ↦ (hme m).comp_quasiMeasurePreserving
      (measurePreserving_eval_infinitePi Ps m).quasiMeasurePreserving)
    (integrable_const _) (fun m ↦ .of_forall fun ω ↦ ?_) ?_
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (add_le_add
      (f.norm_integral_le_norm _) (f.norm_integral_le_norm _))
  · filter_upwards [ae_tendsto_spectralMeasure_sampleCovariance_infinitePi hind hX hunit hy hy₀]
      with ω hω
    have hf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hω f
    simpa only [F, c, Measure.coe_toProbabilityMeasure, sub_self, norm_zero] using
      (hf.sub_const c).norm

section TestIntegrals

variable
  (hind : ∀ m, iIndepFun (fun ij : Fin (p m) × Fin (m + 1) ↦
    fun ω ↦ Xs m ω ij.1 ij.2) (Ps m))
  (hX : ∀ m i j (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Xs m ω i j).re)
    (‖u‖₊ ^ 2 * K) (Ps m))
  (hunit : ∀ m i j, ∫ ω, ‖Xs m ω i j‖ ^ 2 ∂Ps m = 1)
  (hy : Tendsto (fun m : ℕ ↦ (p m : ℝ≥0) / (m + 1)) atTop (𝓝 y)) (hy₀ : y ≠ 0)
  (f : ℝ →ᵇ ℝ)

include hind hX hunit hy hy₀ in
/-- The expected spectral integrals converge to those of the Marchenko–Pastur law
for uniformly sub-Gaussian independent entries of unit second absolute moment.
The underlying probability spaces may vary with matrix size. -/
theorem tendsto_integral_integral_spectralMeasure_sampleCovariance :
    Tendsto (fun m ↦ ∫ ω, (∫ x, f x ∂((sampleCovariance (Xs m ω)).spectralMeasure
      (isHermitian_sampleCovariance _) : Measure ℝ)) ∂Ps m)
      atTop (𝓝 (∫ x, f x ∂marchenkoPastur y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
    (tendsto_integral_norm_integral_spectralMeasure_sampleCovariance_sub hind hX hunit hy hy₀ f)
  have : IsProbabilityMeasure (Ps m) := (hind m).isProbabilityMeasure
  let F (ω : Ωs m) := ∫ x, f x ∂((sampleCovariance (Xs m ω)).spectralMeasure
    (isHermitian_sampleCovariance _) : Measure ℝ)
  let c := ∫ x, f x ∂marchenkoPastur y
  have hIF : Integrable F (Ps m) := integrable_integral_spectralMeasure_sampleCovariance
    (aemeasurable_of_directional_subgaussian hX m) f
  have hsub : (∫ ω, F ω - c ∂Ps m) = (∫ ω, F ω ∂Ps m) - c := by
    rw [integral_sub hIF (integrable_const _)]
    simp
  simpa only [hsub, F, c] using
    norm_integral_le_integral_norm (μ := Ps m) (fun ω ↦ F ω - c)

include hind hX hunit hy hy₀ in
/-- The sample covariance spectral statistics converge in probability to those of the
Marchenko–Pastur law for uniformly sub-Gaussian independent entries of unit second absolute
moment. The underlying probability spaces may vary with matrix size. -/
theorem tendsto_measureReal_norm_integral_spectralMeasure_sampleCovariance_sub_ge
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m ↦ (Ps m).real {ω | ε ≤ ‖(∫ x, f x
      ∂((sampleCovariance (Xs m ω)).spectralMeasure (isHermitian_sampleCovariance _) : Measure ℝ)) -
      ∫ x, f x ∂marchenkoPastur y‖}) atTop (𝓝 0) := by
  have hlim := Tendsto.div_const
    (tendsto_integral_norm_integral_spectralMeasure_sampleCovariance_sub hind hX hunit hy hy₀ f) ε
  simp only [zero_div] at hlim
  refine squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg) (fun m ↦ ?_) hlim
  have : IsProbabilityMeasure (Ps m) := (hind m).isProbabilityMeasure
  have hA := aemeasurable_of_directional_subgaussian hX m
  apply (le_div_iff₀ hε).2
  rw [mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
    (((integrable_integral_spectralMeasure_sampleCovariance hA f).sub (integrable_const _)).norm) ε

end TestIntegrals

end VaryingSpaces

end TauCeti.Probability
