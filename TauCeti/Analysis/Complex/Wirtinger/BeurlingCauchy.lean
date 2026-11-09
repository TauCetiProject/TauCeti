/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Beurling
public import TauCeti.Analysis.Complex.Wirtinger.Schwartz
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Complex.CauchyKernel
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Fourier.L2Multiplier

/-!
# The Beurling operator is the Wirtinger derivative of the Cauchy transform

The Cauchy transform `T f w = π⁻¹ ∫ (w - z)⁻¹ • f z` inverts `bar∂ = (∂ₛ + i ∂ₜ) / 2`, and the
Beurling operator `B`, the Fourier multiplier with symbol `conj ξ / ξ`, is `∂ = (∂ₛ - i ∂ₜ) / 2`
composed with that inverse. This file proves the two identities behind this description.

* On Schwartz functions `B (bar∂ u) = ∂ u`
  (`TauCeti.beurlingL2_toLp_conjWirtingerDerivCLM`,
  `TauCeti.beurlingLp_toLp_conjWirtingerDerivCLM`).
  On the Fourier side `bar∂` and `∂` multiply by `πi ξ` and `πi conj ξ`.
* For smooth compactly supported `f`, `∂ (T f) = B f` almost everywhere
  (`HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp`). In particular
  `∂ (T f) ∈ Lᵖ(ℂ)` for `1 < p < ∞`, and the full real derivative obeys the global bound
  `‖D (T f)‖_{Lᵖ(ℂ)} ≤ C ‖f‖_{Lᵖ(ℂ)}` (`TauCeti.exists_eLpNorm_fderiv_cauchyTransform_le`).

The transform `T f` itself is not a Schwartz function: it decays only like `1 / w`, and for
`1 < p ≤ 2` and data with nonzero integral it is not in `Lᵖ(ℂ)`. The proof of `∂ (T f) = B f`
therefore cuts `T f` off. For a cutoff `χ_R` equal to `1` on the disc of radius `R` and to `0`
outside radius `2 R`, with `‖Dχ_R‖ ≤ C / R`, the product `χ_R • T f` is a Schwartz function, so
`B (bar∂ (χ_R • T f)) = ∂ (χ_R • T f)`. Once `R` exceeds the support radius,
`bar∂ (χ_R • T f) = f + (bar∂ χ_R) • T f` and `∂ (χ_R • T f) = χ_R • ∂ (T f) + (∂ χ_R) • T f`.
Both error terms are bounded by `(C / R) (M / R)` on a disc of radius `2 R`, from the decay
`‖w‖ ‖T f w‖ ≤ M` (`TauCeti.norm_mul_norm_cauchyTransform_le`), so their `L²` norms are
`O(1 / R)`. Hence `χ_R • ∂ (T f) → B f` in `L²`, and Fatou's lemma identifies the pointwise limit
`∂ (T f)` with `B f`. Passing from `L²` to `Lᵖ` uses that the `Lᵖ` and `L²` realizations of `B`
agree on Schwartz functions.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.2 (the Beurling transform `∂ ∘ T` and the Calderón–Zygmund inequality).
* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, second edition, Chapter V, §A
  (the operators `P` and `T` with `∂(P f) = T f` and `bar∂ (P f) = f`).
-/

public noncomputable section

open MeasureTheory Complex ComplexConjugate Metric Filter Topology Function
open scoped ENNReal NNReal SchwartzMap Real ContDiff FourierTransform

namespace TauCeti

/-! ### Pointwise facts -/

section Pointwise

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- In one variable the real derivative is controlled by its two Wirtinger parts:
`‖Df(x)‖ ≤ ‖∂f(x)‖ + ‖bar∂f(x)‖`. -/
theorem norm_fderiv_le_norm_wirtingerDeriv_add_norm_conjWirtingerDeriv (f : ℂ → W) (x : ℂ) :
    ‖fderiv ℝ f x‖ ≤ ‖wirtingerDeriv f x 1‖ + ‖conjWirtingerDeriv f x 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_smul, norm_smul, Complex.norm_conj]
  ring

/-- The Cauchy transform of compactly supported data is as smooth as the data. -/
theorem _root_.HasCompactSupport.contDiff_cauchyTransform {n : ℕ∞} {f : ℂ → W}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ n f) : ContDiff ℝ n (cauchyTransform f) := by
  rw [cauchyTransform_eq_convolution]
  exact (hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    Complex.locallyIntegrable_inv hf).const_smul _

/-- **Decay of the Cauchy transform.** If `f` is integrable and supported in the disc of radius
`r` about the origin, then `‖w‖ ‖T f w‖ ≤ 2 π⁻¹ ‖f‖_{L¹}` for `‖w‖ ≥ 2 r`. -/
theorem norm_mul_norm_cauchyTransform_le {f : ℂ → W} {r : ℝ}
    (hf : support f ⊆ closedBall 0 r) (hfi : Integrable f) {w : ℂ} (hw : 2 * r ≤ ‖w‖) :
    ‖w‖ * ‖cauchyTransform f w‖ ≤ 2 * π⁻¹ * ∫ z, ‖f z‖ := by
  have hπ : 0 < π := Real.pi_pos
  rcases eq_or_ne w 0 with rfl | hw0
  · simp only [norm_zero, zero_mul]
    have : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun z ↦ norm_nonneg (f z)
    positivity
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hpt : ∀ z, ‖(w - z)⁻¹ • f z‖ ≤ 2 * ‖w‖⁻¹ * ‖f z‖ := fun z ↦ by
    by_cases hz : f z = 0
    · simp [hz]
    have hzr : ‖z‖ ≤ r := by simpa using hf hz
    have hwz : ‖w‖ / 2 ≤ ‖w - z‖ := by
      have := norm_sub_norm_le w z
      linarith
    rw [norm_smul, norm_inv]
    gcongr
    calc ‖w - z‖⁻¹ ≤ (‖w‖ / 2)⁻¹ := inv_anti₀ (by positivity) hwz
      _ = 2 * ‖w‖⁻¹ := by field_simp
  have hint := norm_integral_le_of_norm_le (hfi.norm.const_mul (2 * ‖w‖⁻¹)) (.of_forall hpt)
  rw [integral_const_mul] at hint
  rw [cauchyTransform_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hπ.le]
  calc ‖w‖ * (π⁻¹ * ‖∫ z, (w - z)⁻¹ • f z‖)
      ≤ ‖w‖ * (π⁻¹ * (2 * ‖w‖⁻¹ * ∫ z, ‖f z‖)) := by gcongr
    _ = 2 * π⁻¹ * ∫ z, ‖f z‖ := by field_simp

end Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ### The Beurling operator on Schwartz functions -/

/-- The spectral `L²` Beurling operator is the `L²` Fourier multiplier with the Beurling symbol. -/
private theorem beurlingL2_apply (v : Lp F 2 (volume : Measure ℂ)) :
    beurlingL2 F v = Lp.fourierMultiplierCLM F beurlingSymbolLinf v := by
  rw [← FourierTransform.fourierInv_fourier_eq (F := Lp F 2 (volume : Measure ℂ))
      (beurlingL2 F v), fourier_beurlingL2, ← Lp.fourier_fourierMultiplierCLM,
    FourierTransform.fourierInv_fourier_eq]

/-- **`B bar∂ = ∂` on Schwartz functions**, for the spectral `L²` realization of the Beurling
operator. On the Fourier side this is `(conj ξ / ξ) (πi ξ) = πi conj ξ`. -/
theorem beurlingL2_toLp_conjWirtingerDerivCLM (u : 𝓢(ℂ, F)) :
    beurlingL2 F ((SchwartzMap.conjWirtingerDerivCLM F u).toLp 2) =
      (SchwartzMap.wirtingerDerivCLM F u).toLp 2 := by
  rw [beurlingL2_apply]
  refine (SchwartzMap.toLp_eq_fourierMultiplierCLM_of_fourier_eq_smul (F := F) _
    (f := SchwartzMap.conjWirtingerDerivCLM F u) (g := SchwartzMap.wirtingerDerivCLM F u)
    coeFn_beurlingSymbolLinf fun ξ ↦ ?_).symm
  rw [SchwartzMap.fourier_wirtingerDerivCLM_apply,
    SchwartzMap.fourier_conjWirtingerDerivCLM_apply, smul_smul]
  congr 1
  linear_combination (-(π : ℂ) * I) * beurlingSymbol_mul ξ

/-- **`B bar∂ = ∂` on Schwartz functions** in every `Lᵖ`, `1 < p < ∞`. -/
theorem beurlingLp_toLp_conjWirtingerDerivCLM {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : 𝓢(ℂ, F)) :
    beurlingLp p hp hp_top ((SchwartzMap.conjWirtingerDerivCLM F u).toLp p) =
      (SchwartzMap.wirtingerDerivCLM F u).toLp p := by
  apply Lp.ext
  filter_upwards [beurlingLp_toLp hp hp_top (SchwartzMap.conjWirtingerDerivCLM F u),
    (SchwartzMap.wirtingerDerivCLM F u).coeFn_toLp 2 volume,
    (SchwartzMap.wirtingerDerivCLM F u).coeFn_toLp p volume] with z h₁ h₂ h₃
  rw [h₁, beurlingL2_toLp_conjWirtingerDerivCLM, h₂, h₃]

/-! ### The Wirtinger derivative of the Cauchy transform -/

section Cutoff

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- A cutoff equal to `1` on the disc of radius `R` and to `0` outside radius `2 R` has
derivative supported in the closed disc of radius `2 R`, where a decay `‖x‖ ‖u x‖ ≤ M` for
`‖x‖ ≥ R` bounds `‖Dχ‖ ‖u‖` by `A (M / R)`. -/
private theorem norm_fderiv_mul_norm_le_indicator {χ : ℂ → ℝ} {u : ℂ → F} {R A M : ℝ}
    (hR : 0 < R) (hχ1 : ∀ x ∈ closedBall (0 : ℂ) R, χ x = 1)
    (hχ0 : ∀ x, 2 * R < dist x 0 → χ x = 0) (hA : ∀ x, ‖fderiv ℝ χ x‖ ≤ A)
    (hu : ∀ x : ℂ, R ≤ ‖x‖ → ‖x‖ * ‖u x‖ ≤ M) (x : ℂ) :
    ‖fderiv ℝ χ x‖ * ‖u x‖ ≤ (closedBall (0 : ℂ) (2 * R)).indicator (fun _ ↦ A * (M / R)) x := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hM0 : 0 ≤ M := by
    have h := hu R (by simp [abs_of_pos hR])
    exact (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans h
  have hzero : fderiv ℝ χ x = 0 → ‖fderiv ℝ χ x‖ * ‖u x‖ ≤
      (closedBall (0 : ℂ) (2 * R)).indicator (fun _ ↦ A * (M / R)) x := fun h ↦ by
    rw [h, norm_zero, zero_mul]
    exact Set.indicator_nonneg (fun _ _ ↦ by positivity) x
  rcases lt_or_ge ‖x‖ R with hx | hx
  · refine hzero ?_
    have hev : χ =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
      exact hχ1 y (ball_subset_closedBall hy)
    rw [hev.fderiv_eq, fderiv_const_apply]
  rcases lt_or_ge (2 * R) ‖x‖ with hx' | hx'
  · refine hzero ?_
    have hev : χ =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      have hopen : IsOpen {y : ℂ | 2 * R < dist y 0} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      filter_upwards [hopen.mem_nhds (by simpa using hx')] with y hy
      exact hχ0 y hy
    rw [hev.fderiv_eq, fderiv_const_apply]
  rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 hx')]
  have hux : ‖u x‖ ≤ M / R := by
    rw [le_div_iff₀ hR]
    calc ‖u x‖ * R ≤ ‖u x‖ * ‖x‖ := by gcongr
      _ = ‖x‖ * ‖u x‖ := mul_comm _ _
      _ ≤ M := hu x hx
  exact mul_le_mul (hA x) hux (norm_nonneg _) hA0

/-- The `L²` norm of a constant on the closed disc of radius `R`. -/
private theorem eLpNorm_indicator_closedBall_two (c R : ℝ) :
    eLpNorm ((closedBall (0 : ℂ) R).indicator fun _ ↦ c) 2 volume =
      ENNReal.ofReal (|c| * R) * (NNReal.pi : ℝ≥0∞) ^ (2⁻¹ : ℝ) := by
  rw [eLpNorm_indicator_const measurableSet_closedBall.nullMeasurableSet two_ne_zero
    ENNReal.ofNat_ne_top, Complex.volume_closedBall, ENNReal.toReal_ofNat,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), one_div, ← mul_assoc,
    show ((2 : ℝ))⁻¹ = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.pow_rpow_inv_natCast two_ne_zero,
    Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg c)]

end Cutoff

/-- **`∂ (T f) = B f` in `L²`.** For smooth compactly supported `f`, the Wirtinger derivative of
the Cauchy transform agrees almost everywhere with the spectral `L²` Beurling operator applied
to `f`. -/
theorem _root_.HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingL2 {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) :
    (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) =ᵐ[volume]
      beurlingL2 F ((hf.continuous.memLp_of_hasCompactSupport hc).toLp f) := by
  set fS : 𝓢(ℂ, F) := hc.toSchwartzMap hf
  set G := beurlingL2 F (fS.toLp 2 volume)
  change (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) =ᵐ[volume] G
  set u := cauchyTransform f
  have hu : ContDiff ℝ ∞ u := hc.contDiff_cauchyTransform hf
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hwu : Continuous fun x ↦ wirtingerDeriv u x 1 := by
    simp only [wirtingerDeriv_apply]
    fun_prop
  have hcu (x : ℂ) : conjWirtingerDeriv u x 1 = f x :=
    hc.conjWirtingerDeriv_cauchyTransform (hf.of_le (by simp)) x
  -- The support radius `r` and the decay constant `M`.
  obtain ⟨r₀, hr₀⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set r := max r₀ 1
  have hr : 0 < r := lt_max_of_lt_right one_pos
  have hsupp : support f ⊆ closedBall 0 r :=
    (subset_tsupport f).trans (hr₀.trans (closedBall_subset_closedBall (le_max_left _ _)))
  set M := 2 * π⁻¹ * ∫ z, ‖f z‖
  have hdecay (x : ℂ) (hx : 2 * r ≤ ‖x‖) : ‖x‖ * ‖u x‖ ≤ M :=
    norm_mul_norm_cauchyTransform_le hsupp (hf.continuous.integrable_of_hasCompactSupport hc) hx
  -- The cutoffs `χ n`, equal to `1` on the disc of radius `R n = 2 r + n`.
  obtain ⟨C₀, hC₀, hcut⟩ := exists_cutoff_fderiv_bound (E := ℂ)
  set R : ℕ → ℝ := fun n ↦ 2 * r + n
  have hR (n : ℕ) : 0 < R n := by positivity
  choose χ χ' hχs hχ01 hχ1 hχ0 hχd hχ' using fun n ↦ hcut 0 (R n) (hR n)
  have hχfd (n : ℕ) (x : ℂ) : ‖fderiv ℝ (χ n) x‖ ≤ C₀ * (R n)⁻¹ := by
    rw [(hχd n x).fderiv]
    exact hχ' n x
  have hχdiff (n : ℕ) : Differentiable ℝ (χ n) := fun x ↦ (hχd n x).differentiableAt
  have hχc (n : ℕ) : HasCompactSupport (χ n) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * R n)) fun x hx ↦
      hχ0 n x (by simpa [mem_closedBall] using hx)
  have hχf (n : ℕ) (x : ℂ) : χ n x • f x = f x := by
    by_cases hx : f x = 0
    · simp [hx]
    rw [hχ1 n x (closedBall_subset_closedBall (by simp only [R]; linarith [n.cast_nonneg (α := ℝ)])
      (hsupp hx)), one_smul]
  -- The truncations `φ n = χ n • T f` are Schwartz functions.
  set φ : ℕ → ℂ → F := fun n y ↦ χ n y • u y
  have hφs (n : ℕ) : ContDiff ℝ ∞ (φ n) := (hχs n ⊤).smul hu
  have hφc (n : ℕ) : HasCompactSupport (φ n) := (hχc n).smul_right
  set Φ : ℕ → 𝓢(ℂ, F) := fun n ↦ (hφc n).toSchwartzMap (hφs n)
  have hΦ (n : ℕ) : ⇑(Φ n) = φ n := rfl
  -- Bounds on the two cutoff errors.
  have hdecay' (n : ℕ) (x : ℂ) (hx : R n ≤ ‖x‖) : ‖x‖ * ‖u x‖ ≤ M :=
    hdecay x (le_trans (by simp only [R]; linarith [n.cast_nonneg (α := ℝ)]) hx)
  set c : ℕ → ℝ := fun n ↦ C₀ * (R n)⁻¹ * (M / R n)
  have hind (n : ℕ) (x : ℂ) : ‖fderiv ℝ (χ n) x‖ * ‖u x‖ ≤
      (closedBall (0 : ℂ) (2 * R n)).indicator (fun _ ↦ c n) x :=
    norm_fderiv_mul_norm_le_indicator (hR n) (hχ1 n) (hχ0 n) (hχfd n) (hdecay' n) x
  have he (n : ℕ) (x : ℂ) : ‖conjWirtingerDeriv (φ n) x 1 - f x‖ ≤
      (closedBall (0 : ℂ) (2 * R n)).indicator (fun _ ↦ c n) x := by
    have h := norm_conjWirtingerDeriv_smul_sub_smul_le (hχdiff n x)
      (hu.differentiable (by simp) x) (1 : ℂ)
    rw [hcu, hχf, norm_one, mul_one] at h
    exact h.trans (hind n x)
  have hd (n : ℕ) (x : ℂ) : ‖wirtingerDeriv (φ n) x 1 - χ n x • wirtingerDeriv u x 1‖ ≤
      (closedBall (0 : ℂ) (2 * R n)).indicator (fun _ ↦ c n) x := by
    have h := norm_wirtingerDeriv_smul_sub_smul_le (hχdiff n x)
      (hu.differentiable (by simp) x) (1 : ℂ)
    rw [norm_one, mul_one] at h
    exact h.trans (hind n x)
  -- The `L²` size of the errors tends to zero.
  set b : ℕ → ℝ≥0∞ := fun n ↦ eLpNorm ((closedBall (0 : ℂ) (2 * R n)).indicator
    fun _ ↦ c n) 2 volume
  have hb : Tendsto b atTop (𝓝 0) := by
    have hM : 0 ≤ M := by
      have : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun z ↦ norm_nonneg (f z)
      positivity
    have hbeq (n : ℕ) : b n = ENNReal.ofReal (2 * C₀ * M / R n) *
        (NNReal.pi : ℝ≥0∞) ^ (2⁻¹ : ℝ) := by
      simp only [b]
      rw [eLpNorm_indicator_closedBall_two]
      congr 2
      have hRn := (hR n).ne'
      rw [abs_of_nonneg (by simp only [c]; positivity)]
      simp only [c]
      field_simp
    rw [show b = _ from funext hbeq]
    rw [← zero_mul ((NNReal.pi : ℝ≥0∞) ^ (2⁻¹ : ℝ))]
    refine ENNReal.Tendsto.mul_const ?_ (.inr (by simp))
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop ?_)
    exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  -- `χ n • ∂ (T f) → B f` in `L²`.
  obtain ⟨Cb, hCb⟩ := exists_eLpNorm_beurlingL2_le (F := F) (p := 2) (by norm_num)
    ENNReal.ofNat_ne_top
  have hmeasG : AEStronglyMeasurable G volume := Lp.aestronglyMeasurable G
  have hbound (n : ℕ) : eLpNorm (fun x ↦ G x - χ n x • wirtingerDeriv u x 1) 2 volume ≤
      Cb * b n + b n := by
    set v : Lp F 2 (volume : Measure ℂ) :=
      fS.toLp 2 volume - (SchwartzMap.conjWirtingerDerivCLM F (Φ n)).toLp 2 volume
    have hBv : beurlingL2 F v = G - (SchwartzMap.wirtingerDerivCLM F (Φ n)).toLp 2 volume := by
      rw [map_sub, beurlingL2_toLp_conjWirtingerDerivCLM]
    have hvae : ⇑v =ᵐ[volume] fun x ↦ f x - conjWirtingerDeriv (φ n) x 1 := by
      filter_upwards [Lp.coeFn_sub (fS.toLp 2 volume)
        ((SchwartzMap.conjWirtingerDerivCLM F (Φ n)).toLp 2 volume), fS.coeFn_toLp 2 volume,
        (SchwartzMap.conjWirtingerDerivCLM F (Φ n)).coeFn_toLp 2 volume] with x h₁ h₂ h₃
      rw [h₁, Pi.sub_apply, h₂, h₃, SchwartzMap.conjWirtingerDerivCLM_apply, hΦ]
      rfl
    have hBae : ⇑(beurlingL2 F v) =ᵐ[volume] fun x ↦ G x - wirtingerDeriv (φ n) x 1 := by
      rw [hBv]
      filter_upwards [Lp.coeFn_sub G ((SchwartzMap.wirtingerDerivCLM F (Φ n)).toLp 2 volume),
        (SchwartzMap.wirtingerDerivCLM F (Φ n)).coeFn_toLp 2 volume] with x h₁ h₂
      rw [h₁, Pi.sub_apply, h₂, SchwartzMap.wirtingerDerivCLM_apply, hΦ]
    have hwφ : Continuous fun x ↦ wirtingerDeriv (φ n) x 1 := by
      have := (SchwartzMap.wirtingerDerivCLM F (Φ n)).continuous
      simpa only [funext (SchwartzMap.wirtingerDerivCLM_apply (Φ n)), hΦ] using this
    have hχn : Continuous (χ n) := (hχs n 0).continuous
    have h₁ : eLpNorm (fun x ↦ G x - wirtingerDeriv (φ n) x 1) 2 volume ≤ Cb * b n := by
      rw [← eLpNorm_congr_ae hBae]
      refine (hCb v).trans ?_
      gcongr
      rw [eLpNorm_congr_ae hvae]
      refine eLpNorm_mono_real ?_ fun x ↦ ?_
      · exact (hf.continuous.sub (by
          have := (SchwartzMap.conjWirtingerDerivCLM F (Φ n)).continuous
          simpa only [funext (SchwartzMap.conjWirtingerDerivCLM_apply (Φ n)), hΦ]
            using this)).aestronglyMeasurable
      · rw [norm_sub_rev]
        exact he n x
    have h₂ : eLpNorm (fun x ↦ wirtingerDeriv (φ n) x 1 - χ n x • wirtingerDeriv u x 1) 2
        volume ≤ b n :=
      eLpNorm_mono_real (hwφ.sub (hχn.smul hwu)).aestronglyMeasurable (hd n)
    calc eLpNorm (fun x ↦ G x - χ n x • wirtingerDeriv u x 1) 2 volume
        = eLpNorm ((fun x ↦ G x - wirtingerDeriv (φ n) x 1) +
            fun x ↦ wirtingerDeriv (φ n) x 1 - χ n x • wirtingerDeriv u x 1) 2 volume := by
          congr 1
          funext x
          simp
      _ ≤ _ := eLpNorm_add_le one_le_two
      _ ≤ Cb * b n + b n := add_le_add h₁ h₂
  -- Fatou's lemma identifies the pointwise limit.
  have hlim : ∀ x, Tendsto (fun n ↦ G x - χ n x • wirtingerDeriv u x 1) atTop
      (𝓝 (G x - wirtingerDeriv u x 1)) := fun x ↦ by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
    rw [hχ1 n x (mem_closedBall_zero_iff.2 ?_), one_smul]
    have := (Nat.le_ceil ‖x‖).trans (Nat.cast_le.2 hn)
    simp only [R]
    linarith
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (fun n ↦ (hmeasG.sub ((hχs n 0).continuous.smul hwu).aestronglyMeasurable))
    (fun x ↦ G x - wirtingerDeriv u x 1) (hmeasG.sub hwu.aestronglyMeasurable)
    (.of_forall hlim)
  have hzero : eLpNorm (fun x ↦ G x - wirtingerDeriv u x 1) 2 volume = 0 := by
    refine le_antisymm (hfatou.trans ?_) (by positivity)
    have htend : Tendsto (fun n ↦ (Cb : ℝ≥0∞) * b n + b n) atTop (𝓝 0) := by
      simpa using (ENNReal.Tendsto.const_mul hb (.inr ENNReal.coe_ne_top)).add hb
    rw [← htend.liminf_eq]
    exact liminf_le_liminf (.of_forall hbound)
  rw [eLpNorm_eq_zero_iff two_ne_zero] at hzero
  filter_upwards [hzero] with x hx
  exact (sub_eq_zero.1 hx).symm

/-- **`∂ T = B` on smooth compactly supported data.** For `1 < p < ∞` and smooth compactly
supported `f`, the Wirtinger derivative `∂ (T f)` of the Cauchy transform agrees almost
everywhere with the Beurling operator on `Lᵖ(ℂ)` applied to `f`. -/
theorem _root_.HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) =ᵐ[volume]
      beurlingLp p hp hp_top ((hf.continuous.memLp_of_hasCompactSupport hc).toLp f) :=
  (hc.wirtingerDeriv_cauchyTransform_ae_eq_beurlingL2 hf).trans
    (beurlingLp_toLp hp hp_top (hc.toSchwartzMap hf)).symm

/-- For `1 < p < ∞` the Wirtinger derivative `∂ (T f)` of the Cauchy transform of smooth
compactly supported data lies in `Lᵖ(ℂ)`. -/
theorem _root_.HasCompactSupport.memLp_wirtingerDeriv_cauchyTransform {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    MemLp (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) p volume := by
  have : Fact (1 ≤ p) := ⟨hp.le⟩
  exact (Lp.memLp _).ae_eq (hc.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp hf hp hp_top).symm

/-- **The global derivative bound for the Cauchy transform.** For `1 < p < ∞` there is a
constant `C` with `‖D (T f)‖_{Lᵖ(ℂ)} ≤ C ‖f‖_{Lᵖ(ℂ)}` for every smooth compactly supported `f`
with values in a complex Hilbert space. The transform `T f` itself need not lie in `Lᵖ(ℂ)`. -/
theorem exists_eLpNorm_fderiv_cauchyTransform_le {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ f : ℂ → F, HasCompactSupport f → ContDiff ℝ ∞ f →
      eLpNorm (fderiv ℝ (cauchyTransform f)) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨Cb, hCb⟩ := exists_eLpNorm_beurlingL2_le (F := F) hp hp_top
  refine ⟨Cb + 1, fun f hc hf ↦ ?_⟩
  set u := cauchyTransform f
  have hu : ContDiff ℝ ∞ u := hc.contDiff_cauchyTransform hf
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hwu : Continuous fun x ↦ wirtingerDeriv u x 1 := by
    simp only [wirtingerDeriv_apply]
    fun_prop
  have hcu : (fun x ↦ conjWirtingerDeriv u x 1) = f :=
    funext (hc.conjWirtingerDeriv_cauchyTransform (hf.of_le (by simp)))
  have hB : eLpNorm (fun x ↦ wirtingerDeriv u x 1) p volume ≤ Cb * eLpNorm f p volume := by
    rw [eLpNorm_congr_ae (hc.wirtingerDeriv_cauchyTransform_ae_eq_beurlingL2 hf)]
    refine (hCb _).trans_eq ?_
    rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  calc eLpNorm (fderiv ℝ u) p volume
      ≤ eLpNorm (fun x ↦ ‖wirtingerDeriv u x 1‖ + ‖conjWirtingerDeriv u x 1‖) p volume :=
        eLpNorm_mono_real hdu.aestronglyMeasurable
          (norm_fderiv_le_norm_wirtingerDeriv_add_norm_conjWirtingerDeriv u)
    _ ≤ eLpNorm (fun x ↦ wirtingerDeriv u x 1) p volume + eLpNorm f p volume := by
        refine (eLpNorm_add_le (f := fun x ↦ ‖wirtingerDeriv u x 1‖)
          (g := fun x ↦ ‖conjWirtingerDeriv u x 1‖) hp.le).trans_eq ?_
        rw [eLpNorm_norm _ hwu.aestronglyMeasurable,
          eLpNorm_norm (fun x ↦ conjWirtingerDeriv u x 1)
            (hcu ▸ hf.continuous.aestronglyMeasurable), hcu]
    _ ≤ Cb * eLpNorm f p volume + eLpNorm f p volume := by gcongr
    _ = (Cb + 1 : ℝ≥0) * eLpNorm f p volume := by
        rw [ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]

end TauCeti
