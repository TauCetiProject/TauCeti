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
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
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

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ### The Beurling operator on Schwartz functions -/

/-- **`B bar∂ = ∂` on Schwartz functions**, for the spectral `L²` realization of the Beurling
operator. On the Fourier side this is `(conj ξ / ξ) (πi ξ) = πi conj ξ`. -/
theorem beurlingL2_toLp_conjWirtingerDerivCLM (u : 𝓢(ℂ, F)) :
    beurlingL2 F ((SchwartzMap.conjWirtingerDerivCLM F u).toLp 2) =
      (SchwartzMap.wirtingerDerivCLM F u).toLp 2 := by
  rw [beurlingL2_def]
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

/-- For cutoffs at radius `R = a + n` with derivative at most `A / R`, against data of decay
`M / R`, the `L²` norm of the error bound on the disc of radius `2 R` is `O(1 / R)`. -/
private theorem tendsto_eLpNorm_indicator_closedBall {a A M : ℝ} (ha : 0 < a) (hA : 0 ≤ A)
    (hM : 0 ≤ M) :
    Tendsto (fun n : ℕ ↦ eLpNorm ((closedBall (0 : ℂ) (2 * (a + n))).indicator
      fun _ ↦ A * (a + n)⁻¹ * (M / (a + n))) 2 volume) atTop (𝓝 0) := by
  have hbeq (n : ℕ) : eLpNorm ((closedBall (0 : ℂ) (2 * (a + n))).indicator
      fun _ ↦ A * (a + n)⁻¹ * (M / (a + n))) 2 volume =
        ENNReal.ofReal (2 * A * M / (a + n)) * (NNReal.pi : ℝ≥0∞) ^ (2⁻¹ : ℝ) := by
    have hn : 0 < a + n := by positivity
    rw [eLpNorm_indicator_closedBall_two, abs_of_nonneg (by positivity)]
    congr 2
    field_simp
  simp_rw [hbeq]
  rw [← zero_mul ((NNReal.pi : ℝ≥0∞) ^ (2⁻¹ : ℝ))]
  refine ENNReal.Tendsto.mul_const ?_ (.inr (by simp))
  rw [← ENNReal.ofReal_zero]
  exact ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop))

end Cutoff

/-- The Beurling identity `B bar∂ = ∂` with an error: for Schwartz `g` and `φ`,
`‖B g - ∂φ‖_{L²}` is controlled by `‖g - bar∂φ‖_{L²}` through any `L²` bound for `B`. -/
private theorem eLpNorm_beurlingL2_sub_wirtingerDeriv_le {C : ℝ≥0}
    (hC : ∀ v : Lp F 2 (volume : Measure ℂ),
      eLpNorm (beurlingL2 F v) 2 volume ≤ C * eLpNorm v 2 volume) (g φ : 𝓢(ℂ, F)) :
    eLpNorm (fun x ↦ beurlingL2 F (g.toLp 2 volume) x - wirtingerDeriv (⇑φ) x 1) 2 volume ≤
      C * eLpNorm (fun x ↦ g x - conjWirtingerDeriv (⇑φ) x 1) 2 volume := by
  set v : Lp F 2 (volume : Measure ℂ) :=
    g.toLp 2 volume - (SchwartzMap.conjWirtingerDerivCLM F φ).toLp 2 volume
  have hvae : ⇑v =ᵐ[volume] fun x ↦ g x - conjWirtingerDeriv (⇑φ) x 1 := by
    filter_upwards [Lp.coeFn_sub (g.toLp 2 volume)
      ((SchwartzMap.conjWirtingerDerivCLM F φ).toLp 2 volume), g.coeFn_toLp 2 volume,
      (SchwartzMap.conjWirtingerDerivCLM F φ).coeFn_toLp 2 volume] with x h₁ h₂ h₃
    rw [h₁, Pi.sub_apply, h₂, h₃, SchwartzMap.conjWirtingerDerivCLM_apply]
  have hBae : ⇑(beurlingL2 F v) =ᵐ[volume]
      fun x ↦ beurlingL2 F (g.toLp 2 volume) x - wirtingerDeriv (⇑φ) x 1 := by
    rw [map_sub, beurlingL2_toLp_conjWirtingerDerivCLM]
    filter_upwards [Lp.coeFn_sub (beurlingL2 F (g.toLp 2 volume))
      ((SchwartzMap.wirtingerDerivCLM F φ).toLp 2 volume),
      (SchwartzMap.wirtingerDerivCLM F φ).coeFn_toLp 2 volume] with x h₁ h₂
    rw [h₁, Pi.sub_apply, h₂, SchwartzMap.wirtingerDerivCLM_apply]
  rw [← eLpNorm_congr_ae hBae, ← eLpNorm_congr_ae hvae]
  exact hC v

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- **Fatou's lemma for `L²` approximation.** If `g n → g₀` pointwise and the `L²` norms of
`g n` are bounded by a sequence tending to `0`, then `g₀ = 0` almost everywhere. -/
private theorem ae_eq_zero_of_tendsto_of_eLpNorm_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → F} {g₀ : α → F} {c : ℕ → ℝ≥0∞}
    (hg : ∀ n, AEStronglyMeasurable (g n) μ) (hg₀ : AEStronglyMeasurable g₀ μ)
    (hlim : ∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 (g₀ x)))
    (hgc : ∀ n, eLpNorm (g n) 2 μ ≤ c n) (hc : Tendsto c atTop (𝓝 0)) : g₀ =ᵐ[μ] 0 := by
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) hg g₀ hg₀ (.of_forall hlim)
  refine (eLpNorm_eq_zero_iff two_ne_zero).1 (le_antisymm (hfatou.trans ?_) (by positivity))
  rw [← hc.liminf_eq]
  exact liminf_le_liminf (.of_forall hgc)

/-- **One cutoff step.** For a smooth compactly supported cutoff `χ` with `χ • f = f`, the `L²`
distance from `B f` to `χ • ∂ (T f)` is at most `(C + 1) ‖b‖_{L²}` for any pointwise bound `b`
of `‖Dχ‖ ‖T f‖`, where `C` bounds `B` on `L²`. -/
private theorem eLpNorm_beurlingL2_sub_smul_wirtingerDeriv_cauchyTransform_le {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) {C : ℝ≥0}
    (hC : ∀ v : Lp F 2 (volume : Measure ℂ),
      eLpNorm (beurlingL2 F v) 2 volume ≤ C * eLpNorm v 2 volume)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχf : ∀ x, χ x • f x = f x)
    {b : ℂ → ℝ} (hb : ∀ x, ‖fderiv ℝ χ x‖ * ‖cauchyTransform f x‖ ≤ b x) :
    eLpNorm (fun x ↦ beurlingL2 F ((hc.toSchwartzMap hf).toLp 2 volume) x -
      χ x • wirtingerDeriv (cauchyTransform f) x 1) 2 volume ≤
        C * eLpNorm b 2 volume + eLpNorm b 2 volume := by
  set G := beurlingL2 F ((hc.toSchwartzMap hf).toLp 2 volume)
  set u := cauchyTransform f
  have hu : ContDiff ℝ ∞ u := hc.contDiff_cauchyTransform hf
  have hud : Differentiable ℝ u := hu.differentiable (by simp)
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hwu : Continuous fun x ↦ wirtingerDeriv u x 1 :=
    hc.continuous_wirtingerDeriv_cauchyTransform (hf.of_le (by simp))
  -- The truncation `φ = χ • T f` is a Schwartz function.
  set φ : ℂ → F := fun y ↦ χ y • u y
  set Φ : 𝓢(ℂ, F) := hχc.smul_right.toSchwartzMap (hχ.smul hu)
  have hΦ : ⇑Φ = φ := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hfS : ⇑(hc.toSchwartzMap hf) = f := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hwφ : Continuous fun x ↦ wirtingerDeriv φ x 1 := by
    simpa only [funext (SchwartzMap.wirtingerDerivCLM_apply Φ), hΦ] using
      (SchwartzMap.wirtingerDerivCLM F Φ).continuous
  have hcφ : Continuous fun x ↦ conjWirtingerDeriv φ x 1 := by
    simpa only [funext (SchwartzMap.conjWirtingerDerivCLM_apply Φ), hΦ] using
      (SchwartzMap.conjWirtingerDerivCLM F Φ).continuous
  -- `bar∂ φ = f + (bar∂ χ) • T f` and `B bar∂ φ = ∂ φ`.
  have h₁ : eLpNorm (fun x ↦ G x - wirtingerDeriv φ x 1) 2 volume ≤ C * eLpNorm b 2 volume := by
    have h := eLpNorm_beurlingL2_sub_wirtingerDeriv_le hC (hc.toSchwartzMap hf) Φ
    rw [hΦ, hfS] at h
    refine h.trans ?_
    gcongr
    refine eLpNorm_mono_real (hf.continuous.sub hcφ).aestronglyMeasurable fun x ↦ ?_
    have h := norm_conjWirtingerDeriv_smul_sub_smul_le (hχd x) (hud x) (1 : ℂ)
    rw [hc.conjWirtingerDeriv_cauchyTransform (hf.of_le (by simp)), hχf, norm_one,
      mul_one] at h
    rw [norm_sub_rev]
    exact h.trans (hb x)
  -- `∂ φ = χ • ∂ (T f) + (∂ χ) • T f`.
  have h₂ : eLpNorm (fun x ↦ wirtingerDeriv φ x 1 - χ x • wirtingerDeriv u x 1) 2 volume ≤
      eLpNorm b 2 volume := by
    refine eLpNorm_mono_real (hwφ.sub (hχ.continuous.smul hwu)).aestronglyMeasurable
      fun x ↦ ?_
    have h := norm_wirtingerDeriv_smul_sub_smul_le (hχd x) (hud x) (1 : ℂ)
    rw [norm_one, mul_one] at h
    exact h.trans (hb x)
  calc eLpNorm (fun x ↦ G x - χ x • wirtingerDeriv u x 1) 2 volume
      = eLpNorm ((fun x ↦ G x - wirtingerDeriv φ x 1) +
          fun x ↦ wirtingerDeriv φ x 1 - χ x • wirtingerDeriv u x 1) 2 volume := by
        congr 1
        funext x
        simp
    _ ≤ _ := eLpNorm_add_le one_le_two
    _ ≤ C * eLpNorm b 2 volume + eLpNorm b 2 volume := add_le_add h₁ h₂

/-- **`∂ (T f) = B f` in `L²`.** For smooth compactly supported `f`, the Wirtinger derivative of
the Cauchy transform agrees almost everywhere with the spectral `L²` Beurling operator applied
to `f`. -/
theorem _root_.HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingL2 {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) :
    (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) =ᵐ[volume]
      beurlingL2 F ((hf.continuous.memLp_of_hasCompactSupport hc).toLp f) := by
  rw [← hc.toSchwartzMap_toLp hf]
  set G := beurlingL2 F ((hc.toSchwartzMap hf).toLp 2 volume)
  set u := cauchyTransform f
  have hwu : Continuous fun x ↦ wirtingerDeriv u x 1 :=
    hc.continuous_wirtingerDeriv_cauchyTransform (hf.of_le (by simp))
  -- The support radius `r` and the decay constant `M`.
  obtain ⟨r₀, hr₀⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set r := max r₀ 1
  have hr : 0 < r := lt_max_of_lt_right one_pos
  have hsupp : support f ⊆ closedBall 0 r :=
    (subset_tsupport f).trans (hr₀.trans (closedBall_subset_closedBall (le_max_left _ _)))
  set M := 2 * π⁻¹ * ∫ z, ‖f z‖
  have hM : 0 ≤ M := by
    have : 0 ≤ ∫ z, ‖f z‖ := integral_nonneg fun z ↦ norm_nonneg (f z)
    positivity
  -- The cutoffs `χ n`, equal to `1` on the disc of radius `R n = 2 r + n`.
  obtain ⟨C₀, hC₀, hcut⟩ := exists_cutoff_fderiv_bound (E := ℂ)
  set R : ℕ → ℝ := fun n ↦ 2 * r + n
  have hR (n : ℕ) : 0 < R n := by positivity
  have hrR (n : ℕ) : 2 * r ≤ R n := by simp only [R]; linarith [n.cast_nonneg (α := ℝ)]
  choose χ χ' hχs _ hχ1 hχ0 hχd hχ' using fun n ↦ hcut 0 (R n) (hR n)
  have hχfd (n : ℕ) (x : ℂ) : ‖fderiv ℝ (χ n) x‖ ≤ C₀ * (R n)⁻¹ := by
    rw [(hχd n x).fderiv]
    exact hχ' n x
  have hχc (n : ℕ) : HasCompactSupport (χ n) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * R n)) fun x hx ↦
      hχ0 n x (by simpa [mem_closedBall] using hx)
  have hχf (n : ℕ) (x : ℂ) : χ n x • f x = f x := by
    by_cases hx : f x = 0
    · simp [hx]
    rw [hχ1 n x (closedBall_subset_closedBall (by linarith [hrR n]) (hsupp hx)), one_smul]
  -- The cutoff errors have `L²` norm `O(1 / R n)`.
  set b : ℕ → ℂ → ℝ := fun n ↦ (closedBall (0 : ℂ) (2 * R n)).indicator
    fun _ ↦ C₀ * (R n)⁻¹ * (M / R n)
  have hb (n : ℕ) (x : ℂ) : ‖fderiv ℝ (χ n) x‖ * ‖u x‖ ≤ b n x :=
    norm_fderiv_mul_norm_le_indicator (hR n) (hχ1 n) (hχ0 n) (hχfd n)
      (fun x hx ↦ norm_mul_norm_cauchyTransform_le hsupp
        (hf.continuous.integrable_of_hasCompactSupport hc) ((hrR n).trans hx)) x
  obtain ⟨Cb, hCb⟩ := exists_eLpNorm_beurlingL2_le (F := F) (p := 2) (by norm_num)
    ENNReal.ofNat_ne_top
  have htend : Tendsto (fun n ↦ (Cb : ℝ≥0∞) * eLpNorm (b n) 2 volume + eLpNorm (b n) 2 volume)
      atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_indicator_closedBall (a := 2 * r) (by positivity) hC₀ hM
    simpa using (ENNReal.Tendsto.const_mul h (.inr ENNReal.coe_ne_top)).add h
  -- `χ n • ∂ (T f) → ∂ (T f)` pointwise, so Fatou's lemma identifies the limit with `B f`.
  have hlim (x : ℂ) : Tendsto (fun n ↦ G x - χ n x • wirtingerDeriv u x 1) atTop
      (𝓝 (G x - wirtingerDeriv u x 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
    rw [hχ1 n x (mem_closedBall_zero_iff.2 ?_), one_smul]
    have := (Nat.le_ceil ‖x‖).trans (Nat.cast_le.2 hn)
    simp only [R]
    linarith
  have hzero := ae_eq_zero_of_tendsto_of_eLpNorm_le
    (fun n ↦ (Lp.aestronglyMeasurable G).sub ((hχs n 0).continuous.smul hwu).aestronglyMeasurable)
    ((Lp.aestronglyMeasurable G).sub hwu.aestronglyMeasurable) hlim
    (fun n ↦ eLpNorm_beurlingL2_sub_smul_wirtingerDeriv_cauchyTransform_le hc hf hCb (hχs n ⊤)
      (hχc n) (hχf n) (hb n)) htend
  filter_upwards [hzero] with x hx
  exact (sub_eq_zero.1 hx).symm

/-- **`∂ T = B` on smooth compactly supported data.** For `1 < p < ∞` and smooth compactly
supported `f`, the Wirtinger derivative `∂ (T f)` of the Cauchy transform agrees almost
everywhere with the Beurling operator on `Lᵖ(ℂ)` applied to `f`. -/
theorem _root_.HasCompactSupport.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) =ᵐ[volume]
      beurlingLp p hp hp_top ((hf.continuous.memLp_of_hasCompactSupport hc).toLp f) := by
  have h := hc.wirtingerDeriv_cauchyTransform_ae_eq_beurlingL2 hf
  rw [← hc.toSchwartzMap_toLp hf] at h ⊢
  exact h.trans (beurlingLp_toLp hp hp_top _).symm

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
theorem exists_eLpNorm_fderiv_cauchyTransform_le {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ f : ℂ → F, HasCompactSupport f → ContDiff ℝ ∞ f →
      eLpNorm (fderiv ℝ (cauchyTransform f)) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨Cb, hCb⟩ := exists_eLpNorm_beurlingL2_le (F := F) hp hp_top
  refine ⟨Cb + 1, fun f hc hf ↦ ?_⟩
  set u := cauchyTransform f
  have hdu : Continuous (fderiv ℝ u) :=
    (hc.contDiff_cauchyTransform hf).continuous_fderiv (by simp)
  have hwu : Continuous fun x ↦ wirtingerDeriv u x 1 :=
    hc.continuous_wirtingerDeriv_cauchyTransform (hf.of_le (by simp))
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
