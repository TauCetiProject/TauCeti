/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Fourier multipliers on `L²`

Let `E` be a finite-dimensional real inner product space and `F` a complex Hilbert space. For an
essentially bounded symbol `m ∈ L^∞(E)`, the **Fourier multiplier** with symbol `m` is the
operator

`T_m f = 𝓕⁻ (m • 𝓕 f)`

on `L²(E, F)`, where `𝓕 = MeasureTheory.Lp.fourierTransformₗᵢ` is the Fourier transform on `L²`.
By Plancherel's theorem it is bounded, with `‖T_m‖ ≤ ‖m‖_∞`.

Mathlib defines Fourier multipliers on Schwartz functions and on tempered distributions
(`SchwartzMap.fourierMultiplierCLM`, `TemperedDistribution.fourierMultiplierCLM`), but they are
meaningful only for symbols of temperate growth, which are in particular smooth. The symbols
of the classical singular integral operators are bounded but not smooth at the origin: the
Riesz transforms have symbols `-i ξⱼ / ‖ξ‖`, and `∂ⱼ∂ₖ Δ⁻¹` has symbol `ξⱼ ξₖ / ‖ξ‖²`. The `L²`
multiplier accepts any essentially bounded symbol, and it is the `L²`-bounded operator that the
Calderón–Zygmund theory and the Mihlin–Hörmander multiplier theorem start from. Where both are
defined, it agrees with Mathlib's multipliers.

## Main declarations

* `MeasureTheory.Lp.fourierMultiplierCLM`: the Fourier multiplier on `L²` with symbol in `L^∞`.
* `MeasureTheory.Lp.fourier_fourierMultiplierCLM`: `𝓕 (T_m f) = m • 𝓕 f`, and
  `MeasureTheory.Lp.eq_fourierMultiplierCLM_iff`, which characterizes `T_m` by it.
* `MeasureTheory.Lp.norm_fourierMultiplierCLM_le`: the bound `‖T_m‖ ≤ ‖m‖_∞`.
* `MeasureTheory.Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM`: `T_{m₁} ∘ T_{m₂} =
  T_{m₁ m₂}`, with linearity in the symbol and `T_c = c • id` for a constant symbol.
* `MeasureTheory.Lp.adjoint_fourierMultiplierCLM`: the adjoint of `T_m` is `T_{star m}`.
* `SchwartzMap.toLp_fourierMultiplierCLM_eq` and
  `MeasureTheory.Lp.fourierMultiplierCLM_toTemperedDistribution_eq`: for a bounded symbol of
  temperate growth, `T_m` agrees with Mathlib's multipliers on Schwartz functions and, as a
  tempered distribution, on every `f ∈ L²`.
* `MeasureTheory.Lp.coeFn_fourierMultiplierCLM_toLp`: for a Schwartz symbol `σ`, `T_σ` is
  convolution with the Schwartz kernel `𝓕⁻ σ`, that is `T_σ f x = ∫ 𝓕⁻ σ (x - y) • f y` for
  almost every `x`. On Schwartz functions this is `SchwartzMap.fourierMultiplierCLM_eq_convolution`.
* `MeasureTheory.Lp.tendsto_fourierMultiplierCLM_apply`: if the symbols `m n` are uniformly
  bounded and converge to `m₀` almost everywhere, then `T_{m n} f → T_{m₀} f` in `L²`.

## Kernels of multipliers

A bounded symbol `m` is in general not the Fourier transform of an integrable function, so `T_m`
is not a convolution with an integrable kernel. The Calderón–Zygmund theory instead asks for a
kernel representation off the support of the argument, and the proof of the Mihlin–Hörmander
multiplier theorem obtains it by approximation: `m` is cut into Schwartz symbols `σ`, for which
`T_σ` is convolution with `𝓕⁻ σ` at every point, and `T_m` is recovered as the strong limit of
the operators `T_σ`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Sections 2.5 and 6.2.2.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV, §3.
-/

public section

noncomputable section

open scoped ENNReal FourierTransform ComplexInnerProductSpace SchwartzMap InnerProduct Topology
open FourierTransform ContinuousLinearMap Filter

namespace MeasureTheory.Lp

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

variable (F) in
/-- The **Fourier multiplier** on `L²(E, F)` with symbol `m ∈ L^∞(E)`: the bounded operator
`f ↦ 𝓕⁻ (m • 𝓕 f)`, where `𝓕` is the Fourier transform on `L²`. -/
def fourierMultiplierCLM (m : Lp ℂ ∞ (volume : Measure E)) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  fourierInvCLM ℂ (Lp F 2 (volume : Measure E)) ∘L
    (lsmul ℂ ℂ : ℂ →L[ℂ] F →L[ℂ] F).holderL volume ∞ 2 2 m ∘L
      fourierCLM ℂ (Lp F 2 (volume : Measure E))

variable (m m₁ m₂ : Lp ℂ ∞ (volume : Measure E)) (f : Lp F 2 (volume : Measure E))

theorem fourierMultiplierCLM_apply :
    fourierMultiplierCLM F m f = 𝓕⁻ (m • 𝓕 f : Lp F 2 (volume : Measure E)) := by
  rw [fourierMultiplierCLM, comp_apply, comp_apply, fourierCLM_apply, fourierInvCLM_apply]
  refine congrArg 𝓕⁻ (Lp.ext ?_)
  filter_upwards [(lsmul ℂ ℂ : ℂ →L[ℂ] F →L[ℂ] F).coeFn_holder (r := 2) m (𝓕 f),
    coeFn_lpSMul (r := 2) m (𝓕 f)] with x h₁ h₂
  simp [h₁, h₂]

/-- On the Fourier side, the multiplier with symbol `m` is multiplication by `m`. -/
@[simp]
theorem fourier_fourierMultiplierCLM :
    𝓕 (fourierMultiplierCLM F m f) = (m • 𝓕 f : Lp F 2 (volume : Measure E)) := by
  rw [fourierMultiplierCLM_apply, fourier_fourierInv_eq]

variable {m} in
/-- A bounded operator on `L²` is the multiplier with symbol `m` if and only if it acts as
multiplication by `m` on the Fourier side. -/
theorem eq_fourierMultiplierCLM_iff
    {T : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E)} :
    T = fourierMultiplierCLM F m ↔ ∀ f, 𝓕 (T f) = (m • 𝓕 f : Lp F 2 (volume : Measure E)) := by
  refine ⟨fun h f ↦ h ▸ fourier_fourierMultiplierCLM m f, fun h ↦ ?_⟩
  ext1 f
  exact (fourierTransformₗᵢ E F).injective ((h f).trans (fourier_fourierMultiplierCLM m f).symm)

/-- The multiplier with symbol `m` changes the `L²` norm by at most the factor `‖m‖_∞`. -/
theorem norm_fourierMultiplierCLM_apply_le : ‖fourierMultiplierCLM F m f‖ ≤ ‖m‖ * ‖f‖ := by
  rw [← norm_fourier_eq, fourier_fourierMultiplierCLM, ← norm_fourier_eq f]
  exact Lp.norm_smul_le m (𝓕 f)

/-- **Plancherel bound** for Fourier multipliers: `‖T_m‖ ≤ ‖m‖_∞`. -/
theorem norm_fourierMultiplierCLM_le : ‖fourierMultiplierCLM (E := E) F m‖ ≤ ‖m‖ :=
  opNorm_le_bound _ (norm_nonneg m) (norm_fourierMultiplierCLM_apply_le m)

/-! ### Dependence on the symbol -/

@[simp]
theorem fourierMultiplierCLM_zero :
    fourierMultiplierCLM F (0 : Lp ℂ ∞ (volume : Measure E)) = 0 := by
  ext1 f
  simp [fourierMultiplierCLM_apply]

theorem fourierMultiplierCLM_add :
    fourierMultiplierCLM F (m₁ + m₂) = fourierMultiplierCLM F m₁ + fourierMultiplierCLM F m₂ := by
  ext1 f
  simp [fourierMultiplierCLM_apply, Lp.smul_add]

theorem fourierMultiplierCLM_smul (c : ℂ) :
    fourierMultiplierCLM F (c • m) = c • fourierMultiplierCLM F m := by
  ext1 f
  simp [fourierMultiplierCLM_apply, Lp.smul_assoc]

variable {m} in
/-- A multiplier whose symbol is almost everywhere the constant `c` is multiplication by `c`. -/
theorem fourierMultiplierCLM_of_ae_eq_const {c : ℂ} (hm : m =ᵐ[volume] fun _ ↦ c) :
    fourierMultiplierCLM F m = c • ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure E)) := by
  ext1 f
  have : (m • 𝓕 f : Lp F 2 (volume : Measure E)) = c • 𝓕 f := by
    apply Lp.ext
    filter_upwards [coeFn_lpSMul (r := 2) m (𝓕 f), Lp.coeFn_smul c (𝓕 f), hm] with x h₁ h₂ h₃
    simp [h₁, h₂, h₃]
  simp [fourierMultiplierCLM_apply, this]

/-- The composition of two multipliers is the multiplier with the product symbol. -/
theorem fourierMultiplierCLM_compL_fourierMultiplierCLM :
    fourierMultiplierCLM F m₁ ∘L fourierMultiplierCLM F m₂ =
      fourierMultiplierCLM F (m₁ • m₂ : Lp ℂ ∞ (volume : Measure E)) := by
  refine eq_fourierMultiplierCLM_iff.2 fun f ↦ Lp.ext ?_
  simp only [comp_apply, fourier_fourierMultiplierCLM]
  filter_upwards [coeFn_lpSMul (r := 2) m₁ (m₂ • 𝓕 f : Lp F 2 (volume : Measure E)),
    coeFn_lpSMul (r := 2) m₂ (𝓕 f),
    coeFn_lpSMul (r := 2) (m₁ • m₂ : Lp ℂ ∞ (volume : Measure E)) (𝓕 f),
    coeFn_lpSMul (r := ∞) m₁ m₂] with x h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄, smul_smul]

theorem fourierMultiplierCLM_fourierMultiplierCLM_apply :
    fourierMultiplierCLM F m₁ (fourierMultiplierCLM F m₂ f) =
      fourierMultiplierCLM F (m₁ • m₂ : Lp ℂ ∞ (volume : Measure E)) f := by
  rw [← fourierMultiplierCLM_compL_fourierMultiplierCLM, comp_apply]

/-- The adjoint of the multiplier with symbol `m` is the multiplier with the complex conjugate
symbol `star m`. In particular a real symbol gives a self-adjoint multiplier. -/
theorem adjoint_fourierMultiplierCLM :
    (fourierMultiplierCLM (E := E) F m)† = fourierMultiplierCLM F (star m) := by
  refine ((eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [← inner_fourier_eq, fourier_fourierMultiplierCLM, ← inner_fourier_eq f,
    fourier_fourierMultiplierCLM, L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_lpSMul (r := 2) (star m) (𝓕 f), coeFn_lpSMul (r := 2) m (𝓕 g),
    Lp.coeFn_star m] with x h₁ h₂ h₃
  simp [h₁, h₂, h₃, inner_smul_left, inner_smul_right]

/-! ### Comparison with multipliers on Schwartz functions and tempered distributions -/

variable {g : E → ℂ}

/-- On Schwartz functions, the `L²` multiplier with a bounded symbol `g` of temperate growth is
the Schwartz-space multiplier `SchwartzMap.fourierMultiplierCLM F g`. -/
theorem _root_.SchwartzMap.toLp_fourierMultiplierCLM_eq (hg : g.HasTemperateGrowth)
    (hg' : MemLp g ∞) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (hg'.toLp g) (f.toLp 2) =
      (SchwartzMap.fourierMultiplierCLM F g f).toLp 2 := by
  have : (hg'.toLp g • 𝓕 (f.toLp 2) : Lp F 2 (volume : Measure E)) =
      (SchwartzMap.smulLeftCLM F g (𝓕 f)).toLp 2 := by
    apply Lp.ext
    filter_upwards [coeFn_lpSMul (r := 2) (hg'.toLp g) (𝓕 (f.toLp 2)), hg'.coeFn_toLp,
      (𝓕 f).coeFn_toLp 2, (SchwartzMap.smulLeftCLM F g (𝓕 f)).coeFn_toLp 2] with x h₁ h₂ h₃ h₄
    rw [SchwartzMap.toLp_fourier_eq] at h₁
    simp [h₁, h₂, h₃, h₄, SchwartzMap.smulLeftCLM_apply_apply hg]
  rw [fourierMultiplierCLM_apply, this, SchwartzMap.toLp_fourierInv_eq,
    SchwartzMap.fourierMultiplierCLM_apply]

/-- For a bounded symbol `g` of temperate growth, the `L²` multiplier agrees with the multiplier
`TemperedDistribution.fourierMultiplierCLM F g` on tempered distributions: for every `f ∈ L²`,
both send `f` to the same tempered distribution. -/
theorem fourierMultiplierCLM_toTemperedDistribution_eq (hg : g.HasTemperateGrowth)
    (hg' : MemLp g ∞) :
    TemperedDistribution.fourierMultiplierCLM F g (f : 𝓢'(E, F)) =
      (fourierMultiplierCLM F (hg'.toLp g) f : 𝓢'(E, F)) := by
  refine DenseRange.induction_on
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f ?_ fun f ↦ ?_
  · exact isClosed_eq
      (TemperedDistribution.fourierMultiplierCLM F g ∘L toTemperedDistributionCLM F volume 2).cont
      (toTemperedDistributionCLM F volume 2 ∘L fourierMultiplierCLM F (hg'.toLp g)).cont
  · simp [SchwartzMap.toLp_fourierMultiplierCLM_eq hg hg',
      TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq hg]

/-! ### Schwartz symbols and convolution kernels -/

/-- The `L²` form of `SchwartzMap.fourierMultiplierCLM_apply_eq_integral`, before extending to
all of `L²` by density. -/
private theorem coeFn_fourierMultiplierCLM_toLp_toLp (σ : 𝓢(E, ℂ)) (φ : 𝓢(E, F)) :
    fourierMultiplierCLM F (σ.toLp ∞) (φ.toLp 2) =ᵐ[volume] fun x ↦ ∫ y, 𝓕⁻ σ (x - y) • φ y := by
  -- `σ.toLp ∞` is by definition the symbol `(σ.memLp ∞).toLp σ` of the comparison theorem.
  have h : fourierMultiplierCLM F (σ.toLp ∞) (φ.toLp 2) =
      (SchwartzMap.fourierMultiplierCLM F σ φ).toLp 2 :=
    SchwartzMap.toLp_fourierMultiplierCLM_eq σ.hasTemperateGrowth (σ.memLp ∞) φ
  rw [h]
  filter_upwards [SchwartzMap.coeFn_toLp (SchwartzMap.fourierMultiplierCLM F σ φ) 2] with x hx
  rw [hx, SchwartzMap.fourierMultiplierCLM_apply_eq_integral]

/-- The `L²` multiplier with a Schwartz symbol `σ` is convolution with the Schwartz kernel
`𝓕⁻ σ`: for every `f ∈ L²`, `T_σ f x = ∫ 𝓕⁻ σ (x - y) • f y` for almost every `x`. The
integral converges for every `x`, since `y ↦ 𝓕⁻ σ (x - y)` lies in `L²`.

With `k x y = 𝓕⁻ σ (x - y) • id`, this is the kernel representation of `T_σ` that the
Calderón–Zygmund theorems take as hypothesis, valid at almost every point and not only off the
support of `f`. -/
theorem coeFn_fourierMultiplierCLM_toLp (σ : 𝓢(E, ℂ)) (f : Lp F 2 (volume : Measure E)) :
    fourierMultiplierCLM F (σ.toLp ∞) f =ᵐ[volume] fun x ↦ ∫ y, 𝓕⁻ σ (x - y) • f y := by
  have hK : ∀ x, MemLp (fun y ↦ 𝓕⁻ σ (x - y)) 2 volume := fun x ↦
    ((𝓕⁻ σ).memLp 2 volume).comp_measurePreserving (volume.measurePreserving_sub_left x)
  -- Approximate `f` by Schwartz functions `u n`; along a subsequence `T_σ (u n) → T_σ f` almost
  -- everywhere, while the kernel integrals converge at every point.
  obtain ⟨u, hu⟩ : ∃ u : ℕ → 𝓢(E, F), Tendsto (fun n ↦ (u n).toLp 2) atTop (𝓝 f) := by
    have := (SchwartzMap.denseRange_toLpCLM (E := E) (F := F) (p := 2) (μ := volume)
      ENNReal.ofNat_ne_top).closure_range ▸ Set.mem_univ f
    obtain ⟨v, hv, hvf⟩ := mem_closure_iff_seq_limit.1 this
    choose u hu using hv
    refine ⟨u, ?_⟩
    convert hvf using 2 with n
    exact hu n
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp
    (((fourierMultiplierCLM F (σ.toLp ∞)).continuous.tendsto f).comp hu)).exists_seq_tendsto_ae
  have hsch : ∀ᵐ x ∂(volume : Measure E), ∀ n : ℕ,
      fourierMultiplierCLM F (σ.toLp ∞) ((u n).toLp 2) x =
        ∫ y, 𝓕⁻ σ (x - y) • ((u n).toLp 2 : E → F) y := by
    refine ae_all_iff.2 fun n ↦ ?_
    filter_upwards [coeFn_fourierMultiplierCLM_toLp_toLp σ (u n)] with x hx
    rw [hx]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp (u n) 2] with y hy
    rw [hy]
  filter_upwards [hae, hsch] with x hx hxs
  refine tendsto_nhds_unique hx ?_
  -- Pairing with `y ↦ 𝓕⁻ σ (x - y) ∈ L²` is continuous on `L²`.
  have hpair : ∀ g : Lp F 2 (volume : Measure E), (lsmul ℂ ℂ).lpPairing volume 2 2
      ((hK x).toLp _) g = ∫ y, 𝓕⁻ σ (x - y) • g y := fun g ↦ by
    rw [lpPairing_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [(hK x).coeFn_toLp] with y hy
    rw [lsmul_apply, hy]
  simp only [Function.comp_apply, hxs, ← hpair]
  exact ((((lsmul ℂ ℂ).lpPairing volume 2 2 ((hK x).toLp _)).continuous.tendsto f).comp hu).comp
    hns.tendsto_atTop

/-- If the symbols `m n` are bounded in `L^∞` uniformly in `n` and converge to `m₀` almost
everywhere, then `T_{m n} f → T_{m₀} f` in `L²` for every `f ∈ L²`. -/
theorem tendsto_fourierMultiplierCLM_apply {m : ℕ → Lp ℂ ∞ (volume : Measure E)}
    {m₀ : Lp ℂ ∞ (volume : Measure E)} {C : ℝ} (hC : ∀ n, ‖m n‖ ≤ C)
    (hm : ∀ᵐ ξ, Tendsto (fun n ↦ m n ξ) atTop (𝓝 (m₀ ξ))) (f : Lp F 2 (volume : Measure E)) :
    Tendsto (fun n ↦ fourierMultiplierCLM F (m n) f) atTop
      (𝓝 (fourierMultiplierCLM F m₀ f)) := by
  simp only [fourierMultiplierCLM_apply]
  refine ((fourierInvCLM ℂ (Lp F 2 (volume : Measure E))).continuous.tendsto _).comp ?_
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hmb : ∀ g : Lp ℂ ∞ (volume : Measure E), ∀ᵐ ξ, ‖g ξ‖ₑ ≤ ‖g‖ₑ := fun g ↦ by
    rw [Lp.enorm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable g)]
    exact ae_le_eLpNormEssSup
  -- Dominated convergence on the Fourier side, with dominating function `‖𝓕 f‖`.
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (by simp) (by simp)
    (Eventually.of_forall fun n ↦ Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    (Lp.memLp (𝓕 f)) (C := C.toNNReal + ‖m₀‖₊) (Eventually.of_forall fun n ↦ ?_) ?_
  · filter_upwards [coeFn_lpSMul (r := 2) (m n) (𝓕 f), coeFn_lpSMul (r := 2) m₀ (𝓕 f), hmb (m n),
      hmb m₀] with ξ h₁ h₂ h₃ h₄
    rw [h₁, h₂, Pi.smul_apply', Pi.smul_apply', ← sub_smul, enorm_smul, ENNReal.coe_add,
      ← enorm_eq_nnnorm]
    gcongr
    exact enorm_sub_le.trans (add_le_add (h₃.trans ((ofReal_norm (m n)).symm.trans_le
      (ENNReal.ofReal_le_ofReal (hC n)))) h₄)
  · filter_upwards [ae_all_iff.2 fun n ↦ coeFn_lpSMul (r := 2) (m n) (𝓕 f),
      coeFn_lpSMul (r := 2) m₀ (𝓕 f), hm] with ξ h₁ h₂ h₃
    simp only [h₁, h₂, Pi.smul_apply']
    exact h₃.smul_const _

end MeasureTheory.Lp
