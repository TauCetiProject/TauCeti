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
public import TauCeti.MeasureTheory.Function.Lp.Convolution
public import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Fourier.Convolution
import TauCeti.Analysis.Fourier.LpSpace
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Multiplication
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Fourier multipliers on `L²`

Let `E` be a finite-dimensional real inner product space and `F` a complex Hilbert space. For an
essentially bounded symbol `m ∈ L^∞(E)`, the **Fourier multiplier** with symbol `m` is the
operator

`T_m f = 𝓕⁻ (m • 𝓕 f)`

on `L²(E, F)`, where `𝓕 = MeasureTheory.Lp.fourierTransformₗᵢ` is the Fourier transform on `L²`.
By Plancherel's theorem it is conjugate to multiplication by `m`, so it is bounded with
`‖T_m‖ = ‖m‖_∞` (for nonzero `F`).

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
* `MeasureTheory.Lp.fourier_fourierMultiplierCLM`: `𝓕 (T_m f) = m • 𝓕 f`, pointwise almost
  everywhere for a symbol given by a function
  (`MeasureTheory.Lp.coeFn_fourier_fourierMultiplierCLM_toLp`), and
  `MeasureTheory.Lp.eq_fourierMultiplierCLM_iff`, which characterizes `T_m` by it.
* `MeasureTheory.Lp.norm_fourierMultiplierCLM_le`: the bound `‖T_m‖ ≤ ‖m‖_∞`, and
  `MeasureTheory.Lp.norm_fourierMultiplierCLM_toLp_le`: `‖T_m‖ ≤ C` for a symbol given by a
  function bounded by `C` almost everywhere, and `MeasureTheory.Lp.norm_fourierMultiplierCLM`:
  the equality `‖T_m‖ = ‖m‖_∞` for nonzero `F`.
* `MeasureTheory.Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM`: `T_{m₁} ∘ T_{m₂} =
  T_{m₁ m₂}`, with linearity in the symbol and `T_c = c • id` for a constant symbol.
* `MeasureTheory.Lp.adjoint_fourierMultiplierCLM`: the adjoint of `T_m` is `T_{star m}`, so a
  real symbol gives a self-adjoint multiplier
  (`MeasureTheory.Lp.isSelfAdjoint_fourierMultiplierCLM`).
* `SchwartzMap.toLp_fourierMultiplierCLM_eq` and
  `MeasureTheory.Lp.fourierMultiplierCLM_toTemperedDistribution_eq`: for a bounded symbol of
  temperate growth, `T_m` agrees with Mathlib's multipliers on Schwartz functions and, as a
  tempered distribution, on every `f ∈ L²`.
* `SchwartzMap.toLp_eq_fourierMultiplierCLM_of_fourier_eq_smul`: for any bounded symbol `m`, a
  Schwartz function `g` with `𝓕 g = m • 𝓕 f` is `T_m f` in `L²`.
* `SchwartzMap.coeFn_fourierMultiplierCLM_toLp`: for a Schwartz symbol `σ`, `T_σ` is
  convolution with the Schwartz kernel `𝓕⁻ σ`, that is `T_σ f x = ∫ 𝓕⁻ σ (x - y) • f y` for
  almost every `x`. On Schwartz functions this is `SchwartzMap.fourierMultiplierCLM_eq_convolution`.
* `TauCeti.convolutionLp_eq_fourierMultiplierCLM`: convolution with an integrable kernel `k` is
  the multiplier whose symbol is the Fourier transform of `k`, and
  `TauCeti.coeFn_fourier_convolutionLp`, its Fourier-side form `𝓕 (k ⋆ f) = 𝓕 k • 𝓕 f`.
* `MeasureTheory.Lp.tendsto_fourierMultiplierCLM_apply`: if the symbols `m i` are eventually
  uniformly bounded and converge to `m₀` almost everywhere along a countably generated filter,
  then `T_{m i} f → T_{m₀} f` in `L²`.
* `MeasureTheory.Lp.tendsto_fourierMultiplierCLM_apply_self`: symbols uniformly bounded and
  tending to `1` almost everywhere give `T_{m i} f → f` in `L²`.
* `MeasureTheory.Lp.tendsto_sum_fourierMultiplierCLM_of_tendsto`: if the partial sums of the
  symbols are uniformly bounded and converge to `1` almost everywhere, the partial sums of the
  multipliers converge to the identity in `L²`.
* `MeasureTheory.Lp.hasDerivAt_fourierMultiplierCLM_toLp_apply`: if symbols `m s` depending on a
  real parameter are differentiable in `s` at almost every frequency, with derivative `a ξ m' ξ`
  and increments bounded by `C ‖a ξ‖ |s - t|`, then `s ↦ T_{m s} f` has derivative `T_{m'} h` in
  `L²` whenever `𝓕 h = a • 𝓕 f`. With `a = 1` this differentiates multiplier families
  applied to arbitrary `f ∈ L²`; with `a` the symbol of a differential operator `P`, it
  differentiates them applied to `f` with `P f = h ∈ L²`.
* `MeasureTheory.Lp.fourierMultiplierCLM_dilateLp`: `T_m D_r = D_r T_{m (r⁻¹ • ·)}` for the
  normalized dilation `D_r` of `L²`: conjugating a multiplier by a dilation dilates its symbol.

## Kernels of multipliers

A bounded symbol `m` is in general not the Fourier transform of an integrable function, so `T_m`
is not a convolution with an integrable kernel. The Calderón–Zygmund theory instead asks for a
kernel representation off the support of the argument, and the proof of the Mihlin–Hörmander
multiplier theorem obtains it by approximation: `m` is cut into Schwartz symbols `σ`, for which
`T_σ` is convolution with `𝓕⁻ σ` almost everywhere, the convolution integral converging at every
point, and `T_m` is recovered as the strong limit of the operators `T_σ`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Sections 2.5 and 6.2.2.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV, §3.
-/

public section

noncomputable section

open scoped ENNReal FourierTransform ComplexInnerProductSpace SchwartzMap InnerProduct Topology
  Convolution
open FourierTransform ContinuousLinearMap Filter

namespace MeasureTheory.Lp

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The Fourier transform on `L²` commutes with real scalars. -/
@[simp]
theorem fourier_real_smul (r : ℝ) (f : Lp F 2 (volume : Measure E)) : 𝓕 (r • f) = r • 𝓕 f := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), FourierTransform.fourier_smul,
    ← RCLike.real_smul_eq_coe_smul]

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

/-- For a bounded symbol given by a function `m`, the Fourier transform of `T_m f` is
`ξ ↦ m ξ • 𝓕 f ξ` almost everywhere. -/
theorem coeFn_fourier_fourierMultiplierCLM_toLp {m : E → ℂ} (hm : MemLp m ∞ volume) :
    𝓕 (fourierMultiplierCLM F (hm.toLp m) f) =ᵐ[volume] fun ξ ↦ m ξ • 𝓕 f ξ := by
  rw [fourier_fourierMultiplierCLM]
  filter_upwards [coeFn_lpSMul (r := 2) (hm.toLp m) (𝓕 f), hm.coeFn_toLp] with ξ h₁ h₂
  rw [h₁, Pi.smul_apply', h₂]

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

/-- A symbol given by a function bounded by `C` almost everywhere gives a multiplier of operator
norm at most `C`. -/
theorem norm_fourierMultiplierCLM_toLp_le {g : E → ℂ} (hg : MemLp g ∞ volume) {C : ℝ}
    (h : ∀ᵐ ξ ∂volume, ‖g ξ‖ ≤ C) : ‖fourierMultiplierCLM F (hg.toLp g)‖ ≤ C :=
  -- `volume` on `E` is nonzero, so the bound is attained somewhere and `C ≥ 0`.
  have ⟨_, hξ⟩ := h.exists
  (norm_fourierMultiplierCLM_le _).trans (Lp.norm_le_of_ae_bound_top ((norm_nonneg _).trans hξ)
    (by filter_upwards [hg.coeFn_toLp, h] with ξ hξ hξ'; rwa [hξ]))

/-- The `L²` operator norm of the multiplier with symbol `m` is exactly `‖m‖_∞`, for nonzero
`F`. -/
@[simp]
theorem norm_fourierMultiplierCLM [Nontrivial F] : ‖fourierMultiplierCLM (E := E) F m‖ = ‖m‖ := by
  refine (norm_fourierMultiplierCLM_le m).antisymm ?_
  -- By Plancherel, `T_m` is conjugate to multiplication by `m`, whose norm is `‖m‖_∞`.
  rw [← norm_multiplicationOperator (E := F) (p := 2) m]
  refine opNorm_le_bound _ (norm_nonneg (fourierMultiplierCLM F m)) fun g ↦ ?_
  -- Test `T_m` on the inverse Fourier transform of `g`, which has the same norm as `g`.
  have h := (fourierMultiplierCLM F m).le_opNorm (𝓕⁻ g)
  rwa [← norm_fourier_eq (fourierMultiplierCLM F m (𝓕⁻ g)), fourier_fourierMultiplierCLM,
    ← norm_fourier_eq (𝓕⁻ g), fourier_fourierInv_eq, ← multiplicationOperator_apply] at h

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

theorem fourierMultiplierCLM_sub :
    fourierMultiplierCLM F (m₁ - m₂) = fourierMultiplierCLM F m₁ - fourierMultiplierCLM F m₂ :=
  map_sub (AddMonoidHom.mk' (fourierMultiplierCLM F) fourierMultiplierCLM_add) m₁ m₂

/-- The multiplier of a finite sum of symbols is the sum of the multipliers. -/
theorem fourierMultiplierCLM_sum {ι : Type*} (s : Finset ι)
    (m : ι → Lp ℂ ∞ (volume : Measure E)) :
    fourierMultiplierCLM F (∑ i ∈ s, m i) = ∑ i ∈ s, fourierMultiplierCLM F (m i) :=
  map_sum (AddMonoidHom.mk' (fourierMultiplierCLM F) fourierMultiplierCLM_add) m s

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
  -- With the `L^∞` algebra instances in scope, `smul_eq_mul` and `Lp.smul_eq_mul` would rewrite
  -- the Hölder product `m₁ • m₂` to `m₁ * m₂`, so `h₃` and `h₄` would no longer match.
  simp [h₁, h₂, h₃, h₄, smul_smul, -smul_eq_mul, -Lp.smul_eq_mul]

theorem fourierMultiplierCLM_fourierMultiplierCLM_apply :
    fourierMultiplierCLM F m₁ (fourierMultiplierCLM F m₂ f) =
      fourierMultiplierCLM F (m₁ • m₂ : Lp ℂ ∞ (volume : Measure E)) f := by
  rw [← fourierMultiplierCLM_compL_fourierMultiplierCLM, comp_apply]

/-- Two multipliers commute, since their symbols do. -/
theorem fourierMultiplierCLM_fourierMultiplierCLM_comm :
    fourierMultiplierCLM F m₁ (fourierMultiplierCLM F m₂ f) =
      fourierMultiplierCLM F m₂ (fourierMultiplierCLM F m₁ f) := by
  have h : (m₁ • m₂ : Lp ℂ ∞ (volume : Measure E)) = m₂ • m₁ := by
    apply Lp.ext
    filter_upwards [coeFn_lpSMul (r := ∞) m₁ m₂, coeFn_lpSMul (r := ∞) m₂ m₁] with ξ h₁ h₂
    rw [h₁, h₂, Pi.smul_apply', Pi.smul_apply', smul_eq_mul, smul_eq_mul, mul_comm]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply,
    fourierMultiplierCLM_fourierMultiplierCLM_apply, h]

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

variable {m} in
/-- A real symbol, `star m = m`, gives a self-adjoint multiplier. -/
theorem isSelfAdjoint_fourierMultiplierCLM (hm : star m = m) :
    IsSelfAdjoint (fourierMultiplierCLM (E := E) F m) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', adjoint_fourierMultiplierCLM, hm]

/-- The pairing of `g` with the multiplier `T_m f`, computed on the Fourier side:
`⟪g, T_m f⟫ = ∫ m ξ ⟪𝓕 g ξ, 𝓕 f ξ⟫ dξ`. -/
theorem inner_fourierMultiplierCLM_apply (g : Lp F 2 (volume : Measure E)) :
    inner ℂ g (fourierMultiplierCLM F m f) =
      ∫ ξ, m ξ * inner ℂ ((𝓕 g : Lp F 2 (volume : Measure E)) ξ)
        ((𝓕 f : Lp F 2 (volume : Measure E)) ξ) := by
  rw [← inner_fourier_eq, fourier_fourierMultiplierCLM, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_lpSMul (r := 2) m (𝓕 f)] with ξ h
  rw [h, Pi.smul_apply', inner_smul_right]

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

/-- A Schwartz function `g` whose Fourier transform is `m • 𝓕 f` is, in `L²`, the multiplier with
symbol `m` applied to `f`. Here `m` need not have temperate growth: any bounded symbol works, so
this also covers symbols that are discontinuous at the origin. -/
theorem _root_.SchwartzMap.toLp_eq_fourierMultiplierCLM_of_fourier_eq_smul {f g : 𝓢(E, F)}
    {m' : E → ℂ} (hm : m =ᵐ[volume] m') (h : ∀ ξ, 𝓕 g ξ = m' ξ • 𝓕 f ξ) :
    g.toLp 2 = fourierMultiplierCLM F m (f.toLp 2) := by
  refine (fourierInv_fourier_eq (F := Lp F 2 (volume : Measure E)) _).symm.trans ?_
  rw [fourierMultiplierCLM_apply, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  congr 1
  apply Lp.ext
  filter_upwards [(𝓕 g).coeFn_toLp 2, coeFn_lpSMul (r := 2) m ((𝓕 f).toLp 2), hm,
    (𝓕 f).coeFn_toLp 2] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.smul_apply', h₃, h₄, h]

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
theorem _root_.SchwartzMap.coeFn_fourierMultiplierCLM_toLp (σ : 𝓢(E, ℂ))
    (f : Lp F 2 (volume : Measure E)) :
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

/-- **`Lᵖ` bound for an `L²` multiplier with Schwartz symbol.** For a Schwartz symbol `σ`, every
`f ∈ L²` and every `1 ≤ p ≤ ∞`, `‖T_σ f‖_p ≤ ‖𝓕⁻ σ‖₁ ‖f‖_p`: `T_σ f` is the convolution of `f`
with `𝓕⁻ σ`, and Young's inequality applies. Neither side is assumed finite, so `T_σ` maps
`L² ∩ Lᵖ` into `Lᵖ`. On Schwartz functions this is `SchwartzMap.eLpNorm_fourierMultiplierCLM_le`. -/
theorem _root_.SchwartzMap.eLpNorm_fourierMultiplierCLM_toLp_le (σ : 𝓢(E, ℂ))
    (f : Lp F 2 (volume : Measure E)) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fourierMultiplierCLM F (σ.toLp ∞) f) p volume ≤
      eLpNorm (𝓕⁻ (σ : E → ℂ)) 1 volume * eLpNorm f p volume := by
  have hconv : fourierMultiplierCLM F (σ.toLp ∞) f =ᵐ[volume]
      (𝓕⁻ (σ : E → ℂ) ⋆[lsmul ℂ ℂ, volume] (f : E → F)) := by
    filter_upwards [σ.coeFn_fourierMultiplierCLM_toLp f] with x hx
    rw [hx, convolution_lsmul, ← integral_sub_left_eq_self _ volume x]
    simp_rw [sub_sub_cancel, SchwartzMap.fourierInv_coe]
  rw [eLpNorm_congr_ae hconv, ← SchwartzMap.fourierInv_coe]
  refine (eLpNorm_convolution_le _ (𝓕⁻ σ).continuous.aestronglyMeasurable
    (Lp.aestronglyMeasurable f) hp).trans ?_
  grw [opENorm_lsmul_le, one_mul]

/-- **The `L¹ → L^∞` bound** for a multiplier with a Schwartz symbol `σ`: if the kernel `𝓕⁻ σ` is
bounded by `B`, then `‖T_σ f‖_∞ ≤ B ‖f‖₁` for every integrable `f ∈ L²`. -/
theorem _root_.SchwartzMap.eLpNorm_fourierMultiplierCLM_toLp_top_le (σ : 𝓢(E, ℂ)) {B : ℝ}
    (hB : ∀ x, ‖𝓕⁻ σ x‖ ≤ B) {f : Lp F 2 (volume : Measure E)} (hf : Integrable f) :
    eLpNorm (fourierMultiplierCLM F (σ.toLp ∞) f) ∞ volume ≤
      ENNReal.ofReal B * eLpNorm f 1 volume := by
  have hbound : ∀ᵐ x ∂volume, ‖fourierMultiplierCLM F (σ.toLp ∞) f x‖ ≤ B * ∫ y, ‖f y‖ := by
    filter_upwards [SchwartzMap.coeFn_fourierMultiplierCLM_toLp σ f] with x hx
    rw [hx, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hf.norm.const_mul _) (Eventually.of_forall fun y ↦ ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  rw [eLpNorm_exponent_top, eLpNorm_one_eq_lintegral_eNorm,
    ← ofReal_integral_norm_eq_lintegral_eNorm hf,
    ← ENNReal.ofReal_mul ((norm_nonneg _).trans (hB 0))]
  · exact eLpNormEssSup_le_of_ae_bound hbound
  all_goals exact Lp.aestronglyMeasurable _

/-- If the symbols `m i` are eventually bounded in `L^∞` uniformly in `i` along a countably
generated filter `l` and converge to `m₀` almost everywhere along `l`, then
`T_{m i} f → T_{m₀} f` in `L²` along `l` for every `f ∈ L²`. -/
theorem tendsto_fourierMultiplierCLM_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {m : ι → Lp ℂ ∞ (volume : Measure E)} {m₀ : Lp ℂ ∞ (volume : Measure E)} {C : ℝ}
    (hC : ∀ᶠ i in l, ‖m i‖ ≤ C) (hm : ∀ᵐ ξ, Tendsto (fun i ↦ m i ξ) l (𝓝 (m₀ ξ)))
    (f : Lp F 2 (volume : Measure E)) :
    Tendsto (fun i ↦ fourierMultiplierCLM F (m i) f) l (𝓝 (fourierMultiplierCLM F m₀ f)) := by
  -- Reduce to sequences `s n → l`, so that the almost-everywhere statements below range over a
  -- countable index set.
  refine tendsto_iff_seq_tendsto.2 fun s hs ↦ ?_
  replace hC := hs.eventually hC
  replace hm := hm.mono fun ξ hξ ↦ hξ.comp hs
  simp only [Function.comp_def, fourierMultiplierCLM_apply] at hm ⊢
  refine ((fourierInvCLM ℂ (Lp F 2 (volume : Measure E))).continuous.tendsto _).comp ?_
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hmb : ∀ g : Lp ℂ ∞ (volume : Measure E), ∀ᵐ ξ, ‖g ξ‖ₑ ≤ ‖g‖ₑ := fun g ↦ by
    rw [Lp.eNorm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable g)]
    exact ae_le_eLpNormEssSup
  -- Dominated convergence on the Fourier side, with dominating function `‖𝓕 f‖`.
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (by simp)
    (Eventually.of_forall fun n ↦ Lp.aestronglyMeasurable _) (Lp.memLp (𝓕 f))
    (C := C.toNNReal + ‖m₀‖₊) (hC.mono fun n hn ↦ ?_) ?_
  · filter_upwards [coeFn_lpSMul (r := 2) (m (s n)) (𝓕 f), coeFn_lpSMul (r := 2) m₀ (𝓕 f),
      hmb (m (s n)), hmb m₀] with ξ h₁ h₂ h₃ h₄
    rw [h₁, h₂, Pi.smul_apply', Pi.smul_apply', ← sub_smul, eNorm_smul, ENNReal.coe_add,
      ← eNorm_eq_nnNorm]
    gcongr
    exact eNorm_sub_le.trans (add_le_add (h₃.trans ((ofReal_norm (m (s n))).symm.trans_le
      (ENNReal.ofReal_le_ofReal hn))) h₄)
  · filter_upwards [ae_all_iff.2 fun n ↦ coeFn_lpSMul (r := 2) (m (s n)) (𝓕 f),
      coeFn_lpSMul (r := 2) m₀ (𝓕 f), hm] with ξ h₁ h₂ h₃
    simp only [h₁, h₂, Pi.smul_apply']
    exact h₃.smul_const _

/-- **Approximate identities among multipliers.** If the symbols `m i` are eventually bounded
almost everywhere by a constant along a countably generated filter `l` and tend to `1` almost
everywhere along `l`, then `T_{m i} f → f` in `L²` along `l` for every `f ∈ L²`. -/
theorem tendsto_fourierMultiplierCLM_apply_self {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {m : ι → Lp ℂ ∞ (volume : Measure E)} {C : ℝ}
    (hC : ∀ᶠ i in l, ∀ᵐ ξ, ‖m i ξ‖ ≤ C) (hm : ∀ᵐ ξ, Tendsto (fun i ↦ m i ξ) l (𝓝 1))
    (f : Lp F 2 (volume : Measure E)) :
    Tendsto (fun i ↦ fourierMultiplierCLM F (m i) f) l (𝓝 f) := by
  have hC' : ∀ᶠ i in l, ‖m i‖ ≤ max C 0 := hC.mono fun i hi ↦
    Lp.norm_le_of_ae_bound_top (le_max_right C 0) (hi.mono fun ξ hξ ↦ hξ.trans (le_max_left C 0))
  have h1 : MemLp (fun _ : E ↦ (1 : ℂ)) ∞ volume := memLp_top_const 1
  have h := tendsto_fourierMultiplierCLM_apply (F := F) (m₀ := h1.toLp _) hC'
    (by filter_upwards [hm, h1.coeFn_toLp] with ξ h₁ h₂; rwa [h₂]) f
  rwa [fourierMultiplierCLM_of_ae_eq_const h1.coeFn_toLp, one_smul, id_apply] at h

/-- If the partial sums `∑_{i ∈ t N} ψᵢ` of symbols are uniformly bounded by `C` and converge
to `1` almost everywhere, then the partial sums `∑_{i ∈ t N} T_{m i} f` of the Fourier multipliers
with these symbols converge to `f` in `L²` for every `f ∈ L²`. -/
theorem tendsto_sum_fourierMultiplierCLM_of_tendsto {ι : Type*}
    {ψ : ι → E → ℂ} {m : ι → Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ i, m i =ᵐ[volume] ψ i) (t : ℕ → Finset ι) {C : ℝ}
    (hle : ∀ N ξ, ‖∑ i ∈ t N, ψ i ξ‖ ≤ C)
    (hlim : ∀ᵐ ξ ∂(volume : Measure E), Tendsto (fun N ↦ ∑ i ∈ t N, ψ i ξ) atTop (𝓝 1))
    (f : Lp F 2 (volume : Measure E)) :
    Tendsto (fun N ↦ ∑ i ∈ t N, fourierMultiplierCLM F (m i) f) atTop (𝓝 f) := by
  -- The partial sums are the multipliers with the symbols `∑_{i ∈ t N} ψᵢ`.
  have hae : ∀ᵐ ξ ∂(volume : Measure E), ∀ N, (∑ i ∈ t N, m i) ξ = ∑ i ∈ t N, ψ i ξ := by
    refine ae_all_iff.2 fun N ↦ ?_
    filter_upwards [coeFn_fun_finsetSum (t N) m, (eventually_all_finset (t N)).2 fun i _ ↦ hm i]
      with ξ h₁ h₂
    rw [h₁]
    exact Finset.sum_congr rfl fun i hi ↦ h₂ i hi
  have h := tendsto_fourierMultiplierCLM_apply_self (F := F) (l := atTop)
    (m := fun N ↦ ∑ i ∈ t N, m i) (C := C) (Eventually.of_forall fun N ↦ by
      filter_upwards [hae] with ξ hξ
      rw [hξ N]
      exact hle N ξ) (by filter_upwards [hae, hlim] with ξ h₁ h₂; simpa only [h₁] using h₂) f
  simpa only [fourierMultiplierCLM_sum, FunLike.coe_sum, Finset.sum_apply] using h

/-- The `L²` distance between a difference quotient of `s ↦ T_{m s} f` and `T_{m'} h`, computed on
the Fourier side. -/
private theorem norm_slope_fourierMultiplierCLM_toLp_sub {m : ℝ → E → ℂ}
    (hm : ∀ s, MemLp (m s) ∞ volume) {m' : E → ℂ} (hm' : MemLp m' ∞ volume) (t s : ℝ)
    (f h : Lp F 2 (volume : Measure E)) :
    ‖slope (fun s ↦ fourierMultiplierCLM F ((hm s).toLp (m s)) f) t s -
        fourierMultiplierCLM F (hm'.toLp m') h‖ =
      (eLpNorm (fun ξ ↦ ((s - t)⁻¹ • (m s ξ - m t ξ)) • (𝓕 f : Lp F 2 (volume : Measure E)) ξ -
        m' ξ • (𝓕 h : Lp F 2 (volume : Measure E)) ξ) 2 volume).toReal := by
  rw [← norm_fourier_eq, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  rw [slope_def_module, FourierTransform.fourier_sub, fourier_real_smul,
    FourierTransform.fourier_sub]
  set A := 𝓕 (fourierMultiplierCLM F ((hm s).toLp (m s)) f)
  set B := 𝓕 (fourierMultiplierCLM F ((hm t).toLp (m t)) f)
  set D := 𝓕 (fourierMultiplierCLM F (hm'.toLp m') h)
  filter_upwards [Lp.coeFn_sub ((s - t)⁻¹ • (A - B)) D, Lp.coeFn_smul (s - t)⁻¹ (A - B),
    Lp.coeFn_sub A B, coeFn_fourier_fourierMultiplierCLM_toLp f (hm s),
    coeFn_fourier_fourierMultiplierCLM_toLp f (hm t),
    coeFn_fourier_fourierMultiplierCLM_toLp h hm'] with ξ h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, Pi.sub_apply, h₂, Pi.smul_apply, h₃, Pi.sub_apply, h₄, h₅, h₆]
  simp only [sub_smul, smul_sub, smul_assoc]

/-- **Differentiating a family of Fourier multipliers.** Let `m s` be bounded symbols depending
on a real parameter `s`, and let `f, h ∈ L²` with `𝓕 h = a • 𝓕 f`. If, at almost every
frequency, the symbol `s ↦ m s ξ` has derivative `a ξ * m' ξ` at `t`, and its increments satisfy
`‖m s ξ - m t ξ‖ ≤ C ‖a ξ‖ |s - t|` almost everywhere for `s` near `t`, then `s ↦ T_{m s} f` has
derivative `T_{m'} h` at `t` in `L²`. -/
theorem hasDerivAt_fourierMultiplierCLM_toLp_apply {m : ℝ → E → ℂ}
    (hm : ∀ s, MemLp (m s) ∞ volume) {m' : E → ℂ} (hm' : MemLp m' ∞ volume) {a : E → ℂ}
    {C : ℝ} {t : ℝ} {f h : Lp F 2 (volume : Measure E)}
    (hh : (𝓕 h : Lp F 2 (volume : Measure E)) =ᵐ[volume]
      fun ξ ↦ a ξ • (𝓕 f : Lp F 2 (volume : Measure E)) ξ)
    (hderiv : ∀ᵐ ξ ∂volume, HasDerivAt (fun s ↦ m s ξ) (a ξ * m' ξ) t)
    (hbound : ∀ᶠ s in 𝓝[≠] t, ∀ᵐ ξ ∂volume, ‖m s ξ - m t ξ‖ ≤ C * ‖a ξ‖ * |s - t|) :
    HasDerivAt (fun s ↦ fourierMultiplierCLM F ((hm s).toLp (m s)) f)
      (fourierMultiplierCLM F (hm'.toLp m') h) t := by
  set Ff : E → F := ⇑(𝓕 f : Lp F 2 (volume : Measure E))
  set Fh : E → F := ⇑(𝓕 h : Lp F 2 (volume : Measure E))
  -- The Fourier transforms of the difference quotients, as genuine functions.
  set q : ℝ → E → F := fun s ξ ↦ ((s - t)⁻¹ • (m s ξ - m t ξ)) • Ff ξ
  have hq : ∀ s, ‖slope (fun s ↦ fourierMultiplierCLM F ((hm s).toLp (m s)) f) t s -
      fourierMultiplierCLM F (hm'.toLp m') h‖ =
        (eLpNorm (q s - fun ξ ↦ m' ξ • Fh ξ) 2 volume).toReal := fun s ↦
    norm_slope_fourierMultiplierCLM_toLp_sub hm hm' t s f h
  -- `m'` is bounded by its `L^∞` norm `K`.
  set K := ‖hm'.toLp m'‖
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  simp only [hq]
  rw [← ENNReal.toReal_zero]
  refine (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ?_
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (by norm_num) (Eventually.of_forall fun s ↦ ?_)
    (Lp.memLp (𝓕 h)) (C := (C + K).toNNReal) ?_ ?_
  · have h₁ := (hm s).aestronglyMeasurable
    have h₂ := (hm t).aestronglyMeasurable
    simp only [q, Ff]
    fun_prop
  · filter_upwards [hbound, self_mem_nhdsWithin] with s hs hst
    filter_upwards [hh, hs, hm'.coeFn_toLp, Lp.ae_norm_le_norm_top (hm'.toLp m')]
      with ξ hξ hsξ hm'ξ hKξ
    -- Turn the increment bound into a bound on the difference quotient.
    have hslope : ‖(s - t)⁻¹ • (m s ξ - m t ξ)‖ ≤ C * ‖a ξ‖ := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs,
        inv_mul_le_iff₀ (abs_pos.2 (sub_ne_zero.2 hst))]
      exact hsξ.trans_eq (mul_comm _ _)
    have h₁ : ‖q s ξ‖ ≤ C * ‖Fh ξ‖ := calc
      ‖q s ξ‖ = ‖(s - t)⁻¹ • (m s ξ - m t ξ)‖ * ‖Ff ξ‖ := norm_smul _ _
      _ ≤ C * ‖a ξ‖ * ‖Ff ξ‖ := by gcongr
      _ = C * ‖Fh ξ‖ := by rw [hξ, norm_smul, mul_assoc]
    have h₂ : ‖m' ξ • Fh ξ‖ ≤ K * ‖Fh ξ‖ := by
      rw [norm_smul, ← hm'ξ]
      gcongr
    rw [ENNReal.ofNNReal_toNNReal, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul' (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      ((norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (add_mul _ _ _).symm))
  · filter_upwards [hh, hderiv] with ξ hξ hξ'
    have := (hξ'.tendsto_slope).smul_const (Ff ξ)
    simp only [slope_def_module] at this
    rw [hξ, smul_smul, mul_comm]
    exact this

/-! ### Dilations -/

section Dilation

open Measure

/-- The Fourier-side identity behind `MeasureTheory.Lp.fourierMultiplierCLM_dilateLp`. -/
private theorem coeFn_fourier_dilateLp_aux {r : ℝ} (hr : 0 < r) (m : Lp ℂ ∞ (volume : Measure E))
    (f : Lp F 2 (volume : Measure E)) :
    ⇑(m • dilateLp volume ℝ 2 r⁻¹ (inv_pos.2 hr) (𝓕 f) : Lp F 2 (volume : Measure E)) =ᵐ[volume]
      dilateLp volume ℝ 2 r⁻¹ (inv_pos.2 hr)
        (dilateLp volume ℝ ∞ r hr m • 𝓕 f : Lp F 2 (volume : Measure E)) := by
  filter_upwards [coeFn_lpSMul (r := 2) m (dilateLp volume ℝ 2 r⁻¹ (inv_pos.2 hr) (𝓕 f)),
    coeFn_dilateLp (μ := volume) (𝕜 := ℝ) (p := 2) (inv_pos.2 hr) (𝓕 f),
    coeFn_dilateLp_of_ae_eq (𝕜 := ℝ) (inv_pos.2 hr)
      (coeFn_lpSMul (r := 2) (dilateLp volume ℝ ∞ r hr m) (𝓕 f)),
    (quasiMeasurePreserving_smul (volume : Measure E) (inv_ne_zero (inv_pos.2 hr).ne')).ae_eq_comp
      (coeFn_dilateLp_top (μ := volume) (𝕜 := ℝ) hr m)] with ξ h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₄
  rw [h₁, Pi.smul_apply', h₂, h₃, Pi.smul_apply', h₄, inv_inv, inv_smul_smul₀ hr.ne', smul_comm]

/-- **Conjugating a Fourier multiplier by a dilation dilates its symbol.** For `r > 0`, the
multiplier with symbol `m` applied after the normalized dilation `D_r` of `L²` is `D_r` applied
after the multiplier with the dilated symbol `m (r⁻¹ • ·)`, the dilation by `r` on `L^∞`. -/
theorem fourierMultiplierCLM_dilateLp {r : ℝ} (hr : 0 < r) (m : Lp ℂ ∞ (volume : Measure E))
    (f : Lp F 2 (volume : Measure E)) :
    fourierMultiplierCLM F m (dilateLp volume ℝ 2 r hr f) =
      dilateLp volume ℝ 2 r hr (fourierMultiplierCLM F (dilateLp volume ℝ ∞ r hr m) f) := by
  have key : 𝓕 (fourierMultiplierCLM F m (dilateLp volume ℝ 2 r hr f)) =
      𝓕 (dilateLp volume ℝ 2 r hr (fourierMultiplierCLM F (dilateLp volume ℝ ∞ r hr m) f)) := by
    rw [fourier_fourierMultiplierCLM, fourier_dilateLp, fourier_dilateLp,
      fourier_fourierMultiplierCLM]
    exact Lp.ext (coeFn_fourier_dilateLp_aux hr m f)
  exact (fourierTransformₗᵢ E F).injective key

end Dilation

end MeasureTheory.Lp

/-! ### Convolution with an integrable kernel -/

namespace TauCeti

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {k : E → ℝ}

/-- **Convolution with an integrable kernel is a Fourier multiplier on `L²`.** If `k` is
integrable and the symbol `m ∈ L^∞` is almost everywhere the Fourier transform of `k`, then
convolution with `k` on `L²` is the multiplier with symbol `m`. -/
theorem convolutionLp_eq_fourierMultiplierCLM (hk : Integrable k)
    {m : Lp ℂ ∞ (volume : Measure E)} (hm : m =ᵐ[volume] 𝓕 (fun x ↦ (k x : ℂ))) :
    (convolutionLp (p := 2) ENNReal.ofNat_ne_top k volume :
        Lp F 2 (volume : Measure E) →L[ℝ] Lp F 2 (volume : Measure E)) =
      (Lp.fourierMultiplierCLM F m).restrictScalars ℝ := by
  -- Both sides are continuous, and they agree on the dense set of Schwartz functions.
  refine ContinuousLinearMap.coeFn_injective <|
    (SchwartzMap.denseRange_toLpCLM (F := F) (E := E) (p := 2) ENNReal.ofNat_ne_top).equalizer
      (map_continuous _) (map_continuous _) (funext fun φ ↦ ?_)
  simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply, coe_restrictScalars']
  -- The class `φ.toLp 2` is represented by `φ`, so the operator is the convolution `k ⋆ φ`.
  have hconv : convolutionLp (p := 2) ENNReal.ofNat_ne_top k volume (φ.toLp 2) =ᵐ[volume]
      k ⋆ (φ : E → F) := by
    have h := convolutionLp_ae_eq_convolution (p := 2) ENNReal.ofNat_ne_top hk
      (Lp.memLp (φ.toLp 2))
    rw [Lp.toLp_coeFn] at h
    exact h.trans (.of_eq (convolution_congr _ (EventuallyEq.refl _ k) (φ.coeFn_toLp 2)))
  have hh₁ : Integrable (k ⋆ (φ : E → F)) := hk.integrable_convolution _ φ.integrable
  have hh₂ : MemLp (k ⋆ (φ : E → F)) 2 := (Lp.memLp _).ae_eq hconv
  have hS : convolutionLp (p := 2) ENNReal.ofNat_ne_top k volume (φ.toLp 2) = hh₂.toLp _ :=
    Lp.ext (hconv.trans hh₂.coeFn_toLp.symm)
  -- On the Fourier side, both sides are multiplication of `𝓕 φ` by `𝓕 k`.
  have key : (𝓕 (hh₂.toLp _) : Lp F 2 (volume : Measure E)) =
      𝓕 (Lp.fourierMultiplierCLM F m (φ.toLp 2)) := by
    rw [Lp.fourier_fourierMultiplierCLM, SchwartzMap.toLp_fourier_eq]
    refine Lp.ext ?_
    filter_upwards [hh₁.coeFn_fourier_toLp hh₂, Lp.coeFn_lpSMul (r := 2) m ((𝓕 φ).toLp 2),
      (𝓕 φ).coeFn_toLp 2, hm] with ξ hhξ hmξ hφξ hkξ
    rw [hhξ, hmξ, Pi.smul_apply', hkξ, hφξ, Real.fourier_convolution_eq hk φ.integrable,
      SchwartzMap.fourier_coe]
  rw [hS]
  exact (Lp.fourierTransformₗᵢ E F).injective key

/-- **The Fourier transform of a convolution on `L²`.** For an integrable kernel `k` and
`f ∈ L²`, the `L²` Fourier transform of `k ⋆ f` is almost everywhere `ξ ↦ 𝓕 k ξ • 𝓕 f ξ`, with
`k` viewed as complex valued. -/
theorem coeFn_fourier_convolutionLp (hk : Integrable k) (f : Lp F 2 (volume : Measure E)) :
    ⇑(𝓕 (convolutionLp (p := 2) ENNReal.ofNat_ne_top k volume f) :
        Lp F 2 (volume : Measure E)) =ᵐ[volume]
      fun ξ ↦ 𝓕 (fun x ↦ (k x : ℂ)) ξ • (𝓕 f : Lp F 2 (volume : Measure E)) ξ := by
  have hki : Integrable (fun x ↦ (k x : ℂ)) := hk.ofReal
  have hk' : MemLp (𝓕 (fun x ↦ (k x : ℂ))) ∞ volume :=
    (eLpNorm_fourier_top_le _).trans_lt (memLp_one_iff_integrable.2 hki).eLpNorm_lt_top
  have h := congr($(convolutionLp_eq_fourierMultiplierCLM (F := F) hk hk'.coeFn_toLp) f)
  rw [coe_restrictScalars'] at h
  rw [h]
  exact Lp.coeFn_fourier_fourierMultiplierCLM_toLp f hk'

end TauCeti
