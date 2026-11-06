/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.L2Multiplier
public import TauCeti.Analysis.Semigroups.Group.Unitary
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The free Schrödinger propagator on `L²`

Let `E` be a finite-dimensional real inner product space and `F` a complex Hilbert space. The
free Schrödinger equation `i ∂ₜu + Δu = 0` on `E` is solved, on the Fourier side, by
multiplication with a unimodular phase: with Mathlib's normalization of the Fourier transform
`𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`, the Laplacian is the multiplier `-4π² ‖ξ‖²`, so the
propagator `S(t) = exp(itΔ)` is the Fourier multiplier with symbol

`e_t(ξ) = exp(-4π² i t ‖ξ‖²)`.

This file defines `S(t)` on `L²(E, F)` as the `L²` Fourier multiplier
`MeasureTheory.Lp.fourierMultiplierCLM` with that symbol, and proves the group laws: `S(0) = 1`,
`S(s + t) = S(s) S(t)`, `S(t)† = S(-t)`, so that each `S(t)` is unitary, and `t ↦ S(t) f` is
continuous. Together these make `S` a unitary strongly continuous one-parameter group
(`TauCeti.schrodingerGroup`), so the generator theory of
`TauCeti.Analysis.Semigroups.Group.Unitary` applies to it. The propagator commutes with every `L²`
Fourier multiplier `T_m` with symbol `m ∈ L^∞`.

The dispersive estimate `‖S(t) f‖_∞ ≤ (4π|t|)^{-d/2} ‖f‖₁` and the kernel of `S(t)` are in
`TauCeti.Analysis.PDE.Schrodinger.Dispersive`.

## Main declarations

* `TauCeti.schrodingerSymbol`: the symbol `e_t(ξ) = exp(-4π² i t ‖ξ‖²)`.
* `TauCeti.schrodingerPropagator`: the propagator `S(t) = exp(itΔ)` on `L²(E, F)`.
* `TauCeti.coeFn_fourier_schrodingerPropagator`: `𝓕 (S(t) f) = e_t • 𝓕 f` almost everywhere.
* `TauCeti.schrodingerPropagator_zero`, `TauCeti.schrodingerPropagator_add`: the group laws.
* `TauCeti.adjoint_schrodingerPropagator`: `S(t)† = S(-t)`.
* `TauCeti.norm_schrodingerPropagator_apply`, `TauCeti.inner_schrodingerPropagator_apply`:
  conservation of mass, `‖S(t) f‖ = ‖f‖`, and unitarity.
* `TauCeti.continuous_schrodingerPropagator_apply`: strong continuity in `t`.
* `TauCeti.schrodingerPropagator_comp_fourierMultiplierCLM`: `S(t)` commutes with `L²` Fourier
  multipliers.
* `TauCeti.schrodingerGroup`, `TauCeti.isUnitary_schrodingerGroup`: `S` as a unitary C₀-group.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2.
-/

public section

noncomputable section

open scoped ENNReal FourierTransform ComplexInnerProductSpace InnerProduct Topology
open MeasureTheory Complex Filter Real

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E]

/-! ### The symbol -/

/-- The symbol `e_t(ξ) = exp(-4π² i t ‖ξ‖²)` of the free Schrödinger propagator `exp(itΔ)`, for
Mathlib's normalization of the Fourier transform, in which `Δ` has symbol `-4π² ‖ξ‖²`. -/
def schrodingerSymbol (t : ℝ) (ξ : E) : ℂ :=
  cexp ((-4 * π ^ 2 * t * ‖ξ‖ ^ 2 : ℝ) * I)

theorem schrodingerSymbol_apply (t : ℝ) (ξ : E) :
    schrodingerSymbol t ξ = cexp ((-4 * π ^ 2 * t * ‖ξ‖ ^ 2 : ℝ) * I) :=
  (rfl)

/-- The symbol is unimodular. -/
@[simp]
theorem norm_schrodingerSymbol (t : ℝ) (ξ : E) : ‖schrodingerSymbol t ξ‖ = 1 :=
  norm_exp_ofReal_mul_I _

@[simp]
theorem schrodingerSymbol_zero (ξ : E) : schrodingerSymbol 0 ξ = 1 := by
  simp [schrodingerSymbol]

/-- The symbols form a group under multiplication: `e_{s+t} = e_s e_t`. -/
theorem schrodingerSymbol_add (s t : ℝ) (ξ : E) :
    schrodingerSymbol (s + t) ξ = schrodingerSymbol s ξ * schrodingerSymbol t ξ := by
  simp only [schrodingerSymbol, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Complex conjugation reverses time: `conj e_t = e_{-t}`. -/
theorem star_schrodingerSymbol (t : ℝ) (ξ : E) :
    star (schrodingerSymbol t ξ) = schrodingerSymbol (-t) ξ := by
  rw [schrodingerSymbol, schrodingerSymbol, star_def, ← Complex.exp_conj, map_mul, conj_ofReal,
    conj_I]
  congr 1
  push_cast
  ring

@[fun_prop]
theorem continuous_schrodingerSymbol_uncurry :
    Continuous (Function.uncurry (schrodingerSymbol : ℝ → E → ℂ)) := by
  unfold schrodingerSymbol
  fun_prop

@[fun_prop]
theorem continuous_schrodingerSymbol (t : ℝ) : Continuous (schrodingerSymbol t : E → ℂ) := by
  unfold schrodingerSymbol
  fun_prop

/-- The symbol is essentially bounded, so it defines an `L²` Fourier multiplier. -/
theorem memLp_schrodingerSymbol [MeasurableSpace E] [OpensMeasurableSpace E] (t : ℝ)
    (μ : Measure E) :
    MemLp (schrodingerSymbol t) ∞ μ :=
  memLp_top_of_bound (continuous_schrodingerSymbol t).aestronglyMeasurable 1
    (.of_forall fun ξ ↦ (norm_schrodingerSymbol t ξ).le)

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The symbol `e_t` as an element of `L^∞`. -/
private abbrev symbolLp (t : ℝ) : Lp ℂ ∞ (volume : Measure E) :=
  (memLp_schrodingerSymbol t volume).toLp _

private theorem norm_symbolLp_le (t : ℝ) : ‖(symbolLp t : Lp ℂ ∞ (volume : Measure E))‖ ≤ 1 :=
  Lp.norm_top_le_of_ae_bound zero_le_one <| by
    filter_upwards [(memLp_schrodingerSymbol t (volume : Measure E)).coeFn_toLp] with ξ hξ
    rw [hξ, norm_schrodingerSymbol]

private theorem symbolLp_add (s t : ℝ) :
    (symbolLp (s + t) : Lp ℂ ∞ (volume : Measure E)) =
      (symbolLp s : Lp ℂ ∞ (volume : Measure E)) • (symbolLp t : Lp ℂ ∞ (volume : Measure E)) := by
  apply Lp.ext
  filter_upwards [(memLp_schrodingerSymbol (s + t) (volume : Measure E)).coeFn_toLp,
    (memLp_schrodingerSymbol s (volume : Measure E)).coeFn_toLp,
    (memLp_schrodingerSymbol t (volume : Measure E)).coeFn_toLp,
    Lp.coeFn_lpSMul (r := ∞) (symbolLp s : Lp ℂ ∞ (volume : Measure E)) (symbolLp t)]
    with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₄, Pi.smul_apply', h₂, h₃, schrodingerSymbol_add, smul_eq_mul]

private theorem star_symbolLp (t : ℝ) :
    star (symbolLp t : Lp ℂ ∞ (volume : Measure E)) = symbolLp (-t) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (symbolLp t : Lp ℂ ∞ (volume : Measure E)),
    (memLp_schrodingerSymbol t (volume : Measure E)).coeFn_toLp,
    (memLp_schrodingerSymbol (-t) (volume : Measure E)).coeFn_toLp] with ξ h₁ h₂ h₃
  rw [h₁, Pi.star_apply, h₂, h₃, star_schrodingerSymbol]

/-! ### The propagator -/

variable (F) in
/-- The **free Schrödinger propagator** `S(t) = exp(itΔ)` on `L²(E, F)`: the `L²` Fourier
multiplier with the unimodular symbol `e_t(ξ) = exp(-4π² i t ‖ξ‖²)`. On the Fourier side the free
Schrödinger equation `i ∂ₜu + Δu = 0` reads `∂ₜ û = -4π² i ‖ξ‖² û`, which `e_t • 𝓕 f` solves
with initial datum `𝓕 f`. -/
def schrodingerPropagator (t : ℝ) : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F (symbolLp t)

theorem schrodingerPropagator_def (t : ℝ) :
    schrodingerPropagator F t =
      Lp.fourierMultiplierCLM F ((memLp_schrodingerSymbol t (volume : Measure E)).toLp _) :=
  (rfl)

/-- On the Fourier side, `S(t)` is multiplication by the symbol `e_t`. -/
theorem coeFn_fourier_schrodingerPropagator (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (schrodingerPropagator F t f) =ᵐ[volume] fun ξ ↦ schrodingerSymbol t ξ • 𝓕 f ξ := by
  rw [schrodingerPropagator, Lp.fourier_fourierMultiplierCLM]
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (symbolLp t) (𝓕 f),
    (memLp_schrodingerSymbol t (volume : Measure E)).coeFn_toLp] with ξ h₁ h₂
  rw [h₁, Pi.smul_apply', h₂]

/-- `S(t)` is the only bounded operator on `L²` acting on the Fourier side as multiplication by
the symbol `e_t`. -/
theorem eq_schrodingerPropagator_iff {t : ℝ}
    {T : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E)} :
    T = schrodingerPropagator F t ↔
      ∀ f, 𝓕 (T f) =ᵐ[volume] fun ξ ↦ schrodingerSymbol t ξ • 𝓕 f ξ := by
  refine ⟨fun h f ↦ h ▸ coeFn_fourier_schrodingerPropagator t f, fun h ↦ ?_⟩
  ext1 f
  refine (Lp.fourierTransformₗᵢ E F).injective (Lp.ext ?_)
  exact (h f).trans (coeFn_fourier_schrodingerPropagator t f).symm

/-- At time `0` the propagator is the identity. -/
@[simp]
theorem schrodingerPropagator_zero :
    schrodingerPropagator F (0 : ℝ) = ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure E)) := by
  rw [schrodingerPropagator, Lp.fourierMultiplierCLM_of_ae_eq_const (c := 1), one_smul]
  filter_upwards [(memLp_schrodingerSymbol 0 (volume : Measure E)).coeFn_toLp] with ξ hξ
  simp [hξ]

/-- The **group law** `S(s + t) = S(s) S(t)`. -/
theorem schrodingerPropagator_add (s t : ℝ) :
    schrodingerPropagator F (s + t) =
      (schrodingerPropagator F s).comp
        (schrodingerPropagator F t : Lp F 2 (volume : Measure E) →L[ℂ] _) := by
  rw [schrodingerPropagator, schrodingerPropagator, schrodingerPropagator,
    Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM, symbolLp_add]

theorem schrodingerPropagator_add_apply (s t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    schrodingerPropagator F (s + t) f =
      schrodingerPropagator F s (schrodingerPropagator F t f) := by
  rw [schrodingerPropagator_add, ContinuousLinearMap.comp_apply]

@[simp]
theorem schrodingerPropagator_neg_apply_schrodingerPropagator_apply (t : ℝ)
    (f : Lp F 2 (volume : Measure E)) :
    schrodingerPropagator F (-t) (schrodingerPropagator F t f) = f := by
  rw [← schrodingerPropagator_add_apply, neg_add_cancel, schrodingerPropagator_zero,
    ContinuousLinearMap.id_apply]

@[simp]
theorem schrodingerPropagator_apply_schrodingerPropagator_neg_apply (t : ℝ)
    (f : Lp F 2 (volume : Measure E)) :
    schrodingerPropagator F t (schrodingerPropagator F (-t) f) = f := by
  simpa using schrodingerPropagator_neg_apply_schrodingerPropagator_apply (-t) f

/-- The adjoint of `S(t)` is `S(-t)`: the Schrödinger evolution runs backwards under taking
adjoints. -/
theorem adjoint_schrodingerPropagator (t : ℝ) :
    (schrodingerPropagator F t : Lp F 2 (volume : Measure E) →L[ℂ] _)† =
      schrodingerPropagator F (-t) := by
  rw [schrodingerPropagator, Lp.adjoint_fourierMultiplierCLM, star_symbolLp, schrodingerPropagator]

/-- `S(t)` is unitary: it preserves the inner product of `L²`. -/
@[simp]
theorem inner_schrodingerPropagator_apply (t : ℝ) (f g : Lp F 2 (volume : Measure E)) :
    ⟪schrodingerPropagator F t f, schrodingerPropagator F t g⟫ = ⟪f, g⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_schrodingerPropagator,
    schrodingerPropagator_neg_apply_schrodingerPropagator_apply]

/-- **Conservation of mass**: `‖S(t) f‖ = ‖f‖`. -/
@[simp]
theorem norm_schrodingerPropagator_apply (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    ‖schrodingerPropagator F t f‖ = ‖f‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) f,
    inner_schrodingerPropagator_apply]

/-- **Strong continuity**: for every `f ∈ L²`, the orbit `t ↦ S(t) f` is continuous. -/
theorem continuous_schrodingerPropagator_apply (f : Lp F 2 (volume : Measure E)) :
    Continuous fun t : ℝ ↦ schrodingerPropagator F t f := by
  refine continuous_iff_seqContinuous.2 fun τ t₀ hτ ↦ ?_
  refine Lp.tendsto_fourierMultiplierCLM_apply (C := 1) (.of_forall fun n ↦ norm_symbolLp_le _)
    ?_ f
  filter_upwards [ae_all_iff.2 fun n ↦
      (memLp_schrodingerSymbol (τ n) (volume : Measure E)).coeFn_toLp,
    (memLp_schrodingerSymbol t₀ (volume : Measure E)).coeFn_toLp] with ξ h₁ h₂
  simp only [h₁, h₂]
  exact ((continuous_schrodingerSymbol_uncurry.comp (continuous_id.prodMk continuous_const)).tendsto
    t₀).comp hτ

/-- `S(t)` commutes with every `L²` Fourier multiplier `T_m`. -/
theorem schrodingerPropagator_comp_fourierMultiplierCLM (t : ℝ) (m : Lp ℂ ∞ (volume : Measure E)) :
    (schrodingerPropagator F t).comp (Lp.fourierMultiplierCLM F m) =
      (Lp.fourierMultiplierCLM F m).comp (schrodingerPropagator F t) := by
  rw [schrodingerPropagator, Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM,
    Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM]
  congr 1
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := ∞) (symbolLp t : Lp ℂ ∞ (volume : Measure E)) m,
    Lp.coeFn_lpSMul (r := ∞) m (symbolLp t : Lp ℂ ∞ (volume : Measure E))] with ξ h₁ h₂
  rw [h₁, h₂, Pi.smul_apply', Pi.smul_apply', smul_eq_mul, smul_eq_mul, mul_comm]

/-! ### The Schrödinger group -/

variable (F) in
/-- The free Schrödinger evolution as a strongly continuous one-parameter group on `L²(E, F)`,
regarded as a real Banach space: the group operator at time `t` is `S(t) = exp(itΔ)`. -/
def schrodingerGroup : Semigroups.StronglyContinuousGroup (Lp F 2 (volume : Measure E)) where
  toFun t := (schrodingerPropagator F t).restrictScalars ℝ
  map_zero' := by ext1 f; simp
  map_add' s t := by ext1 f; simp [schrodingerPropagator_add_apply]
  continuousAt_zero' f := (continuous_schrodingerPropagator_apply f).continuousAt

@[simp]
theorem schrodingerGroup_apply (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    schrodingerGroup F t f = schrodingerPropagator F t f :=
  (rfl)

/-- The Schrödinger group is unitary. -/
theorem isUnitary_schrodingerGroup :
    (schrodingerGroup F :
      Semigroups.StronglyContinuousGroup (Lp F 2 (volume : Measure E))).IsUnitary :=
  .intro fun t f g ↦ inner_schrodingerPropagator_apply t f g

end TauCeti
