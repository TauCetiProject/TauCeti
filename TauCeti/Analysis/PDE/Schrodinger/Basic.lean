/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.L2Multiplier
public import TauCeti.Analysis.Semigroups.Group.Unitary

/-!
# The Schrödinger propagator on `L²`

On a finite-dimensional real inner product space `E`, the free Schrödinger equation
`i ∂ₜu + Δu = 0` is solved by the **Schrödinger propagator** `S(t) = exp(itΔ)`. In Mathlib's
normalization of the Fourier transform, `𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`, the Laplacian is the
Fourier multiplier with symbol `-4π² ‖ξ‖²`, so `S(t)` is the Fourier multiplier on `L²(E, F)` with
the unimodular symbol

`ξ ↦ exp(-4π² i t ‖ξ‖²)`.

This file constructs `S(t)` as an `L²` Fourier multiplier (`MeasureTheory.Lp.fourierMultiplierCLM`)
and proves the laws that make it a unitary group:

* `S(0) = 1` and `S(s + t) = S(s) S(t)`;
* `S(t)` preserves the `L²` norm and the inner product, and its adjoint is `S(-t)`;
* `t ↦ S(t) f` is continuous for every `f ∈ L²`;
* `S(t)` commutes with every `L²` Fourier multiplier.

Together these give the strongly continuous unitary group `TauCeti.schrodingerGroup`. The
dispersive estimate `‖S(t) f‖_∞ ≤ (4π|t|)^{-n/2} ‖f‖₁` is proved in
`TauCeti.Analysis.PDE.Schrodinger.Dispersive`.

## Main declarations

* `TauCeti.schrodingerSymbol`: the symbol `exp(-4π² i t ‖ξ‖²)`.
* `TauCeti.schrodingerPropagator`: the propagator `S(t)` on `L²(E, F)`.
* `TauCeti.fourier_schrodingerPropagator`: `𝓕 (S(t) f) = exp(-4π² i t ‖·‖²) • 𝓕 f`.
* `TauCeti.schrodingerPropagator_zero`, `TauCeti.schrodingerPropagator_add`: the group law.
* `TauCeti.norm_schrodingerPropagator_apply`, `TauCeti.inner_schrodingerPropagator_apply`,
  `TauCeti.adjoint_schrodingerPropagator`: unitarity.
* `TauCeti.continuous_schrodingerPropagator_apply`: strong continuity.
* `TauCeti.schrodingerGroup`, `TauCeti.isUnitary_schrodingerGroup`: the unitary C₀-group.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2.
-/

public section

noncomputable section

open scoped ENNReal FourierTransform ComplexInnerProductSpace Topology
open MeasureTheory Filter Complex
open Real hiding exp

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- The symbol `ξ ↦ exp(-4π² i t ‖ξ‖²)` of the Schrödinger propagator `exp(itΔ)`, in Mathlib's
normalization of the Fourier transform. -/
def schrodingerSymbol (t : ℝ) (ξ : E) : ℂ :=
  cexp (((-(4 * π ^ 2 * t * ‖ξ‖ ^ 2) : ℝ) : ℂ) * I)

theorem schrodingerSymbol_apply (t : ℝ) (ξ : E) :
    schrodingerSymbol t ξ = cexp (((-(4 * π ^ 2 * t * ‖ξ‖ ^ 2) : ℝ) : ℂ) * I) :=
  (rfl)

/-- The Schrödinger symbol is unimodular. -/
@[simp]
theorem norm_schrodingerSymbol (t : ℝ) (ξ : E) : ‖schrodingerSymbol t ξ‖ = 1 := by
  rw [schrodingerSymbol_apply]
  exact norm_exp_ofReal_mul_I _

@[simp]
theorem schrodingerSymbol_zero (ξ : E) : schrodingerSymbol 0 ξ = 1 := by
  simp [schrodingerSymbol_apply]

theorem schrodingerSymbol_add (s t : ℝ) (ξ : E) :
    schrodingerSymbol (s + t) ξ = schrodingerSymbol s ξ * schrodingerSymbol t ξ := by
  simp only [schrodingerSymbol_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem star_schrodingerSymbol (t : ℝ) (ξ : E) :
    star (schrodingerSymbol t ξ) = schrodingerSymbol (-t) ξ := by
  rw [schrodingerSymbol_apply, schrodingerSymbol_apply, Complex.star_def, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- The Schrödinger symbol is jointly continuous in time and frequency. -/
theorem continuous_schrodingerSymbol_uncurry :
    Continuous fun p : ℝ × E ↦ schrodingerSymbol p.1 p.2 := by
  unfold schrodingerSymbol
  fun_prop

theorem continuous_schrodingerSymbol (t : ℝ) : Continuous (schrodingerSymbol t : E → ℂ) :=
  continuous_schrodingerSymbol_uncurry.comp (Continuous.prodMk_right t)

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Schrödinger symbol is essentially bounded. -/
theorem memLp_schrodingerSymbol (t : ℝ) :
    MemLp (schrodingerSymbol t : E → ℂ) ∞ volume :=
  memLp_top_of_bound (continuous_schrodingerSymbol t).aestronglyMeasurable 1
    (Eventually.of_forall fun ξ ↦ (norm_schrodingerSymbol t ξ).le)

/-- The `L^∞` class of the Schrödinger symbol has norm at most `1`. -/
theorem norm_toLp_schrodingerSymbol_le (t : ℝ) :
    ‖(memLp_schrodingerSymbol (E := E) t).toLp _‖ ≤ 1 := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top]
  · exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun ξ ↦ (norm_schrodingerSymbol t ξ).le))
  · exact (memLp_schrodingerSymbol t).aestronglyMeasurable

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

variable (F) in
/-- The **Schrödinger propagator** `S(t) = exp(itΔ)` on `L²(E, F)`: the Fourier multiplier with
symbol `exp(-4π² i t ‖ξ‖²)`. -/
def schrodingerPropagator (t : ℝ) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F ((memLp_schrodingerSymbol t).toLp _)

theorem schrodingerPropagator_def (t : ℝ) :
    schrodingerPropagator F t =
      Lp.fourierMultiplierCLM (E := E) F ((memLp_schrodingerSymbol t).toLp _) :=
  (rfl)

/-- On the Fourier side, `S(t)` is multiplication by `exp(-4π² i t ‖ξ‖²)`. -/
theorem fourier_schrodingerPropagator (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (schrodingerPropagator F t f) =
      ((memLp_schrodingerSymbol (E := E) t).toLp _ • 𝓕 f : Lp F 2 (volume : Measure E)) :=
  Lp.fourier_fourierMultiplierCLM _ f

/-- `S(0)` is the identity. -/
@[simp]
theorem schrodingerPropagator_zero :
    schrodingerPropagator F 0 = ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure E)) := by
  rw [schrodingerPropagator_def,
    Lp.fourierMultiplierCLM_of_ae_eq_const (E := E) (F := F) (c := 1) ?_, one_smul]
  filter_upwards [(memLp_schrodingerSymbol (E := E) 0).coeFn_toLp] with ξ h
  simp [h]

/-- **The group law** `S(s + t) = S(s) S(t)`. -/
theorem schrodingerPropagator_add (s t : ℝ) :
    schrodingerPropagator F (s + t) =
      schrodingerPropagator F s ∘L schrodingerPropagator (E := E) F t := by
  rw [schrodingerPropagator_def, schrodingerPropagator_def, schrodingerPropagator_def,
    Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM]
  congr 1
  apply Lp.ext
  filter_upwards [(memLp_schrodingerSymbol (E := E) (s + t)).coeFn_toLp,
    (memLp_schrodingerSymbol (E := E) s).coeFn_toLp,
    (memLp_schrodingerSymbol (E := E) t).coeFn_toLp,
    Lp.coeFn_lpSMul (r := ∞) ((memLp_schrodingerSymbol (E := E) s).toLp _)
      ((memLp_schrodingerSymbol (E := E) t).toLp _)] with ξ h₁ h₂ h₃ h₄
  rw [h₄, Pi.smul_apply', h₂, h₃, h₁, smul_eq_mul, schrodingerSymbol_add]

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

/-- `S(t)` has operator norm at most one. -/
theorem norm_schrodingerPropagator_le (t : ℝ) :
    ‖schrodingerPropagator (E := E) F t‖ ≤ 1 :=
  (Lp.norm_fourierMultiplierCLM_le _).trans (norm_toLp_schrodingerSymbol_le t)

/-- **Conservation of the `L²` norm**: `‖S(t) f‖ = ‖f‖`. -/
@[simp]
theorem norm_schrodingerPropagator_apply (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    ‖schrodingerPropagator F t f‖ = ‖f‖ := by
  refine le_antisymm ?_ ?_
  · exact ((schrodingerPropagator F t).le_opNorm f).trans
      (mul_le_of_le_one_left (norm_nonneg f) (norm_schrodingerPropagator_le t))
  · conv_lhs => rw [← schrodingerPropagator_neg_apply_schrodingerPropagator_apply t f]
    exact ((schrodingerPropagator F (-t)).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_schrodingerPropagator_le (-t)))

/-- The adjoint of `S(t)` is `S(-t)`. -/
theorem adjoint_schrodingerPropagator (t : ℝ) :
    ContinuousLinearMap.adjoint (schrodingerPropagator (E := E) F t) =
      schrodingerPropagator F (-t) := by
  rw [schrodingerPropagator_def, schrodingerPropagator_def, Lp.adjoint_fourierMultiplierCLM]
  congr 1
  apply Lp.ext
  filter_upwards [Lp.coeFn_star ((memLp_schrodingerSymbol (E := E) t).toLp _),
    (memLp_schrodingerSymbol (E := E) t).coeFn_toLp,
    (memLp_schrodingerSymbol (E := E) (-t)).coeFn_toLp] with ξ h₁ h₂ h₃
  rw [h₁, Pi.star_apply, h₂, h₃, star_schrodingerSymbol]

/-- `S(t)` preserves the `L²` inner product. -/
@[simp]
theorem inner_schrodingerPropagator_apply (t : ℝ) (f g : Lp F 2 (volume : Measure E)) :
    ⟪schrodingerPropagator F t f, schrodingerPropagator F t g⟫ = ⟪f, g⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_schrodingerPropagator,
    schrodingerPropagator_neg_apply_schrodingerPropagator_apply]

/-- `S(t)` commutes with every `L²` Fourier multiplier. -/
theorem schrodingerPropagator_comp_fourierMultiplierCLM (t : ℝ)
    (m : Lp ℂ ∞ (volume : Measure E)) :
    schrodingerPropagator F t ∘L Lp.fourierMultiplierCLM F m =
      Lp.fourierMultiplierCLM F m ∘L schrodingerPropagator F t := by
  rw [schrodingerPropagator_def, Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM,
    Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM]
  congr 1
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := ∞) ((memLp_schrodingerSymbol (E := E) t).toLp _) m,
    Lp.coeFn_lpSMul (r := ∞) m ((memLp_schrodingerSymbol (E := E) t).toLp _)] with ξ h₁ h₂
  rw [h₁, h₂, Pi.smul_apply', Pi.smul_apply', smul_eq_mul, smul_eq_mul, mul_comm]

/-- **Strong continuity**: `t ↦ S(t) f` is continuous for every `f ∈ L²`. -/
theorem continuous_schrodingerPropagator_apply (f : Lp F 2 (volume : Measure E)) :
    Continuous fun t ↦ schrodingerPropagator F t f := by
  -- Pass to sequences, so that the almost-everywhere representatives of the symbols are chosen
  -- for countably many times only.
  refine continuous_iff_seqContinuous.2 fun τ t hτ ↦ ?_
  refine Lp.tendsto_fourierMultiplierCLM_apply (C := 1)
    (Eventually.of_forall fun n ↦ norm_toLp_schrodingerSymbol_le (τ n)) ?_ f
  filter_upwards [ae_all_iff.2 fun n ↦ (memLp_schrodingerSymbol (E := E) (τ n)).coeFn_toLp,
    (memLp_schrodingerSymbol (E := E) t).coeFn_toLp] with ξ h₁ h₂
  simp only [h₁, h₂]
  exact ((continuous_schrodingerSymbol_uncurry.comp
    (Continuous.prodMk_left ξ)).tendsto t).comp hτ

variable (E F) in
/-- The Schrödinger propagators `t ↦ exp(itΔ)` as a strongly continuous one-parameter group on
`L²(E, F)`. -/
def schrodingerGroup : Semigroups.StronglyContinuousGroup (Lp F 2 (volume : Measure E)) where
  toFun t := (schrodingerPropagator F t).restrictScalars ℝ
  map_zero' := by
    ext1 f
    simp
  map_add' s t := by
    ext1 f
    simp [schrodingerPropagator_add_apply]
  continuousAt_zero' f := (continuous_schrodingerPropagator_apply f).continuousAt

@[simp]
theorem schrodingerGroup_apply (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    schrodingerGroup E F t f = schrodingerPropagator F t f :=
  (rfl)

/-- The Schrödinger group is unitary. -/
theorem isUnitary_schrodingerGroup : (schrodingerGroup E F).IsUnitary :=
  Semigroups.StronglyContinuousGroup.IsUnitary.intro fun t f g ↦
    inner_schrodingerPropagator_apply t f g

end TauCeti
