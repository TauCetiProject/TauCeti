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
# The Schrödinger propagator on `L²`

Let `E` be a finite-dimensional real inner product space and `F` a complex Hilbert space. The
free Schrödinger equation `i ∂ₜ u + Δ u = 0` on `E` is solved by the **Schrödinger propagator**
`S(t) = exp (i t Δ)`. With Mathlib's normalisation of the Fourier transform, which puts `2π` in
the exponent, the Laplacian is the Fourier multiplier `-4π² ‖ξ‖²`, so `S(t)` is the Fourier
multiplier on `L²(E, F)` with the unimodular symbol

`ξ ↦ exp (-4π² i t ‖ξ‖²)`.

This file constructs `S(t)` from the `L²` Fourier multipliers of
`TauCeti.Analysis.Fourier.L2Multiplier` and proves that it is a **strongly continuous unitary
group**: `S(0) = 1`, `S(s + t) = S(s) S(t)`, each `S(t)` preserves the inner product of `L²`
and has adjoint `S(-t)`, and `t ↦ S(t) f` is continuous for every `f ∈ L²`. These are packaged as a
`TauCeti.Semigroups.StronglyContinuousGroup` on `L²`, which is unitary in the sense of
`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary`.

The dispersive estimate `‖S(t) f‖_∞ ≤ (4π |t|)^{-d/2} ‖f‖₁`, which is what distinguishes the
Schrödinger group from an arbitrary unitary group, is proved in
`TauCeti.Analysis.PDE.Schrodinger.Dispersive`.

## Main declarations

* `TauCeti.schrodingerSymbol`: the symbol `ξ ↦ exp (-4π² i t ‖ξ‖²)`.
* `TauCeti.schrodingerPropagator`: the propagator `S(t) = exp (i t Δ)` on `L²(E, F)`.
* `TauCeti.coeFn_fourier_schrodingerPropagator`: `𝓕 (S(t) f) = exp (-4π² i t ‖ξ‖²) 𝓕 f`.
* `TauCeti.schrodingerPropagator_zero`, `TauCeti.schrodingerPropagator_add`: the group law.
* `TauCeti.inner_schrodingerPropagator_apply`, `TauCeti.norm_schrodingerPropagator_apply` and
  `TauCeti.adjoint_schrodingerPropagator`: `S(t)` is unitary with adjoint `S(-t)`.
* `TauCeti.continuous_schrodingerPropagator_apply`: strong continuity.
* `TauCeti.commute_schrodingerPropagator_fourierMultiplierCLM`: `S(t)` commutes with every `L²`
  Fourier multiplier.
* `TauCeti.schrodingerGroup` and `TauCeti.isUnitary_schrodingerGroup`: the propagators form a
  unitary strongly continuous group.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness*, Section IX.7.
-/

public section

noncomputable section

open MeasureTheory Complex Filter ContinuousLinearMap
open scoped ENNReal FourierTransform InnerProductSpace InnerProduct Topology Real

namespace TauCeti

/-! ### The symbol -/

section Symbol

variable {E : Type*} [NormedAddCommGroup E]

/-- The symbol `ξ ↦ exp (-4π² i t ‖ξ‖²)` of the Schrödinger propagator `exp (i t Δ)`, for
Mathlib's normalisation of the Fourier transform, under which `Δ` has symbol `-4π² ‖ξ‖²`. -/
def schrodingerSymbol (t : ℝ) (ξ : E) : ℂ :=
  cexp (-(4 * π ^ 2 * t * I) * ‖ξ‖ ^ 2)

theorem schrodingerSymbol_apply (t : ℝ) (ξ : E) :
    schrodingerSymbol t ξ = cexp (-(4 * π ^ 2 * t * I) * ‖ξ‖ ^ 2) :=
  (rfl)

/-- The Schrödinger symbol is unimodular. -/
@[simp]
theorem norm_schrodingerSymbol (t : ℝ) (ξ : E) : ‖schrodingerSymbol t ξ‖ = 1 := by
  rw [schrodingerSymbol_apply, norm_exp]
  simp [← ofReal_pow]

@[simp]
theorem schrodingerSymbol_zero : schrodingerSymbol (0 : ℝ) = fun _ : E ↦ (1 : ℂ) := by
  ext ξ
  simp [schrodingerSymbol_apply]

/-- The symbols form a one-parameter group under pointwise multiplication. -/
theorem schrodingerSymbol_add (s t : ℝ) (ξ : E) :
    schrodingerSymbol (s + t) ξ = schrodingerSymbol s ξ * schrodingerSymbol t ξ := by
  simp only [schrodingerSymbol_apply, ← exp_add, ofReal_add]
  ring_nf

/-- The complex conjugate of the symbol at time `t` is the symbol at time `-t`. -/
@[simp]
theorem star_schrodingerSymbol (t : ℝ) (ξ : E) :
    star (schrodingerSymbol t ξ) = schrodingerSymbol (-t) ξ := by
  simp only [schrodingerSymbol_apply, RCLike.star_def, ← exp_conj, map_mul, map_neg, map_pow,
    conj_ofReal, conj_I, map_ofNat, ofReal_neg]
  ring_nf

/-- The Schrödinger symbol is jointly continuous in time and frequency. -/
theorem continuous_schrodingerSymbol :
    Continuous fun p : ℝ × E ↦ schrodingerSymbol p.1 p.2 := by
  simp only [schrodingerSymbol_apply]
  fun_prop

/-- The Schrödinger symbol is essentially bounded, for every measure. -/
theorem memLp_schrodingerSymbol [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E)
    (t : ℝ) : MemLp (schrodingerSymbol t) ∞ μ :=
  memLp_top_of_bound (continuous_schrodingerSymbol.comp
    (Continuous.prodMk_right t)).aestronglyMeasurable 1 (ae_of_all _ fun ξ ↦ by simp)

end Symbol

/-! ### The propagator -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The **Schrödinger propagator** `S(t) = exp (i t Δ)` on `L²(E, F)`: the Fourier multiplier
with the unimodular symbol `ξ ↦ exp (-4π² i t ‖ξ‖²)` (`TauCeti.schrodingerSymbol`). On the
Fourier side, where `Δ` is multiplication by `-4π² ‖ξ‖²`, this is the evolution of the free
Schrödinger equation `i ∂ₜ u + Δ u = 0`. -/
def schrodingerPropagator (t : ℝ) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F ((memLp_schrodingerSymbol volume t).toLp _)

theorem schrodingerPropagator_def (t : ℝ) :
    schrodingerPropagator (E := E) (F := F) t =
      Lp.fourierMultiplierCLM F ((memLp_schrodingerSymbol volume t).toLp _) :=
  (rfl)

/-- On the Fourier side, `S(t)` is multiplication by `exp (-4π² i t ‖ξ‖²)`. -/
theorem coeFn_fourier_schrodingerPropagator (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (schrodingerPropagator t f) =ᵐ[volume] fun ξ ↦ schrodingerSymbol t ξ • 𝓕 f ξ := by
  rw [schrodingerPropagator_def, Lp.fourier_fourierMultiplierCLM]
  filter_upwards [Lp.coeFn_lpSMul (r := 2) ((memLp_schrodingerSymbol volume t).toLp _) (𝓕 f),
    (memLp_schrodingerSymbol volume t).coeFn_toLp] with ξ h₁ h₂
  rw [h₁, Pi.smul_apply', h₂]

/-- At time `0` the propagator is the identity. -/
@[simp]
theorem schrodingerPropagator_zero :
    schrodingerPropagator (E := E) (F := F) 0 = ContinuousLinearMap.id ℂ _ := by
  rw [schrodingerPropagator_def, Lp.fourierMultiplierCLM_of_ae_eq_const (c := 1), one_smul]
  filter_upwards [(memLp_schrodingerSymbol volume 0).coeFn_toLp] with ξ h
  rw [h, schrodingerSymbol_zero]

/-- The group law `S(s + t) = S(s) S(t)`. -/
theorem schrodingerPropagator_add (s t : ℝ) :
    schrodingerPropagator (E := E) (F := F) (s + t) =
      schrodingerPropagator s ∘L schrodingerPropagator t := by
  rw [schrodingerPropagator_def, schrodingerPropagator_def, schrodingerPropagator_def,
    Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM]
  congr 1
  refine Lp.ext ?_
  filter_upwards [(memLp_schrodingerSymbol volume (s + t)).coeFn_toLp,
    (memLp_schrodingerSymbol volume s).coeFn_toLp, (memLp_schrodingerSymbol volume t).coeFn_toLp,
    Lp.coeFn_lpSMul (r := ∞) ((memLp_schrodingerSymbol volume s).toLp _)
      ((memLp_schrodingerSymbol volume t).toLp _)] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₄, Pi.smul_apply', h₂, h₃, smul_eq_mul, schrodingerSymbol_add]

theorem schrodingerPropagator_add_apply (s t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    schrodingerPropagator (s + t) f = schrodingerPropagator s (schrodingerPropagator t f) := by
  rw [schrodingerPropagator_add, comp_apply]

@[simp]
theorem schrodingerPropagator_neg_apply_apply (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    schrodingerPropagator (-t) (schrodingerPropagator t f) = f := by
  rw [← schrodingerPropagator_add_apply, neg_add_cancel, schrodingerPropagator_zero, id_apply]

@[simp]
theorem schrodingerPropagator_apply_neg_apply (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    schrodingerPropagator t (schrodingerPropagator (-t) f) = f := by
  rw [← schrodingerPropagator_add_apply, add_neg_cancel, schrodingerPropagator_zero, id_apply]

/-- `S(t)` commutes with every Fourier multiplier on `L²`. -/
theorem commute_schrodingerPropagator_fourierMultiplierCLM (t : ℝ)
    (m : Lp ℂ ∞ (volume : Measure E)) :
    Commute (schrodingerPropagator (F := F) t) (Lp.fourierMultiplierCLM F m) := by
  rw [Commute, SemiconjBy, mul_def, mul_def, schrodingerPropagator_def,
    Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM,
    Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM]
  congr 1
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_lpSMul (r := ∞) ((memLp_schrodingerSymbol volume t).toLp _) m,
    Lp.coeFn_lpSMul (r := ∞) m ((memLp_schrodingerSymbol volume t).toLp _)] with ξ h₁ h₂
  rw [h₁, h₂, Pi.smul_apply', Pi.smul_apply', smul_eq_mul, smul_eq_mul, mul_comm]

/-- The adjoint of `S(t)` is `S(-t)`. -/
theorem adjoint_schrodingerPropagator (t : ℝ) :
    (schrodingerPropagator (E := E) (F := F) t)† = schrodingerPropagator (-t) := by
  rw [schrodingerPropagator_def, schrodingerPropagator_def, Lp.adjoint_fourierMultiplierCLM]
  congr 1
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star ((memLp_schrodingerSymbol volume t).toLp _),
    (memLp_schrodingerSymbol volume t).coeFn_toLp,
    (memLp_schrodingerSymbol volume (-t)).coeFn_toLp] with ξ h₁ h₂ h₃
  rw [h₁, Pi.star_apply, h₂, h₃, star_schrodingerSymbol]

/-- `S(t)` preserves the inner product of `L²`. -/
@[simp]
theorem inner_schrodingerPropagator_apply (t : ℝ) (f g : Lp F 2 (volume : Measure E)) :
    ⟪schrodingerPropagator t f, schrodingerPropagator t g⟫_ℂ = ⟪f, g⟫_ℂ := by
  rw [← adjoint_inner_right, adjoint_schrodingerPropagator, schrodingerPropagator_neg_apply_apply]

/-- `S(t)` preserves the norm of `L²`. -/
@[simp]
theorem norm_schrodingerPropagator_apply (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    ‖schrodingerPropagator t f‖ = ‖f‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_schrodingerPropagator_apply,
    ← norm_eq_sqrt_re_inner]

/-- **Strong continuity**: for every `f ∈ L²`, the orbit `t ↦ S(t) f` is continuous. -/
theorem continuous_schrodingerPropagator_apply (f : Lp F 2 (volume : Measure E)) :
    Continuous fun t ↦ schrodingerPropagator t f := by
  -- Along a sequence of times, dominated convergence on the Fourier side.
  refine continuous_iff_seqContinuous.2 fun s t₀ hs ↦ ?_
  simp only [Function.comp_def, schrodingerPropagator_def]
  refine Lp.tendsto_fourierMultiplierCLM_apply (C := 1) (Eventually.of_forall fun n ↦ ?_) ?_ f
  · refine Lp.norm_top_le_of_ae_bound zero_le_one ?_
    filter_upwards [(memLp_schrodingerSymbol volume (s n)).coeFn_toLp] with ξ h
    rw [h, norm_schrodingerSymbol]
  · filter_upwards [ae_all_iff.2 fun n ↦ (memLp_schrodingerSymbol volume (s n)).coeFn_toLp,
      (memLp_schrodingerSymbol volume t₀).coeFn_toLp] with ξ h₁ h₂
    simp only [h₁, h₂]
    exact (continuous_schrodingerSymbol.comp (Continuous.prodMk_left ξ)).continuousAt.tendsto.comp
      hs

/-! ### The unitary group -/

/-- The Schrödinger propagators `S(t)`, `t ∈ ℝ`, as a strongly continuous group on `L²(E, F)`.
The group API represents operators real-linearly; `TauCeti.schrodingerGroup_apply` recovers
`S(t)`. -/
def schrodingerGroup : Semigroups.StronglyContinuousGroup (Lp F 2 (volume : Measure E)) where
  toFun t := (schrodingerPropagator t).restrictScalars ℝ
  map_zero' := by
    ext1 f
    simp
  map_add' s t := by
    ext1 f
    simp [schrodingerPropagator_add_apply]
  continuousAt_zero' f := (continuous_schrodingerPropagator_apply f).continuousAt

@[simp]
theorem schrodingerGroup_apply (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    schrodingerGroup t f = schrodingerPropagator t f :=
  (rfl)

/-- The Schrödinger group is unitary. -/
theorem isUnitary_schrodingerGroup : (schrodingerGroup (E := E) (F := F)).IsUnitary :=
  -- `IsUnitary` sees `L²` through the real structure induced by its complex one, which agrees
  -- with the real `Lp` structure of `schrodingerGroup` only up to unfolding, so `simp` cannot
  -- match the operators and the term is given directly.
  .intro fun t f g ↦ inner_schrodingerPropagator_apply t f g

end TauCeti
