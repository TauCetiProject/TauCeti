/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# The dual of `L¹`

Let `𝕜` be `ℝ` or `ℂ` (or any `RCLike` field). Integration against an essentially bounded
function `g ∈ L^∞(μ)` is a continuous linear functional `f ↦ ∫ g f dμ` on `L¹(μ)`. This is
Mathlib's Hölder pairing `ContinuousLinearMap.lpPairing` for the multiplication of `𝕜`, at the
exponents `∞` and `1`. On a σ-finite measure space the functional has norm exactly `‖g‖_∞`, so
the pairing is a linear isometry `L^∞(μ) → L¹(μ)*` (`MeasureTheory.Lp.toDualOne`). For a finite
measure it is onto: every continuous linear functional on `L¹(μ)` is integration against an
essentially bounded density. This gives the isometric equivalence `L^∞(μ) ≃ L¹(μ)*`
(`MeasureTheory.Lp.dualOneEquiv`). The integral of the density over a measurable set `s` is the
value of the functional at the indicator function of `s`.

## Main declarations

* `MeasureTheory.Lp.toDualOne`: the isometric pairing `L^∞(μ) → L¹(μ)*` of a σ-finite measure.
* `MeasureTheory.Lp.exists_toDualOne_eq`: for a finite measure, every continuous linear
  functional on `L¹(μ)` is integration against some `g ∈ L^∞(μ)`.
* `MeasureTheory.Lp.dualOneEquiv`: the isometric equivalence `L^∞(μ) ≃ L¹(μ)*` of a finite
  measure, which agrees with `MeasureTheory.Lp.toDualOne` (`MeasureTheory.Lp.coe_dualOneEquiv`).
* `MeasureTheory.Lp.integral_dualOneEquiv_symm_mul`: a functional on `L¹(μ)` is integration
  against its density.
* `MeasureTheory.Lp.setIntegral_dualOneEquiv_symm`: the integral of the density over a set is the
  value of the functional at the indicator function of the set.

## Implementation notes

The density of `φ ∈ L¹(μ)*` is found in `L²(μ)`. For a finite measure, Hölder multiplication by
the constant function `1 ∈ L²(μ)` maps `L²(μ)` continuously into `L¹(μ)`, so `φ` restricts to a
continuous linear functional on `L²(μ)`. The Riesz representation theorem writes it as
`f ↦ ∫ h f` for some `h ∈ L²(μ)`. Testing against simple functions bounds `‖h‖_∞` by `‖φ‖`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le`), and density
of simple functions in `L¹(μ)` gives `φ f = ∫ h f` for every `f ∈ L¹(μ)`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 4.14.
-/

public section

open scoped ENNReal ComplexConjugate

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {μ : Measure α}

variable (𝕜 μ) in
/-- On a σ-finite measure space, the integral pairing `g ↦ (f ↦ ∫ g f dμ)` is a linear isometry
from `L^∞(μ)` to the continuous dual of `L¹(μ)`: integration against `g` is a continuous linear
functional on `L¹(μ)` of norm `‖g‖_∞`. -/
noncomputable def toDualOne [SigmaFinite μ] : Lp 𝕜 ∞ μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ) where
  toLinearMap := ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ ∞ 1 :
    Lp 𝕜 ∞ μ →ₗ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ))
  norm_map' g := by
    set Λ := (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ ∞ 1 g
    have hΛ : ∀ f : Lp 𝕜 1 μ, Λ f = ∫ x, g x * f x ∂μ := fun f => by
      simp [Λ, ContinuousLinearMap.lpPairing_eq_integral]
    -- Hölder's inequality gives `‖Λ‖ ≤ ‖g‖_∞`; testing `Λ` on simple functions gives the converse.
    refine congrArg ENNReal.toReal (le_antisymm (Λ.opENorm_le_bound fun f => ?_) ?_ :
      ‖Λ‖ₑ = ‖g‖ₑ)
    · rw [hΛ, Lp.enorm_def, Lp.enorm_def]
      exact TauCeti.enorm_integral_mul_le
    · rw [Lp.enorm_def]
      refine (Lp.memLp g).eLpNorm_top_le_of_forall_enorm_integral_mul_le fun σ hσ => ?_
      calc ‖∫ x, g x * σ x ∂μ‖ₑ = ‖Λ (hσ.toLp σ)‖ₑ := by
            rw [hΛ]
            congr 1
            exact integral_congr_ae (by filter_upwards [hσ.coeFn_toLp] with x hx; rw [hx])
        _ ≤ ‖Λ‖ₑ * ‖hσ.toLp σ‖ₑ := Λ.le_opENorm _
        _ = ‖Λ‖ₑ * eLpNorm σ 1 μ := by rw [Lp.enorm_def, eLpNorm_congr_ae hσ.coeFn_toLp]

@[simp]
theorem toDualOne_apply [SigmaFinite μ] (g : Lp 𝕜 ∞ μ) (f : Lp 𝕜 1 μ) :
    toDualOne 𝕜 μ g f = ∫ x, g x * f x ∂μ := by
  exact ContinuousLinearMap.lpPairing_eq_integral (B := ContinuousLinearMap.mul 𝕜 𝕜) g f

/-- For a finite measure, every continuous linear functional on `L¹(μ)` is integration against
an essentially bounded function. -/
theorem exists_toDualOne_eq [IsFiniteMeasure μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) :
    ∃ g : Lp 𝕜 ∞ μ, toDualOne 𝕜 μ g = φ := by
  -- Hölder multiplication by the constant `1 ∈ L²(μ)` maps `L²(μ)` continuously into `L¹(μ)`.
  set ι : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 1 μ :=
    (ContinuousLinearMap.mul 𝕜 𝕜).holderL μ 2 2 1 (Lp.const 2 μ (1 : 𝕜))
  have hι : ∀ f, ι f =ᵐ[μ] f := fun f => by
    filter_upwards [(ContinuousLinearMap.mul 𝕜 𝕜).coeFn_holder (r := 1) (Lp.const 2 μ (1 : 𝕜)) f,
      Lp.coeFn_const 2 μ (1 : 𝕜)] with x hx h1
    simp only [ι, ContinuousLinearMap.holderL_apply_apply]
    rw [hx, h1]
    simp
  -- The Riesz representation `h` of `φ ∘ ι` in `L²(μ)` represents `φ` on `L²(μ)`.
  set u : Lp 𝕜 2 μ := (InnerProductSpace.toDual 𝕜 (Lp 𝕜 2 μ)).symm (φ.comp ι)
  set h : α → 𝕜 := fun x => conj (u x)
  have hφ : ∀ (f : Lp 𝕜 1 μ) (f' : Lp 𝕜 2 μ), (f : α → 𝕜) =ᵐ[μ] f' →
      φ f = ∫ x, h x * f x ∂μ := fun f f' hf => by
    have hfι : f = ι f' := Lp.ext (hf.trans (hι f').symm)
    calc φ f = inner 𝕜 u f' := by
          rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, hfι]
      _ = ∫ x, h x * f x ∂μ := by
          rw [L2.inner_def]
          refine integral_congr_ae (hf.mono fun x hx => ?_)
          simp [h, hx, mul_comm]
  -- Testing against simple functions bounds `‖h‖_∞` by `‖φ‖`.
  have hmeas : AEStronglyMeasurable h μ :=
    RCLike.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)
  have hint : Integrable h μ := ((Lp.memLp u).integrable one_le_two).mono hmeas
    (ae_of_all _ fun x => (RCLike.norm_conj _).le)
  have hbound : eLpNorm h ∞ μ ≤ ‖φ‖ₑ :=
    hmeas.eLpNorm_top_le_of_forall_enorm_integral_mul_le (fun _ _ _ => hint.integrableOn)
      fun σ hσ => by
        have hσ₂ := σ.memLp_of_isFiniteMeasure 2 μ
        calc ‖∫ x, h x * σ x ∂μ‖ₑ = ‖φ (hσ.toLp σ)‖ₑ := by
              rw [hφ _ (hσ₂.toLp σ) (hσ.coeFn_toLp.trans hσ₂.coeFn_toLp.symm)]
              congr 1
              exact integral_congr_ae (by filter_upwards [hσ.coeFn_toLp] with x hx; rw [hx])
          _ ≤ ‖φ‖ₑ * ‖hσ.toLp σ‖ₑ := φ.le_opENorm _
          _ = ‖φ‖ₑ * eLpNorm σ 1 μ := by rw [Lp.enorm_def, eLpNorm_congr_ae hσ.coeFn_toLp]
  have hh : MemLp h ∞ μ := memLp_iff.2 (hbound.trans_lt enorm_lt_top)
  refine ⟨hh.toLp h, ContinuousLinearMap.ext fun f => ?_⟩
  -- Both functionals are continuous, and they agree on indicator functions.
  induction f using Lp.induction ENNReal.one_ne_top with
  | indicatorConst c hs hμs =>
    rw [toDualOne_apply, Lp.simpleFunc.coe_indicatorConst,
      hφ _ (indicatorConstLp 2 hs hμs.ne c)
        (indicatorConstLp_coeFn.trans indicatorConstLp_coeFn.symm)]
    exact integral_congr_ae (by filter_upwards [hh.coeFn_toLp] with x hx; rw [hx])
  | add _ _ _ hf hg => rw [map_add, map_add, hf, hg]
  | isClosed => exact isClosed_eq (ContinuousLinearMap.continuous _) φ.continuous

variable (𝕜 μ) in
/-- For a finite measure, the integral pairing `g ↦ (f ↦ ∫ g f dμ)` is an isometric equivalence
between `L^∞(μ)` and the continuous dual of `L¹(μ)`. -/
noncomputable def dualOneEquiv [IsFiniteMeasure μ] :
    Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ) :=
  LinearIsometryEquiv.ofSurjective (toDualOne 𝕜 μ) fun φ => exists_toDualOne_eq φ

@[simp]
theorem coe_dualOneEquiv [IsFiniteMeasure μ] : ⇑(dualOneEquiv 𝕜 μ) = toDualOne 𝕜 μ :=
  LinearIsometryEquiv.coe_ofSurjective _ _

/-- For a finite measure, a continuous linear functional on `L¹(μ)` is integration against its
density `(dualOneEquiv 𝕜 μ).symm φ ∈ L^∞(μ)`. -/
@[simp]
theorem integral_dualOneEquiv_symm_mul [IsFiniteMeasure μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ))
    (f : Lp 𝕜 1 μ) : ∫ x, (dualOneEquiv 𝕜 μ).symm φ x * f x ∂μ = φ f := by
  rw [← toDualOne_apply, ← coe_dualOneEquiv, LinearIsometryEquiv.apply_symm_apply]

/-- For a finite measure, the integral over a measurable set `s` of the density of a continuous
linear functional `φ` on `L¹(μ)` is the value of `φ` at the indicator function of `s`. -/
theorem setIntegral_dualOneEquiv_symm [IsFiniteMeasure μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ))
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (dualOneEquiv 𝕜 μ).symm φ x ∂μ =
      φ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : 𝕜)) := by
  rw [← integral_dualOneEquiv_symm_mul, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := measure_ne_top μ s)
    (c := (1 : 𝕜))] with x hx
  by_cases hxs : x ∈ s <;> simp [hx, hxs]

end MeasureTheory.Lp
