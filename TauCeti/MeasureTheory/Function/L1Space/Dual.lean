/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.MeasureTheory.Function.Lp.Duality
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# The dual of `L¹`

Let `𝕜` be `ℝ` or `ℂ` (or any `RCLike` field), and let `q` and `q'` be Hölder conjugate.
Integration against `g ∈ L^q(μ)` is a continuous linear functional `f ↦ ∫ g f dμ` on `L^q'(μ)`.
This is Mathlib's Hölder pairing `ContinuousLinearMap.lpPairing` for the multiplication of `𝕜`.
On a σ-finite measure space the functional has norm exactly `‖g‖_q`, so the pairing is a linear
isometry `L^q(μ) → L^q'(μ)*` (`MeasureTheory.Lp.toDual`, in
`TauCeti.MeasureTheory.Function.Lp.Duality`). For `q = ∞`, `q' = 1` and a finite
measure it is onto: every continuous linear functional on `L¹(μ)` is integration against an
essentially bounded density. This gives the isometric equivalence `L^∞(μ) ≃ L¹(μ)*`
(`MeasureTheory.Lp.dualOneEquiv`). The integral of the density over a measurable set `s` is the
value of the functional at the indicator function of `s`.

## Main declarations

* `MeasureTheory.Lp.exists_toDual_eq`: for a finite measure, every continuous linear
  functional on `L¹(μ)` is integration against some `g ∈ L^∞(μ)`.
* `MeasureTheory.Lp.dualOneEquiv`: the isometric equivalence `L^∞(μ) ≃ L¹(μ)*` of a finite
  measure, which agrees with `MeasureTheory.Lp.toDual` (`MeasureTheory.Lp.coe_dualOneEquiv`).
* `MeasureTheory.Lp.integral_dualOneEquiv_symm_mul`: a functional on `L¹(μ)` is integration
  against its density.
* `MeasureTheory.Lp.setIntegral_dualOneEquiv_symm`: the integral of the density over a set is the
  value of the functional at the indicator function of the set.

## Implementation notes

The density of `φ ∈ L¹(μ)*` is found in `L²(μ)`. For a finite measure, `L²(μ)` maps continuously
into `L¹(μ)` (`MeasureTheory.Measure.LpToL1CLM`), so `φ` restricts to a continuous linear
functional on `L²(μ)`. The Riesz representation theorem writes it as `f ↦ ∫ h f` for some
`h ∈ L²(μ)`. Testing against simple functions bounds `‖h‖_∞` by `‖φ‖`
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

/-- For a finite measure, every continuous linear functional on `L¹(μ)` is integration against
an essentially bounded function. -/
theorem exists_toDual_eq [IsFiniteMeasure μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) :
    ∃ g : Lp 𝕜 ∞ μ, toDual 𝕜 μ ∞ 1 g = φ := by
  -- The Riesz representation `h` of `φ` restricted to `L²(μ)` represents `φ` on `L²(μ)`.
  set ι : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 1 μ := Measure.LpToL1CLM μ 2
  set u : Lp 𝕜 2 μ := (InnerProductSpace.toDual 𝕜 (Lp 𝕜 2 μ)).symm (φ.comp ι)
  set h : α → 𝕜 := fun x => conj (u x)
  have hφ : ∀ (f : Lp 𝕜 1 μ) (f' : Lp 𝕜 2 μ), (f : α → 𝕜) =ᵐ[μ] f' →
      φ f = ∫ x, h x * f x ∂μ := fun f f' hf => by
    have hfι : f = ι f' := Lp.ext (hf.trans (Measure.LpToL1CLM_coeFn μ 2 f').symm)
    calc φ f = inner 𝕜 u f' := by
          rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, hfι]
      _ = ∫ x, h x * f x ∂μ := by
          rw [L2.inner_def]
          refine integral_congr_ae (hf.mono fun x hx => ?_)
          simp [h, hx, mul_comm]
  -- Testing against simple functions bounds `‖h‖_∞` by `‖φ‖`.
  have hint : Integrable h μ := (Lp.memLp u).star.integrable one_le_two
  have hbound : eLpNorm h ∞ μ ≤ ‖φ‖ₑ :=
    hint.aestronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le
      (fun _ _ _ => hint.integrableOn) fun σ hσ =>
        have hσ₂ := σ.memLp_of_isFiniteMeasure 2 μ
        enorm_integral_mul_le_of_apply_eq φ hσ
          (hφ _ (hσ₂.toLp σ) (hσ.coeFn_toLp.trans hσ₂.coeFn_toLp.symm))
  have hh : MemLp h ∞ μ := memLp_iff.2 (hbound.trans_lt enorm_lt_top)
  refine ⟨hh.toLp h, ContinuousLinearMap.ext fun f => ?_⟩
  -- Both functionals are continuous, and they agree on indicator functions.
  induction f using Lp.induction ENNReal.one_ne_top with
  | indicatorConst c hs hμs =>
    rw [toDual_apply, Lp.simpleFunc.coe_indicatorConst,
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
  LinearIsometryEquiv.ofSurjective (toDual 𝕜 μ ∞ 1) fun φ => exists_toDual_eq φ

@[simp]
theorem coe_dualOneEquiv [IsFiniteMeasure μ] : ⇑(dualOneEquiv 𝕜 μ) = toDual 𝕜 μ ∞ 1 :=
  LinearIsometryEquiv.coe_ofSurjective _ _

@[simp]
theorem dualOneEquiv_symm_toDual [IsFiniteMeasure μ] (g : Lp 𝕜 ∞ μ) :
    (dualOneEquiv 𝕜 μ).symm (toDual 𝕜 μ ∞ 1 g) = g := by
  rw [← coe_dualOneEquiv, LinearIsometryEquiv.symm_apply_apply]

@[simp]
theorem toDual_dualOneEquiv_symm [IsFiniteMeasure μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) :
    toDual 𝕜 μ ∞ 1 ((dualOneEquiv 𝕜 μ).symm φ) = φ := by
  rw [← coe_dualOneEquiv, LinearIsometryEquiv.apply_symm_apply]

/-- For a finite measure, a continuous linear functional on `L¹(μ)` is integration against its
density `(dualOneEquiv 𝕜 μ).symm φ ∈ L^∞(μ)`. -/
@[simp]
theorem integral_dualOneEquiv_symm_mul [IsFiniteMeasure μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ))
    (f : Lp 𝕜 1 μ) : ∫ x, (dualOneEquiv 𝕜 μ).symm φ x * f x ∂μ = φ f := by
  rw [← toDual_apply, toDual_dualOneEquiv_symm]

/-- For a finite measure, the integral over a measurable set `s` of the density of a continuous
linear functional `φ` on `L¹(μ)` is the value of `φ` at the indicator function of `s`. -/
@[simp]
theorem setIntegral_dualOneEquiv_symm [IsFiniteMeasure μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ))
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (dualOneEquiv 𝕜 μ).symm φ x ∂μ =
      φ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : 𝕜)) := by
  simpa using (toDual_indicatorConstLp (q' := 1) ((dualOneEquiv 𝕜 μ).symm φ) hs
    (measure_ne_top μ s) (1 : 𝕜)).symm

end MeasureTheory.Lp
