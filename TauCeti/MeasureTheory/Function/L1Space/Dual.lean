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
import TauCeti.MeasureTheory.Function.Lp.Exponent

/-!
# The dual of `L¹`

Let `𝕜` be `ℝ` or `ℂ` (or any `RCLike` field), and let `q` and `q'` be Hölder conjugate.
Integration against `g ∈ L^q(μ)` is a continuous linear functional `f ↦ ∫ g f dμ` on `L^q'(μ)`.
This is Mathlib's Hölder pairing `ContinuousLinearMap.lpPairing` for the multiplication of `𝕜`.
On a σ-finite measure space the functional has norm exactly `‖g‖_q`, so the pairing is a linear
isometry `L^q(μ) → L^q'(μ)*` (`MeasureTheory.Lp.toDual`, in
`TauCeti.MeasureTheory.Function.Lp.Duality`). For `q = ∞`, `q' = 1` and a σ-finite measure it is
onto: every continuous linear functional on `L¹(μ)` is integration against an essentially bounded
density. This gives the isometric equivalence `L^∞(μ) ≃ L¹(μ)*`
(`MeasureTheory.Lp.dualOneEquiv`). The integral of the density over a measurable set `s` of finite
measure is the value of the functional at the indicator function of `s`. Some hypothesis on `μ` is
needed: for the measure on a point that gives it infinite mass, `L¹(μ) = 0` while `L^∞(μ) = 𝕜`.

## Main declarations

* `MeasureTheory.Lp.exists_toDual_eq`: on a σ-finite measure space, every continuous linear
  functional on `L¹(μ)` is integration against some `g ∈ L^∞(μ)`.
* `MeasureTheory.Lp.dualOneEquiv`: the isometric equivalence `L^∞(μ) ≃ L¹(μ)*` of a σ-finite
  measure, which agrees with `MeasureTheory.Lp.toDual` (`MeasureTheory.Lp.coe_dualOneEquiv`).
* `MeasureTheory.Lp.integral_dualOneEquiv_symm_mul`: a functional on `L¹(μ)` is integration
  against its density.
* `MeasureTheory.Lp.setIntegral_dualOneEquiv_symm`: the integral of the density over a set of
  finite measure is the value of the functional at the indicator function of the set.

## Implementation notes

For a finite measure, the density of `φ ∈ L¹(μ)*` is found in `L²(μ)`. As `L²(μ)` maps continuously
into `L¹(μ)` (`MeasureTheory.Lp.ofExponentLEL`), `φ` restricts to a continuous linear functional on
`L²(μ)`. The Riesz representation theorem writes it as `f ↦ ∫ h f` for some `h ∈ L²(μ)`. Testing
against simple functions bounds `‖h‖_∞` by `‖φ‖`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le`), and density
of simple functions in `L¹(μ)` gives `φ f = ∫ h f` for every `f ∈ L¹(μ)`.

A σ-finite measure `μ` has a positive weight `w` with `∫ w dμ < ∞`
(`MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite`), and `ν = w μ` is a finite measure with
the same null sets as `μ`. Multiplication by `w` is a linear isometry from `L¹(ν)` onto `L¹(μ)`
(`MeasureTheory.withDensitySMulLI`), so `φ` pulls back to a functional on `L¹(ν)`. Its density
`g ∈ L^∞(ν) = L^∞(μ)` represents `φ`: for `f ∈ L¹(μ)`,
`φ f = ∫ g (f / w) dν = ∫ g f dμ`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 4.14.
* G. B. Folland, *Real Analysis*, second edition, Theorem 6.15.
-/

public section

open scoped ENNReal NNReal ComplexConjugate

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {μ : Measure α}

/-- For a finite measure, every continuous linear functional on `L¹(μ)` is integration against
an essentially bounded function. -/
private theorem exists_toDual_eq_of_isFiniteMeasure [IsFiniteMeasure μ]
    (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) :
    ∃ g : Lp 𝕜 ∞ μ, toDual 𝕜 μ ∞ 1 g = φ := by
  -- The Riesz representation `h` of `φ` restricted to `L²(μ)` represents `φ` on `L²(μ)`.
  set ι : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 1 μ := Lp.ofExponentLEL 𝕜 𝕜 one_le_two
  set u : Lp 𝕜 2 μ := (InnerProductSpace.toDual 𝕜 (Lp 𝕜 2 μ)).symm (φ.comp ι)
  set h : α → 𝕜 := fun x => conj (u x)
  have hφ : ∀ (f : Lp 𝕜 1 μ) (f' : Lp 𝕜 2 μ), (f : α → 𝕜) =ᵐ[μ] f' →
      φ f = ∫ x, h x * f x ∂μ := fun f f' hf => by
    have hfι : f = ι f' := Lp.ext (by simpa only [ι, Lp.coeFn_ofExponentLEL] using hf)
    calc φ f = inner 𝕜 u f' := by
          rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply, hfι]
      _ = ∫ x, h x * f x ∂μ := by
          rw [L2.inner_def]
          refine integral_congr_ae (hf.mono fun x hx => ?_)
          simp [h, hx, mul_comm]
  -- Testing against simple functions bounds `‖h‖_∞` by `‖φ‖`.
  have hint : Integrable h μ := (Lp.memLp u).star.integrable one_le_two
  have hbound : eLpNorm h ∞ μ ≤ ‖φ‖ₑ :=
    hint.aestronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le fun σ hσ =>
      have hσ₂ := σ.memLp_of_isFiniteMeasure 2 μ
      enorm_integral_mul_le_of_apply_eq φ hσ
        (hφ _ (hσ₂.toLp σ) (hσ.coeFn_toLp.trans hσ₂.coeFn_toLp.symm))
  have hh : MemLp h ∞ μ := memLp_iff.2 (hbound.trans_lt eNorm_lt_top)
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

/-- **The dual of `L¹`.** On a σ-finite measure space, every continuous linear functional on
`L¹(μ)` is integration against an essentially bounded function. -/
theorem exists_toDual_eq [SigmaFinite μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) :
    ∃ g : Lp 𝕜 ∞ μ, toDual 𝕜 μ ∞ 1 g = φ := by
  -- A positive weight `w` with finite integral makes `ν = w μ` a finite measure with the null sets
  -- of `μ`.
  obtain ⟨w, hw0, hwm, hwi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  set ν := μ.withDensity fun x ↦ (w x : ℝ≥0∞)
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity (hwi.trans ENNReal.one_lt_top).ne
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous' hwm.coe_nnreal_ennreal.aemeasurable
    (.of_forall fun x ↦ ENNReal.coe_ne_zero.2 (hw0 x).ne')
  -- Multiplication by `w` is a `𝕜`-linear isometry `T : L¹(ν) → L¹(μ)`.
  set T := withDensitySMulLI μ (E := 𝕜) hwm
  have hT (u : Lp 𝕜 1 ν) : (T u : α → 𝕜) =ᵐ[μ] fun x ↦ (w x : ℝ) • u x := by
    rw [withDensitySMulLI_apply]
    exact MemLp.coeFn_toLp _
  have hTsmul (c : 𝕜) (u : Lp 𝕜 1 ν) : T (c • u) = c • T u := by
    ext1
    filter_upwards [hT (c • u), hT u, Lp.coeFn_smul c (T u),
      hμν.ae_le (Lp.coeFn_smul c u)] with x h1 h2 h3 h4
    rw [h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply]
    exact smul_comm _ _ _
  -- The functional `ψ u = φ (T u)` on `L¹(ν)` has a density `g ∈ L^∞(ν)`.
  set T' : Lp 𝕜 1 ν →ₗ[𝕜] Lp 𝕜 1 μ := { toFun := T, map_add' := T.map_add, map_smul' := hTsmul }
  set ψ : StrongDual 𝕜 (Lp 𝕜 1 ν) := (φ.toLinearMap.comp T').mkContinuous ‖φ‖ fun u ↦
    (φ.le_opNorm (T u)).trans_eq (by rw [LinearIsometry.norm_map])
  obtain ⟨g, hg⟩ := exists_toDual_eq_of_isFiniteMeasure ψ
  have hgμ : MemLp g ∞ μ := by
    have hg_lt := Lp.eLpNorm_lt_top g
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable g)] at hg_lt
    rw [memLp_iff, eLpNorm_exponent_top ((Lp.aestronglyMeasurable g).mono_ac hμν)]
    exact (eLpNormEssSup_mono_measure _ hμν).trans_lt hg_lt
  refine ⟨hgμ.toLp g, ContinuousLinearMap.ext fun f ↦ ?_⟩
  -- Every `f ∈ L¹(μ)` is `T u` for `u = f / w ∈ L¹(ν)`.
  have hu : MemLp (fun x ↦ ((w x : ℝ)⁻¹ : ℝ) • f x) 1 ν := by
    refine memLp_one_iff_integrable.2 ((integrable_withDensity_iff_integrable_smul hwm).2 ?_)
    refine (memLp_one_iff_integrable.1 (Lp.memLp f)).congr (.of_forall fun x ↦ ?_)
    dsimp only
    rw [NNReal.smul_def, smul_smul, mul_inv_cancel₀ (NNReal.coe_ne_zero.2 (hw0 x).ne'), one_smul]
  have hTu : T (hu.toLp _) = f := by
    ext1
    filter_upwards [hT (hu.toLp _), hμν.ae_le hu.coeFn_toLp] with x h1 h2
    rw [h1, h2, smul_smul, mul_inv_cancel₀ (NNReal.coe_ne_zero.2 (hw0 x).ne'), one_smul]
  calc toDual 𝕜 μ ∞ 1 (hgμ.toLp g) f = ∫ x, (w x : ℝ) • (g x * hu.toLp _ x) ∂μ := by
        rw [toDual_apply]
        refine integral_congr_ae ?_
        filter_upwards [hgμ.coeFn_toLp, hμν.ae_le hu.coeFn_toLp] with x h1 h2
        rw [h1, h2, mul_smul_comm, smul_smul,
          mul_inv_cancel₀ (NNReal.coe_ne_zero.2 (hw0 x).ne'), one_smul]
    _ = ∫ x, g x * hu.toLp _ x ∂ν := (integral_withDensity_eq_integral_smul hwm _).symm
    _ = φ f := by
        rw [← toDual_apply, hg, LinearMap.mkContinuous_apply]
        exact congrArg φ hTu

variable (𝕜 μ) in
/-- On a σ-finite measure space, the integral pairing `g ↦ (f ↦ ∫ g f dμ)` is an isometric
equivalence between `L^∞(μ)` and the continuous dual of `L¹(μ)`. -/
noncomputable def dualOneEquiv [SigmaFinite μ] :
    Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ) :=
  LinearIsometryEquiv.ofSurjective (toDual 𝕜 μ ∞ 1) fun φ => exists_toDual_eq φ

@[simp]
theorem coe_dualOneEquiv [SigmaFinite μ] : ⇑(dualOneEquiv 𝕜 μ) = toDual 𝕜 μ ∞ 1 :=
  LinearIsometryEquiv.coe_ofSurjective _ _

@[simp]
theorem dualOneEquiv_symm_toDual [SigmaFinite μ] (g : Lp 𝕜 ∞ μ) :
    (dualOneEquiv 𝕜 μ).symm (toDual 𝕜 μ ∞ 1 g) = g := by
  rw [← coe_dualOneEquiv, LinearIsometryEquiv.symm_apply_apply]

@[simp]
theorem toDual_dualOneEquiv_symm [SigmaFinite μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) :
    toDual 𝕜 μ ∞ 1 ((dualOneEquiv 𝕜 μ).symm φ) = φ := by
  rw [← coe_dualOneEquiv, LinearIsometryEquiv.apply_symm_apply]

/-- On a σ-finite measure space, a continuous linear functional on `L¹(μ)` is integration against
its density `(dualOneEquiv 𝕜 μ).symm φ ∈ L^∞(μ)`. -/
@[simp]
theorem integral_dualOneEquiv_symm_mul [SigmaFinite μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ))
    (f : Lp 𝕜 1 μ) : ∫ x, (dualOneEquiv 𝕜 μ).symm φ x * f x ∂μ = φ f := by
  rw [← toDual_apply, toDual_dualOneEquiv_symm]

/-- On a σ-finite measure space, the integral over a measurable set `s` of finite measure of the
density of a continuous linear functional `φ` on `L¹(μ)` is the value of `φ` at the indicator
function of `s`. -/
@[simp]
theorem setIntegral_dualOneEquiv_symm [SigmaFinite μ] (φ : StrongDual 𝕜 (Lp 𝕜 1 μ))
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    ∫ x in s, (dualOneEquiv 𝕜 μ).symm φ x ∂μ = φ (indicatorConstLp 1 hs hμs (1 : 𝕜)) := by
  simpa using (toDual_indicatorConstLp (q' := 1) ((dualOneEquiv 𝕜 μ).symm φ) hs hμs (1 : 𝕜)).symm

end MeasureTheory.Lp
