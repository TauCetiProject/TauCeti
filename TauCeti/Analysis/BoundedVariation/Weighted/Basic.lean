/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence

/-!
# Weighted variation and weighted perimeter

Let `E` be a finite-dimensional real inner product space and `W : E → ℝ` a weight, normally of
class `C¹`, with measure `μ = e^{−W} · volume`. The weighted divergence of a vector field `X` is
`div_μ X = div X − ⟨∇W, X⟩`, written here with the derivative `DW(x)(X x) = ⟨∇W(x), X x⟩`, so
that `div (e^{−W} X) = e^{−W} div_μ X` (`TauCeti.trace_fderiv_exp_neg_smul`, in
`TauCeti.Analysis.Distribution.TestFunction.Divergence`).

The **weighted variation** of `u : E → ℝ` on an open set `Ω` is the extended supremum

`V_μ(u; Ω) = ⨆ { ∫ (div X − DW X) e^{−W} u dx | X ∈ 𝓓(Ω, E), ‖X x‖ ≤ 1 for all x }`

(`TauCeti.weightedVariation`), and the **weighted perimeter** of a set is the weighted variation
of its indicator (`TauCeti.weightedPerimeter`). For the Gaussian weight
`W(x) = ‖x‖²/2 + (n/2) log 2π` (`TauCeti.gaussianWeight`), whose measure is the standard Gaussian
measure, the weighted perimeter in the whole space is the **Gaussian perimeter**
(`TauCeti.gaussianPerimeter`); a half-space at distance `s` from the origin has Gaussian perimeter
`φ(s)` for the standard normal density `φ`.

Since `div (e^{−W} X) = e^{−W} div_μ X`, the weighted variation is also the supremum of `∫ u div Y`
over vector fields `Y` with compact support in `Ω` and `‖Y‖ ≤ e^{−W}`, smooth or only `C¹` (the
**density-bounded form**). Comparing these fields with the unit-bounded fields of the Euclidean
variation `|Du|(Ω) = TauCeti.totalVariationOn volume Ω u` gives `m |Du|(Ω) ≤ V_μ(u; Ω) ≤ M |Du|(Ω)`
whenever `m ≤ e^{−W} ≤ M` on `Ω`. As `e^{−W}` is bounded below by a positive constant on every
compact set, a function of finite weighted variation has locally finite Euclidean variation.

The weighted divergence matters: the supremum of `∫_U div X dμ`, which is Tau Ceti's
`TauCeti.perimeter μ Ω U` with the measure `μ` in place of `volume`, is not complement invariant
and assigns positive perimeter to the whole space for the Gaussian measure. The weighted
perimeter has neither defect (`TauCeti.weightedPerimeter_compl`,
`TauCeti.weightedPerimeter_univ`).

## Main declarations

* `TauCeti.weightedVariation W Ω u`, `TauCeti.weightedPerimeter W Ω U`: the weighted variation
  and perimeter.
* `TauCeti.gaussianWeight E`, `TauCeti.gaussianPerimeter U`: the Gaussian weight and the
  Gaussian perimeter.
* `LinearIsometryEquiv.gaussianWeight_apply`, `LinearIsometryEquiv.gaussianWeight_comp`: the
  Gaussian weight is invariant under linear isometry equivalences.
* `TauCeti.weightedVariation_eq_iSup_trace_fderiv`: for a differentiable weight, the weighted
  variation pairs `u` with the divergences of the fields `e^{−W} X`.
* `TauCeti.integral_divergenceCLM_sub_fderiv_mul_exp_neg_eq_zero`: for a `C¹` weight, the weighted
  divergence of a test vector field has `μ`-integral zero.
* `TauCeti.ofReal_integral_le_weightedVariation_of_contDiff`: `C¹` vector fields with compact
  support in `Ω` and norm at most `1` bound the weighted variation from below.
* `TauCeti.weightedVariation_eq_iSup_norm_le_exp_neg` and
  `TauCeti.weightedVariation_eq_iSup_contDiff_norm_le_exp_neg`: the density-bounded form, over
  test vector fields and over `C¹` vector fields bounded by `e^{−W}`.
* `TauCeti.weightedVariation_le_mul_totalVariationOn` and
  `TauCeti.mul_totalVariationOn_le_weightedVariation`: comparison with the Euclidean variation
  under bounds `m ≤ e^{−W} ≤ M` on `Ω`.
* `TauCeti.exists_mul_totalVariationOn_le_weightedVariation`: every compact subset of `Ω` has an
  open neighbourhood `U` and a constant `m > 0` with `m |Du|(U) ≤ V_μ(u; Ω)` for all `u`.
* `TauCeti.exists_totalVariationOn_ne_top_of_weightedVariation_ne_top`: a function of finite
  weighted variation on `Ω` has locally finite Euclidean variation on `Ω`.
* `TauCeti.weightedVariation_congr_ae`, `TauCeti.weightedVariation_mono`,
  `TauCeti.weightedVariation_smul` and `TauCeti.weightedVariation_add_le`: locality,
  monotonicity in the open set, absolute homogeneity and subadditivity.
* `TauCeti.weightedVariation_add_const`, `TauCeti.weightedPerimeter_compl`,
  `TauCeti.weightedPerimeter_empty` and `TauCeti.weightedPerimeter_univ`: for a `C¹` weight,
  constants have no variation and complements have the same perimeter.
* `TauCeti.weightedVariation_weight_add_const`: adding a constant `c` to the weight multiplies the
  weighted variation by `e^{−c}`.
* `TauCeti.weightedVariation_zero_weight` and `TauCeti.weightedPerimeter_zero_weight`: the weight
  `0` gives the Euclidean variation `TauCeti.totalVariationOn volume Ω u` and perimeter
  `TauCeti.perimeter volume Ω U`.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), Section 3.
* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. (2011), equation (2.5).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace TestFunction Set
open scoped ENNReal NNReal Distributions Topology

section GaussianWeight

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **Gaussian weight** `W(x) = ‖x‖²/2 + (n/2) log 2π` with `n = dim E`, so that `e^{−W}` is
the density `(2π)^{−n/2} e^{−‖x‖²/2}` of the standard Gaussian measure against `volume`
(`TauCeti.Probability.stdGaussian_eq_withDensity_norm`). -/
def gaussianWeight (x : E) : ℝ :=
  ‖x‖ ^ 2 / 2 + (Module.finrank ℝ E : ℝ) / 2 * Real.log (2 * Real.pi)

variable {E}

/-- The value of the Gaussian weight. -/
theorem gaussianWeight_def (x : E) :
    gaussianWeight E x = ‖x‖ ^ 2 / 2 + (Module.finrank ℝ E : ℝ) / 2 * Real.log (2 * Real.pi) :=
  (rfl)

/-- The Gaussian weight is smooth. -/
theorem contDiff_gaussianWeight {n : WithTop ℕ∞} : ContDiff ℝ n (gaussianWeight E) := by
  have h : gaussianWeight E = fun x =>
      ‖x‖ ^ 2 / 2 + (Module.finrank ℝ E : ℝ) / 2 * Real.log (2 * Real.pi) :=
    funext gaussianWeight_def
  rw [h]
  exact ((contDiff_norm_sq ℝ).div_const _).add contDiff_const

/-- The Gaussian weight is invariant under linear isometry equivalences:
`W_{E'}(e x) = W_E(x)`. -/
@[simp]
theorem _root_.LinearIsometryEquiv.gaussianWeight_apply {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] (e : E ≃ₗᵢ[ℝ] E') (x : E) :
    gaussianWeight E' (e x) = gaussianWeight E x := by
  simp [gaussianWeight_def, e.toLinearEquiv.finrank_eq]

/-- The Gaussian weight is invariant under linear isometry equivalences, in composed form. -/
@[simp]
theorem _root_.LinearIsometryEquiv.gaussianWeight_comp {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] (e : E ≃ₗᵢ[ℝ] E') : gaussianWeight E' ∘ e = gaussianWeight E :=
  funext e.gaussianWeight_apply

end GaussianWeight

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω Ω' : Opens E} {u v : E → ℝ} {s : Set E}

/-- The **weighted variation** `V_μ(u; Ω)` of `u` on the open set `Ω` for the density `e^{−W}`:
the extended supremum of `∫ (div X − DW X) e^{−W} u dx` over test vector fields `X ∈ 𝓓(Ω, E)`
with `‖X x‖ ≤ 1` everywhere. Here `div X − DW X` is the weighted divergence
`div X − ⟨∇W, X⟩`, so the integral is `∫ u div_μ X dμ` for `μ = e^{−W} · volume`. For the
weight `0` it is `TauCeti.totalVariationOn volume Ω u` (`TauCeti.weightedVariation_zero_weight`).
It is meaningful for a `C¹` weight and `u` locally integrable on `Ω`; otherwise the integrals may
be Mathlib's junk value `0`. -/
def weightedVariation (W : E → ℝ) (Ω : Opens E) (u : E → ℝ) : ℝ≥0∞ :=
  ⨆ (X : 𝓓(Ω, E)) (_ : ∀ x, ‖X x‖ ≤ 1),
    ENNReal.ofReal (∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x)

/-- The defining supremum of `TauCeti.weightedVariation`. -/
theorem weightedVariation_def : weightedVariation W Ω u =
    ⨆ (X : 𝓓(Ω, E)) (_ : ∀ x, ‖X x‖ ≤ 1),
      ENNReal.ofReal (∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x) :=
  (rfl)

/-- The **weighted perimeter** `P_μ(U; Ω)` of `U` in the open set `Ω` for the density `e^{−W}`:
the weighted variation of its indicator. It is meaningful for a `C¹` weight and `U ∩ Ω`
null-measurable. -/
def weightedPerimeter (W : E → ℝ) (Ω : Opens E) (U : Set E) : ℝ≥0∞ :=
  weightedVariation W Ω (U.indicator 1)

/-- The weighted perimeter is the weighted variation of the indicator. -/
theorem weightedPerimeter_def : weightedPerimeter W Ω s = weightedVariation W Ω (s.indicator 1) :=
  (rfl)

/-- The **Gaussian perimeter** `P_γ(U)` of `U`: its weighted perimeter in the whole space for the
Gaussian weight, whose measure is the standard Gaussian measure. A half-space at distance `s`
from the origin has Gaussian perimeter `φ(s)` for the standard normal density `φ`. -/
def gaussianPerimeter (U : Set E) : ℝ≥0∞ :=
  weightedPerimeter (gaussianWeight E) ⊤ U

/-- The Gaussian perimeter is the weighted perimeter in the whole space for the Gaussian
weight. -/
theorem gaussianPerimeter_def : gaussianPerimeter s = weightedPerimeter (gaussianWeight E) ⊤ s :=
  (rfl)

/-! ### Admissible fields -/

/-- An admissible test vector field bounds the weighted variation from below. -/
theorem ofReal_integral_le_weightedVariation (X : 𝓓(Ω, E)) (hX : ∀ x, ‖X x‖ ≤ 1) :
    ENNReal.ofReal (∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x) ≤
      weightedVariation W Ω u :=
  le_iSup₂ (f := fun (X : 𝓓(Ω, E)) (_ : ∀ x, ‖X x‖ ≤ 1) => ENNReal.ofReal
    (∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x)) X hX

/-- Upper bounds for the weighted variation are tested on admissible test vector fields. -/
theorem weightedVariation_le_iff {c : ℝ≥0∞} : weightedVariation W Ω u ≤ c ↔
    ∀ X : 𝓓(Ω, E), (∀ x, ‖X x‖ ≤ 1) →
      ENNReal.ofReal (∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x) ≤
        c :=
  iSup₂_le_iff

/-- **The divergence form.** For a differentiable weight, the weighted variation pairs `u` with the
divergences `div (e^{−W} X)` of the fields `e^{−W} X`, `X ∈ 𝓓(Ω, E)` with `‖X‖ ≤ 1`. -/
theorem weightedVariation_eq_iSup_trace_fderiv (hW : Differentiable ℝ W) :
    weightedVariation W Ω u = ⨆ (X : 𝓓(Ω, E)) (_ : ∀ x, ‖X x‖ ≤ 1), ENNReal.ofReal
      (∫ x, LinearMap.trace ℝ E
        (fderiv ℝ (fun y => Real.exp (-W y) • X y) x : E →ₗ[ℝ] E) * u x) := by
  refine iSup_congr fun X => iSup_congr fun _ => congrArg ENNReal.ofReal ?_
  congr 1 with x
  rw [trace_fderiv_exp_neg_smul (hW x) ((X.contDiff.differentiable (by simp)) x),
    divergenceCLM_apply]

/-! ### The weighted divergence of a test vector field -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The weighted divergence of a test vector field vanishes off its support. -/
private theorem weightedDivergence_eq_zero (X : 𝓓(Ω, E)) {x : E} (hx : x ∉ tsupport X) :
    (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) = 0 := by
  rw [divergenceCLM_apply, fderiv_of_notMem_tsupport ℝ hx, image_eq_zero_of_notMem_tsupport hx]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- For a `C¹` weight, the weighted divergence of a test vector field is continuous. -/
private theorem continuous_weightedDivergence (hW : ContDiff ℝ 1 W) (X : 𝓓(Ω, E)) :
    Continuous fun x => (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) :=
  ((divergenceCLM X).continuous.sub ((hW.continuous_fderiv one_ne_zero).clm_apply
    X.continuous)).mul hW.continuous.neg.rexp

/-- For a `C¹` weight and `u` locally integrable on `Ω`, the weighted pairing of `u` with a test
vector field on `Ω` is integrable. -/
theorem integrable_weightedDivergence_mul (hW : ContDiff ℝ 1 W)
    (hu : LocallyIntegrableOn u Ω) (X : 𝓓(Ω, E)) :
    Integrable fun x => (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x := by
  have hK : IsCompact (tsupport X) := X.hasCompactSupport
  refine (integrableOn_iff_integrable_of_support_subset fun x hx => ?_).1
    (IntegrableOn.continuousOn_mul (continuous_weightedDivergence hW X).continuousOn
      (hu.integrableOn_compact_subset X.tsupport_subset hK) hK)
  by_contra hxs
  apply hx
  rw [weightedDivergence_eq_zero X hxs, zero_mul]

/-- **The weighted divergence theorem.** For a `C¹` weight, `∫ div_μ X dμ = 0` for every test
vector field `X`: the integral of `(div X − DW X) e^{−W}` vanishes. -/
theorem integral_divergenceCLM_sub_fderiv_mul_exp_neg_eq_zero (hW : ContDiff ℝ 1 W)
    (X : 𝓓(Ω, E)) :
    ∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) = 0 := by
  have hY : ContDiff ℝ 1 fun y => Real.exp (-W y) • X y :=
    hW.neg.exp.smul (X.contDiff.of_le (by simp))
  have hYc : HasCompactSupport fun y => Real.exp (-W y) • X y := X.hasCompactSupport.smul_left
  have hint : Integrable (fderiv ℝ fun y => Real.exp (-W y) • X y) :=
    (hY.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hYc.fderiv (𝕜 := ℝ))
  calc ∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x)
      = ∫ x, traceCLM ℝ E (fderiv ℝ (fun y => Real.exp (-W y) • X y) x) := by
        congr 1 with x
        rw [traceCLM_apply, trace_fderiv_exp_neg_smul (hW.differentiable one_ne_zero x)
          ((X.contDiff.differentiable (by simp)) x), divergenceCLM_apply]
    _ = traceCLM ℝ E (∫ x, fderiv ℝ (fun y => Real.exp (-W y) • X y) x) :=
        (traceCLM ℝ E).integral_comp_comm hint
    _ = 0 := by rw [integral_fderiv_eq_zero_of_hasCompactSupport hY hYc, map_zero]

/-! ### Density-bounded fields -/

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- For a `C¹` weight, the density `e^{−W}` is `C¹`. -/
private theorem contDiff_exp_neg (hW : ContDiff ℝ 1 W) : ContDiff ℝ 1 fun x => Real.exp (-W x) :=
  by fun_prop

/-- For a `C¹` weight, a `C¹` vector field `X` with compact support in `Ω` and `‖X x‖ ≤ 1`
everywhere bounds the weighted variation from below, as the test vector fields of its definition
do (`TauCeti.ofReal_integral_le_weightedVariation`). -/
theorem ofReal_integral_le_weightedVariation_of_contDiff (hW : ContDiff ℝ 1 W)
    (hu : LocallyIntegrableOn u Ω) {X : E → E} (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X)
    (hXΩ : tsupport X ⊆ Ω) (hX1 : ∀ x, ‖X x‖ ≤ 1) :
    ENNReal.ofReal (∫ x, (LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E) - fderiv ℝ W x (X x)) *
      Real.exp (-W x) * u x) ≤ weightedVariation W Ω u := by
  have hWd := hW.differentiable one_ne_zero
  have hdiv {Y : E → E} (hY : ContDiff ℝ 1 Y) (x : E) :
      LinearMap.trace ℝ E (fderiv ℝ (fun y => Real.exp (-W y) • Y y) x : E →ₗ[ℝ] E) =
        (LinearMap.trace ℝ E (fderiv ℝ Y x : E →ₗ[ℝ] E) - fderiv ℝ W x (Y x)) *
          Real.exp (-W x) :=
    trace_fderiv_exp_neg_smul (hWd x) (hY.differentiable one_ne_zero x)
  have key := ofReal_integral_trace_fderiv_fun_smul_mul_le_iSup hu (contDiff_exp_neg hW)
    continuousOn_const (fun _ _ => one_pos) hX hXc hXΩ hX1
  simp_rw [hdiv hX] at key
  refine key.trans (iSup₂_le fun φ hφ => ?_)
  simp_rw [hdiv (φ.contDiff.of_le (by simp)), ← divergenceCLM_apply]
  exact ofReal_integral_le_weightedVariation φ hφ

/-- **Density-bounded fields.** For a `C¹` weight, a `C¹` vector field `Y` with compact support in
`Ω` and `‖Y x‖ ≤ e^{−W(x)}` everywhere bounds the weighted variation from below:
`∫ div Y * u ≤ V_μ(u; Ω)`, where `div Y = tr (DY)`. -/
theorem ofReal_integral_trace_fderiv_mul_le_weightedVariation (hW : ContDiff ℝ 1 W)
    (hu : LocallyIntegrableOn u Ω) {Y : E → E} (hY : ContDiff ℝ 1 Y) (hYc : HasCompactSupport Y)
    (hYΩ : tsupport Y ⊆ Ω) (hYW : ∀ x, ‖Y x‖ ≤ Real.exp (-W x)) :
    ENNReal.ofReal (∫ x, LinearMap.trace ℝ E (fderiv ℝ Y x : E →ₗ[ℝ] E) * u x) ≤
      weightedVariation W Ω u := by
  -- `Y = e^{−W} X` for the `C¹` field `X = e^{W} Y` of norm at most `1`.
  have hX : ContDiff ℝ 1 fun y => Real.exp (W y) • Y y := hW.exp.fun_smul hY
  have hYX : (fun y => Real.exp (-W y) • Real.exp (W y) • Y y) = Y := funext fun y => by
    rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  have hX1 (x : E) : ‖Real.exp (W x) • Y x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, ← le_div_iff₀' (Real.exp_pos _),
      one_div, ← Real.exp_neg]
    exact hYW x
  refine le_of_eq_of_le ?_ (ofReal_integral_le_weightedVariation_of_contDiff hW hu hX
    hYc.smul_left ((tsupport_smul_subset_right _ _).trans hYΩ) hX1)
  congr 2 with x
  rw [← trace_fderiv_exp_neg_smul ((hW.differentiable one_ne_zero) x)
    (hX.differentiable one_ne_zero x), hYX]

/-- **The density-bounded form.** For a `C¹` weight and `u` locally integrable on `Ω`, the
weighted variation is the supremum of `∫ div Y * u` over test vector fields `Y ∈ 𝓓(Ω, E)` with
`‖Y x‖ ≤ e^{−W(x)}` everywhere. -/
theorem weightedVariation_eq_iSup_norm_le_exp_neg (hW : ContDiff ℝ 1 W)
    (hu : LocallyIntegrableOn u Ω) :
    weightedVariation W Ω u = ⨆ (Y : 𝓓(Ω, E)) (_ : ∀ x, ‖Y x‖ ≤ Real.exp (-W x)),
      ENNReal.ofReal (∫ x, divergenceCLM Y x * u x) := by
  refine le_antisymm ?_ (iSup₂_le fun Y hY => ?_)
  · rw [weightedVariation_eq_iSup_trace_fderiv (hW.differentiable one_ne_zero)]
    refine iSup₂_le fun X hX => ?_
    -- The field `e^{−W} X` is only `C¹`; approximate it by test fields bounded by `e^{−W}`.
    have key := ofReal_integral_trace_fderiv_fun_smul_mul_le_iSup (g := fun _ => 1) hu
      contDiff_const (contDiff_exp_neg hW).continuous.continuousOn (fun _ _ => Real.exp_pos _)
      ((contDiff_exp_neg hW).fun_smul (X.contDiff.of_le (by simp))) X.hasCompactSupport.smul_left
      ((tsupport_smul_subset_right _ _).trans X.tsupport_subset) fun x => by
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (hX x)
    simp only [one_smul] at key
    simpa only [divergenceCLM_apply] using key
  · simp_rw [divergenceCLM_apply]
    exact ofReal_integral_trace_fderiv_mul_le_weightedVariation hW hu
      (Y.contDiff.of_le (by simp)) Y.hasCompactSupport Y.tsupport_subset hY

/-- **The density-bounded form over `C¹` fields.** For a `C¹` weight and `u` locally integrable
on `Ω`, the weighted variation is the supremum of `∫ div Y * u` over `C¹` vector fields `Y` with
compact support in `Ω` and `‖Y x‖ ≤ e^{−W(x)}` everywhere, where `div Y = tr (DY)`. -/
theorem weightedVariation_eq_iSup_contDiff_norm_le_exp_neg (hW : ContDiff ℝ 1 W)
    (hu : LocallyIntegrableOn u Ω) :
    weightedVariation W Ω u = ⨆ (Y : E → E) (_ : ContDiff ℝ 1 Y) (_ : HasCompactSupport Y)
      (_ : tsupport Y ⊆ Ω) (_ : ∀ x, ‖Y x‖ ≤ Real.exp (-W x)),
      ENNReal.ofReal (∫ x, LinearMap.trace ℝ E (fderiv ℝ Y x : E →ₗ[ℝ] E) * u x) := by
  refine le_antisymm ?_ (iSup_le fun Y => iSup_le fun hY => iSup_le fun hYc => iSup_le
    fun hYΩ => iSup_le fun hYW =>
      ofReal_integral_trace_fderiv_mul_le_weightedVariation hW hu hY hYc hYΩ hYW)
  rw [weightedVariation_eq_iSup_norm_le_exp_neg hW hu]
  refine iSup₂_le fun Y hY => ?_
  simp_rw [divergenceCLM_apply]
  exact le_iSup_of_le (Y : E → E) <| le_iSup_of_le (Y.contDiff.of_le (by simp)) <|
    le_iSup_of_le Y.hasCompactSupport <| le_iSup_of_le Y.tsupport_subset <| le_iSup_of_le hY le_rfl

/-! ### Elementary laws -/

/-- The weighted variation of the zero function vanishes. -/
@[simp]
theorem weightedVariation_zero : weightedVariation W Ω 0 = 0 := by
  simp [weightedVariation_def]

/-- The empty set has weighted perimeter zero. -/
@[simp]
theorem weightedPerimeter_empty : weightedPerimeter W Ω ∅ = 0 := by
  rw [weightedPerimeter_def, indicator_empty]
  exact weightedVariation_zero

/-- **Locality.** The weighted variation on `Ω` only depends on `u` almost everywhere on `Ω`. -/
theorem weightedVariation_congr_ae (h : u =ᵐ[volume.restrict Ω] v) :
    weightedVariation W Ω u = weightedVariation W Ω v := by
  refine iSup_congr fun X => iSup_congr fun _ => congrArg ENNReal.ofReal ?_
  have hΩ (w : E → ℝ) :
      ∫ x in (Ω : Set E), (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * w x =
        ∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * w x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [weightedDivergence_eq_zero X fun hmem => hx (X.tsupport_subset hmem), zero_mul]
  rw [← hΩ, ← hΩ]
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- **Locality.** Modifying a set by a null set inside `Ω` does not change its weighted perimeter
in `Ω`. -/
theorem weightedPerimeter_congr_ae {t : Set E} (h : s =ᵐ[volume.restrict Ω] t) :
    weightedPerimeter W Ω s = weightedPerimeter W Ω t :=
  weightedVariation_congr_ae (indicator_ae_eq_of_ae_eq_set h)

/-- **Monotonicity in the open set.** A test vector field on a smaller open set is one on the
larger set, so the weighted variation grows with the open set. -/
theorem weightedVariation_mono (h : Ω' ≤ Ω) :
    weightedVariation W Ω' u ≤ weightedVariation W Ω u := by
  refine weightedVariation_le_iff.2 fun X hX => ?_
  let X' : 𝓓(Ω, E) := ⟨X, X.contDiff, X.hasCompactSupport, X.tsupport_subset.trans h⟩
  have hX' (x : E) : divergenceCLM X' x = divergenceCLM X x := by simp [X']
  have hcoe : (X' : E → E) = X := rfl
  simpa only [hX', hcoe] using ofReal_integral_le_weightedVariation (W := W) (u := u) X' hX

/-- The weighted perimeter grows with the open set. -/
theorem weightedPerimeter_mono (h : Ω' ≤ Ω) :
    weightedPerimeter W Ω' s ≤ weightedPerimeter W Ω s :=
  weightedVariation_mono h

/-- The weighted variation of `-u` is that of `u`. -/
@[simp]
theorem weightedVariation_neg : weightedVariation W Ω (-u) = weightedVariation W Ω u := by
  have key : ∀ w : E → ℝ, weightedVariation W Ω (-w) ≤ weightedVariation W Ω w := fun w =>
    weightedVariation_le_iff.2 fun X hX => by
      have : ∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * (-w) x =
          ∫ x, (divergenceCLM (-X) x - fderiv ℝ W x ((-X) x)) * Real.exp (-W x) * w x := by
        congr 1 with x
        simp only [Pi.neg_apply, map_neg, FunLike.coe_neg]
        ring
      rw [this]
      exact ofReal_integral_le_weightedVariation (-X) fun x => by simpa using hX x
  exact le_antisymm (key u) (by simpa using key (-u))

/-- The weighted variation is positively homogeneous: `V_μ(c u; Ω) = c V_μ(u; Ω)` for `c ≥ 0`. -/
theorem weightedVariation_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) :
    weightedVariation W Ω (c • u) = ENNReal.ofReal c * weightedVariation W Ω u := by
  simp_rw [weightedVariation_def, ENNReal.mul_iSup]
  refine iSup_congr fun X => iSup_congr fun _ => ?_
  rw [← ENNReal.ofReal_mul hc, ← integral_const_mul]
  congr 2 with x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The weighted variation is absolutely homogeneous: `V_μ(c u; Ω) = |c| V_μ(u; Ω)`. -/
theorem weightedVariation_smul (c : ℝ) :
    weightedVariation W Ω (c • u) = ‖c‖ₑ * weightedVariation W Ω u := by
  rw [Real.eNorm_eq_ofReal_abs]
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc, weightedVariation_smul_of_nonneg hc]
  · rw [abs_of_nonpos hc, ← weightedVariation_smul_of_nonneg (neg_nonneg.2 hc), neg_smul,
      weightedVariation_neg]

/-- **Subadditivity.** For a `C¹` weight and `u` locally integrable on `Ω`,
`V_μ(u + v; Ω) ≤ V_μ(u; Ω) + V_μ(v; Ω)`. No integrability of `v` is needed. -/
theorem weightedVariation_add_le (hW : ContDiff ℝ 1 W) (hu : LocallyIntegrableOn u Ω) :
    weightedVariation W Ω (u + v) ≤ weightedVariation W Ω u + weightedVariation W Ω v := by
  refine weightedVariation_le_iff.2 fun X hX => ?_
  have hiu := integrable_weightedDivergence_mul hW hu X
  by_cases hiv : Integrable fun x =>
      (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * v x
  · have hsplit :
        ∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * (u + v) x =
          (∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x) +
            ∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * v x := by
      rw [← integral_add hiu hiv]
      simp only [Pi.add_apply, mul_add]
    rw [hsplit]
    exact ENNReal.ofReal_add_le.trans (add_le_add (ofReal_integral_le_weightedVariation X hX)
      (ofReal_integral_le_weightedVariation X hX))
  · rw [integral_undef fun h => hiv ((h.sub hiu).congr (.of_forall fun x => by simp [mul_add]))]
    simp

/-- For a `C¹` weight, adding a constant does not change the weighted variation. No
integrability of `u` is needed. -/
@[simp]
theorem weightedVariation_add_const (hW : ContDiff ℝ 1 W) (c : ℝ) :
    weightedVariation W Ω (fun x => u x + c) = weightedVariation W Ω u := by
  refine iSup_congr fun X => iSup_congr fun _ => congrArg ENNReal.ofReal ?_
  have hc : Integrable fun x =>
      (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * c :=
    (integrable_weightedDivergence_mul hW (locallyIntegrableOn_const c) X)
  have hc0 : ∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * c = 0 := by
    rw [integral_mul_const, integral_divergenceCLM_sub_fderiv_mul_exp_neg_eq_zero hW, zero_mul]
  simp_rw [mul_add]
  by_cases hu : Integrable fun x =>
      (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x
  · rw [integral_add hu hc, hc0, add_zero]
  · rw [integral_undef hu, integral_undef fun h => hu <| by
      simpa only [Pi.sub_def, add_sub_cancel_right] using h.sub hc]

/-- For a `C¹` weight, `V_μ(c − u; Ω) = V_μ(u; Ω)`. -/
theorem weightedVariation_const_sub (hW : ContDiff ℝ 1 W) (c : ℝ) :
    weightedVariation W Ω (fun x => c - u x) = weightedVariation W Ω u := by
  rw [← weightedVariation_neg (u := u), ← weightedVariation_add_const (u := -u) hW c]
  simp only [Pi.neg_apply, neg_add_eq_sub]

/-- For a `C¹` weight, a constant function has weighted variation zero. -/
@[simp]
theorem weightedVariation_const (hW : ContDiff ℝ 1 W) (c : ℝ) :
    weightedVariation W Ω (fun _ => c) = 0 := by
  simpa using weightedVariation_add_const (Ω := Ω) (u := 0) hW c

/-- For a `C¹` weight, a set and its complement have the same weighted perimeter. -/
@[simp]
theorem weightedPerimeter_compl (hW : ContDiff ℝ 1 W) :
    weightedPerimeter W Ω sᶜ = weightedPerimeter W Ω s := by
  rw [weightedPerimeter_def, weightedPerimeter_def, indicator_compl]
  exact weightedVariation_const_sub hW 1

/-- For a `C¹` weight, the whole space has weighted perimeter zero. -/
@[simp]
theorem weightedPerimeter_univ (hW : ContDiff ℝ 1 W) : weightedPerimeter W Ω univ = 0 := by
  rw [← compl_empty, weightedPerimeter_compl hW, weightedPerimeter_empty]

/-! ### Changing the weight -/

/-- Adding a constant `c` to the weight multiplies the weighted variation by `e^{−c}`. -/
theorem weightedVariation_weight_add_const (c : ℝ) :
    weightedVariation (fun x => W x + c) Ω u =
      ENNReal.ofReal (Real.exp (-c)) * weightedVariation W Ω u := by
  simp_rw [weightedVariation_def, ENNReal.mul_iSup]
  refine iSup_congr fun X => iSup_congr fun _ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← integral_const_mul]
  congr 2 with x
  rw [fderiv_add_const, neg_add, Real.exp_add]
  ring

/-- Adding a constant `c` to the weight multiplies the weighted perimeter by `e^{−c}`. -/
theorem weightedPerimeter_weight_add_const (c : ℝ) :
    weightedPerimeter (fun x => W x + c) Ω s =
      ENNReal.ofReal (Real.exp (-c)) * weightedPerimeter W Ω s :=
  weightedVariation_weight_add_const c

/-- The weight `0`, whose measure is `volume`, gives the Euclidean variation. -/
theorem weightedVariation_zero_weight :
    weightedVariation 0 Ω u = totalVariationOn volume Ω u := by
  rw [weightedVariation_def, totalVariationOn_def]
  refine iSup_congr fun X => iSup_congr fun _ => congrArg ENNReal.ofReal ?_
  simp

/-- The weight `0`, whose measure is `volume`, gives the Euclidean perimeter. -/
theorem weightedPerimeter_zero_weight :
    weightedPerimeter 0 Ω s = perimeter volume Ω s := by
  rw [weightedPerimeter_def, perimeter_def, weightedVariation_zero_weight]

/-! ### Comparison with the Euclidean variation -/

/-- A nonnegative scalar factor of a test vector field comes out of its divergence pairing. -/
private theorem ofReal_integral_divergenceCLM_smul_mul (c : ℝ≥0) (Y : 𝓓(Ω, E)) :
    ENNReal.ofReal (∫ x, divergenceCLM ((c : ℝ) • Y) x * u x) =
      c * ENNReal.ofReal (∫ x, divergenceCLM Y x * u x) := by
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg, ← integral_const_mul]
  congr 2 with x
  rw [map_smul, smul_apply, smul_eq_mul, mul_assoc]

/-- **Comparison with the Euclidean variation, upper bound.** For a `C¹` weight with
`e^{−W} ≤ M` on `Ω` and `u` locally integrable on `Ω`, `V_μ(u; Ω) ≤ M |Du|(Ω)`, where
`|Du|(Ω) = TauCeti.totalVariationOn volume Ω u`. -/
theorem weightedVariation_le_mul_totalVariationOn (hW : ContDiff ℝ 1 W)
    (hu : LocallyIntegrableOn u Ω) {M : ℝ≥0} (hM : ∀ x ∈ Ω, Real.exp (-W x) ≤ M) :
    weightedVariation W Ω u ≤ M * totalVariationOn volume Ω u := by
  rw [weightedVariation_eq_iSup_norm_le_exp_neg hW hu]
  refine iSup₂_le fun Y hY => ?_
  have hYM (x : E) : ‖Y x‖ ≤ M := by
    by_cases hx : x ∈ tsupport Y
    · exact (hY x).trans (hM x (Y.tsupport_subset hx))
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact M.coe_nonneg
  rcases eq_or_ne M 0 with rfl | hM0
  · -- A field bounded by `0` vanishes.
    have hY0 : Y = 0 := by
      ext x
      simpa using hYM x
    simp [hY0]
  · have hMpos : (0 : ℝ) < M := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hM0)
    have hY1 (x : E) : ‖((M : ℝ)⁻¹ • Y) x‖ ≤ 1 := by
      rw [smul_apply, norm_smul, Real.norm_of_nonneg (inv_pos.2 hMpos).le,
        inv_mul_le_iff₀ hMpos, mul_one]
      exact hYM x
    calc ENNReal.ofReal (∫ x, divergenceCLM Y x * u x)
        = M * ENNReal.ofReal (∫ x, divergenceCLM ((M : ℝ)⁻¹ • Y) x * u x) := by
          rw [← ofReal_integral_divergenceCLM_smul_mul, smul_smul, mul_inv_cancel₀ hMpos.ne',
            one_smul]
      _ ≤ M * totalVariationOn volume Ω u := by
          gcongr
          exact ofReal_integral_le_totalVariationOn _ hY1

/-- **Comparison with the Euclidean variation, lower bound.** For a `C¹` weight with
`m ≤ e^{−W}` on `Ω` and `u` locally integrable on `Ω`, `m |Du|(Ω) ≤ V_μ(u; Ω)`, where
`|Du|(Ω) = TauCeti.totalVariationOn volume Ω u`. -/
theorem mul_totalVariationOn_le_weightedVariation (hW : ContDiff ℝ 1 W)
    (hu : LocallyIntegrableOn u Ω) {m : ℝ≥0} (hm : ∀ x ∈ Ω, (m : ℝ) ≤ Real.exp (-W x)) :
    m * totalVariationOn volume Ω u ≤ weightedVariation W Ω u := by
  rw [totalVariationOn_def, ENNReal.mul_iSup]
  refine iSup_le fun X => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hX => ?_
  rw [weightedVariation_eq_iSup_norm_le_exp_neg hW hu]
  have hmX (x : E) : ‖((m : ℝ) • X) x‖ ≤ Real.exp (-W x) := by
    rw [smul_apply, norm_smul, Real.norm_of_nonneg m.coe_nonneg]
    by_cases hx : x ∈ tsupport X
    · exact (mul_le_of_le_one_right m.coe_nonneg (hX x)).trans (hm x (X.tsupport_subset hx))
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero]
      exact (Real.exp_pos _).le
  exact le_iSup₂_of_le ((m : ℝ) • X) hmX (ofReal_integral_divergenceCLM_smul_mul m X).ge

/-- **Local comparison with the Euclidean variation.** For a `C¹` weight, every compact subset
`K` of `Ω` has an open neighbourhood `U ≤ Ω` and a constant `m > 0` such that
`m |Du|(U) ≤ V_μ(u; Ω)` for every `u` locally integrable on `Ω`, where
`|Du|(U) = TauCeti.totalVariationOn volume U u`: `e^{−W}` is bounded below by a positive constant
near `K`. -/
theorem exists_mul_totalVariationOn_le_weightedVariation (hW : ContDiff ℝ 1 W) {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ U : Opens E, K ⊆ (U : Set E) ∧ U ≤ Ω ∧ ∃ m : ℝ≥0, m ≠ 0 ∧
      ∀ v : E → ℝ, LocallyIntegrableOn v Ω →
        m * totalVariationOn volume U v ≤ weightedVariation W Ω v := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  let U : Opens E := ⟨Metric.thickening δ K, Metric.isOpen_thickening⟩
  have hUΩ : U ≤ Ω := (Metric.thickening_subset_cthickening δ K).trans hδΩ
  -- `e^{−W}` has a positive lower bound `m` on the compact set `cthickening δ K ⊇ U`.
  obtain ⟨m, hm, hmW⟩ := hK.cthickening.exists_forall_le'
    (contDiff_exp_neg hW).continuous.continuousOn fun x _ => Real.exp_pos (-W x)
  refine ⟨U, Metric.self_subset_thickening hδ K, hUΩ, ⟨m, hm.le⟩, NNReal.coe_ne_zero.1 hm.ne',
    fun v hv => ?_⟩
  exact (mul_totalVariationOn_le_weightedVariation (m := ⟨m, hm.le⟩) hW (hv.mono_set hUΩ)
    fun x hx => hmW x (Metric.thickening_subset_cthickening δ K hx)).trans
    (weightedVariation_mono hUΩ)

/-- **Finite weighted variation gives locally bounded variation.** For a `C¹` weight and `u`
locally integrable on `Ω`, if `V_μ(u; Ω) < ∞`, then every compact subset of `Ω` has an open
neighbourhood on which `u` has finite Euclidean variation `TauCeti.totalVariationOn volume`. -/
theorem exists_totalVariationOn_ne_top_of_weightedVariation_ne_top (hW : ContDiff ℝ 1 W)
    (hu : LocallyIntegrableOn u Ω) (h : weightedVariation W Ω u ≠ ∞) :
    ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U u ≠ ∞ := by
  intro K hK hKΩ
  obtain ⟨U, hKU, -, m, hm0, hle⟩ := exists_mul_totalVariationOn_le_weightedVariation hW hK hKΩ
  refine ⟨U, hKU, fun htop => h ?_⟩
  have hmu := hle u hu
  rw [htop, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hm0)] at hmu
  exact top_le_iff.1 hmu

/-! ### The Gaussian perimeter -/

/-- The empty set has Gaussian perimeter zero. -/
@[simp]
theorem gaussianPerimeter_empty : gaussianPerimeter (∅ : Set E) = 0 :=
  weightedPerimeter_empty

/-- The whole space has Gaussian perimeter zero. -/
@[simp]
theorem gaussianPerimeter_univ : gaussianPerimeter (univ : Set E) = 0 :=
  weightedPerimeter_univ contDiff_gaussianWeight

/-- A set and its complement have the same Gaussian perimeter. -/
@[simp]
theorem gaussianPerimeter_compl : gaussianPerimeter sᶜ = gaussianPerimeter s :=
  weightedPerimeter_compl contDiff_gaussianWeight

/-- Modifying a set by a null set does not change its Gaussian perimeter. -/
theorem gaussianPerimeter_congr_ae {t : Set E} (h : s =ᵐ[volume] t) :
    gaussianPerimeter s = gaussianPerimeter t :=
  weightedPerimeter_congr_ae (by simpa using h)

end TauCeti
