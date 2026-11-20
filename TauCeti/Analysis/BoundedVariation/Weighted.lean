/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts

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
* `TauCeti.weightedVariation_eq_iSup_trace_fderiv`: for a differentiable weight, the weighted
  variation pairs `u` with the divergences of the fields `e^{−W} X`.
* `TauCeti.integral_divergenceCLM_sub_fderiv_mul_exp_neg_eq_zero`: for a `C¹` weight, the weighted
  divergence of a test vector field has `μ`-integral zero.
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
open scoped ENNReal Distributions Topology

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
