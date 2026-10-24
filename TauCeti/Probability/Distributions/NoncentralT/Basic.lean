/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Gaussian
public import TauCeti.Probability.Distributions.NoncentralF.Basic
public import TauCeti.Probability.Distributions.StudentT.ChiSquared
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Noncentral t laws

For positive degrees of freedom `ν` and real noncentrality `δ`, the noncentral t law is the law
of `(Z + δ) / √(V / ν)`, where `Z` is a standard Gaussian variable and `V` is an independent
chi-squared variable with `ν` degrees of freedom. Invalid degrees give the zero measure.

Moving the noncentrality into the Gaussian factor presents the law as the Student-type ratio
`Z' / √(V / ν)` with `Z'` Gaussian of mean `δ` and unit variance. From this presentation we
derive the central case, the reflection `δ ↦ -δ`, and the identification of the square of a
noncentral t variable with a noncentral F variable with numerator degree one and noncentrality
`δ ^ 2`. Conditioning on the chi-squared factor shows that the law has a density with respect to
Lebesgue measure.

## Main definitions

* `TauCeti.Probability.noncentralTMeasure` — the noncentral t law.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_noncentralTMeasure` — normalization.
* `TauCeti.Probability.noncentralTMeasure_eq_map_gaussianReal` — the ratio of a Gaussian
  variable with mean `δ` and the normalized chi-squared square root.
* `TauCeti.Probability.noncentralTMeasure_zero_noncentrality` — zero noncentrality gives
  Student's t law.
* `TauCeti.Probability.noncentralTMeasure_map_neg` — reflection negates the noncentrality.
* `TauCeti.Probability.noncentralTMeasure_map_sq` — the square law is noncentral F with
  degrees `1` and `ν` and noncentrality `δ ^ 2`.
* `TauCeti.Probability.absolutelyContinuous_noncentralTMeasure` — the law has a density with
  respect to Lebesgue measure.
* `TauCeti.Probability.measurable_noncentralTMeasure` — joint parameter measurability.
* `TauCeti.Probability.hasLaw_noncentralT_of_gaussian_chiSquared` — the random-variable form of
  the defining ratio.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 31.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ν δ : ℝ}

/-- The noncentral t law with `ν` degrees of freedom and noncentrality `δ`: the law of
`(Z + δ) / √(V / ν)` for a standard Gaussian `Z` and an independent `V` with law
`chiSquaredMeasure ν`. It is the zero measure unless `0 < ν`. -/
def noncentralTMeasure (ν δ : ℝ) : Measure ℝ :=
  if 0 < ν then
    ((gaussianReal 0 1).prod (chiSquaredMeasure ν)).map (fun z ↦ (z.1 + δ) / √(z.2 / ν))
  else 0

/-- For positive degrees, the noncentral t law is the defining ratio pushforward. -/
theorem noncentralTMeasure_eq_map (hν : 0 < ν) (δ : ℝ) :
    noncentralTMeasure ν δ =
      ((gaussianReal 0 1).prod (chiSquaredMeasure ν)).map (fun z ↦ (z.1 + δ) / √(z.2 / ν)) := by
  rw [noncentralTMeasure, ite_eq_left hν]

/-- For nonpositive degrees, the noncentral t measure is zero. -/
@[simp]
theorem noncentralTMeasure_of_nonpos (hν : ν ≤ 0) (δ : ℝ) : noncentralTMeasure ν δ = 0 := by
  rw [noncentralTMeasure, ite_eq_right hν.not_gt]

/-- For positive degrees, the noncentral t law is the law of `Z / √(V / ν)` for a Gaussian `Z`
with mean `δ` and unit variance and an independent `V` with law `chiSquaredMeasure ν`. -/
theorem noncentralTMeasure_eq_map_gaussianReal (hν : 0 < ν) (δ : ℝ) :
    noncentralTMeasure ν δ =
      ((gaussianReal δ 1).prod (chiSquaredMeasure ν)).map (fun z ↦ z.1 / √(z.2 / ν)) := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  have hprod : ((gaussianReal 0 1).prod (chiSquaredMeasure ν)).map (Prod.map (· + δ) id) =
      (gaussianReal δ 1).prod (chiSquaredMeasure ν) := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, gaussianReal_map_add_const,
      Measure.map_id, zero_add]
  rw [noncentralTMeasure_eq_map hν, ← hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- The noncentral t law is a probability measure for positive degrees. -/
theorem isProbabilityMeasure_noncentralTMeasure (hν : 0 < ν) (δ : ℝ) :
    IsProbabilityMeasure (noncentralTMeasure ν δ) := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  rw [noncentralTMeasure_eq_map hν]
  infer_instance

/-- The noncentral t measure is a probability measure exactly when the degrees are positive. -/
@[simp]
theorem isProbabilityMeasure_noncentralTMeasure_iff :
    IsProbabilityMeasure (noncentralTMeasure ν δ) ↔ 0 < ν := by
  refine ⟨fun h ↦ ?_, fun hν ↦ isProbabilityMeasure_noncentralTMeasure hν δ⟩
  by_contra hν
  rw [noncentralTMeasure_of_nonpos (not_lt.1 hν)] at h
  exact IsProbabilityMeasure.ne_zero (0 : Measure ℝ) rfl

/-- The noncentral t law is a finite measure for every choice of parameters. -/
instance isFiniteMeasure_noncentralTMeasure (ν δ : ℝ) :
    IsFiniteMeasure (noncentralTMeasure ν δ) := by
  by_cases hν : 0 < ν
  · let _ := isProbabilityMeasure_noncentralTMeasure hν δ
    infer_instance
  · rw [noncentralTMeasure_of_nonpos (not_lt.1 hν)]
    infer_instance

/-! ### Relations with Student's t and the noncentral F laws -/

/-- At zero noncentrality the noncentral t law is Student's t law, for every degree. -/
@[simp]
theorem noncentralTMeasure_zero_noncentrality (ν : ℝ) :
    noncentralTMeasure ν 0 = studentTMeasure ν := by
  by_cases hν : 0 < ν
  · simp only [noncentralTMeasure_eq_map hν, add_zero, map_div_sqrt_chiSquaredMeasure hν]
  · rw [noncentralTMeasure_of_nonpos (not_lt.1 hν), studentTMeasure_of_nonpos (not_lt.1 hν)]

/-- Reflecting a noncentral t variable negates its noncentrality. -/
@[simp]
theorem noncentralTMeasure_map_neg (ν δ : ℝ) :
    (noncentralTMeasure ν δ).map (fun x ↦ -x) = noncentralTMeasure ν (-δ) := by
  by_cases hν : 0 < ν
  swap
  · simp [noncentralTMeasure_of_nonpos (not_lt.1 hν)]
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  have hprod : ((gaussianReal δ 1).prod (chiSquaredMeasure ν)).map (Prod.map (fun x ↦ -x) id) =
      (gaussianReal (-δ) 1).prod (chiSquaredMeasure ν) := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, gaussianReal_map_neg,
      Measure.map_id]
  rw [noncentralTMeasure_eq_map_gaussianReal hν, noncentralTMeasure_eq_map_gaussianReal hν,
    ← hprod, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp [neg_div]

/-- The square of a noncentral t variable with `ν` degrees of freedom and noncentrality `δ` is a
noncentral F variable with degrees `1` and `ν` and noncentrality `δ ^ 2`. Both sides are zero for
`ν ≤ 0`. -/
@[simp]
theorem noncentralTMeasure_map_sq (ν δ : ℝ) :
    (noncentralTMeasure ν δ).map (fun x ↦ x ^ 2) = noncentralFMeasure 1 ν (‖δ‖₊ ^ 2) := by
  by_cases hν : 0 < ν
  swap
  · simp [noncentralTMeasure_of_nonpos (not_lt.1 hν), hν]
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  let μ := (gaussianReal δ 1).prod (chiSquaredMeasure ν)
  -- The chi-squared coordinate is positive almost everywhere, so squaring the ratio cancels its
  -- square-root denominator.
  have hsq : (fun z : ℝ × ℝ ↦ (z.1 / √(z.2 / ν)) ^ 2) =ᵐ[μ] fun z ↦ z.1 ^ 2 / 1 / (z.2 / ν) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_pos_chiSquaredMeasure hν)] with z hz
    rw [div_pow, sq_sqrt (div_pos hz hν).le, div_one]
  have hprod : μ.map (Prod.map (fun x ↦ x ^ 2) id) =
      (noncentralChiSquaredMeasure 1 (‖δ‖₊ ^ 2)).prod (chiSquaredMeasure ν) := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, gaussianReal_map_sq_noncentral,
      Measure.map_id]
  rw [noncentralTMeasure_eq_map_gaussianReal hν, Measure.map_map (by fun_prop) (by fun_prop),
    noncentralFMeasure_eq_map one_pos hν, ← hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_congr hsq

/-! ### Absolute continuity -/

/-- The noncentral t law is absolutely continuous with respect to Lebesgue measure, for every
choice of parameters. -/
theorem absolutelyContinuous_noncentralTMeasure (ν δ : ℝ) :
    noncentralTMeasure ν δ ≪ volume := by
  by_cases hν : 0 < ν
  swap
  · simp [noncentralTMeasure_of_nonpos (not_lt.1 hν)]
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  rw [noncentralTMeasure_eq_map_gaussianReal hν, Measure.map_apply (by fun_prop) hs,
    Measure.prod_apply_symm
      ((by fun_prop : Measurable fun z : ℝ × ℝ ↦ z.1 / √(z.2 / ν)) hs)]
  -- For each positive value `c` of the denominator, the Gaussian factor charges the null set
  -- `{x | x / c ∈ s}` with mass zero, since scaling by `c⁻¹` preserves Lebesgue-null sets.
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [ae_pos_sqrt_div_chiSquaredMeasure hν] with v hv
  have hset : (fun x ↦ (x, v)) ⁻¹' ((fun z : ℝ × ℝ ↦ z.1 / √(z.2 / ν)) ⁻¹' s) =
      (fun x ↦ x * (√(v / ν))⁻¹) ⁻¹' s := by
    ext x
    simp [div_eq_mul_inv]
  have hac : (gaussianReal δ 1).map (fun x ↦ x * (√(v / ν))⁻¹) ≪ volume := by
    refine ((gaussianReal_absolutelyContinuous δ one_ne_zero).map (by fun_prop)).trans ?_
    rw [Real.map_volume_mul_right (inv_ne_zero hv.ne')]
    exact Measure.smul_absolutelyContinuous
  rw [hset, ← Measure.map_apply (by fun_prop) hs]
  exact hac hs0

/-- The noncentral t law has no atoms, for every choice of parameters. -/
instance nullSingletonClass_noncentralTMeasure (ν δ : ℝ) :
    NullSingletonClass (noncentralTMeasure ν δ) :=
  ⟨fun x ↦ absolutelyContinuous_noncentralTMeasure ν δ (measure_singleton x)⟩

/-! ### Parameter measurability -/

/-- The full totalized noncentral t family is jointly measurable in its degree and its
noncentrality. -/
@[fun_prop]
theorem measurable_noncentralTMeasure :
    Measurable fun p : ℝ × ℝ ↦ noncentralTMeasure p.1 p.2 := by
  -- On the valid set, use the degree `|ν|` in the chi-squared factor so that it is a probability
  -- law at every parameter and the product is measurable as a `ProbabilityMeasure`.
  have hprod : Measurable fun p : ℝ × ℝ ↦ (⟨(gaussianReal 0 1).prod (chiSquaredMeasure |p.1|),
      by
        let _ := isProbabilityMeasure_chiSquaredMeasure (abs_nonneg p.1)
        infer_instance⟩ : ProbabilityMeasure (ℝ × ℝ)) := by
    have hV : Measurable fun p : ℝ × ℝ ↦ (⟨chiSquaredMeasure |p.1|,
        isProbabilityMeasure_chiSquaredMeasure (abs_nonneg _)⟩ : ProbabilityMeasure ℝ) :=
      (measurable_chiSquaredMeasure.comp (f := fun p : ℝ × ℝ ↦ |p.1|) (by fun_prop)).subtype_mk
    exact (ProbabilityMeasure.measurable_fun_prod.comp
      ((measurable_const (a := (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))).prodMk
        hV)).subtype_mk
  have hratio : Measurable fun p : ℝ × ℝ ↦
      (((gaussianReal 0 1).prod (chiSquaredMeasure |p.1|)).map
        (fun z ↦ (z.1 + p.2) / √(z.2 / p.1)) : Measure ℝ) := by
    have hmap := TauCeti.MeasureTheory.measurable_probabilityMeasure_map_of_measurable_uncurry
      (f := fun (p : ℝ × ℝ) (z : ℝ × ℝ) ↦ (z.1 + p.2) / √(z.2 / p.1)) (by fun_prop)
    exact measurable_subtype_coe.comp (hmap.comp (hprod.prodMk measurable_id))
  have h : Measurable fun p : ℝ × ℝ ↦ if 0 < p.1 then
      ((gaussianReal 0 1).prod (chiSquaredMeasure |p.1|)).map
        (fun z ↦ (z.1 + p.2) / √(z.2 / p.1)) else 0 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) hratio measurable_const
  convert h using 1
  funext p
  by_cases hp : 0 < p.1
  · simp [noncentralTMeasure_eq_map hp, hp, abs_of_pos hp]
  · simp [noncentralTMeasure_of_nonpos (not_lt.1 hp), hp]

/-! ### Random-variable forms -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Z V : Ω → ℝ}

/-- If `Z` is standard Gaussian and `V` is an independent chi-squared variable with `ν > 0`
degrees of freedom, then `(Z + δ) / √(V / ν)` has the noncentral t law with `ν` degrees of
freedom and noncentrality `δ`. -/
theorem hasLaw_noncentralT_of_gaussian_chiSquared (hν : 0 < ν) (hZV : IndepFun Z V P)
    (hZ : HasLaw Z (gaussianReal 0 1) P) (hV : HasLaw V (chiSquaredMeasure ν) P) :
    HasLaw (fun ω ↦ (Z ω + δ) / √(V ω / ν)) (noncentralTMeasure ν δ) P := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  let _ : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  have hratio : HasLaw (fun z : ℝ × ℝ ↦ (z.1 + δ) / √(z.2 / ν)) (noncentralTMeasure ν δ)
      ((gaussianReal 0 1).prod (chiSquaredMeasure ν)) :=
    ⟨by fun_prop, (noncentralTMeasure_eq_map hν δ).symm⟩
  exact hratio.fun_comp (hZV.hasLaw_prod hZ hV)

/-- A variable with a noncentral t law has a probability density function with respect to
Lebesgue measure. -/
theorem hasPDF_of_hasLaw_noncentralTMeasure (hX : HasLaw X (noncentralTMeasure ν δ) P) :
    HasPDF X P :=
  ⟨hX.aemeasurable, by rw [hX.map_eq]; infer_instance,
    hX.map_eq ▸ absolutelyContinuous_noncentralTMeasure ν δ⟩

end TauCeti.Probability
