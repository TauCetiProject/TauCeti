/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.FisherSnedecor.ChiSquared
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Basic
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Noncentral F laws

For positive degrees of freedom `m` and `n` and noncentrality `l ≥ 0`, the noncentral F law is
the law of the variance ratio `(U / m) / (V / n)` of independent variables `U` and `V`, where
`U` is noncentral chi-squared with degree `m` and noncentrality `l` and `V` is central
chi-squared with degree `n`. Invalid degrees give the zero measure.

Since the noncentral chi-squared law is a Poisson mixture of central chi-squared laws, the
noncentral F law is the Poisson mixture, with weights of rate `l / 2`, of the scaled central F
laws `((m + 2 * j) / m) • F(m + 2 * j, n)`. This presentation is the route to the density,
distribution function, quantile and moments of the family.

## Main definitions

* `TauCeti.Probability.noncentralFMeasure` — the noncentral F law.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_noncentralFMeasure` — normalization.
* `TauCeti.Probability.noncentralFMeasure_eq_sum` and
  `TauCeti.Probability.noncentralFMeasure_eq_bind` — the Poisson mixture of scaled central F laws.
* `TauCeti.Probability.noncentralFMeasure_zero_noncentrality` — zero noncentrality gives
  Fisher's F law.
* `TauCeti.Probability.absolutelyContinuous_noncentralFMeasure` — the law has a density with
  respect to Lebesgue measure.
* `TauCeti.Probability.support_noncentralFMeasure` — the topological support is `[0, ∞)`.
* `TauCeti.Probability.measurable_noncentralFMeasure` — joint parameter measurability.
* `TauCeti.Probability.hasLaw_noncentralF_of_noncentralChiSquared` — the random-variable form of
  the defining ratio.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {m n : ℝ} {l : ℝ≥0}

/-- The noncentral F law with numerator degree `m`, denominator degree `n` and noncentrality `l`:
the law of `(U / m) / (V / n)` for independent `U` with law `noncentralChiSquaredMeasure m l` and
`V` with law `chiSquaredMeasure n`. It is the zero measure unless `0 < m` and `0 < n`. -/
def noncentralFMeasure (m n : ℝ) (l : ℝ≥0) : Measure ℝ :=
  if 0 < m ∧ 0 < n then
    ((noncentralChiSquaredMeasure m l).prod (chiSquaredMeasure n)).map
      (fun z ↦ z.1 / m / (z.2 / n))
  else 0

/-- For positive degrees, the noncentral F law is the defining variance-ratio pushforward. -/
theorem noncentralFMeasure_eq_map (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    noncentralFMeasure m n l =
      ((noncentralChiSquaredMeasure m l).prod (chiSquaredMeasure n)).map
        (fun z ↦ z.1 / m / (z.2 / n)) := by
  rw [noncentralFMeasure, ite_eq_left ⟨hm, hn⟩]

/-- For invalid degrees, the noncentral F measure is zero. -/
@[simp]
theorem noncentralFMeasure_of_not_pos (h : ¬ (0 < m ∧ 0 < n)) (l : ℝ≥0) :
    noncentralFMeasure m n l = 0 := by
  rw [noncentralFMeasure, ite_eq_right h]

/-- The noncentral F law is a probability measure for positive degrees. -/
theorem isProbabilityMeasure_noncentralFMeasure (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    IsProbabilityMeasure (noncentralFMeasure m n l) := by
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure hm.le l
  let _ := isProbabilityMeasure_chiSquaredMeasure hn.le
  rw [noncentralFMeasure_eq_map hm hn]
  infer_instance

/-- The noncentral F measure is a probability measure exactly when both degrees are positive. -/
@[simp]
theorem isProbabilityMeasure_noncentralFMeasure_iff :
    IsProbabilityMeasure (noncentralFMeasure m n l) ↔ 0 < m ∧ 0 < n := by
  refine ⟨fun h ↦ ?_, fun h ↦ isProbabilityMeasure_noncentralFMeasure h.1 h.2 l⟩
  by_contra hmn
  rw [noncentralFMeasure_of_not_pos hmn] at h
  exact not_isProbabilityMeasure_zero h

/-- The noncentral F law is a finite measure for every choice of parameters. -/
instance isFiniteMeasure_noncentralFMeasure (m n : ℝ) (l : ℝ≥0) :
    IsFiniteMeasure (noncentralFMeasure m n l) := by
  by_cases h : 0 < m ∧ 0 < n
  · let _ := isProbabilityMeasure_noncentralFMeasure h.1 h.2 l
    infer_instance
  · rw [noncentralFMeasure_of_not_pos h]
    infer_instance

/-! ### The Poisson mixture of scaled central F laws -/

/-- The noncentral F law is the Poisson-weighted sum, with weights of rate `l / 2`, of the
central F laws `F(m + 2 * j, n)` scaled by `(m + 2 * j) / m`. For `n ≤ 0` both sides are
zero. -/
theorem noncentralFMeasure_eq_sum (hm : 0 < m) (l : ℝ≥0) :
    noncentralFMeasure m n l = Measure.sum fun j : ℕ ↦
      poissonMeasure (l / 2) {j} •
        (fisherSnedecorMeasure (m + 2 * j) n).map (fun x ↦ (m + 2 * j) / m * x) := by
  by_cases hn : 0 < n
  swap
  · simp [hn]
  let _ := isProbabilityMeasure_chiSquaredMeasure hn.le
  rw [noncentralFMeasure_eq_map hm hn, noncentralChiSquaredMeasure_eq_sum hm.le,
    Measure.prod_sum_left, Measure.map_sum (by fun_prop)]
  congr 1
  funext j
  -- Rescaling the numerator from `m + 2 * j` to `m` scales the central F law of the component.
  have hk : 0 < m + 2 * j := by positivity
  rw [Measure.prod_smul_left, Measure.map_smul _ (by fun_prop),
    ← map_scaled_div_chiSquaredMeasure hk hn, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 2
  funext z
  simp only [Function.comp_apply]
  field_simp

/-- The noncentral F law as a `Measure.bind` mixture of scaled central F laws over the Poisson
law of rate `l / 2`. -/
theorem noncentralFMeasure_eq_bind (hm : 0 < m) (l : ℝ≥0) :
    noncentralFMeasure m n l = (poissonMeasure (l / 2)).bind fun j ↦
      (fisherSnedecorMeasure (m + 2 * j) n).map (fun x ↦ (m + 2 * j) / m * x) := by
  ext s hs
  rw [noncentralFMeasure_eq_sum hm, Measure.sum_apply _ hs,
    Measure.bind_apply hs (.of_discrete), lintegral_countable']
  simp only [Measure.smul_apply, smul_eq_mul, mul_comm]

/-- Set evaluation as an extended-real Poisson series; the formula holds for every set. -/
theorem noncentralFMeasure_apply (hm : 0 < m) (l : ℝ≥0) (s : Set ℝ) :
    noncentralFMeasure m n l s = ∑' j : ℕ, poissonMeasure (l / 2) {j} *
      (fisherSnedecorMeasure (m + 2 * j) n).map (fun x ↦ (m + 2 * j) / m * x) s := by
  rw [noncentralFMeasure_eq_sum hm, Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- Nonnegative integration against the noncentral F law can be performed component by
component, without measurability, finiteness or integrability assumptions on the observable. -/
theorem lintegral_noncentralFMeasure (hm : 0 < m) (l : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂noncentralFMeasure m n l = ∑' j : ℕ, poissonMeasure (l / 2) {j} *
      ∫⁻ x, f ((m + 2 * j) / m * x) ∂fisherSnedecorMeasure (m + 2 * j) n := by
  rw [noncentralFMeasure_eq_sum hm, lintegral_sum_measure]
  congr 1
  funext j
  have hj : (m + 2 * j) / m ≠ 0 := by positivity
  have he : MeasurableEmbedding fun x : ℝ ↦ (m + 2 * j) / m * x :=
    (Homeomorph.mulLeft₀ _ hj).measurableEmbedding
  rw [lintegral_smul_measure, smul_eq_mul, he.lintegral_map]

/-- At zero noncentrality the noncentral F law is Fisher's F law, for every pair of degrees. -/
@[simp]
theorem noncentralFMeasure_zero_noncentrality (m n : ℝ) :
    noncentralFMeasure m n 0 = fisherSnedecorMeasure m n := by
  by_cases h : 0 < m ∧ 0 < n
  · rw [noncentralFMeasure_eq_map h.1 h.2, noncentralChiSquaredMeasure_zero_noncentrality,
      map_scaled_div_chiSquaredMeasure h.1 h.2]
  · rw [noncentralFMeasure_of_not_pos h, fisherSnedecorMeasure_of_not_pos h]

/-- The noncentral F law dominates its Poisson-zero component, the central F law with the same
degrees weighted by `exp (-l / 2)`, for every choice of parameters. -/
theorem smul_fisherSnedecorMeasure_le_noncentralFMeasure (m n : ℝ) (l : ℝ≥0) :
    ENNReal.ofReal (exp (-(l : ℝ) / 2)) • fisherSnedecorMeasure m n ≤
      noncentralFMeasure m n l := by
  by_cases hm : 0 < m
  swap
  · simp [hm]
  have hle := Measure.le_sum (fun j : ℕ ↦ poissonMeasure (l / 2) {j} •
    (fisherSnedecorMeasure (m + 2 * j) n).map (fun x ↦ (m + 2 * j) / m * x)) 0
  rw [← noncentralFMeasure_eq_sum hm] at hle
  simpa [poissonMeasure_singleton, div_self hm.ne', NNReal.coe_div, neg_div] using hle

/-! ### Support and absolute continuity -/

/-- A noncentral F variable is positive almost surely, for every choice of parameters. -/
theorem ae_pos_noncentralFMeasure (m n : ℝ) (l : ℝ≥0) :
    ∀ᵐ x ∂noncentralFMeasure m n l, 0 < x := by
  by_cases h : 0 < m ∧ 0 < n
  · let _ := isProbabilityMeasure_chiSquaredMeasure h.2.le
    let _ := isProbabilityMeasure_noncentralChiSquaredMeasure h.1.le l
    rw [noncentralFMeasure_eq_map h.1 h.2, ae_map_iff (by fun_prop) measurableSet_Ioi]
    filter_upwards [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioi.prod measurableSet_Ioi)
      |>.2 ((ae_pos_noncentralChiSquaredMeasure h.1 l).mono fun x hx ↦
        (ae_pos_chiSquaredMeasure h.2).mono fun y hy ↦ ⟨hx, hy⟩)] with z hz
    exact div_pos (div_pos hz.1 h.1) (div_pos hz.2 h.2)
  · simp [noncentralFMeasure_of_not_pos h]

/-- The noncentral F law is absolutely continuous with respect to Lebesgue measure, for every
choice of parameters. -/
theorem absolutelyContinuous_noncentralFMeasure (m n : ℝ) (l : ℝ≥0) :
    noncentralFMeasure m n l ≪ volume := by
  by_cases h : 0 < m ∧ 0 < n
  · rw [noncentralFMeasure_eq_sum h.1]
    refine Measure.absolutelyContinuous_sum_left fun j ↦
      (Measure.AbsolutelyContinuous.smul_left ?_ _)
    have hj : (m + 2 * j) / m ≠ 0 := by have := h.1; positivity
    have hmap := ((withDensity_absolutelyContinuous volume
      (fisherSnedecorPDF (m + 2 * j) n)).map (measurable_const_mul ((m + 2 * j) / m)))
    rw [← fisherSnedecorMeasure_eq_withDensity, Real.map_volume_mul_left hj] at hmap
    exact hmap.trans (Measure.smul_absolutelyContinuous)
  · simp [noncentralFMeasure_of_not_pos h]

/-- The noncentral F law has no atoms, for every choice of parameters. -/
instance nullSingletonClass_noncentralFMeasure (m n : ℝ) (l : ℝ≥0) :
    NullSingletonClass (noncentralFMeasure m n l) :=
  ⟨fun x ↦ absolutelyContinuous_noncentralFMeasure m n l (measure_singleton x)⟩

/-- For positive degrees the topological support is the closed nonnegative half-line, although
the variable is positive almost surely. -/
@[simp]
theorem support_noncentralFMeasure (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    (noncentralFMeasure m n l).support = Ici 0 := by
  apply Set.Subset.antisymm
  · exact Measure.support_subset_of_isClosed isClosed_Ici
      ((ae_pos_noncentralFMeasure m n l).mono fun _ hx ↦ le_of_lt hx)
  · have hw : ENNReal.ofReal (exp (-(l : ℝ) / 2)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.2 (exp_pos _)
    have hac := (Measure.absolutelyContinuous_smul hw).trans
      (smul_fisherSnedecorMeasure_le_noncentralFMeasure m n l).absolutelyContinuous
    rw [← support_fisherSnedecorMeasure hm hn]
    exact hac.support_mono

/-! ### Parameter measurability -/

/-- The full totalized noncentral F family is jointly measurable in its two degrees and its
noncentrality. -/
@[fun_prop]
theorem measurable_noncentralFMeasure :
    Measurable fun p : ℝ × ℝ × ℝ≥0 ↦ noncentralFMeasure p.1 p.2.1 p.2.2 := by
  -- On the valid set, use degrees `|m|` and `|n|` so that both factors are probability laws at
  -- every parameter and the product is measurable as a `ProbabilityMeasure`.
  have hU : Measurable fun p : ℝ × ℝ × ℝ≥0 ↦ (⟨noncentralChiSquaredMeasure |p.1| p.2.2,
      isProbabilityMeasure_noncentralChiSquaredMeasure (abs_nonneg _) _⟩ :
        ProbabilityMeasure ℝ) :=
    (measurable_noncentralChiSquaredMeasure.comp
      (f := fun p : ℝ × ℝ × ℝ≥0 ↦ (|p.1|, p.2.2)) (by fun_prop)).subtype_mk
  have hV : Measurable fun p : ℝ × ℝ × ℝ≥0 ↦ (⟨chiSquaredMeasure |p.2.1|,
      isProbabilityMeasure_chiSquaredMeasure (abs_nonneg _)⟩ : ProbabilityMeasure ℝ) :=
    (measurable_chiSquaredMeasure.comp (f := fun p : ℝ × ℝ × ℝ≥0 ↦ |p.2.1|)
      (by fun_prop)).subtype_mk
  have hratio : Measurable fun p : ℝ × ℝ × ℝ≥0 ↦
      (((noncentralChiSquaredMeasure |p.1| p.2.2).prod (chiSquaredMeasure |p.2.1|)).map
        (fun z ↦ z.1 / p.1 / (z.2 / p.2.1)) : Measure ℝ) := by
    have hprod : Measurable fun p : ℝ × ℝ × ℝ≥0 ↦ (⟨(noncentralChiSquaredMeasure |p.1| p.2.2).prod
        (chiSquaredMeasure |p.2.1|), by
          let _ := isProbabilityMeasure_noncentralChiSquaredMeasure (abs_nonneg p.1) p.2.2
          let _ := isProbabilityMeasure_chiSquaredMeasure (abs_nonneg p.2.1)
          infer_instance⟩ : ProbabilityMeasure (ℝ × ℝ)) :=
      (ProbabilityMeasure.measurable_fun_prod.comp (hU.prodMk hV)).subtype_mk
    have hmap := TauCeti.MeasureTheory.measurable_probabilityMeasure_map_of_measurable_uncurry
      (f := fun (p : ℝ × ℝ × ℝ≥0) (z : ℝ × ℝ) ↦ z.1 / p.1 / (z.2 / p.2.1)) (by fun_prop)
    exact measurable_subtype_coe.comp (hmap.comp (hprod.prodMk measurable_id))
  have hvalid : MeasurableSet {p : ℝ × ℝ × ℝ≥0 | 0 < p.1 ∧ 0 < p.2.1} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd.fst)
  have h : Measurable fun p : ℝ × ℝ × ℝ≥0 ↦ if 0 < p.1 ∧ 0 < p.2.1 then
      ((noncentralChiSquaredMeasure |p.1| p.2.2).prod (chiSquaredMeasure |p.2.1|)).map
        (fun z ↦ z.1 / p.1 / (z.2 / p.2.1)) else 0 :=
    Measurable.ite hvalid hratio measurable_const
  convert h using 1
  funext p
  by_cases h : 0 < p.1 ∧ 0 < p.2.1
  · simp [noncentralFMeasure_eq_map h.1 h.2, h, abs_of_pos h.1, abs_of_pos h.2]
  · simp [h]

/-! ### Random-variable forms -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ}

/-- If `X` is noncentral chi-squared with degree `m` and noncentrality `l`, and `Y` is an
independent central chi-squared variable with degree `n`, then the variance ratio
`(X / m) / (Y / n)` has the noncentral F law. -/
theorem hasLaw_noncentralF_of_noncentralChiSquared (hm : 0 < m) (hn : 0 < n)
    (hXY : IndepFun X Y P) (hX : HasLaw X (noncentralChiSquaredMeasure m l) P)
    (hY : HasLaw Y (chiSquaredMeasure n) P) :
    HasLaw (fun ω ↦ X ω / m / (Y ω / n)) (noncentralFMeasure m n l) P := by
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure hm.le l
  let _ := isProbabilityMeasure_chiSquaredMeasure hn.le
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hratio : HasLaw (fun z : ℝ × ℝ ↦ z.1 / m / (z.2 / n)) (noncentralFMeasure m n l)
      ((noncentralChiSquaredMeasure m l).prod (chiSquaredMeasure n)) :=
    ⟨by fun_prop, (noncentralFMeasure_eq_map hm hn l).symm⟩
  exact hratio.fun_comp (hXY.hasLaw_prod hX hY)

/-- A variable with a noncentral F law has a probability density function with respect to
Lebesgue measure. -/
theorem hasPDF_of_hasLaw_noncentralFMeasure (hX : HasLaw X (noncentralFMeasure m n l) P) :
    HasPDF X P :=
  ⟨hX.aemeasurable, by rw [hX.map_eq]; infer_instance,
    hX.map_eq ▸ absolutelyContinuous_noncentralFMeasure m n l⟩

end TauCeti.Probability
