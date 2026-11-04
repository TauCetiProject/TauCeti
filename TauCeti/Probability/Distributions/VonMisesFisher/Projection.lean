/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Basic
public import TauCeti.Probability.Distributions.Uniform.Sphere.Coordinate
public import TauCeti.Probability.Distributions.Beta.PDF
import TauCeti.Probability.Cdf.Density

/-!
# Mean-direction projections of von Mises–Fisher laws

In dimension `d ≥ 2`, projection onto the unit direction gives the exponential tilt of
the centered symmetric Beta law of shape `(d - 1) / 2`. Its Lebesgue density is positive
on `(-1, 1)` and zero elsewhere, with a normalizing constant given by a one-dimensional
Beta integral. This supplies a scalar cdf and an interior-root characterization of quantiles.

The projection identity uses `map_inner_uniformSphereMeasure` and transport of exponential
tilting. The cdf and quantile arguments follow the fixed-interval API in
`TauCeti.Probability.Distributions.VonMises.Angle`.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), §9.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Real Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace TauCeti.Probability

/-- The mean-direction projection density in dimension at least two, expressed using the
centered symmetric Beta density and its exponential normalizer. It is zero in dimensions
below two and at negative concentration. -/
def vonMisesFisherProjectionPDFReal (d : ℕ) (κ x : ℝ) : ℝ :=
  if 2 ≤ d ∧ 0 ≤ κ then
    let a := ((d : ℝ) - 1) / 2
    betaPDFReal a a ((x + 1) / 2) / 2 *
      (exp (κ * x) / ∫ y, exp (κ * (-1 + 2 * y)) ∂betaMeasure a a)
  else 0

/-- The extended nonnegative projection density. -/
def vonMisesFisherProjectionPDF (d : ℕ) (κ x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (vonMisesFisherProjectionPDFReal d κ x)

/-- The extended density is the nonnegative lift of the real density. -/
theorem vonMisesFisherProjectionPDF_eq_ofReal (d : ℕ) (κ x : ℝ) :
    vonMisesFisherProjectionPDF d κ x =
      ENNReal.ofReal (vonMisesFisherProjectionPDFReal d κ x) := (rfl)

/-- The real projection density is measurable. -/
@[fun_prop]
theorem measurable_vonMisesFisherProjectionPDFReal (d : ℕ) (κ : ℝ) :
    Measurable (vonMisesFisherProjectionPDFReal d κ) := by
  unfold vonMisesFisherProjectionPDFReal
  fun_prop

/-- The extended projection density is measurable. -/
@[fun_prop]
theorem measurable_vonMisesFisherProjectionPDF (d : ℕ) (κ : ℝ) :
    Measurable (vonMisesFisherProjectionPDF d κ) :=
  (measurable_vonMisesFisherProjectionPDFReal d κ).ennreal_ofReal

/-- Invalid dimension or negative concentration gives zero projection density. -/
@[simp]
theorem vonMisesFisherProjectionPDFReal_of_invalid {d : ℕ} {κ x : ℝ}
    (h : ¬(2 ≤ d ∧ 0 ≤ κ)) : vonMisesFisherProjectionPDFReal d κ x = 0 := by
  simp [vonMisesFisherProjectionPDFReal, h]

/-- The projection density vanishes off the open unit interval, including at its endpoints. -/
@[simp]
theorem vonMisesFisherProjectionPDFReal_of_notMem_Ioo {d : ℕ} {κ x : ℝ}
    (hx : x ∉ Ioo (-1) 1) : vonMisesFisherProjectionPDFReal d κ x = 0 := by
  have h : ¬(0 < (x + 1) / 2 ∧ (x + 1) / 2 < 1) := by
    intro ht
    apply hx
    constructor <;> linarith [ht.1, ht.2]
  simp only [vonMisesFisherProjectionPDFReal, betaPDFReal, ite_eq_right h, zero_div,
    zero_mul, ite_self]

/-- On the open unit interval the projection density is proportional to
`exp (κ * x) * (1 - x²)^((d - 3) / 2)`, with its full normalizing constant. -/
theorem vonMisesFisherProjectionPDFReal_of_mem {d : ℕ} (hd : 2 ≤ d) {κ x : ℝ}
    (hκ : 0 ≤ κ) (hx : x ∈ Ioo (-1) 1) :
    vonMisesFisherProjectionPDFReal d κ x =
      exp (κ * x) * (1 - x ^ 2) ^ (((d : ℝ) - 3) / 2) /
        (2 ^ ((d : ℝ) - 2) *
          beta (((d : ℝ) - 1) / 2) (((d : ℝ) - 1) / 2) *
            ∫ y, exp (κ * (-1 + 2 * y)) ∂
              betaMeasure (((d : ℝ) - 1) / 2) (((d : ℝ) - 1) / 2)) := by
  let q := ((d : ℝ) - 1) / 2 - 1
  have hq : q = ((d : ℝ) - 3) / 2 := by dsimp [q]; ring
  have hprod : (x + 1) / 2 * (1 - (x + 1) / 2) = (1 - x ^ 2) / 4 := by ring
  have hfour : (4 : ℝ) ^ q * 2 = 2 ^ ((d : ℝ) - 2) := by
    calc
      (4 : ℝ) ^ q * 2 = 2 ^ (2 * q) * 2 ^ (1 : ℝ) := by
        rw [rpow_one, rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ = 2 ^ (2 * q + 1) := (rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ = 2 ^ ((d : ℝ) - 2) := by congr 1; dsimp [q]; ring
  have hbeta : betaPDFReal (((d : ℝ) - 1) / 2) (((d : ℝ) - 1) / 2) ((x + 1) / 2) =
      (1 / beta (((d : ℝ) - 1) / 2) (((d : ℝ) - 1) / 2)) *
        ((1 - x ^ 2) / 4) ^ q := by
    rw [betaPDFReal, ite_eq_left ⟨by linarith [hx.1], by linarith [hx.2]⟩, mul_assoc,
      ← mul_rpow (by linarith [hx.1]) (by linarith [hx.2]), hprod]
  rw [vonMisesFisherProjectionPDFReal, ite_eq_left ⟨hd, hκ⟩]
  dsimp only
  rw [hbeta, div_rpow (by nlinarith [hx.1, hx.2]) (by norm_num), ← hfour, ← hq]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The totalized real projection density is nonnegative at every parameter. -/
theorem vonMisesFisherProjectionPDFReal_nonneg (d : ℕ) (κ x : ℝ) :
    0 ≤ vonMisesFisherProjectionPDFReal d κ x := by
  by_cases h : 2 ≤ d ∧ 0 ≤ κ
  · rw [vonMisesFisherProjectionPDFReal, ite_eq_left h]
    have ha : 0 < ((d : ℝ) - 1) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast h.1
      linarith
    exact mul_nonneg (div_nonneg (betaPDFReal_nonneg ha ha _) two_pos.le)
      (div_nonneg (exp_pos _).le (integral_nonneg fun _ ↦ (exp_pos _).le))
  · simp [vonMisesFisherProjectionPDFReal_of_invalid h]

/-- The projection density is positive exactly in the open unit interval. -/
@[simp]
theorem vonMisesFisherProjectionPDFReal_pos_iff {d : ℕ} (hd : 2 ≤ d) {κ : ℝ}
    (hκ : 0 ≤ κ) (x : ℝ) :
    0 < vonMisesFisherProjectionPDFReal d κ x ↔ x ∈ Ioo (-1) 1 := by
  have ha : 0 < ((d : ℝ) - 1) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  let _ := isProbabilityMeasureBeta ha ha
  have hb : ∀ᵐ y ∂betaMeasure (((d : ℝ) - 1) / 2) (((d : ℝ) - 1) / 2),
      -1 + 2 * y ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [ae_mem_Icc_betaMeasure _ _] with y hy
    constructor <;> linarith [hy.1, hy.2]
  have hi : Integrable (fun y : ℝ ↦ exp (κ * (-1 + 2 * y)))
      (betaMeasure (((d : ℝ) - 1) / 2) (((d : ℝ) - 1) / 2)) :=
    integrable_exp_mul_of_mem_Icc (by fun_prop) hb
  constructor
  · contrapose!
    intro hx
    simp [vonMisesFisherProjectionPDFReal_of_notMem_Ioo hx]
  · intro hx
    rw [vonMisesFisherProjectionPDFReal, ite_eq_left ⟨hd, hκ⟩]
    exact mul_pos (div_pos (betaPDFReal_pos (by linarith [hx.1])
      (by linarith [hx.2]) ha ha) two_pos) (div_pos (exp_pos _) (integral_exp_pos hi))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The mean-direction projection is a tilt of the centered symmetric Beta law. -/
theorem map_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    (vonMisesFisherMeasure m κ).map (fun x : sphere (0 : E) 1 ↦ ⟪(m : E), (x : E)⟫) =
      ((betaMeasure (((Module.finrank ℝ E : ℝ) - 1) / 2)
        (((Module.finrank ℝ E : ℝ) - 1) / 2)).map (fun y ↦ -1 + 2 * y)).tilted
          (fun y ↦ κ * y) := by
  rw [vonMisesFisherMeasure_of_nonneg m hκ, vonMisesFisherNaturalMeasure_def]
  simp only [real_inner_smul_left]
  rw [← Function.comp_def (f := fun y : ℝ ↦ κ * y), Measure.map_tilted _ (by fun_prop)
    (by fun_prop), map_inner_uniformSphereMeasure hd]
  simp

/-- The projection law has the explicit normalized exponential-Beta density. -/
theorem map_inner_vonMisesFisherMeasure_eq_withDensity (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) (κ : ℝ) :
    (vonMisesFisherMeasure m κ).map (fun x : sphere (0 : E) 1 ↦ ⟪(m : E), (x : E)⟫) =
      volume.withDensity (vonMisesFisherProjectionPDF (Module.finrank ℝ E) κ) := by
  by_cases hκ : 0 ≤ κ
  · let a := ((Module.finrank ℝ E : ℝ) - 1) / 2
    have ha : 0 < a := by
      have : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hd
      dsimp [a]
      linarith
    have hbase : (betaMeasure a a).map (fun y ↦ -1 + 2 * y) =
        volume.withDensity (fun x ↦ ENNReal.ofReal (betaPDFReal a a ((x + 1) / 2) / 2)) := by
      rw [betaMeasure, map_affine_withDensity_volume _ (by norm_num)]
      congr 1
      ext x
      simp only [affineDensity_apply, betaPDF, sub_neg_eq_add,
        abs_of_pos (by norm_num : 0 < (2 : ℝ))]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    have hZ : (∫ y, exp (κ * y) ∂(betaMeasure a a).map (fun y ↦ -1 + 2 * y)) =
        ∫ y, exp (κ * (-1 + 2 * y)) ∂betaMeasure a a := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    rw [map_inner_vonMisesFisherMeasure hd m hκ, hbase,
      tilted_withDensity (by fun_prop) (by fun_prop), ← hbase, hZ]
    apply withDensity_congr_ae
    refine ae_of_all _ fun x ↦ ?_
    rw [vonMisesFisherProjectionPDF, vonMisesFisherProjectionPDFReal, ite_eq_left ⟨hd, hκ⟩]
    exact (ENNReal.ofReal_mul (div_nonneg (betaPDFReal_nonneg ha ha _) two_pos.le)).symm
  · have hf : vonMisesFisherProjectionPDF (Module.finrank ℝ E) κ = 0 := by
      funext x
      simp [vonMisesFisherProjectionPDF, vonMisesFisherProjectionPDFReal, hκ]
    simp [vonMisesFisherMeasure_of_neg m (lt_of_not_ge hκ), hf]

/-- The extended projection density has total integral one at every valid parameter. -/
@[simp]
theorem lintegral_vonMisesFisherProjectionPDF_eq_one {d : ℕ} (hd : 2 ≤ d) {κ : ℝ}
    (hκ : 0 ≤ κ) : ∫⁻ x, vonMisesFisherProjectionPDF d κ x = 1 := by
  let m : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by simp⟩
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  have hmap := map_inner_vonMisesFisherMeasure_eq_withDensity (by simpa using hd) m κ
  have hmass := congrArg (fun μ : Measure ℝ ↦ μ univ) hmap
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    finrank_euclideanSpace_fin] using hmass.symm

/-- The real projection density has total integral one at every valid parameter. -/
@[simp]
theorem integral_vonMisesFisherProjectionPDFReal_eq_one {d : ℕ} (hd : 2 ≤ d) {κ : ℝ}
    (hκ : 0 ≤ κ) : ∫ x, vonMisesFisherProjectionPDFReal d κ x = 1 := by
  have hnonneg := ae_of_all volume (vonMisesFisherProjectionPDFReal_nonneg d κ)
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg
    (measurable_vonMisesFisherProjectionPDFReal d κ).aestronglyMeasurable]
  simpa only [vonMisesFisherProjectionPDF_eq_ofReal, ENNReal.toReal_one] using
    congrArg ENNReal.toReal (lintegral_vonMisesFisherProjectionPDF_eq_one hd hκ)

/-- The projection law has the stated Radon–Nikodym derivative relative to Lebesgue measure. -/
theorem rnDeriv_map_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) (κ : ℝ) :
    ((vonMisesFisherMeasure m κ).map (fun x : sphere (0 : E) 1 ↦ ⟪(m : E), (x : E)⟫)).rnDeriv
      volume =ᵐ[volume] vonMisesFisherProjectionPDF (Module.finrank ℝ E) κ := by
  rw [map_inner_vonMisesFisherMeasure_eq_withDensity hd m κ]
  exact Measure.rnDeriv_withDensity _ (measurable_vonMisesFisherProjectionPDF _ _)

/-- The projection lies strictly between the endpoints almost surely. -/
theorem ae_mem_Ioo_map_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} :
    ∀ᵐ y ∂(vonMisesFisherMeasure m κ).map
      (fun x : sphere (0 : E) 1 ↦ ⟪(m : E), (x : E)⟫), y ∈ Ioo (-1) 1 := by
  rw [map_inner_vonMisesFisherMeasure_eq_withDensity hd m κ,
    ae_withDensity_iff (measurable_vonMisesFisherProjectionPDF _ _)]
  refine ae_of_all _ fun y hy ↦ ?_
  by_contra hx
  exact hy (by simp [vonMisesFisherProjectionPDF,
    vonMisesFisherProjectionPDFReal_of_notMem_Ioo hx])

/-- The topological support of the projection is the closed unit interval. -/
theorem support_map_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    ((vonMisesFisherMeasure m κ).map
      (fun x : sphere (0 : E) 1 ↦ ⟪(m : E), (x : E)⟫)).support = Icc (-1) 1 := by
  rw [map_inner_vonMisesFisherMeasure_eq_withDensity hd m κ,
    Measure.support_withDensity_eq_closure (measurable_vonMisesFisherProjectionPDF _ _)
      isOpen_Ioo, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  ext y
  exact ENNReal.ofReal_ne_zero_iff.trans (vonMisesFisherProjectionPDFReal_pos_iff hd hκ y)

/-- The mean-direction projection has a continuous cdf. -/
theorem continuous_cdf_map_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    Continuous (cdf ((vonMisesFisherMeasure m κ).map
      (fun x : sphere (0 : E) 1 ↦ ⟪(m : E), (x : E)⟫))) := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  have : NullSingletonClass ((vonMisesFisherMeasure m κ).map
      (fun x : sphere (0 : E) 1 ↦ ⟪(m : E), (x : E)⟫)) := by
    rw [map_inner_vonMisesFisherMeasure_eq_withDensity hd m κ]
    infer_instance
  exact Measure.continuous_cdf_of_noAtoms _

/-- The projection cdf is zero at and below the lower endpoint. -/
theorem cdf_map_inner_vonMisesFisherMeasure_of_le (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ x : ℝ} (hκ : 0 ≤ κ) (hx : x ≤ -1) :
    cdf ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)) x = 0 := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  exact Measure.cdf_eq_zero_of_ae_lt _
    ((ae_mem_Ioo_map_inner_vonMisesFisherMeasure hd m).mono fun _ hy ↦ hx.trans_lt hy.1)

/-- The projection cdf is one at and above the upper endpoint. -/
theorem cdf_map_inner_vonMisesFisherMeasure_of_ge (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ x : ℝ} (hκ : 0 ≤ κ) (hx : 1 ≤ x) :
    cdf ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)) x = 1 := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  exact Measure.cdf_eq_one_of_ae_le _
    ((ae_mem_Ioo_map_inner_vonMisesFisherMeasure hd m).mono fun _ hy ↦ hy.2.le.trans hx)

/-- The cdf integrates the projection density from the lower endpoint, for every real argument. -/
theorem cdf_map_inner_vonMisesFisherMeasure_eq_integral (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) (x : ℝ) :
    cdf ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)) x =
        ∫ y in (-1)..x, vonMisesFisherProjectionPDFReal (Module.finrank ℝ E) κ y := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  simpa only [cdf_map_inner_vonMisesFisherMeasure_of_le hd m hκ le_rfl, sub_zero] using
    cdf_sub_cdf_eq_integral_of_eq_withDensity
      (map_inner_vonMisesFisherMeasure_eq_withDensity hd m κ)
      (measurable_vonMisesFisherProjectionPDFReal _ _).aemeasurable
      (ae_of_all _ (vonMisesFisherProjectionPDFReal_nonneg (Module.finrank ℝ E) κ)) (-1) x

/-- The projection cdf is strictly increasing on its closed support interval. -/
theorem strictMonoOn_cdf_map_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    StrictMonoOn (cdf ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫))) (Icc (-1) 1) := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  exact Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Icc
    (by rw [support_map_inner_vonMisesFisherMeasure hd m hκ])

/-- The projection cdf is positive exactly above the lower support endpoint. -/
theorem cdf_map_inner_vonMisesFisherMeasure_pos_iff (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ x : ℝ} (hκ : 0 ≤ κ) :
    0 < cdf ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)) x ↔ -1 < x := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  exact Measure.cdf_pos_iff_of_support_eq_Icc _
    (ae_mem_Ioo_map_inner_vonMisesFisherMeasure hd m)
    (support_map_inner_vonMisesFisherMeasure hd m hκ)

/-- The projection cdf is less than one exactly below the upper support endpoint. -/
theorem cdf_map_inner_vonMisesFisherMeasure_lt_one_iff (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ x : ℝ} (hκ : 0 ≤ κ) :
    cdf ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)) x < 1 ↔ x < 1 := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  exact Measure.cdf_lt_one_iff_of_support_eq_Icc _
    (ae_mem_Ioo_map_inner_vonMisesFisherMeasure hd m)
    (support_map_inner_vonMisesFisherMeasure hd m hκ)

/-- Interior projection quantiles lie in the open unit interval. -/
theorem quantile_map_inner_vonMisesFisherMeasure_mem_Ioo (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ u : ℝ} (hκ : 0 ≤ κ) (hu : u ∈ Ioo 0 1) :
    ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)).quantile u ∈ Ioo (-1) 1 := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  exact ordConnected_Ioo.quantile_mem (ae_mem_Ioo_map_inner_vonMisesFisherMeasure hd m)
    hu.1 hu.2

/-- The projection quantile is the unique interior root of the integral cdf. -/
theorem quantile_map_inner_vonMisesFisherMeasure_eq_iff (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ u x : ℝ} (hκ : 0 ≤ κ) (hu : u ∈ Ioo 0 1) :
    ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)).quantile u = x ↔
      x ∈ Ioo (-1) 1 ∧
        (∫ y in (-1)..x, vonMisesFisherProjectionPDFReal (Module.finrank ℝ E) κ y) = u := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  simpa only [cdf_map_inner_vonMisesFisherMeasure_eq_integral hd m hκ] using
    Measure.quantile_eq_iff_of_ae_mem_of_strictMonoOn _ ordConnected_Ioo
      (ae_mem_Ioo_map_inner_vonMisesFisherMeasure hd m)
      (continuous_cdf_map_inner_vonMisesFisherMeasure hd m hκ)
      ((strictMonoOn_cdf_map_inner_vonMisesFisherMeasure hd m hκ).mono Ioo_subset_Icc_self) hu

/-- Projection quantiles are strictly increasing at interior levels. -/
theorem strictMonoOn_quantile_map_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    StrictMonoOn ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)).quantile (Ioo 0 1) := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  exact Measure.strictMonoOn_quantile _ (continuous_cdf_map_inner_vonMisesFisherMeasure hd m hκ)

/-- Projection quantiles are continuous at interior levels. -/
theorem continuousOn_quantile_map_inner_vonMisesFisherMeasure (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    ContinuousOn ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)).quantile (Ioo 0 1) := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  exact Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Icc
    (strictMonoOn_cdf_map_inner_vonMisesFisherMeasure hd m hκ)
    (fun _ hu ↦ Ioo_subset_Icc_self (quantile_map_inner_vonMisesFisherMeasure_mem_Ioo hd m hκ hu))

/-- Projection quantiles tend to the lower support endpoint as the level decreases to zero. -/
theorem tendsto_quantile_map_inner_vonMisesFisherMeasure_nhdsGT_zero
    (hd : 2 ≤ Module.finrank ℝ E) (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)).quantile (𝓝[>] 0) (𝓝 (-1)) := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_mem_Ioo_map_inner_vonMisesFisherMeasure hd m).mono fun _ hy ↦ hy.1.le)
    (fun _ hx ↦ (cdf_map_inner_vonMisesFisherMeasure_pos_iff hd m hκ).2 hx)

/-- Projection quantiles tend to the upper support endpoint as the level increases to one. -/
theorem tendsto_quantile_map_inner_vonMisesFisherMeasure_nhdsLT_one
    (hd : 2 ≤ Module.finrank ℝ E) (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto ((vonMisesFisherMeasure m κ).map
      (fun y : sphere (0 : E) 1 ↦ ⟪(m : E), (y : E)⟫)).quantile (𝓝[<] 1) (𝓝 1) := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one _
    ((ae_mem_Ioo_map_inner_vonMisesFisherMeasure hd m).mono fun _ hy ↦ hy.2.le)
    (fun _ hx ↦ (cdf_map_inner_vonMisesFisherMeasure_lt_one_iff hd m hκ).2 hx)

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → sphere (0 : E) 1} {m : sphere (0 : E) 1} {κ : ℝ}

/-- Projecting a von Mises–Fisher random point onto its direction gives a tilted centered Beta
variable. -/
theorem HasLaw.inner_vonMisesFisherMeasure (hX : HasLaw X (vonMisesFisherMeasure m κ) P)
    (hd : 2 ≤ Module.finrank ℝ E) (hκ : 0 ≤ κ) :
    HasLaw (fun ω ↦ ⟪(m : E), (X ω : E)⟫)
      (((betaMeasure (((Module.finrank ℝ E : ℝ) - 1) / 2)
        (((Module.finrank ℝ E : ℝ) - 1) / 2)).map (fun y ↦ -1 + 2 * y)).tilted
          (fun y ↦ κ * y)) P :=
  (HasLaw.mk (by fun_prop) (map_inner_vonMisesFisherMeasure hd m hκ)).fun_comp hX

/-- The mean-direction projection of a von Mises–Fisher random point has a Lebesgue density. -/
theorem HasLaw.hasPDF_inner_vonMisesFisherMeasure
    (hX : HasLaw X (vonMisesFisherMeasure m κ) P)
    (hd : 2 ≤ Module.finrank ℝ E) :
    HasPDF (fun ω ↦ ⟪(m : E), (X ω : E)⟫) P := by
  apply hasPDF_of_hasLaw_withDensity (measurable_vonMisesFisherProjectionPDF _ _).aemeasurable
  rw [← map_inner_vonMisesFisherMeasure_eq_withDensity hd m κ]
  exact (hasLaw_map (X := fun x : sphere (0 : E) 1 ↦ ⟪(m : E), (x : E)⟫)
    (by fun_prop)).comp hX

end ProbabilityTheory
