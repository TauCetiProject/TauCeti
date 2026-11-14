/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Censoring
public import TauCeti.Probability.Distributions.TruncatedNormal.Basic
import TauCeti.Probability.Distributions.TruncatedNormal.Moments

/-!
# Censored Gaussian laws and contrast with conditional truncation

Projecting a Gaussian random variable `X ∼ N(m, v)` onto a closed interval `[l, r]` (or onto a
closed half-line `[l, ∞)` or `(-∞, r]`) produces a censored Gaussian law: the probability mass of
each clipped tail becomes a point mass at the corresponding boundary point, while the restriction
to the open interior remains unchanged.

This pushforward is distinct from conditional truncation (`truncatedNormalMeasure m v s`), which
conditions `N(m, v)` on `s` and renormalizes the surviving density:

* At positive variance, `truncatedNormalMeasure m v s` has null singletons for every conditioning
  set `s` (`nullSingletonClass_truncatedNormalMeasure`) and its cumulative distribution function
  is globally continuous when `s` has positive Gaussian mass
  (`continuous_cdf_truncatedNormalMeasure`).
* By contrast, at positive variance and for `l < r`, the two-sided censored Gaussian law puts
  positive point masses `Φ ((l - m) / √v)` at `l` and `Φ ((m - r) / √v)` at `r`, and zero mass on
  every other singleton (`map_coe_projIcc_gaussianReal_singleton_ne_zero_iff`). Across all
  variances `v : ℝ≥0` (including the Dirac boundary `v = 0`) and all `l ≤ r`, a censored Gaussian
  law never has null singletons (`not_nullSingletonClass_map_coe_projIcc_gaussianReal`), its cdf is
  never continuous (`not_continuous_cdf_map_coe_projIcc_gaussianReal`), and it never coincides with
  any positive-variance `truncatedNormalMeasure`
  (`map_coe_projIcc_gaussianReal_ne_truncatedNormalMeasure`). The same contrast holds for one-sided
  lower and upper censoring via `Set.projIci` and `Set.projIic`.

Combining the moment decompositions of `TauCeti.Probability.Distributions.Censoring` with the
interval-truncated Gaussian mean from `TauCeti.Probability.Distributions.TruncatedNormal.Moments`
also yields closed-form expectations for two-sided and one-sided censored Gaussian laws across all
variances `v : ℝ≥0`.

## Main results

* `TauCeti.Probability.map_coe_projIcc_gaussianReal_real_singleton_left` and
  `TauCeti.Probability.map_coe_projIcc_gaussianReal_real_singleton_right` — standardized endpoint
  atom weights `Φ ((l - m) / √v)` and `Φ ((m - r) / √v)` for `l < r` and `v ≠ 0`;
* `TauCeti.Probability.map_coe_projIcc_gaussianReal_singleton_ne_zero_iff` — at positive variance,
  the atoms of the `[l, r]`-clipped Gaussian law are precisely `{l, r}`;
* `TauCeti.Probability.not_nullSingletonClass_map_coe_projIcc_gaussianReal` and
  `TauCeti.Probability.map_coe_projIcc_gaussianReal_ne_truncatedNormalMeasure` — censored Gaussian
  laws never have null singletons and are distinct from every positive-variance truncated normal
  law (with one-sided counterparts for `Set.projIci` and `Set.projIic`);
* `TauCeti.Probability.continuousAt_cdf_map_coe_projIcc_gaussianReal_iff` and
  `TauCeti.Probability.not_continuous_cdf_map_coe_projIcc_gaussianReal` — exact cdf continuity
  locus away from the clipping endpoints;
* `TauCeti.Probability.integral_id_map_coe_projIcc_gaussianReal`,
  `TauCeti.Probability.integral_id_map_coe_projIci_gaussianReal`, and
  `TauCeti.Probability.integral_id_map_coe_projIic_gaussianReal` — closed-form means of two-sided
  and one-sided censored Gaussian laws.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

local notation "clip[" l ", " r "; " h "]" =>
  (fun x : ℝ ↦ (Set.projIcc l r h x : ℝ))

/-! ### Two-sided censored Gaussian laws -/

/-- At zero variance, projecting `gaussianReal m 0` onto `[l, r]` gives the Dirac mass at the
projected mean. -/
theorem map_coe_projIcc_gaussianReal_zero_var (m : ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (gaussianReal m 0).map clip[l, r; hlr] = Measure.dirac (clip[l, r; hlr] m) := by
  rw [gaussianReal_zero_var, Measure.map_dirac' (by fun_prop)]

/-- At positive variance and for `l < r`, the real mass of the lower endpoint atom `{l}` of the
`[l, r]`-censored Gaussian law is `Φ ((l - m) / √v)`. -/
theorem map_coe_projIcc_gaussianReal_real_singleton_left (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {l r : ℝ} (hlr : l < r) :
    ((gaussianReal m v).map clip[l, r; hlr.le]).real {l} =
      cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ)) := by
  rw [Measure.map_coe_projIcc_real_singleton_left _ hlr, ← cdf_eq_real,
    cdf_gaussianReal_eq_cdf_zero_one m hv l]

/-- At positive variance and for `l < r`, the real mass of the upper endpoint atom `{r}` of the
`[l, r]`-censored Gaussian law is `Φ ((m - r) / √v)`. -/
theorem map_coe_projIcc_gaussianReal_real_singleton_right (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {l r : ℝ} (hlr : l < r) :
    ((gaussianReal m v).map clip[l, r; hlr.le]).real {r} =
      cdf (gaussianReal 0 1) ((m - r) / √(v : ℝ)) := by
  rw [Measure.map_coe_projIcc_real_singleton_right _ hlr,
    measureReal_Ici_gaussianReal_eq_cdf m hv r]

/-- At positive variance and for any `l ≤ r`, the singletons of nonzero mass under the
`[l, r]`-censored Gaussian law are precisely the endpoints `l` and `r`. -/
theorem map_coe_projIcc_gaussianReal_singleton_ne_zero_iff (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {l r : ℝ} (hlr : l ≤ r) (x : ℝ) :
    (gaussianReal m v).map clip[l, r; hlr] {x} ≠ 0 ↔ x = l ∨ x = r := by
  have := nullSingletonClass_gaussianReal (μ := m) hv
  rcases hlr.eq_or_lt with rfl | hlt
  · rw [Measure.map_coe_projIcc_self, measure_univ, one_smul, or_self]
    by_cases hx : x = l
    · subst hx
      simp
    · simp [Measure.dirac_apply' _ (measurableSet_singleton x), hx]
  · by_cases hxl : x = l
    · subst hxl
      refine iff_of_true ?_ (Or.inl rfl)
      rw [Measure.map_coe_projIcc_singleton_left _ hlt]
      exact (gaussianReal_Iic_pos m hv x).ne'
    · by_cases hxr : x = r
      · subst hxr
        refine iff_of_true ?_ (Or.inr rfl)
        rw [Measure.map_coe_projIcc_singleton_right _ hlt]
        exact (gaussianReal_Ici_pos m hv x).ne'
      · refine iff_of_false ?_ (not_or.mpr ⟨hxl, hxr⟩)
        by_cases hxI : x ∈ Icc l r
        · have hxIoo : x ∈ Ioo l r :=
            ⟨lt_of_le_of_ne hxI.1 (Ne.symm hxl), lt_of_le_of_ne hxI.2 hxr⟩
          simp [Measure.map_coe_projIcc_singleton_of_mem_Ioo _ hlt.le hxIoo]
        · simp [Measure.map_coe_projIcc_singleton_of_notMem_Icc _ hlt.le hxI]

/-- At positive variance, the lower endpoint `l` carries positive mass under `[l, r]`-censoring. -/
theorem map_coe_projIcc_gaussianReal_singleton_left_pos (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {l r : ℝ} (hlr : l ≤ r) :
    0 < (gaussianReal m v).map clip[l, r; hlr] {l} :=
  pos_iff_ne_zero.mpr
    ((map_coe_projIcc_gaussianReal_singleton_ne_zero_iff m hv hlr l).mpr (Or.inl rfl))

/-- At positive variance, the upper endpoint `r` carries positive mass under `[l, r]`-censoring. -/
theorem map_coe_projIcc_gaussianReal_singleton_right_pos (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {l r : ℝ} (hlr : l ≤ r) :
    0 < (gaussianReal m v).map clip[l, r; hlr] {r} :=
  pos_iff_ne_zero.mpr
    ((map_coe_projIcc_gaussianReal_singleton_ne_zero_iff m hv hlr r).mpr (Or.inr rfl))

/-- Across all parameters `m`, `v` (including `v = 0`) and all `l ≤ r`, the `[l, r]`-censored
Gaussian law never has null singletons. -/
theorem not_nullSingletonClass_map_coe_projIcc_gaussianReal (m : ℝ) (v : ℝ≥0)
    {l r : ℝ} (hlr : l ≤ r) :
    ¬ NullSingletonClass ((gaussianReal m v).map clip[l, r; hlr]) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [map_coe_projIcc_gaussianReal_zero_var]
    exact Measure.not_nullSingletonClass_dirac _
  · have := nullSingletonClass_gaussianReal (μ := m) hv
    rw [Measure.nullSingletonClass_map_coe_projIcc_iff_of_nullSingletonClass _ hlr]
    exact fun h ↦ (gaussianReal_Iic_pos m hv l).ne' h.1

/-- No `[l, r]`-censored Gaussian law (even at zero variance) equals a positive-variance
conditionally truncated normal law `truncatedNormalMeasure m' v' s` for any set `s`. -/
theorem map_coe_projIcc_gaussianReal_ne_truncatedNormalMeasure (m m' : ℝ) (v : ℝ≥0)
    {v' : ℝ≥0} (hv' : v' ≠ 0) {l r : ℝ} (hlr : l ≤ r) (s : Set ℝ) :
    (gaussianReal m v).map clip[l, r; hlr] ≠ truncatedNormalMeasure m' v' s := fun h ↦
  not_nullSingletonClass_map_coe_projIcc_gaussianReal m v hlr
    (h ▸ nullSingletonClass_truncatedNormalMeasure m' hv' s)

/-- At positive variance, the cdf of the `[l, r]`-censored Gaussian law vanishes below `l`,
equals the unrescaled standard Gaussian cdf `Φ ((x - m) / √v)` on `[l, r)`, and equals `1` from
`r` onwards. -/
theorem cdf_map_coe_projIcc_gaussianReal_eq_cdf_zero_one (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {l r : ℝ} (hlr : l ≤ r) (x : ℝ) :
    cdf ((gaussianReal m v).map clip[l, r; hlr]) x =
      if x < l then 0 else if x < r then cdf (gaussianReal 0 1) ((x - m) / √(v : ℝ)) else 1 := by
  rw [Measure.cdf_map_coe_projIcc _ hlr x, cdf_gaussianReal_eq_cdf_zero_one m hv x]

/-- At positive variance, the cdf of the `[l, r]`-censored Gaussian law is continuous at `x` if
and only if `x` is neither endpoint `l` nor `r`. -/
theorem continuousAt_cdf_map_coe_projIcc_gaussianReal_iff (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {l r : ℝ} (hlr : l ≤ r) (x : ℝ) :
    ContinuousAt (cdf ((gaussianReal m v).map clip[l, r; hlr])) x ↔ x ≠ l ∧ x ≠ r := by
  have : IsProbabilityMeasure ((gaussianReal m v).map clip[l, r; hlr]) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  rw [Measure.continuousAt_cdf_iff, ← not_ne_iff,
    map_coe_projIcc_gaussianReal_singleton_ne_zero_iff m hv hlr x, not_or]

/-- Across all parameters `m`, `v` (including `v = 0`) and all `l ≤ r`, the cdf of the
`[l, r]`-censored Gaussian law is not continuous. -/
theorem not_continuous_cdf_map_coe_projIcc_gaussianReal (m : ℝ) (v : ℝ≥0)
    {l r : ℝ} (hlr : l ≤ r) :
    ¬ Continuous (cdf ((gaussianReal m v).map clip[l, r; hlr])) := by
  have : IsProbabilityMeasure ((gaussianReal m v).map clip[l, r; hlr]) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  intro hc
  refine not_nullSingletonClass_map_coe_projIcc_gaussianReal m v hlr ⟨fun x ↦ ?_⟩
  exact (Measure.continuousAt_cdf_iff _ x).mp hc.continuousAt

/-- For every interior probability level `0 < u < 1` and every variance `v : ℝ≥0` (including
`v = 0`), the quantile of the `[l, r]`-censored Gaussian law is the projection onto `[l, r]` of
`m + √v * z u`, where `z` is the standard Gaussian quantile. -/
theorem quantile_map_coe_projIcc_gaussianReal (m : ℝ) (v : ℝ≥0) {l r u : ℝ} (hlr : l ≤ r)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    ((gaussianReal m v).map clip[l, r; hlr]).quantile u =
      clip[l, r; hlr] (m + √(v : ℝ) * (gaussianReal 0 1).quantile u) := by
  rw [Measure.quantile_map_coe_projIcc _ hlr hu, quantile_gaussianReal_eq_add_mul m v hu]

/-! ### Closed-form means via interval-truncated Gaussian moments -/

/-- For every variance `v : ℝ≥0` (including `v = 0`) and any `l ≤ r`, the expectation of the
`[l, r]`-censored Gaussian law combines the two endpoint atom contributions with the interior
Gaussian contribution. -/
theorem integral_id_map_coe_projIcc_gaussianReal (m : ℝ) (v : ℝ≥0) {l r : ℝ} (hlr : l ≤ r) :
    ∫ x : ℝ, x ∂((gaussianReal m v).map clip[l, r; hlr]) =
      cdf (gaussianReal m v) l * l +
        m * (cdf (gaussianReal m v) r - cdf (gaussianReal m v) l) +
        v * (gaussianPDFReal m v l - gaussianPDFReal m v r) +
        (1 - cdf (gaussianReal m v) r) * r := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [map_coe_projIcc_gaussianReal_zero_var, integral_dirac]
    simp only [Set.coe_projIcc, cdf_gaussianReal_zero, NNReal.coe_zero, zero_mul, add_zero]
    split_ifs <;> grind
  · rcases hlr.eq_or_lt with rfl | hlt
    · rw [Measure.map_coe_projIcc_self, measure_univ, one_smul, integral_dirac]
      ring
    · have := nullSingletonClass_gaussianReal (μ := m) hv
      have hint := setIntegral_id_gaussianReal m v (s := Ioo l r)
        (EReal.coe_le_coe_iff.2 hlt.le) (by rw [EReal.preimage_coe_Ioo])
        (by rw [EReal.preimage_coe_Icc]; exact Ioo_subset_Icc_self)
      have hmass : (gaussianReal m v).real (Ioo l r) =
          cdf (gaussianReal m v) r - cdf (gaussianReal m v) l := by
        rw [Measure.measureReal_eq_sub_of_preimage_Ioo_subset (l := (l : EReal)) (r := (r : EReal))
          (EReal.coe_le_coe_iff.2 hlt.le) (by rw [EReal.preimage_coe_Ioo])
          (by rw [EReal.preimage_coe_Icc]; exact Ioo_subset_Icc_self)]
        simp [← cdf_eq_real]
      rw [Measure.integral_id_map_coe_projIcc _ hlt, ← cdf_eq_real,
        Measure.measureReal_Ici_eq_one_sub_cdf, hint, hmass, gaussianPDFRealEReal_coe,
        gaussianPDFRealEReal_coe]
      ring

/-! ### Lower-censored Gaussian laws -/

/-- At zero variance, lower censoring `gaussianReal m 0` at `l` gives the Dirac mass at
`max l m`. -/
theorem map_coe_projIci_gaussianReal_zero_var (m l : ℝ) :
    (gaussianReal m 0).map (fun x : ℝ ↦ (Set.projIci l x : ℝ)) =
      Measure.dirac (Set.projIci l m : ℝ) := by
  rw [gaussianReal_zero_var, Measure.map_dirac' (by simp only [Set.coe_projIci]; fun_prop)]

/-- At positive variance, the real mass of the cutoff atom `{l}` of the lower-censored Gaussian
law is `Φ ((l - m) / √v)`. -/
theorem map_coe_projIci_gaussianReal_real_singleton_self (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (l : ℝ) :
    ((gaussianReal m v).map fun x : ℝ ↦ (Set.projIci l x : ℝ)).real {l} =
      cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ)) := by
  rw [Measure.map_coe_projIci_real_singleton_self, ← cdf_eq_real,
    cdf_gaussianReal_eq_cdf_zero_one m hv l]

/-- At positive variance, `{l}` is the unique singleton of nonzero mass under lower censoring at
`l`. -/
theorem map_coe_projIci_gaussianReal_singleton_ne_zero_iff (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (l x : ℝ) :
    (gaussianReal m v).map (fun y : ℝ ↦ (Set.projIci l y : ℝ)) {x} ≠ 0 ↔ x = l := by
  have := nullSingletonClass_gaussianReal (μ := m) hv
  rcases lt_trichotomy x l with hxl | rfl | hlx
  · exact iff_of_false
      (by simp [Measure.map_coe_projIci_singleton_of_notMem_Ici _ (not_le.mpr hxl)]) hxl.ne
  · exact iff_of_true
      (by rw [Measure.map_coe_projIci_singleton_self]; exact (gaussianReal_Iic_pos m hv x).ne')
      rfl
  · exact iff_of_false
      (by simp [Measure.map_coe_projIci_singleton_of_mem_Ioi _ hlx]) hlx.ne'

/-- At positive variance, the cutoff `l` carries positive mass under lower censoring. -/
theorem map_coe_projIci_gaussianReal_singleton_self_pos (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (l : ℝ) :
    0 < (gaussianReal m v).map (fun y : ℝ ↦ (Set.projIci l y : ℝ)) {l} :=
  pos_iff_ne_zero.mpr ((map_coe_projIci_gaussianReal_singleton_ne_zero_iff m hv l l).mpr rfl)

/-- Across all parameters `m`, `v` (including `v = 0`) and `l`, the lower-censored Gaussian law
never has null singletons. -/
theorem not_nullSingletonClass_map_coe_projIci_gaussianReal (m : ℝ) (v : ℝ≥0) (l : ℝ) :
    ¬ NullSingletonClass ((gaussianReal m v).map fun x : ℝ ↦ (Set.projIci l x : ℝ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [map_coe_projIci_gaussianReal_zero_var]
    exact Measure.not_nullSingletonClass_dirac _
  · have := nullSingletonClass_gaussianReal (μ := m) hv
    rw [Measure.nullSingletonClass_map_coe_projIci_iff_of_nullSingletonClass]
    exact (gaussianReal_Iic_pos m hv l).ne'

/-- No lower-censored Gaussian law equals a positive-variance `truncatedNormalMeasure`. -/
theorem map_coe_projIci_gaussianReal_ne_truncatedNormalMeasure (m m' : ℝ) (v : ℝ≥0)
    {v' : ℝ≥0} (hv' : v' ≠ 0) (l : ℝ) (s : Set ℝ) :
    (gaussianReal m v).map (fun x : ℝ ↦ (Set.projIci l x : ℝ)) ≠
      truncatedNormalMeasure m' v' s := fun h ↦
  not_nullSingletonClass_map_coe_projIci_gaussianReal m v l
    (h ▸ nullSingletonClass_truncatedNormalMeasure m' hv' s)

/-- At positive variance, the cdf of the lower-censored Gaussian law vanishes below `l` and equals
`Φ ((x - m) / √v)` from `l` onwards. -/
theorem cdf_map_coe_projIci_gaussianReal_eq_cdf_zero_one (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (l x : ℝ) :
    cdf ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIci l y : ℝ)) x =
      if x < l then 0 else cdf (gaussianReal 0 1) ((x - m) / √(v : ℝ)) := by
  rw [Measure.cdf_map_coe_projIci _ l x, cdf_gaussianReal_eq_cdf_zero_one m hv x]

/-- At positive variance, the cdf of the lower-censored Gaussian law at `l` is continuous at `x`
if and only if `x ≠ l`. -/
theorem continuousAt_cdf_map_coe_projIci_gaussianReal_iff (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (l x : ℝ) :
    ContinuousAt (cdf ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIci l y : ℝ))) x ↔ x ≠ l := by
  have : IsProbabilityMeasure ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIci l y : ℝ)) :=
    (Measure.isProbabilityMeasure_map_iff (by simp only [Set.coe_projIci]; fun_prop)).mpr
      inferInstance
  rw [Measure.continuousAt_cdf_iff, ← not_ne_iff,
    map_coe_projIci_gaussianReal_singleton_ne_zero_iff m hv l x]

/-- Across all parameters `m`, `v` and `l`, the cdf of the lower-censored Gaussian law is not
continuous. -/
theorem not_continuous_cdf_map_coe_projIci_gaussianReal (m : ℝ) (v : ℝ≥0) (l : ℝ) :
    ¬ Continuous (cdf ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIci l y : ℝ))) := by
  have : IsProbabilityMeasure ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIci l y : ℝ)) :=
    (Measure.isProbabilityMeasure_map_iff (by simp only [Set.coe_projIci]; fun_prop)).mpr
      inferInstance
  intro hc
  refine not_nullSingletonClass_map_coe_projIci_gaussianReal m v l ⟨fun x ↦ ?_⟩
  exact (Measure.continuousAt_cdf_iff _ x).mp hc.continuousAt

/-- For every interior probability level `0 < u < 1` and every variance `v : ℝ≥0`, lower censoring
takes the Gaussian quantile to `max l (m + √v * z u)`. -/
theorem quantile_map_coe_projIci_gaussianReal (m : ℝ) (v : ℝ≥0) (l : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIci l y : ℝ)).quantile u =
      (Set.projIci l (m + √(v : ℝ) * (gaussianReal 0 1).quantile u) : ℝ) := by
  rw [Measure.quantile_map_coe_projIci _ l hu, quantile_gaussianReal_eq_add_mul m v hu]

/-- For every variance `v : ℝ≥0` (including `v = 0`), the expectation of the Gaussian law
lower-censored at `l` is `F(l) * l + m * (1 - F(l)) + v * gaussianPDFReal m v l`, where
`F = cdf (gaussianReal m v)`. -/
theorem integral_id_map_coe_projIci_gaussianReal (m : ℝ) (v : ℝ≥0) (l : ℝ) :
    ∫ x : ℝ, x ∂((gaussianReal m v).map fun y : ℝ ↦ (Set.projIci l y : ℝ)) =
      cdf (gaussianReal m v) l * l + m * (1 - cdf (gaussianReal m v) l) +
        v * gaussianPDFReal m v l := by
  have hint : Integrable id ((gaussianReal m v).restrict (Ioi l)) :=
    ((memLp_id_gaussianReal' (μ := m) (v := v) 1 (by simp)).integrable le_rfl).restrict
  have htail := setIntegral_id_gaussianReal m v (s := Ioi l) (EReal.coe_lt_top l).le
    (fun x hx ↦ EReal.coe_lt_coe_iff.1 hx.1)
    (fun x (hx : l < x) ↦ ⟨(EReal.coe_lt_coe_iff.2 hx).le, le_top⟩)
  rw [Measure.integral_id_map_coe_projIci _ l hint, ← cdf_eq_real, htail,
    Measure.measureReal_Ioi_eq_one_sub_cdf, gaussianPDFRealEReal_coe, gaussianPDFRealEReal_top]
  ring

/-! ### Upper-censored Gaussian laws -/

/-- At zero variance, upper censoring `gaussianReal m 0` at `r` gives the Dirac mass at
`min r m`. -/
theorem map_coe_projIic_gaussianReal_zero_var (m r : ℝ) :
    (gaussianReal m 0).map (fun x : ℝ ↦ (Set.projIic r x : ℝ)) =
      Measure.dirac (Set.projIic r m : ℝ) := by
  rw [gaussianReal_zero_var, Measure.map_dirac' (by simp only [Set.coe_projIic]; fun_prop)]

/-- At positive variance, the real mass of the cutoff atom `{r}` of the upper-censored Gaussian
law is `Φ ((m - r) / √v)`. -/
theorem map_coe_projIic_gaussianReal_real_singleton_self (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (r : ℝ) :
    ((gaussianReal m v).map fun x : ℝ ↦ (Set.projIic r x : ℝ)).real {r} =
      cdf (gaussianReal 0 1) ((m - r) / √(v : ℝ)) := by
  rw [Measure.map_coe_projIic_real_singleton_self,
    measureReal_Ici_gaussianReal_eq_cdf m hv r]

/-- At positive variance, `{r}` is the unique singleton of nonzero mass under upper censoring at
`r`. -/
theorem map_coe_projIic_gaussianReal_singleton_ne_zero_iff (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (r x : ℝ) :
    (gaussianReal m v).map (fun y : ℝ ↦ (Set.projIic r y : ℝ)) {x} ≠ 0 ↔ x = r := by
  have := nullSingletonClass_gaussianReal (μ := m) hv
  rcases lt_trichotomy x r with hxr | rfl | hrx
  · exact iff_of_false
      (by simp [Measure.map_coe_projIic_singleton_of_mem_Iio _ hxr]) hxr.ne
  · exact iff_of_true
      (by rw [Measure.map_coe_projIic_singleton_self]; exact (gaussianReal_Ici_pos m hv x).ne')
      rfl
  · exact iff_of_false
      (by simp [Measure.map_coe_projIic_singleton_of_notMem_Iic _ (not_le.mpr hrx)]) hrx.ne'

/-- At positive variance, the cutoff `r` carries positive mass under upper censoring. -/
theorem map_coe_projIic_gaussianReal_singleton_self_pos (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (r : ℝ) :
    0 < (gaussianReal m v).map (fun y : ℝ ↦ (Set.projIic r y : ℝ)) {r} :=
  pos_iff_ne_zero.mpr ((map_coe_projIic_gaussianReal_singleton_ne_zero_iff m hv r r).mpr rfl)

/-- Across all parameters `m`, `v` (including `v = 0`) and `r`, the upper-censored Gaussian law
never has null singletons. -/
theorem not_nullSingletonClass_map_coe_projIic_gaussianReal (m : ℝ) (v : ℝ≥0) (r : ℝ) :
    ¬ NullSingletonClass ((gaussianReal m v).map fun x : ℝ ↦ (Set.projIic r x : ℝ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [map_coe_projIic_gaussianReal_zero_var]
    exact Measure.not_nullSingletonClass_dirac _
  · have := nullSingletonClass_gaussianReal (μ := m) hv
    rw [Measure.nullSingletonClass_map_coe_projIic_iff_of_nullSingletonClass]
    exact (gaussianReal_Ici_pos m hv r).ne'

/-- No upper-censored Gaussian law equals a positive-variance `truncatedNormalMeasure`. -/
theorem map_coe_projIic_gaussianReal_ne_truncatedNormalMeasure (m m' : ℝ) (v : ℝ≥0)
    {v' : ℝ≥0} (hv' : v' ≠ 0) (r : ℝ) (s : Set ℝ) :
    (gaussianReal m v).map (fun x : ℝ ↦ (Set.projIic r x : ℝ)) ≠
      truncatedNormalMeasure m' v' s := fun h ↦
  not_nullSingletonClass_map_coe_projIic_gaussianReal m v r
    (h ▸ nullSingletonClass_truncatedNormalMeasure m' hv' s)

/-- At positive variance, the cdf of the upper-censored Gaussian law equals `Φ ((x - m) / √v)`
below `r` and `1` from `r` onwards. -/
theorem cdf_map_coe_projIic_gaussianReal_eq_cdf_zero_one (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (r x : ℝ) :
    cdf ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIic r y : ℝ)) x =
      if x < r then cdf (gaussianReal 0 1) ((x - m) / √(v : ℝ)) else 1 := by
  rw [Measure.cdf_map_coe_projIic _ r x, cdf_gaussianReal_eq_cdf_zero_one m hv x]

/-- At positive variance, the cdf of the upper-censored Gaussian law at `r` is continuous at `x`
if and only if `x ≠ r`. -/
theorem continuousAt_cdf_map_coe_projIic_gaussianReal_iff (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (r x : ℝ) :
    ContinuousAt (cdf ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIic r y : ℝ))) x ↔ x ≠ r := by
  have : IsProbabilityMeasure ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIic r y : ℝ)) :=
    (Measure.isProbabilityMeasure_map_iff (by simp only [Set.coe_projIic]; fun_prop)).mpr
      inferInstance
  rw [Measure.continuousAt_cdf_iff, ← not_ne_iff,
    map_coe_projIic_gaussianReal_singleton_ne_zero_iff m hv r x]

/-- Across all parameters `m`, `v` and `r`, the cdf of the upper-censored Gaussian law is not
continuous. -/
theorem not_continuous_cdf_map_coe_projIic_gaussianReal (m : ℝ) (v : ℝ≥0) (r : ℝ) :
    ¬ Continuous (cdf ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIic r y : ℝ))) := by
  have : IsProbabilityMeasure ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIic r y : ℝ)) :=
    (Measure.isProbabilityMeasure_map_iff (by simp only [Set.coe_projIic]; fun_prop)).mpr
      inferInstance
  intro hc
  refine not_nullSingletonClass_map_coe_projIic_gaussianReal m v r ⟨fun x ↦ ?_⟩
  exact (Measure.continuousAt_cdf_iff _ x).mp hc.continuousAt

/-- For every interior probability level `0 < u < 1` and every variance `v : ℝ≥0`, upper censoring
takes the Gaussian quantile to `min r (m + √v * z u)`. -/
theorem quantile_map_coe_projIic_gaussianReal (m : ℝ) (v : ℝ≥0) (r : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIic r y : ℝ)).quantile u =
      (Set.projIic r (m + √(v : ℝ) * (gaussianReal 0 1).quantile u) : ℝ) := by
  rw [Measure.quantile_map_coe_projIic _ r hu, quantile_gaussianReal_eq_add_mul m v hu]

/-- For every variance `v : ℝ≥0` (including `v = 0`), the expectation of the Gaussian law
upper-censored at `r` is `m * F(r) - v * gaussianPDFReal m v r + (1 - F(r)) * r`, where
`F = cdf (gaussianReal m v)`. -/
theorem integral_id_map_coe_projIic_gaussianReal (m : ℝ) (v : ℝ≥0) (r : ℝ) :
    ∫ x : ℝ, x ∂((gaussianReal m v).map fun y : ℝ ↦ (Set.projIic r y : ℝ)) =
      m * cdf (gaussianReal m v) r - v * gaussianPDFReal m v r +
        (1 - cdf (gaussianReal m v) r) * r := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [map_coe_projIic_gaussianReal_zero_var, integral_dirac]
    simp only [Set.coe_projIic, cdf_gaussianReal_zero, NNReal.coe_zero, zero_mul, sub_zero]
    split_ifs <;> grind
  · have := nullSingletonClass_gaussianReal (μ := m) hv
    have hint : Integrable id ((gaussianReal m v).restrict (Iio r)) :=
      ((memLp_id_gaussianReal' (μ := m) (v := v) 1 (by simp)).integrable le_rfl).restrict
    have htail := setIntegral_id_gaussianReal m v (s := Iio r) (EReal.bot_lt_coe r).le
      (fun x hx ↦ EReal.coe_lt_coe_iff.1 hx.2)
      (fun x (hx : x < r) ↦ ⟨bot_le, (EReal.coe_lt_coe_iff.2 hx).le⟩)
    rw [measureReal_congr (Iio_ae_eq_Iic (μ := gaussianReal m v) (a := r)),
      ← cdf_eq_real] at htail
    rw [Measure.integral_id_map_coe_projIic _ r hint, htail,
      Measure.measureReal_Ici_eq_one_sub_cdf, gaussianPDFRealEReal_bot, gaussianPDFRealEReal_coe]
    ring

end TauCeti.Probability
