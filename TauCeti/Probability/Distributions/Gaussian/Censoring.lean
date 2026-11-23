/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Censoring
public import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# Censored Gaussian laws

Projecting a Gaussian random variable `X ∼ N(m, v)` onto a closed interval `[l, r]` (or onto a
closed half-line `[l, ∞)` or `(-∞, r]`) produces a censored Gaussian law: the probability mass of
each clipped tail becomes a point mass at the corresponding boundary point, while the restriction
to the open interior remains unchanged.

At positive variance and for `l < r`, the two-sided censored Gaussian law puts positive point
masses `Φ ((l - m) / √v)` at `l` and `Φ ((m - r) / √v)` at `r`, and zero mass on every other
singleton (`map_coe_projIcc_gaussianReal_singleton_ne_zero_iff`). Across all variances `v : ℝ≥0`
(including the Dirac boundary `v = 0`) and all `l ≤ r`, a censored Gaussian law never has null
singletons (`not_nullSingletonClass_map_coe_projIcc_gaussianReal`) and its cumulative distribution
function is never continuous (`not_continuous_cdf_map_coe_projIcc_gaussianReal`). The same
phenomena hold for one-sided lower and upper censoring via `Set.projIci` and `Set.projIic`. For the
structural contrast with positive-variance conditionally truncated normal laws
(`truncatedNormalMeasure`), see `TauCeti.Probability.Distributions.TruncatedNormal.Censoring`.

## Main results

* `TauCeti.Probability.map_coe_projIcc_gaussianReal_real_singleton_left` and
  `TauCeti.Probability.map_coe_projIcc_gaussianReal_real_singleton_right` — standardized endpoint
  atom weights `Φ ((l - m) / √v)` and `Φ ((m - r) / √v)` for `l < r` and `v ≠ 0`;
* `TauCeti.Probability.map_coe_projIcc_gaussianReal_singleton_ne_zero_iff` — at positive variance,
  the atoms of the `[l, r]`-clipped Gaussian law are precisely `{l, r}`;
* `TauCeti.Probability.not_nullSingletonClass_map_coe_projIcc_gaussianReal`,
  `TauCeti.Probability.not_nullSingletonClass_map_coe_projIci_gaussianReal`, and
  `TauCeti.Probability.not_nullSingletonClass_map_coe_projIic_gaussianReal` — censored Gaussian
  laws never have null singletons;
* `TauCeti.Probability.continuousAt_cdf_map_coe_projIcc_gaussianReal_iff` and
  `TauCeti.Probability.not_continuous_cdf_map_coe_projIcc_gaussianReal` — exact cdf continuity
  locus away from the clipping endpoints (with one-sided counterparts).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

local notation "clip[" l ", " r "; " h "]" =>
  (fun x : ℝ ↦ (Set.projIcc l r h x : ℝ))

/-! ### Two-sided censored Gaussian laws -/

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
  simp [Measure.map_coe_projIcc_singleton_ne_zero_iff_of_nullSingletonClass _ hlr x,
    (gaussianReal_Iic_pos m hv l).ne', (gaussianReal_Ici_pos m hv r).ne']

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
@[simp]
theorem not_nullSingletonClass_map_coe_projIcc_gaussianReal (m : ℝ) (v : ℝ≥0)
    {l r : ℝ} (hlr : l ≤ r) :
    ¬ NullSingletonClass ((gaussianReal m v).map clip[l, r; hlr]) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var, Measure.map_dirac' (by fun_prop)]
    exact not_nullSingletonClass_dirac _
  · have := nullSingletonClass_gaussianReal (μ := m) hv
    rw [Measure.nullSingletonClass_map_coe_projIcc_iff_of_nullSingletonClass _ hlr]
    exact fun h ↦ (gaussianReal_Iic_pos m hv l).ne' h.1

/-- At positive variance, the cdf of the `[l, r]`-censored Gaussian law is continuous at `x` if
and only if `x` is neither endpoint `l` nor `r`. -/
theorem continuousAt_cdf_map_coe_projIcc_gaussianReal_iff (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {l r : ℝ} (hlr : l ≤ r) (x : ℝ) :
    ContinuousAt (cdf ((gaussianReal m v).map clip[l, r; hlr])) x ↔ x ≠ l ∧ x ≠ r := by
  have := nullSingletonClass_gaussianReal (μ := m) hv
  simp [Measure.continuousAt_cdf_map_coe_projIcc_iff_of_nullSingletonClass _ hlr x,
    (gaussianReal_Iic_pos m hv l).ne', (gaussianReal_Ici_pos m hv r).ne']

/-- Across all parameters `m`, `v` (including `v = 0`) and all `l ≤ r`, the cdf of the
`[l, r]`-censored Gaussian law is not continuous. -/
theorem not_continuous_cdf_map_coe_projIcc_gaussianReal (m : ℝ) (v : ℝ≥0)
    {l r : ℝ} (hlr : l ≤ r) :
    ¬ Continuous (cdf ((gaussianReal m v).map clip[l, r; hlr])) := by
  rw [Measure.continuous_cdf_iff]
  exact not_nullSingletonClass_map_coe_projIcc_gaussianReal m v hlr

/-! ### Lower-censored Gaussian laws -/

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
  simp [Measure.map_coe_projIci_singleton_ne_zero_iff_of_nullSingletonClass _ l x,
    (gaussianReal_Iic_pos m hv l).ne']

/-- At positive variance, the cutoff `l` carries positive mass under lower censoring. -/
theorem map_coe_projIci_gaussianReal_singleton_self_pos (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (l : ℝ) :
    0 < (gaussianReal m v).map (fun y : ℝ ↦ (Set.projIci l y : ℝ)) {l} :=
  pos_iff_ne_zero.mpr ((map_coe_projIci_gaussianReal_singleton_ne_zero_iff m hv l l).mpr rfl)

/-- Across all parameters `m`, `v` (including `v = 0`) and `l`, the lower-censored Gaussian law
never has null singletons. -/
@[simp]
theorem not_nullSingletonClass_map_coe_projIci_gaussianReal (m : ℝ) (v : ℝ≥0) (l : ℝ) :
    ¬ NullSingletonClass ((gaussianReal m v).map fun x : ℝ ↦ (Set.projIci l x : ℝ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var, Measure.map_dirac' (by simp only [Set.coe_projIci]; fun_prop)]
    exact not_nullSingletonClass_dirac _
  · have := nullSingletonClass_gaussianReal (μ := m) hv
    rw [Measure.nullSingletonClass_map_coe_projIci_iff_of_nullSingletonClass]
    exact (gaussianReal_Iic_pos m hv l).ne'

/-- At positive variance, the cdf of the lower-censored Gaussian law at `l` is continuous at `x`
if and only if `x ≠ l`. -/
theorem continuousAt_cdf_map_coe_projIci_gaussianReal_iff (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (l x : ℝ) :
    ContinuousAt (cdf ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIci l y : ℝ))) x ↔ x ≠ l := by
  have := nullSingletonClass_gaussianReal (μ := m) hv
  simp [Measure.continuousAt_cdf_map_coe_projIci_iff_of_nullSingletonClass _ l x,
    (gaussianReal_Iic_pos m hv l).ne']

/-- Across all parameters `m`, `v` and `l`, the cdf of the lower-censored Gaussian law is not
continuous. -/
theorem not_continuous_cdf_map_coe_projIci_gaussianReal (m : ℝ) (v : ℝ≥0) (l : ℝ) :
    ¬ Continuous (cdf ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIci l y : ℝ))) := by
  rw [Measure.continuous_cdf_iff]
  exact not_nullSingletonClass_map_coe_projIci_gaussianReal m v l

/-! ### Upper-censored Gaussian laws -/

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
  simp [Measure.map_coe_projIic_singleton_ne_zero_iff_of_nullSingletonClass _ r x,
    (gaussianReal_Ici_pos m hv r).ne']

/-- At positive variance, the cutoff `r` carries positive mass under upper censoring. -/
theorem map_coe_projIic_gaussianReal_singleton_self_pos (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (r : ℝ) :
    0 < (gaussianReal m v).map (fun y : ℝ ↦ (Set.projIic r y : ℝ)) {r} :=
  pos_iff_ne_zero.mpr ((map_coe_projIic_gaussianReal_singleton_ne_zero_iff m hv r r).mpr rfl)

/-- Across all parameters `m`, `v` (including `v = 0`) and `r`, the upper-censored Gaussian law
never has null singletons. -/
@[simp]
theorem not_nullSingletonClass_map_coe_projIic_gaussianReal (m : ℝ) (v : ℝ≥0) (r : ℝ) :
    ¬ NullSingletonClass ((gaussianReal m v).map fun x : ℝ ↦ (Set.projIic r x : ℝ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var, Measure.map_dirac' (by simp only [Set.coe_projIic]; fun_prop)]
    exact not_nullSingletonClass_dirac _
  · have := nullSingletonClass_gaussianReal (μ := m) hv
    rw [Measure.nullSingletonClass_map_coe_projIic_iff_of_nullSingletonClass]
    exact (gaussianReal_Ici_pos m hv r).ne'

/-- At positive variance, the cdf of the upper-censored Gaussian law at `r` is continuous at `x`
if and only if `x ≠ r`. -/
theorem continuousAt_cdf_map_coe_projIic_gaussianReal_iff (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (r x : ℝ) :
    ContinuousAt (cdf ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIic r y : ℝ))) x ↔ x ≠ r := by
  have := nullSingletonClass_gaussianReal (μ := m) hv
  simp [Measure.continuousAt_cdf_map_coe_projIic_iff_of_nullSingletonClass _ r x,
    (gaussianReal_Ici_pos m hv r).ne']

/-- Across all parameters `m`, `v` and `r`, the cdf of the upper-censored Gaussian law is not
continuous. -/
theorem not_continuous_cdf_map_coe_projIic_gaussianReal (m : ℝ) (v : ℝ≥0) (r : ℝ) :
    ¬ Continuous (cdf ((gaussianReal m v).map fun y : ℝ ↦ (Set.projIic r y : ℝ))) := by
  rw [Measure.continuous_cdf_iff]
  exact not_nullSingletonClass_map_coe_projIic_gaussianReal m v r

end TauCeti.Probability
