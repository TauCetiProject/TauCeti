/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Covering.Besicovitch
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Essential convexity from interval sections

Let `s` be a Lebesgue-measurable set in a finite-dimensional real inner product space. Suppose
that in a unit direction `e`, almost every parallel line section `{t | y + t • e ∈ s}` agrees
almost everywhere with an interval (a possibly empty or unbounded `OrdConnected` subset of
`ℝ`). Then, along each line in direction `e`, the Lebesgue density points of `s` (the points at
which the proportion of `s` in small closed balls tends to one) form an interval. Consequently,
if `s` has interval sections in every unit direction, its density points form a convex set,
and `s` agrees almost everywhere with a convex set.

The proof compares cylinders around the line through two density points `x` and `x + d • e`.
On almost every parallel line, either the section meets both end cylinders, and then by the
interval property it covers the middle cylinder up to a null set, or it misses one end cylinder
entirely, and then that cylinder loses at least as much as the middle one. Integrating over
the transverse coordinates bounds the missing volume of the middle cylinder by the missing
volumes of the end cylinders. These are negligible by Mathlib's
`MeasureTheory.Measure.tendsto_addHaar_inter_smul_zero_of_density_zero_aux2`. Only the
exceptional transverse null set of the direction `e` is used.

Interval sections in every direction are the necessary condition for equality in Steiner's
perimeter inequality found by Cagnetti, Colombo, De Philippis and Maggi, *Rigidity of equality
cases in Steiner's perimeter inequality*, Anal. PDE 7 (2014), §1.2 and Theorem A. Essential
convexity reduces the equality analysis to convex representatives.

## Main results

* `TauCeti.tendsto_volume_inter_closedBall_add_smul_div_of_ae_lineSection_ordConnected`: a point
  between two density points on a line in a direction with interval sections is a density point.
* `TauCeti.convex_setOf_tendsto_volume_inter_closedBall_div`: with interval sections in every
  direction, the set of density points is convex.
* `TauCeti.exists_convex_ae_eq_of_ae_lineSection_ordConnected`: with interval sections in every
  direction, the set agrees almost everywhere with a convex set.
-/

public section

open Filter Metric MeasureTheory Set Topology
open scoped ENNReal Pointwise RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e : E}

/-- On a line where `S` agrees a.e. with an interval, the part of a middle window missed by `S`
is at most the total missed in two windows of the same length on either side. -/
private theorem volume_closedBall_diff_le {S I : Set ℝ} (hI : I.OrdConnected)
    (hSI : S =ᵐ[volume] I) {a b c r : ℝ} (hab : a + r ≤ b - r) (hbc : b + r ≤ c - r) :
    volume (closedBall b r \ S) ≤ volume (closedBall a r \ S) + volume (closedBall c r \ S) := by
  have hdiff (A : Set ℝ) : volume (A \ S) = volume (A \ I) :=
    measure_congr (EventuallyEqSet.diff .rfl hSI)
  simp only [hdiff]
  have hfull (d : ℝ) (hd : Disjoint (closedBall d r) I) :
      volume (closedBall b r \ I) ≤ volume (closedBall d r \ I) := by
    rw [hd.sdiff_eq_left]
    calc volume (closedBall b r \ I) ≤ volume (closedBall b r) := measure_mono sdiff_subset
      _ = volume (closedBall d r) := by rw [Real.volume_closedBall, Real.volume_closedBall]
  by_cases ha : Disjoint (closedBall a r) I
  · exact (hfull a ha).trans le_self_add
  by_cases hc : Disjoint (closedBall c r) I
  · exact (hfull c hc).trans le_add_self
  obtain ⟨u, hu, huI⟩ := not_disjoint_iff.1 ha
  obtain ⟨v, hv, hvI⟩ := not_disjoint_iff.1 hc
  rw [Real.closedBall_eq_Icc] at hu hv
  have hsub : closedBall b r ⊆ I := by
    intro t ht
    rw [Real.closedBall_eq_Icc] at ht
    exact hI.out huI hvI ⟨by linarith [hu.2, ht.1], by linarith [hv.1, ht.2]⟩
  rw [sdiff_eq_empty.2 hsub, measure_empty]
  exact zero_le

/-- The closed unit cylinder around the line `ℝ ∙ e`, of unit radius and half-length one. -/
private def lineCylinder (e : E) : Set E :=
  {v | ‖v - ⟪e, v⟫ • e‖ ≤ 1 ∧ |⟪e, v⟫| ≤ 1}

private theorem mem_singleton_add_smul_lineCylinder (w : E) {r : ℝ} (hr : 0 < r) (v : E) :
    v ∈ {w} + r • lineCylinder e ↔ ‖v - w - ⟪e, v - w⟫ • e‖ ≤ r ∧ |⟪e, v - w⟫| ≤ r := by
  rw [singleton_add, image_add_left, mem_preimage, mem_smul_set_iff_inv_smul_mem₀ hr.ne',
    neg_add_eq_sub]
  simp only [lineCylinder, mem_ofPred_eq, inner_smul_right, ← smul_smul, ← smul_sub, norm_smul,
    abs_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_le_iff₀ hr, mul_one]

private theorem isClosed_lineCylinder : IsClosed (lineCylinder e) := by
  simp only [lineCylinder, ofPred_and]
  exact (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)

private theorem closedBall_subset_lineCylinder (he : ‖e‖ = 1) :
    closedBall (0 : E) 1 ⊆ lineCylinder e := by
  intro v hv
  rw [mem_closedBall_zero_iff] at hv
  have hproj := (ℝ ∙ e)ᗮ.norm_starProjection_apply_le v
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_unit_singleton ℝ he]
    at hproj
  refine ⟨hproj.trans hv, ?_⟩
  calc |⟪e, v⟫| ≤ ‖e‖ * ‖v‖ := abs_real_inner_le_norm e v
    _ ≤ 1 := by rw [he, one_mul]; exact hv

private theorem lineCylinder_subset_closedBall (he : ‖e‖ = 1) :
    lineCylinder e ⊆ closedBall (0 : E) 2 := by
  rintro v ⟨h₁, h₂⟩
  rw [mem_closedBall_zero_iff]
  calc ‖v‖ = ‖(v - ⟪e, v⟫ • e) + ⟪e, v⟫ • e‖ := by rw [sub_add_cancel]
    _ ≤ ‖v - ⟪e, v⟫ • e‖ + ‖⟪e, v⟫ • e‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs]
      exact add_le_add h₁ h₂
    _ = 2 := by norm_num

private theorem closedBall_eq_singleton_add_smul (w : E) {r : ℝ} (hr : 0 < r) :
    closedBall w r = {w} + r • closedBall (0 : E) 1 := by
  rw [← affinity_unitClosedBall hr.le, ← singleton_vadd, vadd_eq_add]

private theorem closedBall_subset_singleton_add_smul_lineCylinder (he : ‖e‖ = 1) (w : E) {r : ℝ}
    (hr : 0 < r) : closedBall w r ⊆ {w} + r • lineCylinder e := by
  rw [closedBall_eq_singleton_add_smul w hr]
  exact add_subset_add_left (smul_set_mono (closedBall_subset_lineCylinder he))

/-- The parallel sections of the part of a cylinder around `x + c • e` missed by `s`. -/
private theorem lineSection_compl_inter_singleton_add_smul_lineCylinder (he : ‖e‖ = 1)
    (s : Set E) (x : E) (c : ℝ) {r : ℝ} (hr : 0 < r) (y : (ℝ ∙ e)ᗮ) :
    {t : ℝ | (y : E) + t • e ∈ sᶜ ∩ ({x + c • e} + r • lineCylinder e)} =
      {_t : ℝ | ‖(y : E) - (x - ⟪e, x⟫ • e)‖ ≤ r} ∩
        (closedBall (⟪e, x⟫ + c) r \ {t : ℝ | (y : E) + t • e ∈ s}) := by
  have hy : ⟪e, (y : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  ext t
  have hinner : ⟪e, (y : E) + t • e - (x + c • e)⟫ = t - (⟪e, x⟫ + c) := by
    simp only [inner_sub_right, inner_add_right, inner_smul_right, hy, hee]
    ring
  have hperp : (y : E) + t • e - (x + c • e) - (t - (⟪e, x⟫ + c)) • e =
      (y : E) - (x - ⟪e, x⟫ • e) := by
    simp only [sub_smul, add_smul]
    abel
  simp only [mem_inter_iff, mem_compl_iff, mem_singleton_add_smul_lineCylinder _ hr, hinner,
    hperp, mem_ofPred_eq, Set.mem_sdiff, mem_closedBall, Real.dist_eq]
  tauto

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem measurableSet_singleton_add_smul_lineCylinder (w : E) (r : ℝ) :
    MeasurableSet ({w} + r • lineCylinder e) := by
  rw [singleton_add, image_add_left]
  exact (continuous_const_add (-w)).measurable
    (isClosed_lineCylinder.measurableSet.const_smul₀ r)

/-- In a direction with interval sections, the volume of the part of a middle cylinder missed by
`s` is at most the sum of the corresponding volumes for two cylinders further along the line. -/
private theorem volume_compl_inter_lineCylinder_le (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume)
    (h : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, I.OrdConnected ∧
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (x : E) {c d r : ℝ} (hr : 0 < r) (hc : 2 * r ≤ c) (hcd : c + 2 * r ≤ d) :
    volume (sᶜ ∩ ({x + c • e} + r • lineCylinder e)) ≤
      volume (sᶜ ∩ ({x} + r • lineCylinder e)) +
        volume (sᶜ ∩ ({x + d • e} + r • lineCylinder e)) := by
  have hQ (w : E) : NullMeasurableSet (sᶜ ∩ ({w} + r • lineCylinder e)) volume :=
    hs.compl.inter (measurableSet_singleton_add_smul_lineCylinder w r).nullMeasurableSet
  rw [volume_eq_lintegral_volume_lineSection e he (hQ _),
    volume_eq_lintegral_volume_lineSection e he (hQ _),
    volume_eq_lintegral_volume_lineSection e he (hQ _),
    ← lintegral_add_left' (aemeasurable_volume_lineSection e he (hQ x))]
  refine lintegral_mono_ae ?_
  filter_upwards [h] with y ⟨I, hI, hSI⟩
  have hx := lineSection_compl_inter_singleton_add_smul_lineCylinder he s x 0 hr y
  rw [zero_smul, add_zero, add_zero] at hx
  rw [hx, lineSection_compl_inter_singleton_add_smul_lineCylinder he s x c hr y,
    lineSection_compl_inter_singleton_add_smul_lineCylinder he s x d hr y]
  by_cases hy : ‖(y : E) - (x - ⟪e, x⟫ • e)‖ ≤ r
  · simp only [hy, ofPred_true, univ_inter]
    exact volume_closedBall_diff_le hI hSI (by linarith) (by linarith)
  · simp [hy]

/-- At a density point `x` of a null-measurable set `s`, the volume of the part of the cylinder
`{x} + r • lineCylinder e` missed by `s` is small compared with the volume of `closedBall x r`. -/
private theorem tendsto_volume_compl_inter_lineCylinder_div (he : ‖e‖ = 1) {s : Set E}
    (hs : NullMeasurableSet s volume) {x : E}
    (hx : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
      (𝓝 1)) :
    Tendsto (fun r => volume (sᶜ ∩ ({x} + r • lineCylinder e)) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by
  have hball : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      volume (closedBall x r) ≠ 0 ∧ volume (closedBall x r) ≠ ∞ := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    exact ⟨(measure_closedBall_pos volume x hr).ne', measure_closedBall_lt_top.ne⟩
  refine (Measure.tendsto_addHaar_inter_smul_zero_of_density_zero_aux2 volume sᶜ x
    ((hs.tendsto_measure_compl_inter_div_iff hball).2 hx) (lineCylinder e) (closedBall 0 1)
    (measure_closedBall_pos volume 0 one_pos).ne' 2 two_pos
    (lineCylinder_subset_closedBall he)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [← closedBall_eq_singleton_add_smul x hr]

/-- **Density points along a line with interval sections.** Suppose that almost every line
section of a Lebesgue-measurable set `s` in the unit direction `e` agrees a.e. with an interval.
If `x` and `x + d • e` are Lebesgue density points of `s`, then so is every `x + c • e` with
`0 ≤ c ≤ d`. -/
theorem tendsto_volume_inter_closedBall_add_smul_div_of_ae_lineSection_ordConnected
    (he : ‖e‖ = 1) {s : Set E} (hs : NullMeasurableSet s volume)
    (h : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, I.OrdConnected ∧
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    {x : E} {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d)
    (hx : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
      (𝓝 1))
    (hd : Tendsto (fun r => volume (s ∩ closedBall (x + d • e) r) /
      volume (closedBall (x + d • e) r)) (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun r => volume (s ∩ closedBall (x + c • e) r) /
      volume (closedBall (x + c • e) r)) (𝓝[>] 0) (𝓝 1) := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa using hx
  rcases hcd.eq_or_lt with rfl | hcd
  · exact hd
  have hball : ∀ᶠ r in 𝓝[>] (0 : ℝ), volume (closedBall (x + c • e) r) ≠ 0 ∧
      volume (closedBall (x + c • e) r) ≠ ∞ := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    exact ⟨(measure_closedBall_pos volume _ hr).ne', measure_closedBall_lt_top.ne⟩
  rw [← hs.tendsto_measure_compl_inter_div_iff hball]
  have hsum := (tendsto_volume_compl_inter_lineCylinder_div he hs hx).add
    (tendsto_volume_compl_inter_lineCylinder_div he hs hd)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  have hδ : (0 : ℝ) < min c (d - c) / 2 := by
    have : 0 < d - c := sub_pos.2 hcd
    positivity
  filter_upwards [Ioo_mem_nhdsGT hδ] with r ⟨hr, hrδ⟩
  have h₁ : 2 * r ≤ c := by linarith [min_le_left c (d - c)]
  have h₂ : c + 2 * r ≤ d := by linarith [min_le_right c (d - c)]
  rw [Measure.addHaar_closedBall_center volume (x + c • e),
    Measure.addHaar_closedBall_center volume x,
    Measure.addHaar_closedBall_center volume (x + d • e), ← ENNReal.add_div]
  gcongr
  calc volume (sᶜ ∩ closedBall (x + c • e) r)
      ≤ volume (sᶜ ∩ ({x + c • e} + r • lineCylinder e)) := by
        gcongr
        exact closedBall_subset_singleton_add_smul_lineCylinder he _ hr
    _ ≤ _ := volume_compl_inter_lineCylinder_le he hs h x hr h₁ h₂

/-- **Essential convexity.** If almost every line section of a Lebesgue-measurable set `s`, in
every unit direction, agrees a.e. with an interval, then the Lebesgue density points of `s` form
a convex set. -/
theorem convex_setOf_tendsto_volume_inter_closedBall_div {s : Set E}
    (hs : NullMeasurableSet s volume)
    (h : ∀ e : E, ‖e‖ = 1 → ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, I.OrdConnected ∧
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    Convex ℝ {x | Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 1)} := by
  intro x hx z hz a b ha hb hab
  rcases eq_or_ne x z with rfl | hxz
  · rwa [← add_smul, hab, one_smul]
  have hd : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz.symm)
  set e := ‖z - x‖⁻¹ • (z - x) with he_def
  have he : ‖e‖ = 1 := by rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hd.ne']
  have hz' : z = x + ‖z - x‖ • e := by
    rw [he_def, smul_smul, mul_inv_cancel₀ hd.ne', one_smul, add_sub_cancel]
  have hp : a • x + b • z = x + (b * ‖z - x‖) • e := by
    obtain rfl : a = 1 - b := by linarith
    rw [he_def, smul_smul, mul_assoc, mul_inv_cancel₀ hd.ne', mul_one]
    module
  rw [mem_ofPred_eq, hp]
  rw [hz'] at hz
  refine tendsto_volume_inter_closedBall_add_smul_div_of_ae_lineSection_ordConnected he hs
    (h e he) (by positivity) (mul_le_of_le_one_left hd.le (by linarith)) hx hz

/-- **Essential convexity.** A Lebesgue-measurable set whose line sections, in every unit
direction, almost all agree a.e. with intervals agrees almost everywhere with a convex set.
A canonical such set is its set of Lebesgue density points, by
`TauCeti.convex_setOf_tendsto_volume_inter_closedBall_div` and
`MeasureTheory.NullMeasurableSet.ae_eq_setOf_tendsto_measure_inter_div`. -/
theorem exists_convex_ae_eq_of_ae_lineSection_ordConnected {s : Set E}
    (hs : NullMeasurableSet s volume)
    (h : ∀ e : E, ‖e‖ = 1 → ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, ∃ I : Set ℝ, I.OrdConnected ∧
      {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    ∃ K : Set E, Convex ℝ K ∧ s =ᵐ[volume] K :=
  ⟨_, convex_setOf_tendsto_volume_inter_closedBall_div hs h,
    hs.ae_eq_setOf_tendsto_measure_inter_div⟩

end TauCeti
