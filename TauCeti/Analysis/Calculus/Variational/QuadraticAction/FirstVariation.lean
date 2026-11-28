/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.Variational.QuadraticAction.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.StronglyMeasurable.OperatorField
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# First variation of a quadratic action with square-integrable velocity

For continuous positions and square-integrable velocities, the quadratic kinetic action
admits affine variations. A compact buffer and bounded spatial derivatives provide an
integrable quadratic bound, so differentiation under the integral gives the first variation.
`TauCeti.exists_affine_compact_buffer` gives one compact subset of an open spatial domain
containing all sufficiently small affine variations of a continuous path.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 7.2.
* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped intervalIntegral ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

/-- A continuous affine variation of a compact path has a uniform buffer inside any open
spatial domain containing the path. -/
theorem exists_affine_compact_buffer [LocallyCompactSpace E] {a b : ℝ} {U : Set E}
    (hU : IsOpen U) (u η : ℝ → E) (hu : ContinuousOn u (Icc a b))
    (hη : ContinuousOn η (Icc a b)) (huU : MapsTo u (Icc a b) U) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ U ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ ε : ℝ, |ε| < δ → MapsTo (fun s ↦ u s + ε • η s) (Icc a b) K := by
  have hcompact := isCompact_Icc.image_of_continuousOn hu
  obtain ⟨K, hK, huK, hKU⟩ := exists_compact_between hcompact hU (image_subset_iff.mpr huU)
  obtain ⟨r, hr, hmargin⟩ := hcompact.exists_cthickening_subset_open isOpen_interior huK
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hη
  let C := max D 0
  have hC : 0 ≤ C := le_max_right _ _
  have hCp : 0 < C + 1 := by positivity
  let δ := min 1 (r / (C + 1))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hr hCp)
  have hδr : δ * (C + 1) ≤ r := (le_div_iff₀ hCp).mp (min_le_right _ _)
  refine ⟨K, hK, hKU, δ, hδ, min_le_left _ _, ?_⟩
  intro ε hε s hs
  have hηbound : ‖η s‖ ≤ C := (hD s hs).trans (le_max_left _ _)
  have hnorm : ‖ε • η s‖ < r := by
    rw [norm_smul, Real.norm_eq_abs]
    have hmul := mul_le_mul_of_nonneg_left hηbound (abs_nonneg ε)
    have hmul' := mul_le_mul_of_nonneg_right hε.le hC
    nlinarith
  apply interior_subset (hmargin ?_)
  apply Metric.mem_cthickening_of_dist_le _ (u s) _ _ (mem_image_of_mem u hs)
  simpa only [dist_eq_norm, add_sub_cancel_left] using hnorm.le

-- Cache the canonical operator-space structures used in the public coefficient types.
/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticActionDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticActionDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticActionBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticActionBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The canonical normed additive structure on the operator coefficient space. -/
local instance quadraticActionTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The canonical real normed-space structure on the operator coefficient space. -/
local instance quadraticActionTrilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The symmetric quadratic kinetic-plus-potential density has the displayed parameter
derivative under affine position and velocity variations. -/
theorem hasDerivAt_quadraticDensity_affine
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (V : E → ℝ)
    (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (DV : E →L[ℝ] ℝ)
    (x η v ν : E) (ε : ℝ)
    (hG : HasFDerivAt G DG (x + ε • η))
    (hV : HasFDerivAt V DV (x + ε • η))
    (hsym : ∀ z z' : E, G (x + ε • η) z z' = G (x + ε • η) z' z) :
    HasDerivAt
      (fun e : ℝ ↦ G (x + e • η) (v + e • ν) (v + e • ν) / 2 +
        V (x + e • η))
      (DG η (v + ε • ν) (v + ε • ν) / 2 +
        G (x + ε • η) (v + ε • ν) ν + DV η) ε := by
  have hx : HasDerivAt (fun e : ℝ ↦ x + e • η) η ε := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id ε).smul_const η).const_add x
  have hv : HasDerivAt (fun e : ℝ ↦ v + e • ν) ν ε := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id ε).smul_const ν).const_add v
  have hGc : HasDerivAt (fun e : ℝ ↦ G (x + e • η)) (DG η) ε :=
    by simpa only [Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt ε (l := G) (l' := DG) hG hx
  have hGvv := (hGc.clm_apply hv).clm_apply hv
  have hpot : HasDerivAt (fun e : ℝ ↦ V (x + e • η)) (DV η) ε :=
    HasFDerivAt.comp_hasDerivAt ε (l := V) (l' := DV) hV hx
  have hcalc := (hGvv.div_const 2).add hpot
  convert hcalc using 1
  simp only [add_apply]
  rw [hsym ν (v + ε • ν)]
  ring

/-- A uniform quadratic polynomial bounds the affine variation density by a constant times
one plus squared velocity. -/
private theorem quadratic_domination_polynomial {x D : ℝ} (hD : 0 ≤ D) :
    (x + D) ^ 2 / 2 + (x + D) + 1 ≤ (D ^ 2 + D + 3) * (1 + x ^ 2) := by
  nlinarith [sq_nonneg (x - D), sq_nonneg (x - 1),
    mul_nonneg hD (sq_nonneg x), mul_nonneg (sq_nonneg D) (sq_nonneg x)]

/-- Bounded coefficients and variation directions dominate the affine density derivative by an
integrable quadratic velocity bound. -/
private theorem norm_quadraticDensity_deriv_le
    (G : E →L[ℝ] E →L[ℝ] ℝ) (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : E →L[ℝ] ℝ) (v η ν : E) {ε C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : |ε| ≤ 1)
    (hG : ‖G‖ ≤ C) (hDG : ‖DG‖ ≤ C) (hDV : ‖DV‖ ≤ C)
    (hη : ‖η‖ ≤ D) (hν : ‖ν‖ ≤ D) :
    ‖DG η (v + ε • ν) (v + ε • ν) / 2 + G (v + ε • ν) ν + DV η‖ ≤
      C * D * (D ^ 2 + D + 3) * (1 + ‖v‖ ^ 2) := by
  let W := ‖v‖ + D
  have hv : ‖v + ε • ν‖ ≤ W := by
    calc
      ‖v + ε • ν‖ ≤ ‖v‖ + ‖ε • ν‖ := norm_add_le _ _
      _ = ‖v‖ + |ε| * ‖ν‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖v‖ + 1 * D := by gcongr
      _ = W := by rw [one_mul]
  have hDGη : ‖DG η‖ ≤ C * D :=
    (DG.le_opNorm η).trans (mul_le_mul hDG hη (norm_nonneg η) hC)
  have ht : ‖DG η (v + ε • ν) (v + ε • ν)‖ ≤ C * D * W ^ 2 := by
    calc
      _ ≤ ‖DG η‖ * ‖v + ε • ν‖ * ‖v + ε • ν‖ := (DG η).le_opNorm₂ _ _
      _ ≤ (C * D) * W * W := by gcongr
      _ = C * D * W ^ 2 := by ring
  have hg : ‖G (v + ε • ν) ν‖ ≤ C * W * D := by
    calc
      _ ≤ ‖G‖ * ‖v + ε • ν‖ * ‖ν‖ := G.le_opNorm₂ _ _
      _ ≤ C * W * D := by gcongr
  have hdv : ‖DV η‖ ≤ C * D :=
    (DV.le_opNorm η).trans (mul_le_mul hDV hη (norm_nonneg η) hC)
  calc
    _ ≤ (‖DG η (v + ε • ν) (v + ε • ν) / 2‖ + ‖G (v + ε • ν) ν‖) +
        ‖DV η‖ := (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (C * D * W ^ 2 / 2 + C * W * D) + C * D := by
      rw [norm_div, Real.norm_ofNat]
      gcongr
    _ = C * D * (W ^ 2 / 2 + W + 1) := by ring
    _ ≤ C * D * ((D ^ 2 + D + 3) * (1 + ‖v‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (quadratic_domination_polynomial hD)
        (mul_nonneg hC hD)
    _ = _ := by ring

/-- The three terms of the quadratic first variation are measurable under measurable data. -/
private theorem aestronglyMeasurable_quadraticFirstVariation {μ : Measure ℝ}
    {B : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {DB : ℝ → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ} {DV : ℝ → E →L[ℝ] ℝ}
    {η ν w : ℝ → E}
    (hB : AEStronglyMeasurable B μ) (hDB : AEStronglyMeasurable DB μ)
    (hDV : AEStronglyMeasurable DV μ) (hη : AEStronglyMeasurable η μ)
    (hν : AEStronglyMeasurable ν μ) (hw : AEStronglyMeasurable w μ) :
    AEStronglyMeasurable (fun s ↦ DB s (η s) (w s) (w s) / 2 +
      B s (w s) (ν s) + DV s (η s)) μ := by
  have hDη := (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ))
    |>.aestronglyMeasurable_comp₂ hDB hη
  have hDVη := (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂ hDV hη
  exact (((hDη.bilin_apply hw hw).div₀ aestronglyMeasurable_const).add
    (hB.bilin_apply hw hν)).add hDVη

private theorem quadraticAffine_integrability {a b δ C : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ)
    (K : Set E) (u w η ν : ℝ → E)
    (hu : ContinuousOn u (Icc a b)) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (hη : ContinuousOn η (Icc a b)) (hν : ContinuousOn ν (Icc a b))
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (DG : ℝ × E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : ℝ × E → E →L[ℝ] ℝ)
    (hGcont : ContinuousOn G (Icc a b ×ˢ K))
    (hVcont : ContinuousOn V (Icc a b ×ˢ K))
    (hDGcont : ContinuousOn DG (Icc a b ×ˢ K))
    (hDVcont : ContinuousOn DV (Icc a b ×ˢ K))
    (hmem : ∀ e ∈ Ioo (-δ) δ, ∀ s ∈ Icc a b, u s + e • η s ∈ K)
    (hcoeff : ∀ s ∈ Icc a b, ∀ x ∈ K, ‖G (s, x)‖ ≤ C) :
    (∀ e ∈ Ioo (-δ) δ, AEStronglyMeasurable (fun s ↦
      G (s, u s + e • η s) (w s + e • ν s) (w s + e • ν s) / 2 +
        V (s, u s + e • η s)) (volume.restrict (Icc a b))) ∧
    IntervalIntegrable (fun s ↦ G (s, u s) (w s) (w s) / 2 + V (s, u s)) volume a b ∧
    AEStronglyMeasurable (fun s ↦ DG (s, u s) (η s) (w s) (w s) / 2 +
      G (s, u s) (w s) (ν s) + DV (s, u s) (η s)) (volume.restrict (Icc a b)) := by
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hΓ (e : ℝ) : ContinuousOn (fun s ↦ (s, u s + e • η s)) (Icc a b) :=
    continuousOn_id.prodMk (hu.add (continuousOn_const.smul hη))
  have hΓmem (e : ℝ) (he : e ∈ Ioo (-δ) δ) :
      MapsTo (fun s ↦ (s, u s + e • η s)) (Icc a b) (Icc a b ×ˢ K) :=
    fun s hs ↦ ⟨hs, hmem e he s hs⟩
  have hGε (e : ℝ) (he : e ∈ Ioo (-δ) δ) :
      ContinuousOn (fun s ↦ G (s, u s + e • η s)) (Icc a b) :=
    hGcont.comp (hΓ e) (hΓmem e he)
  have hVε (e : ℝ) (he : e ∈ Ioo (-δ) δ) :
      ContinuousOn (fun s ↦ V (s, u s + e • η s)) (Icc a b) :=
    hVcont.comp (hΓ e) (hΓmem e he)
  have hG0 : ContinuousOn (fun s ↦ G (s, u s)) (Icc a b) := by
    simpa only [zero_smul, add_zero] using hGε 0 hzero
  have hV0 : ContinuousOn (fun s ↦ V (s, u s)) (Icc a b) := by
    simpa only [zero_smul, add_zero] using hVε 0 hzero
  have hDG0 : ContinuousOn (fun s ↦ DG (s, u s)) (Icc a b) := by
    simpa only [zero_smul, add_zero, Function.comp_def] using hDGcont.comp (hΓ 0) (hΓmem 0 hzero)
  have hDV0 : ContinuousOn (fun s ↦ DV (s, u s)) (Icc a b) := by
    simpa only [zero_smul, add_zero, Function.comp_def] using hDVcont.comp (hΓ 0) (hΓmem 0 hzero)
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    have hv := hw.aestronglyMeasurable.add
      ((hν.aestronglyMeasurable measurableSet_Icc).const_smul e)
    exact ((MeasureTheory.AEStronglyMeasurable.bilin_apply
      ((hGε e he).aestronglyMeasurable measurableSet_Icc) hv hv).div₀
        aestronglyMeasurable_const).add ((hVε e he).aestronglyMeasurable measurableSet_Icc)
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    have hB : MemLp (fun s ↦ G (s, u s)) ⊤ (volume.restrict (Icc a b)) := by
      apply memLp_top_of_bound (hG0.aestronglyMeasurable measurableSet_Icc) C
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact hcoeff s hs _ (by
        simpa only [zero_smul, add_zero] using hmem 0 hzero s hs)
    have hkin := hB.integrable_bilinear_apply hw hw
    exact (hkin.div_const 2).add hV0.integrableOn_Icc
  · exact aestronglyMeasurable_quadraticFirstVariation
      (hG0.aestronglyMeasurable measurableSet_Icc) (hDG0.aestronglyMeasurable measurableSet_Icc)
      (hDV0.aestronglyMeasurable measurableSet_Icc) (hη.aestronglyMeasurable measurableSet_Icc)
      (hν.aestronglyMeasurable measurableSet_Icc) hw.aestronglyMeasurable

/-- Dominated differentiation computes the actual quadratic-plus-potential action derivative for
L² velocities and compactly buffered affine variations. -/
theorem hasDerivAt_quadraticAction_affine {a b δ C D : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (K : Set E) (u w η ν : ℝ → E)
    (hu : ContinuousOn u (Icc a b)) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (hη : ContinuousOn η (Icc a b)) (hν : ContinuousOn ν (Icc a b))
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (DG : ℝ × E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : ℝ × E → E →L[ℝ] ℝ)
    (hGcont : ContinuousOn G (Icc a b ×ˢ K))
    (hVcont : ContinuousOn V (Icc a b ×ˢ K))
    (hDGcont : ContinuousOn DG (Icc a b ×ˢ K))
    (hDVcont : ContinuousOn DV (Icc a b ×ˢ K))
    (hmem : ∀ e ∈ Ioo (-δ) δ, ∀ s ∈ Icc a b, u s + e • η s ∈ K)
    (hGderiv : ∀ s ∈ Icc a b, ∀ x ∈ K, HasFDerivAt (fun x ↦ G (s, x)) (DG (s, x)) x)
    (hVderiv : ∀ s ∈ Icc a b, ∀ x ∈ K, HasFDerivAt (fun x ↦ V (s, x)) (DV (s, x)) x)
    (hsym : ∀ s ∈ Icc a b, ∀ x ∈ K, ∀ v v' : E, G (s, x) v v' = G (s, x) v' v)
    (hcoeff : ∀ s ∈ Icc a b, ∀ x ∈ K,
      ‖G (s, x)‖ ≤ C ∧ ‖DG (s, x)‖ ≤ C ∧ ‖DV (s, x)‖ ≤ C)
    (hdir : ∀ s ∈ Icc a b, ‖η s‖ ≤ D ∧ ‖ν s‖ ≤ D) :
    IntervalIntegrable
      (fun s ↦ DG (s, u s) (η s) (w s) (w s) / 2 + G (s, u s) (w s) (ν s) +
        DV (s, u s) (η s)) volume a b ∧
    HasDerivAt
      (fun e : ℝ ↦ quadraticAction G V (fun s ↦ u s + e • η s)
        (fun s ↦ w s + e • ν s) a b)
      (∫ s in a..b,
        DG (s, u s) (η s) (w s) (w s) / 2 + G (s, u s) (w s) (ν s) +
          DV (s, u s) (η s)) 0 := by
  have hmem0 : u a ∈ K := by
    simpa only [zero_smul, add_zero] using hmem 0 ⟨neg_lt_zero.mpr hδ, hδ⟩ a ⟨le_rfl, hab⟩
  have hC : 0 ≤ C := (norm_nonneg _).trans (hcoeff a ⟨le_rfl, hab⟩ (u a) hmem0).1
  have hD : 0 ≤ D := (norm_nonneg _).trans (hdir a ⟨le_rfl, hab⟩).1
  let f (e s : ℝ) :=
    G (s, u s + e • η s) (w s + e • ν s) (w s + e • ν s) / 2 +
      V (s, u s + e • η s)
  let f' (e s : ℝ) :=
    DG (s, u s + e • η s) (η s) (w s + e • ν s) (w s + e • ν s) / 2 +
      G (s, u s + e • η s) (w s + e • ν s) (ν s) + DV (s, u s + e • η s) (η s)
  let bound (s : ℝ) := C * D * (D ^ 2 + D + 3) * (1 + ‖w s‖ ^ 2)
  have hnhds : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ
  have hsub : uIoc a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]
    exact Ioc_subset_Icc_self
  obtain ⟨hfm, hfint, hf'm⟩ := quadraticAffine_integrability hab hδ K u w η ν hu hw hη hν
    G V DG DV hGcont hVcont hDGcont hDVcont hmem
    (fun s hs x hx ↦ (hcoeff s hs x hx).1)
  have hfint : IntervalIntegrable (f 0) volume a b := by
    simpa only [f, zero_smul, add_zero] using hfint
  have hf'm : AEStronglyMeasurable (f' 0) (volume.restrict (Icc a b)) := by
    simpa only [f', zero_smul, add_zero] using hf'm
  have hboundint : IntervalIntegrable bound volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact ((integrable_const (1 : ℝ)).add hw.norm.integrable_sq).const_mul (C * D * (D ^ 2 + D + 3))
  have hdifferentiation := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := f') (bound := bound) hnhds
    (by
      filter_upwards [hnhds] with e he
      exact (hfm e he).mono_measure (Measure.restrict_mono hsub le_rfl)) hfint
    (hf'm.mono_measure (Measure.restrict_mono hsub le_rfl))
    (by
      filter_upwards with s hs e he
      have hcs := hcoeff s (hsub hs) _ (hmem e he s (hsub hs))
      exact norm_quadraticDensity_deriv_le _ _ _ (w s) (η s) (ν s) hC hD
        ((abs_lt.mpr he).le.trans hδ1) hcs.1 hcs.2.1 hcs.2.2
        (hdir s (hsub hs)).1 (hdir s (hsub hs)).2)
    hboundint
    (by
      filter_upwards with s hs e he
      exact hasDerivAt_quadraticDensity_affine (fun x ↦ G (s, x)) (fun x ↦ V (s, x))
        _ _ (u s) (η s) (w s) (ν s) e
        (hGderiv s (hsub hs) _ (hmem e he s (hsub hs)))
        (hVderiv s (hsub hs) _ (hmem e he s (hsub hs)))
        (hsym s (hsub hs) _ (hmem e he s (hsub hs))))
  simpa only [quadraticAction_def, f, f', zero_smul, add_zero] using hdifferentiation

end

end TauCeti
